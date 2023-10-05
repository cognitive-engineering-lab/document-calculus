(* This module implements the extensions to the document calculus.

   These extensions operate mostly in "user space" rather than at the language level,
   so it's clearer to implement the extensions shallowly within OCaml rather than
   deeply in System F. *)


(* These type definitions are the same as the DArtTProgNested in article.ml,
   but much more readable thanks to OCaml's syntax and sugar.

   See Section 3.4.2 for the formal model of these types. *) 
module Node = struct
  type 'a struct_node = string * (string * string) list * 'a
  [@@deriving show]

  type t = NText of string | NNode of t list struct_node
  [@@deriving show]

  type 'a fragment = FBase of 'a | FList of 'a fragment list
  type fnode = FText of string | FNode of fnode fragment struct_node

  let rec elim_frags (f : fnode fragment) : t list = 
    match f with
    | FBase base -> (match base with
        | FText s -> [NText s]
        | FNode (tag, attrs, children) -> [NNode (tag, attrs, elim_frags children)])
    | FList list -> List.concat (List.map elim_frags list)
end


(* Implementation of Section 4.1. Automatically generates section numbers
   and reference labels from the document structure, and checks for invalid
   references. *)
module References = struct
  type id_ctxt = (string * int list) list
  [@@deriving show]

  let rec section_ids_at_depth (n : Node.t) (d : int list) : id_ctxt * int list =
    let (k, ks) = match d with 
      | [] -> failwith "section_ids_at_depth: empty depth"
      | k :: ks -> (k, ks) in
    match n with 
    | NText _ -> ([], k :: ks)
    | NNode (tag, attrs, children) -> 
      (match (tag, List.assoc_opt "id" attrs) with
       | ("section", Some id) ->
         let ctx = section_ids_at_depth_list children (1 :: k :: ks) in
         ((id, k :: ks) :: ctx, (k + 1) :: ks)
       | _ -> 
         let ctx = section_ids_at_depth_list children (k :: ks) in
         (ctx, k :: ks))
  and section_ids_at_depth_list children d =
    let (ctx, _) = List.fold_left (fun (ctx, d) n' -> 
        let (ctx', d') = section_ids_at_depth n' d in
        (ctx @ ctx', d')) ([], d) children  in
    ctx

  let section_ids (n : Node.t) : id_ctxt = 
    let (ctx, _) = section_ids_at_depth n [1] in ctx

  let rec valid (ctx : id_ctxt) (n : Node.t) : bool = 
    match n with
    | NText _ -> true
    | NNode (tag, attrs, children) ->
      (match (tag, List.assoc_opt "target" attrs) with
       | ("ref", Some id) -> List.mem_assoc id ctx
       | _ -> List.for_all (valid ctx) children)

  let section_number_to_string (n : int list) : string = 
    Stdlib.String.concat "." (List.map string_of_int (List.rev n))

  let rec replace_refs (ctx : id_ctxt) (n : Node.t) : Node.t = 
    match n with
    | NText s -> NText s
    | NNode (tag, attrs, children) ->
      (match (tag, List.assoc_opt "target" attrs) with
       | ("ref", Some id) -> NText (section_number_to_string (List.assoc id ctx))
       | _ -> NNode (tag, attrs, List.map (replace_refs ctx) children))
end

(* Implementation of Section 4.2. Converts a document from a pre-forested 
   intermediate representation into the final format by breaking newlines
   into paragraphs. *)
module Reforestation = struct
  let is_block tag = List.mem tag ["section"; "para"; "h1"]

  let rec reforest (ns : Node.t list) (par : Node.t list) : Node.t list = 
    let flush_par = Node.NNode ("para", [], List.rev par) in
    match ns with
    | [] -> [flush_par]
    | n :: ns' ->
      (match n with 
       | NText "\n\n" -> flush_par :: reforest ns' []
       | NText s -> reforest ns' (NText s :: par)
       | NNode (tag, attrs, children) -> 
         if is_block tag then
           flush_par :: NNode (tag, attrs, reforest children []) :: reforest ns' []
         else
           reforest ns' (NNode (tag, attrs, children) :: par))
end

(* Implementation of Section 4.3. Defines a simple virtual DOM with 
   stateful components, along with functions to update the tree with signals
   and then convert it to a final article. *)
module Reactivity = struct
  type signal = string         
  type comp_id = int
  type inst_id = int

  (* Technical note: we need a recursive module so we can define 
     mutually recursive types where one of them involves a module (i.e., Instance). *)
  module rec T : sig
    (* A component is a tree node with persistent state. *)
    type ('props, 'state) component = {      
      (* Initialization function converts properties to state. *)
      init : 'props -> 'state;

      (* Update function changes state in response to a signal. *)
      update : signal -> 'state -> 'state;

      (* View function converts the state into a virtual DOM tree (including components). *)
      view : 'state -> T.rnode;

      (* Internal identifier used to determine whether two components are the same. *)
      id : comp_id;
    }

    (* An instance is a realization of a component with a particular set of
       properties and state.

       Note that we have to make Instance a module so we can use it as an existential
       type, i.e. to erase its props/state types and allow the component tree
       to hold many component instances of different types. *)
    module type Instance = sig
      type props
      type state

      val id : inst_id
      val com : (props, state) T.component
      val props : props
      val state : state
      val node : T.rnode
    end

    type defprops = (string * string) list
    module type JsonPropInstance = Instance with type props = defprops

    (* The type of the virtual DOM. Basically a document tree with instances. *)
    type rnode = 
      | RText of string 
      | RNode of rnode list Node.struct_node 
      | RInstance of (module T.JsonPropInstance)
  end = T
  open T

  (* Creates a new instance by erasing its types. *)
  let erase_instance (type a) (type b) (id : inst_id) (com : (a, b) component) (props : a) (state : b) (node: rnode) : (module Instance with type props = a) =
    (module struct
      type props = a
      type state = b

      let id = id
      let com = com
      let props = props
      let state = state
      let node = node
    end)

  (* Generates a new instance ID from a hidden counter. *)
  let gen_inst_id : unit -> inst_id =
    let counter = ref 0 in
    fun () -> 
      let id = !counter in
      counter := id + 1;
      id

  (* Generates a new component ID from a hidden counter. *)
  let gen_comp_id : unit -> comp_id =
    let counter = ref 0 in
    fun () -> 
      let id = !counter in
      counter := id + 1;
      id

  (* Creates a new instance from a component definition and a set of properties. *)
  let instantiate (type a) (type b) (com : (a, b) component) (props : a) : (module Instance with type props = a) = 
    let state = com.init props in
    let node = com.view state in
    let id = gen_inst_id () in  
    erase_instance id com props state node

  (* A representation of user-provided events. *)
  type signal_map = (inst_id * signal) list

  (* Steps a VDOM tree to a new VDOM tree given the input signals. *)
  let rec doc_step (signals : signal_map) (n : rnode) : rnode =
    match n with
    | RText _ -> n
    | RNode (tag, attrs, children) -> 
      let children' = List.map (doc_step signals) children in
      RNode (tag, attrs, children')
    | RInstance (module I) ->
      (match List.assoc_opt I.id signals with
       | Some signal ->
         let state' = I.com.update signal I.state in
         let node' = I.com.view state' in
         RInstance (erase_instance I.id I.com I.props state' (reconcile signals I.node node'))
       | None ->
         RInstance (erase_instance I.id I.com I.props I.state (doc_step signals I.node)))

  (* Reconciles two trees, persisting components from the old tree when applicable. *)
  and reconcile (signals : signal_map) (n : rnode) (n' : rnode) : rnode =
    match (n, n') with
    | (RNode (tag, attrs, children), RNode (tag', attrs', children')) ->
      if tag = tag' && attrs = attrs' && List.length children = List.length children'   then
        let children'' = List.map2 (reconcile signals) children children' in
        RNode (tag, attrs, children'')
      else
        n'
    | (RInstance (module I), RInstance (module I')) ->
      if I.com.id = I'.com.id && I.props = I'.props then 
        doc_step signals n
      else
        n'      
    | _ -> n'

  (* Converts a VDOM tree into a normal document tree, i.e. removing instances. *)
  let rec doc_view (n : rnode) : Node.t = 
    match n with
    | RText s -> NText s
    | RNode (tag, attrs, children) ->
      NNode (tag, attrs, List.map doc_view children)
    | RInstance (module I) -> doc_view I.node
end