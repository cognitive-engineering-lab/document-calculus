(* module StdString = Stdlib.String

   type 'a struct_node = string * (string * string) list * 'a
   [@@deriving show]

   type node = NText of string | NNode of node list struct_node
   [@@deriving show]

   type 'a fragment = FBase of 'a | FList of 'a fragment list
   type fnode = FText of string | FNode of fnode fragment struct_node

   let rec elim_frags (f : fnode fragment) : node list = 
   match f with
   | FBase base -> (match base with
      | FText s -> [NText s]
      | FNode (tag, attrs, children) -> [NNode (tag, attrs, elim_frags children)])
   | FList list -> List.concat (List.map elim_frags list)

   type id_ctxt = (string * int list) list
   [@@deriving show]

   let rec section_ids_at_depth (n : node) (d : int list) : id_ctxt * int list =
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

   let section_ids (n : node) : id_ctxt = 
   let (ctx, _) = section_ids_at_depth n [1] in ctx

   let rec valid (ctx : id_ctxt) (n : node) : bool = 
   match n with
   | NText _ -> true
   | NNode (tag, attrs, children) ->
    (match (tag, List.assoc_opt "target" attrs) with
     | ("ref", Some id) -> List.mem_assoc id ctx
     | _ -> List.for_all (valid ctx) children)

   let section_number_to_string (n : int list) : string = 
   StdString.concat "." (List.map string_of_int (List.rev n))

   let rec replace_refs (ctx : id_ctxt) (n : node) : node = 
   match n with
   | NText s -> NText s
   | NNode (tag, attrs, children) ->
    (match (tag, List.assoc_opt "target" attrs) with
     | ("ref", Some id) -> NText (section_number_to_string (List.assoc id ctx))
     | _ -> NNode (tag, attrs, List.map (replace_refs ctx) children))

   let is_block tag = List.mem tag ["section"; "para"; "h1"]

   let rec reforest (ns : node list) (par : node list) : node list = 
   let flush_par = NNode ("para", [], List.rev par) in
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

   type signal = string         
   type comp_id = int
   type inst_id = int

   module rec React : sig
   type ('props, 'state) component = {
    id : comp_id;
    init : 'props -> 'state;
    update : signal -> 'state -> 'state;
    view : 'state -> React.rnode;
   }

   module type Instance = sig
    type props
    type state

    val id : inst_id
    val com : (props, state) React.component
    val props : props
    val state : state
    val node : React.rnode
   end

   type defprops = (string * string) list
   module type JsonPropInstance = Instance with type props = defprops

   type rnode = 
    | RText of string 
    | RNode of rnode list struct_node 
    | RInstance of (module React.JsonPropInstance)
   end = React
   open React

   let instance (type a) (type b) (id : inst_id) (com : (a, b) React.component) (props : a) (state : b) (node: rnode) : (module Instance with type props = a) =
   (module struct
    type props = a
    type state = b

    let id = id
    let com = com
    let props = props
    let state = state
    let node = node
   end)

   let gen_inst_id  :unit -> inst_id=
   let counter = ref 0 in
   fun () -> 
    let id = !counter in
    counter := id + 1;
    id


   let gen_comp_id : unit -> comp_id =
   let counter = ref 0 in
   fun () -> 
    let id = !counter in
    counter := id + 1;
    id

   let instantiate (type a) (type b) (com : (a, b) component) (props : a) : (module Instance with type props = a) = 
   let state = com.init props in
   let node = com.view state in
   let id = gen_inst_id () in  
   instance id com props state node

   type signal_map = (inst_id * signal) list

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
       RInstance (instance I.id I.com I.props state' (reconcile signals I.node node'))
     | None ->
       RInstance (instance I.id I.com I.props I.state (doc_step signals I.node)))
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

   let rec doc_view (n : rnode) : node = 
   match n with
   | RText s -> NText s
   | RNode (tag, attrs, children) ->
    NNode (tag, attrs, List.map doc_view children)
   | RInstance (module I) -> doc_view I.node *)
