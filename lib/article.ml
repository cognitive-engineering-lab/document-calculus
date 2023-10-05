[@@@warning "-partial-match"]

(* This module provides the D^Article levels of the document calculus.contents

   Note: we do not implement an OCaml model for D^Article_Lit or D^Article_TLit, 
   as neither have any actual implementation details.
*)

open Base
open String
open Bindlib

(* D^Article_Prog level of the document calculus. 
   Adds a standard library of node types for attributed, tagged trees. 
   Does not require any changes to the language. *)
module DArtProg = struct
  open DStrLit
  open DStrProg
  open Prelude

  (* Type of node attributes. *)
  let tyattr = _TProd _TString _TString

  (* Type of the interior of a node. *)
  let tystructnode ty = _TProd _TString (_TProd (tylist tyattr) ty)

  (* Type of a document node. *)
  let tynode = 
    let node = mktfree "node" in
    _TRec node (_TSum _TString (tystructnode (tylist (_TVar node))))

  (* The recursive type unfolded. *)
  let tynodebody = _TSum _TString (tystructnode (tylist tynode))

  let nodelist = list tynode

  (* Constructors for text nodes and recursive nodes. *)
  let text e = _Fold tynode (_Inject Left tynodebody e)
  let node nt at e = _Fold tynode (_Inject Right tynodebody (_Pair nt (_Pair at e)))
end

(* D^Article_TProg level of the document calculus. 
   Adds tree templates with support for all the template parts in D^String_TProg. *)
module DArtTProg = struct
  open DStrLit
  open DStrProg
  open DArtProg
  open DStrTLit
  open Prelude

  (* We extend the template language with attributes nodes. In a concrete syntax, you
     might write one like: <span style="color:red">Hello world!</span> *)
  type Template.part += 
      TplNode of string * (string * Expr.t) list * Template.t

  (* We extend the expression language with tree templates, which are like
     string templates but they desugar to trees instead of strings. *)
  type Expr.t += 
      TreeTmpl of Template.t

  (* Smart constructors for Bindlib. *)
  let _TplNode : string -> (string * Expr.t box) list -> Template.t box -> Template.part box = 
    fun nt attrs children ->
    let (keys, vals) = List.split attrs in
    box_apply2 (fun vals children -> 
        let attrs = List.combine keys vals in
        TplNode (nt, attrs, children)
      ) (box_list vals) children    
  let _TreeTmpl : Template.t box -> Expr.t box = box_apply (fun t -> TreeTmpl t)

  (* Desugaring a tree template does not require adding a join,
     unlike desugaring a string template. *)
  let desugar_expr = function 
    | TreeTmpl t -> desugar_template (unbox tynode, t)

  let desugar_attrs at = 
    (list tyattr (List.map (fun (k, v) -> _Pair (_EString k) (Expr.desugar v)) at))

  (* This is where our TplCtx type comes into play. When we see a TplStr,
     we know to make it a node rather than a plain string 
     if we're in a `tynode` context. *)
  let desugar_tpart (ty, p) = 
    let in_ctx = Type.eq ty (unbox tynode) in
    match p with
    | TplStr s when in_ctx -> text (_EString s)
    | TplNode (tag, attrs, children) when in_ctx -> 
      node 
        (_EString tag) 
        (desugar_attrs attrs)
        (desugar_template (ty, children))

  let typecheck (ctx, e) = match e with 
    | TreeTmpl tpl -> 
      let t = (typecheck_template (TplCtx tynode :: ctx, tpl)) in
      if Type.unbox_eq t (tylist tynode) then tylist tynode
      else raise (Type_error "tree template")

  let typecheck_tpart (ctx, p) = 
    let ty = ctx_tpl_ty ctx in 
    match p with
    | TplNode (_, attrs, children) ->
      List.iter (fun (_, v) -> 
          if not (Type.unbox_eq (Expr.typecheck (ctx, v)) ty) then 
            raise (Type_error "attrs")) 
        attrs;
      if Type.unbox_eq (typecheck_template (ctx, children)) (tylist ty) then ty 
      else raise (Type_error "children")      

  (* Boring code. *)

  let show_template = function
    | TplNode (nt, _, kt) -> Printf.sprintf "<%s>%s</%s>" nt (show_ttext kt) nt

  let show_expr (_ctx, e) = match e with 
    | TreeTmpl kt -> show_ttext kt

  let eval = function 
    | TreeTmpl _ -> raise Not_desugared

  let lift_expr = function 
    | TreeTmpl _ -> raise Not_desugared

  let lift_part = function
    | TplNode (tag, attrs, t) -> 
      box_apply (fun t -> TplNode (tag, attrs, t)) (Template.lift t)

  let eq_expr = function 
    | (TreeTmpl _, _) | (_, TreeTmpl _) -> raise Not_desugared

  let desugar_tpart_in_context = Open_func.noop 
  let typecheck_tpart_in_context = Open_func.noop 
end
let register_darttprog () =
  Expr.register (module DArtTProg);
  Template.register (module DArtTProg)

(* Implementation of the "fragment" strategy for D^Article_TProg. *)
module DArtTProgNested = struct
  open DStrLit
  open DStrTLit
  open DStrProg
  open DArtTProg
  open DStrTProg
  open DArtProg
  open Prelude

  (* Add a new FragTpl expression which is like TreeTpl but uses the alternative
      desugaring strategy. It still desugars to terms of the same type. *)
  type Expr.t += 
    | FragTpl of Template.t

  let _FragTpl = box_apply (fun t -> FragTpl t)

  (* Lots of type definitions... it's a little obscured due to the embedding 
     in System F. To see a clearer presentation, either:
     - Check out the symbolic formalism in Section 3.2.4 of the paper.
     - Check out extensions.ml for a shallow OCaml embedding.
       (The code below was largely transliterated from the other OCaml code.) *)
  let tree = mktfree "tree"
  let tyfrag t = _TRec tree (_TSum t (tylist (_TVar tree)))
  let tyfragbody t = _TSum t (tylist (tyfrag t))

  let fragbase t e = _Fold (tyfrag t) (_Inject Left (tyfragbody t) e)
  let fraglist t e = _Fold (tyfrag t) (_Inject Right (tyfragbody t) e)

  let fnode = mktfree "fnode"
  let tyfnode = _TRec fnode (_TSum _TString (tystructnode (tyfrag (_TVar fnode))))
  let tyfnodebody = _TSum _TString (tystructnode (tyfrag tyfnode))

  let tynodetree = tyfrag tyfnode

  let ftext e = fragbase tyfnode (_Fold tyfnode (_Inject Left tyfnodebody e))
  let fnode nt at e = fragbase tyfnode (_Fold tyfnode (_Inject Right tyfnodebody (_Pair nt (_Pair at e))))

  let elim_fragsv = mkefree "elim_frags"
  let elim_frags = 
    let (fl, base, textv, nd, listv) = (mkefree "fl", mkefree "base", mkefree "text", mkefree "nd", mkefree "list") in
    _Fix elim_fragsv (_TFun tynodetree (tylist tynode)) (lam1 fl tynodetree (
        _Case
          (_Unfold tynodetree (_Var fl))
          base
          (_Case
             (_Unfold tyfnode (_Var base))
             textv (list tynode [text (_Var textv)])
             nd (list tynode [
                 node
                   (_Project (_Var nd) Left)
                   (_Project (_Project (_Var nd) Right) Left)
                   (app1 (_Var elim_fragsv) (_Project (_Project (_Var nd) Right) Right))]))           
          listv
          (flatten tynode 
             (foreach tynodetree (tylist tynode) (_Var elim_fragsv) (_Var listv)))))

  let desugar_template_elems_as_fraglist t =
    fraglist tyfnode (desugar_template (unbox tynodetree, t)) 

  let desugar_expr = function FragTpl t -> app1 elim_frags (desugar_template_elems_as_fraglist t)

  (* Override "default" desugaring for non-fragment templates *)
  let desugar_tpart_in_context (ty, lt, lts) = 
    let in_ctx = Type.eq ty (unbox tynodetree) in
    match lt with 
    | TplForeach _ | TplIf _ when in_ctx -> 
      cons (Type.lift ty) (Template.desugar_part (ty, lt)) (desugar_template (ty, lts))

  let desugar_tpart (ty, p) = 
    let in_ctx = Type.eq ty (unbox tynodetree) in
    match p with
    | TplStr s when in_ctx -> ftext (_EString s)
    | TplNode (tag, attrs, t) when in_ctx -> 
      fnode (_EString tag) (desugar_attrs attrs) (desugar_template_elems_as_fraglist t)
    | TplForeach (e, xty, t) when in_ctx -> 
      let (x, t) = unbind t in
      fraglist tyfnode (
        foreach (Type.lift xty) (Type.lift ty) (lam1 x (Type.lift xty) (desugar_template_elems_as_fraglist t)) (Expr.desugar e))
    | TplIf (e, t1, t2) when in_ctx -> 
      if_ (Expr.desugar e) (desugar_template_elems_as_fraglist t1) (desugar_template_elems_as_fraglist t2)

  let typecheck (ctx, e) = match e with FragTpl t -> 
    if Type.unbox_eq (typecheck_template (TplCtx tynodetree :: ctx, t)) (tylist tynodetree) then tylist tynode
    else raise (Type_error "tree template")

  let lift_expr = function 
    | FragTpl _ -> raise Not_desugared
  let eq_expr = function 
    | (FragTpl _, _) | (_, FragTpl _) -> raise Not_desugared

  let eval = Open_func.noop
  let show_expr = Open_func.noop
  let subst_expr = Open_func.noop
  let show_template = Open_func.noop
  let typecheck_tpart = Open_func.noop  
  let lift_part = Open_func.noop    
  let typecheck_tpart_in_context = Open_func.noop
end
let register_dartprognested () =
  Expr.register (module DArtTProgNested);
  Template.register (module DArtTProgNested)