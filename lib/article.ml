[@@@warning "-partial-match"]

open Base
open String
open Bindlib

(* Note: we do not implement an OCaml model for D^Article_Lit or D^Article_TLit, as neither
   have any actual implementation details.*)

(* D^Article_Prog level of the document calculus. 
   Adds a standard library of node types for attributed, tagged trees. *)
module DTreeProg = struct
  open DStrLit
  open DStrProg
  open Prelude

  let tyattr = _TProd _TString _TString
  let tystructnode ty = _TProd _TString (_TProd (tylist tyattr) ty)

  let node = mktfree "node"
  let tynode = _TRec node (_TSum _TString (tystructnode (tylist (_TVar node))))
  let tynodebody = _TSum _TString (tystructnode (tylist tynode))
  let nodelist = list tynode

  let text e = _Fold tynode (_Inject Left tynodebody e)
  let node nt at e = _Fold tynode (_Inject Right tynodebody (_Pair nt (_Pair at e)))
end

(* D^Article_TProg level of the document calculus. 
   Adds tree templates with support for all the template parts in D^String_TProg. *)
module DTreeTProg = struct
  open DStrLit
  open DStrProg
  open DTreeProg
  open DStrTLit
  open Prelude

  type Template.part += 
      TplNode of string * (string * Expr.t) list * Template.t

  type Expr.t += 
      TreeTmpl of Template.t

  let _TplNode : string -> (string * Expr.t box) list -> Template.t box -> Template.part box = 
    fun nt attrs children ->
    let (keys, vals) = List.split attrs in
    box_apply2 (fun vals children -> 
        let attrs = List.combine keys vals in
        TplNode (nt, attrs, children)
      ) (box_list vals) children    

  let _TreeTmpl : Template.t box -> Expr.t box = box_apply (fun t -> TreeTmpl t)

  let desugar_expr = function 
    | TreeTmpl t -> desugar_template (unbox tynode, t)

  let desugar_attrs at = 
    (list tyattr (List.map (fun (k, v) -> _Pair (_EString k) (Expr.desugar v)) at))

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
    | TreeTmpl t -> 
      if Type.unbox_eq (typecheck_template (TplCtx tynode :: ctx, t)) (tylist tynode) then tylist tynode
      else raise (Type_error "tree template")

  let typecheck_tpart (ctx, p) = 
    let ty = ctx_tpl_ty ctx in 
    match p with
    | TplNode (_, attrs, children) ->
      List.iter (fun (_, v) -> 
          if not (Type.unbox_eq (Expr.typecheck (ctx, v)) ty) then raise (Type_error "attrs")) attrs;
      if Type.unbox_eq (typecheck_template (ctx, children)) (tylist ty) then ty 
      else raise (Type_error "children")      

  let typecheck_tpart_in_context = Open_func.noop

  (* Boring code *)

  let show_template = function
    | TplNode (nt, _ (* TODO *), kt) -> Printf.sprintf "<%s>%s</%s>" nt (show_ttext kt) nt

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
end
let register_dtreetprog () =
  Expr.register (module DTreeTProg);
  Template.register (module DTreeTProg)

(* Implementation of the "fragment" strategy for D^Article_TProg. *)
module DTreeTProgNested = struct
  open DStrLit
  open DStrTLit
  open DStrProg
  open DTreeTProg
  open DStrTProg
  open DTreeProg
  open Prelude

  type Expr.t += 
    | FragTpl of Template.t

  let _FragTpl = box_apply (fun t -> FragTpl t)

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

  (* A more readable version of this function (and the above typedefs) is in extensions.ml. *)
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

let register_dtreeprognested () =
  Expr.register (module DTreeTProgNested);
  Template.register (module DTreeTProgNested)