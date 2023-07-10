[@@@warning "-partial-match"]

open Base
open String

(* Note: we do not implement an OCaml model for D^Article_Lit or D^Article_TLit, as neither
   have any actual implementation details.*)

(* D^Article_Prog level of the document calculus. 
   Adds a standard library of node types for attributed, tagged trees. *)
module DTreeProg = struct
  open DStrLit
  open DStrProg
  open Prelude

  let tyattr = TProd (TString, TString)
  let tystructnode ty = TProd(TString, TProd(tylist tyattr, ty))
  let tynode = TRec("node", TSum(TString, tystructnode (tylist (TVar "node"))))
  let tynodebody = TSum(TString, tystructnode (tylist tynode))
  let nodelist = list tynode

  let text e = Fold(tynode, Inject (Left, tynodebody, e))
  let node nt at e = Fold(tynode, Inject (Right, tynodebody, Pair (nt, Pair(at, e))))
end

(* D^Article_TProg level of the document calculus. 
   Adds tree templates with support for all the template parts in D^String_TProg. *)
module DTreeTProg = struct
  open DStrLit
  open DStrProg
  open DTreeProg
  open DStrTLit
  open Prelude

  type Template.part += TNode of string * (string * Expr.t) list * Template.t

  type Expr.t += TreeTmpl of Template.t

  let desugar_expr = function TreeTmpl t -> desugar_template (tynode, t)

  let desugar_attrs at = 
    (list tyattr (List.map (fun (k, v) -> Pair (EString k, Expr.desugar v)) at))

  let desugar_tpart (ty, p) = match p with
    | TStr s when ty = tynode -> text (EString s)
    | TNode (tag, attrs, children) when ty = tynode -> 
      node 
        (EString tag) 
        (desugar_attrs attrs)
        (desugar_template (ty, children))

  let typecheck (ctx, e) = match e with TreeTmpl t -> 
    if typecheck_template (TplCtx tynode :: ctx, t) = tylist tynode then tylist tynode
    else raise (Type_error "tree template")

  let typecheck_tpart (ctx, p) = 
    let ty = ctx_tpl_ty ctx in 
    match p with
    | TNode (_, attrs, children) ->
      List.iter (fun (_, v) -> 
          if Expr.typecheck (ctx, v) <> ty then raise (Type_error "attrs")) attrs;
      if typecheck_template (ctx, children) <> tylist ty then raise (Type_error "children");
      ty

  let typecheck_tpart_in_context = Open_func.noop

  (* Boring code *)

  let show_template = function
    | TNode (nt, _ (* TODO *), kt) -> Printf.sprintf "<%s>%s</%s>" nt (show_ttext kt) nt

  let show_expr = function TreeTmpl kt -> show_ttext kt

  let eval = function TreeTmpl _ -> raise Not_desugared


  let subst_expr (_, _, e2) = match e2 with TreeTmpl _ -> raise Not_desugared

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

  type Expr.t += FragTpl of Template.t

  let tyfrag t = TRec("tree", TSum(t, tylist (TVar "tree")))
  let tyfragbody t = TSum(t, tylist (tyfrag t))

  let fragbase t e = Fold(tyfrag t, Inject (Left, tyfragbody t, e))
  let fraglist t e = Fold(tyfrag t, Inject (Right, tyfragbody t, e))  

  let tyfnode = TRec("fnode", TSum(TString, tystructnode (tyfrag (TVar "fnode"))))
  let tyfnodebody = TSum(TString, tystructnode (tyfrag tyfnode))

  let tynodetree = tyfrag tyfnode

  let ftext e = fragbase tyfnode (Fold(tyfnode, Inject (Left, tyfnodebody, e)))
  let fnode nt at e = fragbase tyfnode (Fold(tyfnode, Inject (Right, tyfnodebody, Pair(nt, Pair(at, e)))))

  (* A more readable version of this function (and the above typedefs) is in extensions.ml. *)
  let elim_frags = 
    Fix ("elim_frags", TFun(tynodetree, tylist tynode), lam1 "fl" tynodetree (
        Case {
          expr = Unfold(tynodetree, Var "fl");
          left = ("base", Case {
              expr = Unfold(tyfnode, Var "base");
              left = ("text", list tynode [text (Var "text")]);
              right = ("nd", list tynode 
                         [node
                            (Project (Var "nd", Left)) 
                            (Project (Project (Var "nd", Right), Left))
                            (app1 (Var "elim_frags") (Project (Project (Var "nd", Right), Right)))])
            });
          right = ("list", 
                   flatten tynode 
                     (foreach tynodetree (tylist tynode) (Var "elim_frags") (Var "list")))
        }))

  let desugar_template_elems_as_fraglist t =
    fraglist tyfnode (desugar_template (tynodetree, t)) 

  let desugar_expr = function FragTpl t -> app1 elim_frags (desugar_template_elems_as_fraglist t)

  (* Override "default" desugaring for non-fragment templates *)
  let desugar_tpart_in_context (ty, lt, lts) = match lt with 
    | TForeach _ | TIf _ when ty = tynodetree -> 
      cons ty (Template.desugar_part (ty, lt)) (desugar_template (ty, lts))

  let desugar_tpart (ty, p) = match p with
    | TStr s when ty = tynodetree -> ftext (EString s)
    | TNode (tag, attrs, t) when ty = tynodetree -> 
      fnode (EString tag) (desugar_attrs attrs) (desugar_template_elems_as_fraglist t)
    | TForeach (e, x, xty, t) when ty = tynodetree -> 
      fraglist tyfnode (
        foreach xty ty (lam1 x xty (desugar_template_elems_as_fraglist t)) (Expr.desugar e))
    | TIf (e, t1, t2) when ty = tynodetree -> 
      if_ (Expr.desugar e) (desugar_template_elems_as_fraglist t1) (desugar_template_elems_as_fraglist t2)

  let typecheck (ctx, e) = match e with FragTpl t -> 
    if typecheck_template (TplCtx tynodetree :: ctx, t) = tylist tynodetree then tylist tynode
    else raise (Type_error "tree template")

  let eval = Open_func.noop

  let show_expr = Open_func.noop
  let subst_expr = Open_func.noop
  let show_template = Open_func.noop
  let typecheck_tpart = Open_func.noop  
  let typecheck_tpart_in_context = Open_func.noop
end
let register_dtreeprognested () =
  Expr.register (module DTreeTProgNested);
  Template.register (module DTreeTProgNested)