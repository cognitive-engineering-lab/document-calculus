[@@@warning "-partial-match"]

open Base
module StdString = Stdlib.String

(* D^String_Lit level of the document calculus.
   String literals are the only kind of expression, and strings are the only kind of type. *)
module DStrLit = struct
  type Expr.t += EString of string

  type Type.t += TString

  let eval = function EString s -> EString s

  let typecheck (_, e) = match e with EString _ -> TString

  let subst_expr (_, _, e2) = match e2 with EString s -> EString s

  let subst_type (_, _, t2) = match t2 with TString -> TString

  let desugar_expr = function EString s -> EString s

  let show_expr = function EString s -> Printf.sprintf "\"%s\"" s

  let show_type = function TString -> "string"
end

let register_dstrlit () =
  Type.register (module DStrLit);
  Expr.register (module DStrLit)


(* D^String_Prog level of the document calculus.
   An implementation of the static and dynamic semantics for System F with a base type of strings. *)
module DStrProg = struct
  open DStrLit

  type dir = Left | Right

  type Expr.t += 
    | Concat of Expr.t * Expr.t 
    | Let of var * Expr.t * Expr.t
    | Fix of var * Type.t * Expr.t
    | Var of var
    | Inject of dir * Type.t * Expr.t
    | Case of {
        expr: Expr.t;
        left: var * Expr.t;
        right: var * Expr.t
      }
    | Lambda of var * Type.t * Expr.t
    | App of Expr.t * Expr.t
    | Unit
    | Pair of Expr.t * Expr.t
    | Project of Expr.t * dir
    | Fold of Type.t * Expr.t
    | Unfold of Type.t * Expr.t
    | TyLambda of var * Expr.t
    | TyApp of Expr.t * Type.t
    | Pack of Type.t * Expr.t * Type.t
    | Unpack of var * var * Expr.t * Expr.t

  type Type.ctx_elem += 
    | BoundVar of var * Type.t 
    | BoundTypeVar of var

  type Type.t +=
    | TFun of Type.t * Type.t
    | TProd of Type.t * Type.t
    | TSum of Type.t * Type.t
    | TUnit
    | TForall of var * Type.t
    | TExists of var * Type.t
    | TRec of var * Type.t
    | TVar of var

  let eval = function
    | Concat (e1, e2) -> 
      let (EString s1, EString s2) = (Expr.eval e1, Expr.eval e2) in
      EString (s1 ^ s2)
    | Let (x, e1, e2) -> Expr.eval(Expr.subst (x, (Expr.eval e1), e2))
    | Fix (x, t, e) -> Expr.eval (Expr.subst (x, Fix (x, t, e), e))
    | Var _ -> raise Undefined_behavior
    | Inject (dir, t, e) -> Inject (dir, t, Expr.eval e)
    | Case {expr; left = (x, e1); right = (y, e2)} -> 
      let (Inject (dir, _, e)) = Expr.eval expr in
      Expr.eval (Expr.subst ((match dir with Left -> x | Right -> y), e, (match dir with Left -> e1 | Right -> e2)))
    | Lambda (x, t, e) -> Lambda (x, t, e)
    | App (e1, e2) -> 
      let Lambda (x, _, e) = Expr.eval e1 in
      let e2' = Expr.eval e2 in
      Expr.eval (Expr.subst (x, e2', e))
    | Pair (e1, e2) -> Pair (Expr.eval e1, Expr.eval e2)
    | Project (e, d) -> 
      let Pair (v1, v2) = Expr.eval e in
      (match d with Left -> v1 | Right -> v2)
    | Fold (t, e) -> Fold (t, Expr.eval e)
    | Unfold (_, e) -> 
      let Fold (_, e) = Expr.eval e in 
      e
    | TyLambda (x, e) -> TyLambda (x, e)
    | TyApp (e, _) -> 
      let TyLambda (_, e) = Expr.eval e in
      Expr.eval e    
    | Unit -> Unit
    | Pack (t1, e, t2) -> Pack (t1, Expr.eval e, t2)
    | Unpack (x, _, e1, e2) ->
      let Pack (_, v, _) = Expr.eval e1 in
      Expr.eval (Expr.subst (x, v, e2))

  let typecheck (ctx, e) = match e with 
    | Concat (e1, e2) -> 
      let (t1, t2) = (Expr.typecheck (ctx, e1), Expr.typecheck (ctx, e2)) in
      (match (t1, t2) with
       | (TString, TString) -> TString
       | _ -> raise (Type_error "concat"))
    | Let (x, e1, e2) -> 
      let t1 = Expr.typecheck (ctx, e1) in
      Expr.typecheck ((BoundVar (x, t1)) :: ctx, e2)
    | Fix (x, t, e) ->
      Expr.typecheck ((BoundVar (x, t)) :: ctx, e)
    | Var x -> 
      let ty_opt = List.find_map (fun elem -> match elem with 
          | BoundVar (y, t) -> if x = y then Some t else None
          | _ -> None) ctx in 
      (match ty_opt with
       | Some ty -> ty
       | None -> raise (Type_error (Printf.sprintf "Var: %s" x)))
    | Inject (dir, t, e') -> 
      let t' = Expr.typecheck (ctx, e') in
      let t'' = (match (dir, t) with 
          | (Left, TSum (t'', _)) ->  t''
          | (Right, TSum (_, t'')) -> t''
          | _ -> raise (Type_error (Printf.sprintf "inject: not a sum: %s" (Expr.show e)))) in
      if t' = t'' then t else raise (Type_error (Printf.sprintf "inject: %s != %s" (Type.show t') (Type.show t'')))
    | Case {expr; left = (x, e1); right = (y, e2)} ->
      let t = Expr.typecheck (ctx, expr) in
      (match t with
       | TSum (t1, t2) -> 
         let t1' = Expr.typecheck ((BoundVar (x, t1)) :: ctx, e1) in
         let t2' =  Expr.typecheck ((BoundVar (y, t2)) :: ctx, e2) in
         if t1' = t2' then t1' else raise (Type_error (Printf.sprintf "case: %s != %s" (Type.show t1') (Type.show t2')))
       | _ -> raise (Type_error "case"))
    | Lambda (x, t, e) -> 
      let t' = Expr.typecheck ((BoundVar (x, t)) :: ctx, e) in
      TFun (t, t')
    | App (e1, e2) -> 
      let t1 = Expr.typecheck (ctx, e1) in 
      let t2 = Expr.typecheck (ctx, e2) in
      (match t1 with
       | TFun (t1', t1'') -> if t1' = t2 then t1'' else raise (Type_error (Printf.sprintf "app: %s != %s" (Type.show t1') (Type.show t2)))
       | _ -> raise (Type_error "app"))
    | Pair (e1, e2) -> 
      let t1 = Expr.typecheck (ctx, e1) in
      let t2 = Expr.typecheck (ctx, e2) in 
      TProd (t1, t2)
    | Project (e, d) ->
      let t = Expr.typecheck (ctx, e) in
      (match t with
       | TProd (t1, t2) -> (match d with Left -> t1 | Right -> t2)
       | _ -> raise (Type_error (Printf.sprintf "project from non-product: %s" (Type.show t))))
    | Fold (t, e) ->
      let TRec(x, t') = t in
      let t'' = Expr.typecheck ((BoundVar (x, t)) :: ctx, e) in
      let t''' = Type.subst (x, t, t') in
      if  t''' = t'' then t else raise (Type_error (Printf.sprintf "fold: %s != %s" (Type.show t'') (Type.show t''')))
    | Unfold (t, e) ->
      let TRec(x, t') = t in
      let t'' = Expr.typecheck (ctx, e) in
      if t = t'' then Type.subst (x, t, t') else raise (Type_error "unfold")
    | TyLambda (x, e) -> 
      let t = Expr.typecheck ((BoundTypeVar x) :: ctx, e) in
      TForall (x, t)
    | TyApp (e, t) ->
      let t' = Expr.typecheck (ctx, e) in
      (match t' with
       | TForall (x, t'') -> Type.subst (x, t, t'')
       | _ -> raise (Type_error "tyapp"))
    | Unit -> TUnit    
    | Pack (t1, e, t2) ->
      let TExists(a, t') = t2 in
      if Type.subst (a, t1, t') = Expr.typecheck (ctx, e) then t2 else raise (Type_error "pack")
    | Unpack (x, a, e1, e2) ->
      let t = Expr.typecheck (ctx, e1) in
      (match t with
       | TExists (b, t') -> 
         let t'' = Type.subst (b, TVar a, t') in
         Expr.typecheck ((BoundTypeVar a) :: (BoundVar (x, t'')) :: ctx, e2)
       | _ -> raise (Type_error "unpack"))

  (* ignore alpha-renaming for now *)
  let subst_expr (x, e1, e2) = match e2 with  
    | Concat (e1', e2') -> Concat (Expr.subst (x, e1, e1'), Expr.subst (x, e1, e2'))
    | Let (y, e1', e2') ->
      Let (y, Expr.subst (x, e1, e1'), if x = y then e2' else Expr.subst (x, e1, e2'))
    | Fix (y, t, e') -> Fix (y, t, if x = y then e' else Expr.subst (x, e1, e'))
    | Var y -> if x = y then e1 else Var y
    | Inject (dir, t, e') -> Inject (dir, t, Expr.subst (x, e1, e'))
    | Case {expr; left = (y, e1'); right = (z, e2')} ->
      Case {
        expr = Expr.subst (x, e1, expr);
        left = (y, if x = y then e1' else Expr.subst (x, e1, e1'));
        right = (z, if x = z then e2' else Expr.subst (x, e1, e2'))
      }
    | Lambda (y, t, e') -> Lambda (y, t, if x = y then e' else Expr.subst (x, e1, e'))
    | App (e1', e2') -> App (Expr.subst (x, e1, e1'), Expr.subst (x, e1, e2'))
    | Pair (e1', e2') -> Pair (Expr.subst (x, e1, e1'), Expr.subst (x, e1, e2'))
    | Project (e', d) -> Project (Expr.subst (x, e1, e'), d)
    | Fold (t, e') -> Fold (t, Expr.subst (x, e1, e'))
    | Unfold (t, e') -> Unfold (t, Expr.subst (x, e1, e'))
    | TyLambda (y, e') -> TyLambda (y, if x = y then e' else Expr.subst (x, e1, e'))
    | TyApp (e', t) -> TyApp (Expr.subst (x, e1, e'), t)
    | Unit -> Unit

  let subst_type (x, t1, t2) = match t2 with
    | TFun (t1', t1'') -> TFun (Type.subst (x, t1, t1'), Type.subst (x, t1, t1''))
    | TProd (t1', t1'') -> TProd (Type.subst (x, t1, t1'), Type.subst (x, t1, t1''))
    | TSum (t1', t1'') -> TSum (Type.subst (x, t1, t1'), Type.subst (x, t1, t1''))
    | TUnit -> TUnit
    | TForall (y, t) -> TForall (y, if x = y then t else Type.subst (x, t1, t))
    | TRec (y, t) -> TRec (y, if x = y then t else Type.subst (x, t1, t))
    | TVar y -> if x = y then t1 else TVar y

  let desugar_expr = function
    | Concat (e1, e2) -> Concat(Expr.desugar e1, Expr.desugar e2)
    | Let (x, e1, e2) -> Let(x, Expr.desugar e1, Expr.desugar e2)
    | Fix (x, t, e) -> Fix(x, t, Expr.desugar e)
    | Var x -> Var x
    | Inject (dir, t, e) -> Inject (dir, t, Expr.desugar e)
    | Case {expr; left = (x, e1); right = (y, e2)} -> 
      Case {
        expr = Expr.desugar expr;
        left = (x, Expr.desugar e1);
        right = (y, Expr.desugar e2)
      }
    | Lambda (x, t, e) -> Lambda (x, t, Expr.desugar e)
    | App (e1, e2) -> App (Expr.desugar e1, Expr.desugar e2)
    | Pair (e1, e2) -> Pair (Expr.desugar e1, Expr.desugar e2)
    | Project (e, n) -> Project (Expr.desugar e, n)
    | Fold (t, e) -> Fold (t, Expr.desugar e)
    | Unfold (t, e) -> Unfold (t, Expr.desugar e)
    | TyLambda (x, e) -> TyLambda (x, Expr.desugar e)
    | TyApp (e, t) -> TyApp (Expr.desugar e, t)
    | Unit -> Unit

  let show_dir = function Left -> "l" | Right -> "r"

  let show_expr = function
    | Concat (e1, e2) -> Printf.sprintf "%s + %s" (Expr.show e1) (Expr.show e2)
    | Let (x, e1, e2) -> Printf.sprintf "let %s = %s in\n%s" x (Expr.show e1) (Expr.show e2)
    | Fix (x, t, e) -> Printf.sprintf "fix (%s : %s). %s" x (Type.show t) (Expr.show e)
    | Var x -> x
    | Inject (d, t, e) -> 
      Printf.sprintf "in%s(%s as %s)" (show_dir d) (Expr.show e) (Type.show t)
    | Case {expr; left = (x, e1); right = (y, e2)} -> 
      Printf.sprintf "case %s of inl(%s) -> %s | inr(%s) -> %s" (Expr.show expr) x (Expr.show e1) y (Expr.show e2)
    | Lambda (x, t, e) -> Printf.sprintf " fun (%s:%s). %s" x (Type.show t) (Expr.show e)
    | App (e1, e2) -> Printf.sprintf "%s %s" (Expr.show e1) (Expr.show e2)
    | Pair (e1, e2) -> Printf.sprintf "(%s, %s)" (Expr.show e1) (Expr.show e2)
    | Project (e, d) -> Printf.sprintf "%s.%s" (Expr.show e) (show_dir d)
    | Fold (t, e) -> 
      (match t with
       | TRec ("list", _) -> 
         let  Inject (d, _, e) = e in
         (match d with
          | Left -> "[]"
          | Right -> 
            let Pair (e1, e2) = e in
            Printf.sprintf "%s :: %s" (Expr.show e1) (Expr.show e2))
       | TRec ("node", _) ->
         let Inject (d, _, e) = e in
         (match d with
          | Left -> Printf.sprintf "<text>%s</text>" (Expr.show e)
          | Right -> 
            let Pair(nt, children) = e in
            Printf.sprintf "<%s>%s</%s>" (Expr.show nt) (Expr.show children) (Expr.show nt))
       | _ -> Printf.sprintf "fold %s as (%s)"  (Expr.show e) (Type.show t))
    | Unfold (t, e) -> Printf.sprintf "unfold %s from (%s)" (Expr.show e) (Type.show t) 
    | TyLambda (x, e) -> Printf.sprintf "tfun %s -> %s" x (Expr.show e)
    | TyApp (e, t) -> Printf.sprintf "%s[%s]" (Expr.show e) (Type.show t)
    | Unit -> "()"

  let show_type = function
    | TFun (t1, t2) -> Printf.sprintf "%s -> %s" (Type.show t1) (Type.show t2)
    | TProd (t1, t2) -> Printf.sprintf "%s * %s" (Type.show t1) (Type.show t2)
    | TSum (t1, t2) -> Printf.sprintf "%s + %s" (Type.show t1) (Type.show t2)
    | TUnit -> "unit"
    | TForall (x, t) -> Printf.sprintf "forall %s. %s" x (Type.show t)
    | TRec (x, t) -> Printf.sprintf "rec %s. %s" x (Type.show t)
    | TVar x -> x
end
let register_dstrprog () =
  Expr.register (module DStrProg);
  Type.register (module DStrProg)

(* A body of helper functions for constructing DStrProg terms, 
   as well as a standard library of types (like list) and functions (like map, join). *)
module Prelude = struct
  open DStrLit
  open DStrProg

  let app1 f x = App (f, x)
  let app2 f x y = App (App (f, x), y)
  let app3 f x y z = App (App (App (f, x), y), z)

  let tyapp1 f x = TyApp (f, x)
  let tyapp2 f x y = TyApp (TyApp (f, x), y)  

  let lam1 x t e = Lambda (x,t, e)
  let lam2 x t1 y t2 e = Lambda (x, t1, Lambda (y, t2, e))
  let lam3 x t1 y t2 z t3 e = Lambda (x, t1, Lambda (y, t2, Lambda (z, t3, e)))

  let tylam1 x e = TyLambda (x, e)
  let tylam2 x y e = TyLambda (x, TyLambda (y, e))

  let tya = TVar "a"
  let tyb = TVar "b"

  let eunit = Unit

  let tybool = TSum (TUnit, TUnit)
  let false_ = Inject (Right, tybool, eunit)
  let true_ = Inject (Left, tybool, eunit) 
  let if_ expr then_ else_ = Case {
      expr; left = ("_", then_); right = ("_", else_)
    }


  let tylist t = TRec ("list", TSum (TUnit, TProd (t, TVar "list")))
  let tylistbody t = TSum (TUnit, TProd (t, tylist t))

  let enil = TyLambda ("a", Fold(tylist tya, Inject (Left, tylistbody tya, eunit)))
  let nil t = tyapp1 enil t

  let econs = tylam1 "a" (
      lam2 "x" tya "y" (tylist tya) 
        (Fold(tylist tya, Inject (Right, tylistbody tya, Pair (Var "x", Var "y")))))
  let cons a = app2 (tyapp1 econs a)

  let efold = 
    let fty = TFun(tya, TFun(tyb, tyb)) in
    let ty = TFun(fty, TFun(tyb, TFun(tylist tya, tyb))) in
    tylam2 "a" "b" (Fix ("fold", ty, lam3 "f" fty "z" tyb "l" (tylist tya) (Case {
        expr = Unfold(tylist tya, Var "l");
        left = ("_", Var "z");
        right = ("cell", 
                 app2 (Var "f")
                   (Project (Var "cell", Left)) 
                   (app3 (Var "fold") 
                      (Var "f") 
                      (Var "z") 
                      (Project (Var "cell", Right))));
      })))
  let fold a b = app3 (tyapp2 (Var "fold") a b)

  let eappend = tylam1 "a" (lam2 "x" (tylist tya) "y" (tylist tya) (
      fold tya (tylist tya) (tyapp1 (Var "cons") tya)
        (Var "y") 
        (Var "x")    
    ))
  let eflatten = tylam1 "a" (lam1 "x" (tylist (tylist tya)) (
      fold (tylist tya) (tylist tya) 
        (tyapp1 (Var "append") tya) 
        (nil tya) 
        (Var "x")
    ))
  let eforeach = tylam2 "a" "b" (lam2 "f" (TFun (tya, tyb)) "l" (tylist tya) (
      fold tya (tylist tyb)
        (lam2 "x" tya "xs" (tylist tyb) 
           (cons tyb (app1 (Var "f") (Var "x")) (Var "xs")))
        (nil tyb) 
        (Var "l")
    ))

  let ejoin = lam1 "l" (tylist TString) (
      fold TString TString
        (lam2 "x" TString "y" TString (Concat (Var "x", Var "y")))
        (EString "") 
        (Var "l")
    )

  let prelude = [
    ("nil", enil);
    ("cons", econs);
    ("fold", efold);
    ("append", eappend);
    ("flatten", eflatten);
    ("foreach", eforeach);
    ("join", ejoin)
  ]

  let join = app1 (Var "join")
  let append a = app2 (tyapp1 (Var "append") a)
  let flatten a = app1 (tyapp1 (Var "flatten") a)
  let foreach a b = app2 (tyapp2 (Var "foreach") a b)
  let list a l = List.fold_right (cons a) l (nil a)

  let with_prelude e = List.fold_right (fun (v, f) e -> Let(v, f, e)) prelude e 
end

(* D^String_TLit level of the document calculus.
   Adds the simplest kind of template: string template literals. *)
module DStrTLit = struct
  open DStrLit
  open Prelude

  type Type.ctx_elem += TplCtx of Type.t

  type Template.part += TStr of string | TExpr of Expr.t

  type Expr.t += StrTmpl of Template.t

  let desugar_template (ty, t) = match t with 
    | [] -> nil ty 
    | lt :: lts -> Template.desugar_in_context (ty, lt, lts)

  let desugar_tpart_in_context (ty, p, ps) = 
    cons ty (Template.desugar_part (ty, p)) (desugar_template (ty, ps))

  let desugar_expr = function StrTmpl t -> join (desugar_template (TString, t))

  let desugar_tpart (ty, p) = match (ty, p) with
    | (TString, TStr s) -> EString s
    | (_, TExpr e) -> Expr.desugar e    

  let ctx_tpl_ty ctx = List.find_map 
      (fun elem -> match elem with TplCtx t -> Some t | _ -> None) 
      ctx |> Option.get

  let typecheck_template (ctx, t) = 
    let ty = ctx_tpl_ty ctx in
    match t with 
    | [] -> tylist ty
    | p :: ps -> Template.typecheck_in_context (ctx, p, ps)      

  let typecheck_tpart (ctx, p) = 
    let ty = ctx_tpl_ty ctx in
    match p with
    | TStr _ -> ty
    | TExpr e -> 
      if Expr.typecheck (ctx, e) = ty then ty 
      else raise (Type_error "typecheck_tpart")

  let typecheck_tpart_in_context (ctx, p, ps) =
    let ty = ctx_tpl_ty ctx in
    if Template.typecheck_part (ctx, p) <> ty then raise (Type_error "typecheck_tpart_in_context");    
    typecheck_template (ctx, ps)

  let typecheck (ctx, e) = match e with 
      StrTmpl t -> 
      if typecheck_template (TplCtx TString :: ctx, t) = tylist TString then
        TString
      else raise (Type_error "typecheck")



  (* Boring code *)

  let eval = function StrTmpl _ -> raise Not_desugared    


  let subst_expr (_, _, e2) = match e2 with StrTmpl _ -> raise Not_desugared    

  let show_ttext kt = (StdString.concat "" (List.map Template.show kt))

  let show_expr = function StrTmpl kt -> Printf.sprintf "`%s`" (show_ttext kt)

  let show_template = function
    | TStr s -> s
    | TExpr e -> Printf.sprintf "{%s}" (Expr.show e)    
end
let register_dstrtlit () =
  Expr.register (module DStrTLit);
  Template.register (module DStrTLit)

(* D^String_TProg level of the document calculus.
   Adds set, foreach, if, and splice as template parts. *)
module DStrTProg = struct
  open DStrProg
  open DStrTLit
  open Prelude

  type Template.part +=
    | TSet of var * Expr.t
    | TForeach of Expr.t * var * Type.t * Template.t   
    | TIf of Expr.t * Template.t * Template.t
    | TSplice of Expr.t 

  let desugar_tpart_in_context (ty, p, ps) = match p with 
    | TSet (x, e) -> Let (x, e, desugar_template (ty, ps))
    | TSplice e -> 
      append ty (Expr.desugar e) (desugar_template (ty, ps))
    | TForeach (e, x, xty, t) -> 
      let t' = 
        TSplice (
          flatten ty
            (foreach xty (tylist ty)
               (lam1 x xty (desugar_template (ty, t))) 
               (Expr.desugar e))) in
      Template.desugar_in_context (ty, t', ps)
    | TIf (e, t1, t2) ->
      let t' = TSplice (if_ (Expr.desugar e) (desugar_template (ty, t1)) (desugar_template (ty, t2))) in
      Template.desugar_in_context (ty, t', ps)

  let typecheck_tpart_in_context (ctx, p, ps) = 
    let ty = ctx_tpl_ty ctx in 
    match p with 
    | TSet (x, e) ->
      let ety = Expr.typecheck (ctx, e) in 
      typecheck_template (BoundVar (x, ety) :: ctx, ps)
    | TSplice e ->
      let ety = Expr.typecheck (ctx, e) in 
      if ety = tylist ty then typecheck_template (ctx, ps) 
      else raise (Type_error "typecheck_tpart_in_context")
    | TForeach (e, x, xty, t) ->
      let ety = Expr.typecheck (ctx, e) in
      let t' = typecheck_template (BoundVar (x, xty) :: ctx, t) in
      if ety = tylist xty && t' = tylist ty then typecheck_template (ctx, ps)
      else raise (Type_error "typecheck_tpart_in_context")
    | TIf (e, t1, t2) ->
      let ety = Expr.typecheck (ctx, e) in
      let t1' = typecheck_template (ctx, t1) in
      let t2' = typecheck_template (ctx, t2) in
      if ety = tybool && t1' = tylist ty && t2' = tylist ty then typecheck_template (ctx, ps)
      else raise (Type_error "typecheck_tpart_in_context")


  (* Boring code *)

  let show_template = function
    | TForeach (e1, x, t, kt) -> Printf.sprintf "{{ foreach (%s : %s) in %s }} %s {{ endforeach }}" x (Type.show t) (Expr.show e1) (show_ttext kt)
    | TSet (x, e) -> Printf.sprintf "{{ %s = %s }}" x (Expr.show e)
    | TSplice e -> Printf.sprintf ",@%s" (Expr.show e)

  let typecheck_tpart = Open_func.noop

  let desugar_tpart = Open_func.noop
end
let register_dstrtprog () = 
  Template.register (module DStrTProg)