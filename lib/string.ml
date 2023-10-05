[@@@warning "-partial-match"]

(* This module provides the D^String levels of the document calculus.
   I recommend skipping to DStrTLit if you want to see the interesting parts. *)

open Base
open Bindlib

(* D^String_Lit level of the document calculus.
   String literals are the only kind of expression, and strings are the only kind of type. *)
module DStrLit = struct
  (* We add string expressions and string types. *)
  type Expr.t += 
    | EString of string
  type Type.t += 
    | TString

  (* We use Bindlib <https://lepigre.fr/ocaml-bindlib/> to handle binding.
     This requires special constructor functions for all syntax elements,
     which are prefixed with an underscore. *)
  let _EString : string -> Expr.t box = fun s -> box (EString s)
  let _TString = box TString

  (* The eval and typecheck functions are straightforward. *)
  let eval = function 
    | EString s -> EString s
  let typecheck (_, e) = match e with 
    | EString _ -> _TString

  (* Many other functions that you can ignore.
     Some of these will be useful later, but for now we are just
     defining the uninteresting case of strings. *)

  let show_expr (_, e) =  match e with 
    | EString s -> Printf.sprintf "\"%s\"" s
  let show_type (_, ty) = match ty with 
    | TString -> "string"
  let desugar_expr = function 
    | EString s -> _EString s
  let lift_expr = function 
    | EString s -> _EString s
  let lift_type = function 
    | TString -> _TString
  let eq_expr = function
    | (EString s1, EString s2) -> s1 = s2
  let eq_type = function 
    | (TString, TString) -> true
end

(* Call this function to load this language fragment into the open functions. *)
let register_dstrlit () =
  Type.register (module DStrLit);
  Expr.register (module DStrLit)


(* D^String_Prog level of the document calculus.
   An implementation of the static and dynamic semantics for System F with a base type of strings. *)
module DStrProg = struct
  open DStrLit

  type dir = Left | Right

  (* Add all of System F's expressions... *)
  type Expr.t += 
    | Concat of Expr.t * Expr.t 
    | Let of Expr.t * Expr.t Expr.binder
    | Fix of Type.t * Expr.t Expr.binder
    | Var of Expr.var
    | Inject of dir * Type.t * Expr.t
    | Case of {
        expr: Expr.t;
        left: Expr.t Expr.binder;
        right: Expr.t Expr.binder;
      }
    | Lambda of Type.t * Expr.t Expr.binder
    | App of Expr.t * Expr.t
    | Unit
    | Pair of Expr.t * Expr.t
    | Project of Expr.t * dir
    | Fold of Type.t * Expr.t
    | Unfold of Type.t * Expr.t
    | TyLambda of Type.t Expr.binder
    | TyApp of Expr.t * Type.t
    | Pack of Type.t * Expr.t * Type.t
    | Unpack of Expr.t * (Expr.t, (Type.t, Expr.t) binder) binder

  (* ... and types ... *)
  type Type.t +=
    | TFun of Type.t * Type.t
    | TProd of Type.t * Type.t
    | TSum of Type.t * Type.t
    | TUnit
    | TForall of Type.t Type.binder
    | TExists of Type.t Type.binder
    | TRec of Type.t Type.binder
    | TVar of Type.var

  (* ... and type context elements. *)
  type Type.ctx_elem += 
    | BoundVar of Expr.var * Type.t box
    | BoundTypeVar of Type.var

  (* The code below is a relatively rote implementation of System F.
     It mostly looks like you would find in e.g. TAPL. 
     Most of the idiosyncracies (like the huge number of constructor functions)
     are due to requirements of Bindlib. *)

  let mkefree = new_var (fun x -> Var x)
  let mktfree = new_var (fun x -> TVar x)

  let _Var : Expr.t var -> Expr.t box = 
    box_var
  let _Concat : Expr.t box -> Expr.t box -> Expr.t box = 
    box_apply2 (fun a b -> Concat (a, b))
  let _Let : Expr.t var -> Expr.t box -> Expr.t box -> Expr.t box =
    fun x e1 e2 -> box_apply2 (fun e1 e2 -> Let (e1, e2)) e1 (bind_var x e2)
  let _App : Expr.t box -> Expr.t box -> Expr.t box = 
    box_apply2 (fun a b -> App (a, b))
  let _Lambda :  Expr.t var -> Type.t box -> Expr.t box -> Expr.t box =
    fun x t e -> box_apply2 (fun t e -> Lambda (t, e)) t (bind_var x e)
  let _TyLambda : Type.t var -> Expr.t box -> Expr.t box =
    fun a e -> box_apply (fun e -> TyLambda e) (bind_var a e)
  let _TyApp : Expr.t box -> Type.t box -> Expr.t box =
    box_apply2 (fun e t -> TyApp (e, t))
  let _Unit : Expr.t box =
    box Unit
  let _Pair : Expr.t box -> Expr.t box -> Expr.t box =
    box_apply2 (fun a b -> Pair (a, b))
  let _Project : Expr.t box -> dir -> Expr.t box =
    fun e d -> box_apply (fun e -> Project (e, d)) e
  let _Fold : Type.t box -> Expr.t box -> Expr.t box =
    box_apply2 (fun t e -> Fold (t, e))
  let _Unfold : Type.t box -> Expr.t box -> Expr.t box =
    box_apply2 (fun t e -> Unfold (t, e))
  let _Fix : Expr.t var -> Type.t box -> Expr.t box -> Expr.t box =
    fun x t e -> box_apply2 (fun t e -> Fix (t, e)) t (bind_var x e)    
  let _Pack : Type.t box -> Expr.t box -> Type.t box -> Expr.t box =
    box_apply3 (fun t1 e t2 -> Pack (t1, e, t2))
  let _Unpack : Expr.t var -> Type.t var -> Expr.t box -> Expr.t box -> Expr.t box =
    fun x a e1 e2 -> box_apply2 (fun e1 e2 -> Unpack (e1, e2)) e1 (bind_var x (bind_var a e2))
  let _Inject : dir -> Type.t box -> Expr.t box -> Expr.t box =
    fun d t e -> box_apply2 (fun t e -> Inject (d, t, e)) t e
  let _Case : Expr.t box -> Expr.t var -> Expr.t box -> Expr.t var -> Expr.t box -> Expr.t box =
    fun expr x left y right -> 
    box_apply3 (fun expr left right  -> Case {expr; left; right}) expr (bind_var x left) (bind_var y right)  

  let _TUnit : Type.t box = box TUnit
  let _TProd : Type.t box -> Type.t box -> Type.t box =
    box_apply2 (fun a b -> TProd (a, b))
  let _TSum : Type.t box -> Type.t box -> Type.t box =
    box_apply2 (fun a b -> TSum (a, b))
  let _TFun : Type.t box -> Type.t box -> Type.t box =
    box_apply2 (fun a b -> TFun (a, b))
  let _TForall : Type.t var -> Type.t box -> Type.t box =
    fun a t -> box_apply (fun t -> TForall t) (bind_var a t)
  let _TRec : Type.t var -> Type.t box -> Type.t box =
    fun a t -> box_apply (fun t -> TRec t) (bind_var a t)
  let _TExists : Type.t var -> Type.t box -> Type.t box =
    fun a t -> box_apply (fun t -> TExists t) (bind_var a t)
  let _TVar : Type.t var -> Type.t box =
    box_var    

  let eval = function
    | Concat (e1, e2) -> 
      let (EString s1, EString s2) = (Expr.eval e1, Expr.eval e2) in
      EString (s1 ^ s2)
    | Let (e1, e2) -> Expr.eval (subst e2 (Expr.eval e1))
    | Fix (t, e) -> Expr.eval (subst e (Fix (t, e)))
    | Var _ -> raise Undefined_behavior
    | Inject (dir, t, e) -> Inject (dir, t, Expr.eval e)
    | Case {expr; left; right} -> 
      let (Inject (dir, _, e)) = Expr.eval expr in
      Expr.eval (subst
                   (match dir with Left -> left | Right -> right)
                   e)        
    | Lambda (t, e) -> Lambda (t, e)
    | App (e1, e2) -> 
      let Lambda (_, e) = Expr.eval e1 in
      let e2' = Expr.eval e2 in
      Expr.eval (subst e e2')
    | Unit -> Unit
    | Pair (e1, e2) -> Pair (Expr.eval e1, Expr.eval e2)
    | Project (e, d) -> 
      let Pair (v1, v2) = Expr.eval e in
      (match d with Left -> v1 | Right -> v2)
    | Fold (t, e) -> Fold (t, Expr.eval e)
    | Unfold (_, e) -> 
      let Fold (_, e) = Expr.eval e in 
      e
    | TyLambda e -> TyLambda e
    | TyApp (e, t) -> 
      let TyLambda e = Expr.eval e in
      Expr.eval (subst e t)
    | Pack (t1, e, t2) -> Pack (t1, Expr.eval e, t2)
    | Unpack (e1, e2) ->
      let Pack (t, v, _) = Expr.eval e1 in
      Expr.eval (subst (subst e2 v) t)      

  let eq_type = function
    | (TFun (t1, t2), TFun (t1', t2')) -> Type.eq t1 t1' && Type.eq t2 t2'
    | (TProd (t1, t2), TProd (t1', t2')) -> Type.eq t1 t1' && Type.eq t2 t2'
    | (TSum (t1, t2), TSum (t1', t2')) -> Type.eq t1 t1' && Type.eq t2 t2'
    | (TUnit, TUnit) -> true
    | (TForall t1, TForall t2) -> eq_binder Type.eq t1 t2
    | (TExists t1, TExists t2) -> eq_binder Type.eq t1 t2
    | (TRec t1, TRec t2) -> eq_binder Type.eq t1 t2
    | (TVar x, TVar y) -> eq_vars x y

  let eq_expr = function
    | (Concat (e1, e2), Concat (e1', e2')) -> Expr.eq e1 e1' && Expr.eq e2 e2'
    | (Let (e1, e2), Let (e1', e2')) -> Expr.eq e1 e1' && eq_binder Expr.eq e2 e2'
    | (Fix (t, e), Fix (t', e')) -> Type.eq t t' && eq_binder Expr.eq e e'
    | (Var x, Var y) -> eq_vars x y
    | (Inject (d, t, e), Inject (d', t', e')) -> d = d' && Type.eq t t' && Expr.eq e e'
    | (Case {expr; left; right}, Case {expr = expr'; left = left'; right = right'}) -> 
      Expr.eq expr expr' && eq_binder Expr.eq left left' && eq_binder Expr.eq right right'
    | (Lambda (t, e), Lambda (t', e')) -> Type.eq t t' && eq_binder Expr.eq e e'
    | (App (e1, e2), App (e1', e2')) -> Expr.eq e1 e1' && Expr.eq e2 e2'
    | (Unit, Unit) -> true
    | (Pair (e1, e2), Pair (e1', e2')) -> Expr.eq e1 e1' && Expr.eq e2 e2'
    | (Project (e, d), Project (e', d')) -> Expr.eq e e' && d = d'
    | (Fold (t, e), Fold (t', e')) -> Type.eq t t' && Expr.eq e e'
    | (Unfold (t, e), Unfold (t', e')) -> Type.eq t t' && Expr.eq e e'
    | (TyLambda e, TyLambda e') -> eq_binder Expr.eq e e'
    | (TyApp (e, t), TyApp (e', t')) -> Expr.eq e e' && Type.eq t t'
    | (Pack (t1, e, t2), Pack (t1', e', t2')) -> Type.eq t1 t1' && Expr.eq e e' && Type.eq t2 t2'
    | (Unpack (e1, e2), Unpack (e1', e2')) -> Expr.eq e1 e1' && eq_binder (eq_binder Expr.eq) e2 e2'        

  let show_dir = function Left -> "l" | Right -> "r"

  let show_expr (ctx, e) = match e with
    | Concat (e1, e2) -> Printf.sprintf "%s + %s" (Expr.show_ctx (ctx, e1)) (Expr.show_ctx (ctx, e2))
    | Let (e1, e2) -> 
      let (x, e2, ctx) = unbind_in ctx e2 in
      Printf.sprintf "let %s = %s in\n%s" 
        (name_of x) 
        (Expr.show_ctx (ctx, e1)) 
        (Expr.show_ctx (ctx, e2))
    | Fix (t, e) -> 
      let (x, e, ctx) = unbind_in ctx e in
      Printf.sprintf "fix (%s : %s). %s" 
        (name_of x) 
        (Type.show_ctx (ctx, t)) 
        (Expr.show_ctx (ctx, e))
    | Var x -> name_of x
    | Inject (d, t, e) -> 
      Printf.sprintf "in%s(%s as %s)" (show_dir d) (Expr.show_ctx (ctx, e)) (Type.show_ctx (ctx, t))
    | Case {expr; left; right} -> 
      let (x, left, ctx) = unbind_in ctx left in
      let (y, right, ctx) = unbind_in ctx right in
      Printf.sprintf "case %s of inl(%s) -> %s | inr(%s) -> %s" 
        (Expr.show_ctx (ctx, expr)) 
        (name_of x) (Expr.show_ctx (ctx, left)) 
        (name_of y) (Expr.show_ctx (ctx, right))
    | Lambda (t, e) -> 
      let (x, e, ctx) = unbind_in ctx e in
      Printf.sprintf " fun (%s:%s). %s" 
        (name_of x) 
        (Type.show_ctx (ctx, t)) 
        (Expr.show_ctx (ctx, e))
    | App (e1, e2) -> Printf.sprintf "%s %s" (Expr.show_ctx (ctx, e1)) (Expr.show_ctx (ctx, e2))
    | Pair (e1, e2) -> Printf.sprintf "(%s, %s)" (Expr.show_ctx (ctx, e1)) (Expr.show_ctx (ctx, e2))
    | Project (e, d) -> Printf.sprintf "%s.%s" (Expr.show_ctx (ctx, e)) (show_dir d)
    | Fold (t, e) -> 
      (match t with
       (* | TRec ("list", _) -> 
          let  Inject (d, _, e) = e in
          (match d with
          | Left -> "[]"
          | Right -> 
            let Pair (e1, e2) = e in
            Printf.sprintf "%s :: %s" (Expr.show_ctx (ctx, e1)) (Expr.show_ctx (ctx, e2)))
          | TRec ("node", _) ->
          let Inject (d, _, e) = e in
          (match d with
          | Left -> Printf.sprintf "<text>%s</text>" (Expr.show_ctx (ctx, e))
          | Right -> 
            let Pair(nt, children) = e in
            Printf.sprintf "<%s>%s</%s>" (Expr.show_ctx (ctx, nt)) (Expr.show_ctx (ctx, children)) (Expr.show_ctx (ctx, nt))) *)
       | _ -> Printf.sprintf "fold %s as (%s)"  (Expr.show_ctx (ctx, e)) (Type.show_ctx (ctx, t)))
    | Unfold (t, e) -> Printf.sprintf "unfold %s from (%s)" (Expr.show_ctx (ctx, e)) (Type.show_ctx (ctx, t) )
    | TyLambda e -> 
      let (x, e, ctx) = unbind_in ctx e in
      Printf.sprintf "tfun %s -> %s" (name_of x) (Expr.show_ctx (ctx, e))
    | TyApp (e, t) -> Printf.sprintf "%s[%s]" (Expr.show_ctx (ctx, e)) (Type.show_ctx (ctx, t))
    | Unit -> "()"

  let show_type (ctx, t) = match t with
    | TFun (t1, t2) -> Printf.sprintf "(%s -> %s)" (Type.show_ctx (ctx, t1)) (Type.show_ctx (ctx, t2))
    | TProd (t1, t2) -> Printf.sprintf "%s * %s" (Type.show_ctx (ctx, t1)) (Type.show_ctx (ctx, t2))
    | TSum (t1, t2) -> Printf.sprintf "%s + %s" (Type.show_ctx (ctx, t1)) (Type.show_ctx (ctx, t2))
    | TUnit -> "unit"
    | TForall t -> 
      let (x, t, ctx) = unbind_in ctx t in
      Printf.sprintf "forall %s. %s" (name_of x) (Type.show_ctx (ctx, t))
    | TRec t -> 
      let (x, t, ctx) = unbind_in ctx t in
      if (name_of x) = "list" then
        let TSum (_, TProd (t', _)) = t in
        Printf.sprintf "%s list" (Type.show_ctx (ctx, t'))
      else 
        Printf.sprintf "rec %s. %s" (name_of x) (Type.show_ctx (ctx, t))
    | TVar x -> name_of x

  let typecheck (ctx, e) = match e with 
    | Concat (e1, e2) -> 
      let (t1, t2) = (Expr.typecheck (ctx, e1), (Expr.typecheck (ctx, e2))) in
      (match (unbox t1, unbox t2) with
       | (TString, TString) -> _TString
       | _ -> raise (Type_error "concat"))
    | Let (e1, e2) -> 
      let t1 = Expr.typecheck (ctx, e1) in
      let (x, e2') = unbind e2 in
      Expr.typecheck ((BoundVar (x, t1)) :: ctx, e2')
    | Fix (t, e) ->
      let (x, e') = unbind e in
      Expr.typecheck ((BoundVar (x, Type.lift t)) :: ctx, e')
    | Var x -> 
      let ty_opt = List.find_map (fun elem -> match elem with 
          | BoundVar (y, t) -> 
            if eq_vars x y then Some t else None
          | _ -> None) ctx in 
      (match ty_opt with
       | Some ty -> ty
       | None -> raise (Type_error (Printf.sprintf "Var: %s" (name_of x))))
    | Inject (dir, t, e') -> 
      let t' = Expr.typecheck (ctx, e') in
      let t'' = (match (dir, t) with 
          | (Left, TSum (t'', _)) ->  t''
          | (Right, TSum (_, t'')) -> t''
          | _ -> raise (Type_error (Printf.sprintf "inject: not a sum: %s" (Expr.show e)))) in
      if Type.eq (unbox t') t'' then Type.lift t 
      else raise (Type_error (Printf.sprintf "inject: %s != %s" (Type.show (unbox t')) (Type.show t'')))
    | Case {expr; left; right} ->
      let t = Expr.typecheck (ctx, expr) in
      (match unbox t with
       | TSum (t1, t2) -> 
         let (x, left') = unbind left in
         let (y, right') = unbind right in
         let t1' = Expr.typecheck ((BoundVar (x, Type.lift t1)) :: ctx, left') in
         let t2' =  Expr.typecheck ((BoundVar (y, Type.lift t2)) :: ctx, right') in
         if Type.unbox_eq t1' t2' then t1' 
         else raise (Type_error (Printf.sprintf "case: %s != %s" (Type.show (unbox t1')) (Type.show (unbox t2'))))
       | _ -> raise (Type_error "case"))
    | Lambda (t, e) -> 
      let (x, e') = unbind e in
      let t' = Expr.typecheck ((BoundVar (x, Type.lift t)) :: ctx, e') in
      _TFun (Type.lift t) t'
    | App (e1, e2) -> 
      let t1 = Expr.typecheck (ctx, e1) in 
      let t2 = Expr.typecheck (ctx, e2) in
      (match unbox t1 with
       | TFun (t1', t1'') -> 
         if Type.eq t1' (unbox t2) then (Type.lift t1'') 
         else raise (Type_error (Printf.sprintf "app: %s : %s != %s : %s" (Expr.show e1) (Type.show t1') (Expr.show e2) (Type.show (unbox t2))))
       | _ -> raise (Type_error "app"))
    | Pair (e1, e2) -> 
      let t1 = Expr.typecheck (ctx, e1) in
      let t2 = Expr.typecheck (ctx, e2) in 
      _TProd t1 t2
    | Project (e, d) ->
      let t = Expr.typecheck (ctx, e) in
      (match unbox t with
       | TProd (t1, t2) -> Type.lift (match d with Left -> t1 | Right -> t2)
       | _ -> raise (Type_error (Printf.sprintf "project from non-product: %s" (Type.show (unbox t)))))
    | Fold (t, e) ->
      let TRec t0 = t in      
      let t2 = Expr.typecheck (ctx, e) in
      let t3 = subst t0 t in
      if  Type.eq (unbox t2) t3 then Type.lift t 
      else raise (Type_error (Printf.sprintf "fold: %s != %s" (Type.show (unbox t2)) (Type.show t3)))
    | Unfold (t, e) ->
      let TRec t0 = t in
      let t1 = Expr.typecheck (ctx, e) in
      if Type.eq t (unbox t1) then Type.lift (subst t0 t)
      else raise (Type_error "unfold")
    | TyLambda e -> 
      let (alpha, e') = unbind e in
      let t = Expr.typecheck ((BoundTypeVar alpha) :: ctx, e') in
      _TForall alpha t      
    | TyApp (e, t) ->
      let t0 = Expr.typecheck (ctx, e) in
      (match (unbox t0) with
       | TForall t1 -> Type.lift (subst t1 t)
       | _ -> raise (Type_error "tyapp"))
    | Unit -> _TUnit    
    | Pack (t1, e, t2ex) ->
      let TExists t2 = t2ex in
      if Type.eq (unbox (Expr.typecheck (ctx, e))) (subst t2 t1) then Type.lift t2ex 
      else raise (Type_error "pack")
    | Unpack (e1, e2) ->
      (match unbox (Expr.typecheck (ctx, e1)) with
       | TExists t0 ->
         let (alpha, t1) = unbind t0 in
         let (x, e3) = unbind e2 in
         let ctx' = (BoundTypeVar alpha) :: (BoundVar (x, Type.lift t1)) :: ctx in
         Expr.typecheck (ctx', (subst e3 (TVar alpha)))
       | _ -> raise (Type_error "unpack"))

  let desugar_expr = function
    | Concat (e1, e2) -> _Concat (Expr.desugar e1) (Expr.desugar e2)
    | Let (e1, e2) ->
      let (x, e2) = unbind e2 in
      _Let x (Expr.desugar e1) (Expr.desugar e2)
    | Fix (t, e) -> 
      let (x, e) = unbind e in
      _Fix x (Type.lift t) (Expr.desugar e)
    | Var x -> _Var x
    | Inject (dir, t, e) -> _Inject dir (Type.lift t) (Expr.desugar e)
    | Case {expr; left; right} -> 
      let (x, left) = unbind left in
      let (y, right) = unbind right in
      _Case (Expr.desugar expr) x (Expr.desugar left) y (Expr.desugar right)
    | Lambda (t, e) -> 
      let (x, e) = unbind e in
      _Lambda x (Type.lift t) (Expr.desugar e)
    | App (e1, e2) -> 
      _App (Expr.desugar e1) (Expr.desugar e2)
    | Pair (e1, e2) -> 
      _Pair (Expr.desugar e1) (Expr.desugar e2)
    | Project (e, n) -> 
      _Project (Expr.desugar e) n
    | Fold (t, e) -> 
      _Fold (Type.lift t) (Expr.desugar e)
    | Unfold (t, e) -> 
      _Unfold (Type.lift t) (Expr.desugar e)
    | TyLambda e ->
      let (x, e) = unbind e in
      _TyLambda x (Expr.desugar e)
    | TyApp (e, t) -> 
      _TyApp (Expr.desugar e) (Type.lift t)
    | Unit -> _Unit
    | Pack (t1, e, t2) -> 
      _Pack (Type.lift t1) (Expr.desugar e) (Type.lift t2)
    | Unpack (e1, e2) -> 
      let (x, e2') = unbind e2 in
      let (a, e2'') = unbind e2' in
      _Unpack x a (Expr.desugar e1) (Expr.desugar e2'')

  let lift_type = function
    | TFun (t1, t2) -> _TFun (Type.lift t1) (Type.lift t2)
    | TProd (t1, t2) -> _TProd (Type.lift t1) (Type.lift t2)
    | TSum (t1, t2) -> _TSum (Type.lift t1) (Type.lift t2)
    | TUnit -> _TUnit
    | TForall t -> box_apply (fun t -> TForall t) (box_binder Type.lift t)
    | TExists t -> box_apply (fun t -> TExists t) (box_binder Type.lift t)
    | TRec t -> box_apply (fun t -> TRec t) (box_binder Type.lift t)
    | TVar x -> box_var x

  let lift_expr = function
    | Concat (e1, e2) -> _Concat (Expr.lift e1) (Expr.lift e2)
    | Let (e1, e2) -> box_apply2 (fun e1 e2 -> Let (e1, e2)) (Expr.lift e1) (box_binder Expr.lift e2)
    | Fix (t, e) -> box_apply2 (fun t e -> Fix (t, e)) (Type.lift t) (box_binder Expr.lift e)
    | Var x -> box_var x
    | Inject (d, t, e) -> _Inject d (Type.lift t) (Expr.lift e)
    | Case {expr; left; right} -> 
      box_apply3 (fun expr left right -> Case {expr; left; right}) (Expr.lift expr) (box_binder Expr.lift left) (box_binder Expr.lift right)
    | Lambda (t, e) -> box_apply2 (fun t e -> Lambda (t, e)) (Type.lift t) (box_binder Expr.lift e)
    | App (e1, e2) -> _App (Expr.lift e1) (Expr.lift e2)
    | Pair (e1, e2) -> _Pair (Expr.lift e1) (Expr.lift e2)
    | Project (e, d) -> _Project (Expr.lift e) d
    | Fold (t, e) -> _Fold (Type.lift t) (Expr.lift e)
    | Unfold (t, e) -> _Unfold (Type.lift t) (Expr.lift e)
    | TyLambda e -> box_apply (fun e -> TyLambda e) (box_binder Expr.lift e)
    | TyApp (e, t) -> _TyApp (Expr.lift e) (Type.lift t)
    | Unit -> _Unit
    | Pack (t1, e, t2) -> _Pack (Type.lift t1) (Expr.lift e) (Type.lift t2)
    | Unpack (e1, e2) -> 
      box_apply2 (fun e1 e2 -> Unpack (e1, e2)) (Expr.lift e1) (box_binder (box_binder Expr.lift) e2)
end

let register_dstrprog () =
  Expr.register (module DStrProg);
  Type.register (module DStrProg)

(* A body of helper functions for constructing DStrProg terms, 
   as well as a standard library of types (like list) and functions (like map, join). *)
module Prelude = struct
  open DStrLit
  open DStrProg

  let app1 f x = _App f x
  let app2 f x y = _App (_App f x) y
  let app3 f x y z = _App (_App (_App f x) y) z

  let tyapp1 f x = _TyApp f x
  let tyapp2 f x y = _TyApp (_TyApp f x) y

  let lam1 x t e = _Lambda x t e
  let lam2 x t1 y t2 e = _Lambda x t1 (_Lambda y t2 e)
  let lam3 x t1 y t2 z t3 e = _Lambda x t1 (_Lambda y t2 (_Lambda z t3 e))

  let tylam1 x e = _TyLambda x e
  let tylam2 x y e = _TyLambda x (_TyLambda y e)

  let tya = mktfree "a"
  let tva = _TVar tya
  let tyb = mktfree "b"
  let tvb = _TVar tyb

  let eunit = _Unit

  let tybool = _TSum _TUnit _TUnit
  let false_ = _Inject Right tybool eunit
  let true_ = _Inject Left tybool eunit
  let ignore = mkefree "_"
  let if_ expr then_ else_ = _Case expr ignore then_ ignore else_

  let tylist = mktfree "list"
  let tylist t = _TRec tylist (_TSum _TUnit (_TProd t (_TVar tylist)))
  let tylistbody t = _TSum _TUnit (_TProd t (tylist t))

  let vnil = mkefree "nil"
  let enil = _TyLambda tya (_Fold (tylist tva) (_Inject Left (tylistbody tva) eunit))
  let nil t = tyapp1 enil t

  let x = mkefree "x"
  let y = mkefree "y"
  let f = mkefree "f"
  let l = mkefree "l"
  let z = mkefree "z"
  let xs = mkefree "xs"
  let econs = 
    tylam1 tya (
      lam2 x tva y (tylist tva)
        (_Fold (tylist tva) (_Inject Right (tylistbody tva) (_Pair (_Var x) (_Var y)))))
  let vcons = mkefree "cons"
  let cons a = app2 (tyapp1 econs a)

  let vfold = mkefree "fold"

  let efold = 
    let fty = _TFun tva (_TFun tvb tvb) in
    let ty = _TFun fty (_TFun tvb (_TFun (tylist tva) tvb)) in
    let cell = mkefree "cell" in
    tylam2 tya tyb 
      (_Fix vfold ty 
         (lam3 f fty z tvb l (tylist tva) 
            (_Case
               (_Unfold (tylist tva) (_Var l))
               ignore (_Var z)
               cell 
               (app2 (_Var f)
                  (_Project (_Var cell) Left) 
                  (app3 (_Var vfold) 
                     (_Var f) 
                     (_Var z) 
                     (_Project (_Var cell) Right))))))

  let fold a b = app3 (tyapp2 (_Var vfold) a b)

  let vappend = mkefree "append"
  let eappend = tylam1 tya (lam2 x (tylist tva) y (tylist tva) (
      fold tva (tylist tva) (tyapp1 (_Var vcons) tva)
        (_Var y)
        (_Var x)
    ))
  let vflatten = mkefree "flatten"
  let eflatten = tylam1 tya (lam1 x (tylist (tylist tva)) (
      fold (tylist tva) (tylist tva) 
        (tyapp1 (_Var vappend) tva) 
        (nil tva) 
        (_Var x)
    ))
  let vforeach = mkefree "foreach"
  let eforeach = tylam2 tya tyb (lam2 f (_TFun tva tvb) l (tylist tva) (
      fold tva (tylist tvb)
        (lam2 x tva xs (tylist tvb) 
           (cons tvb (app1 (_Var f) (_Var x)) (_Var xs)))
        (nil tvb) 
        (_Var l)
    ))

  let vjoin = mkefree "join"
  let ejoin = lam1 l (tylist _TString) (
      fold _TString _TString
        (lam2 x _TString y _TString (_Concat (_Var x) (_Var y)))
        (_EString "") 
        (_Var l)
    )

  let prelude = [
    (vnil, enil);
    (vcons, econs);
    (vfold, efold);
    (vappend, eappend);
    (vflatten, eflatten);
    (vforeach, eforeach);
    (vjoin, ejoin) 
  ]

  let join = app1 (_Var vjoin)
  let append a = app2 (tyapp1 (_Var vappend) a)
  let flatten a = app1 (tyapp1 (_Var vflatten) a)
  let foreach a b = app2 (tyapp2 (_Var vforeach) a b)
  let list a l = List.fold_right (cons a) l (nil a)

  let with_prelude e = List.fold_right (fun (v, f) e -> _Let v f e) prelude e 
  let desugar_with_prelude e = with_prelude (Expr.desugar (unbox e))
end

(* D^String_TLit level of the document calculus.
   Adds the simplest kind of template: string template literals. *)
module DStrTLit = struct
  open DStrLit
  open Prelude

  (* A template is composed of parts. The base parts are strings and expressions.
     Note that Template.t = Template.part list. *)
  type Template.part += 
    | TplStr of string 
    | TplExpr of Expr.t

  (* A template is embedded within a string template expression. *)
  type Expr.t += 
    | StrTmpl of Template.t

  (* The kind of template being type-checked is added to the type context. 
     For now we just have string templates, but later we will add trees. *)
  type Type.ctx_elem += 
    | TplCtx of Type.t box

  (* Bindlib constructors for each syntax element. *)
  let _TplStr s = box (TplStr s)
  let _TplExpr = box_apply (fun e -> TplExpr e)

  let _StrTmpl = box_apply (fun t -> StrTmpl t)

  (* These desugaring functions define the semantics of templates 
     by translating them into the core expression language. *)

  (* A template desugars to a list of its desugared parts.
     This is specifically NOT implemented with a List.map because
     some template parts (like set-bindings) do not appear as values. *)
  let desugar_template (t_tcx, tpl) = match tpl with 
    | [] -> nil (Type.lift t_tcx)
    | lt :: lts -> Template.desugar_in_context (t_tcx, lt, lts)

  (* The baseline inductive case is that {|p :: ps|} -> {|p|} :: {|ps|}. *)
  let desugar_tpart_in_context (t_tcx, p, ps) = 
    cons (Type.lift t_tcx) (Template.desugar_part (t_tcx, p)) (desugar_template (t_tcx, ps))

  let desugar_tpart (t_tcx, p) = match (t_tcx, p) with
    (* A template string desugars into a plain string 
       when in the context of a string template.*)
    | (TString, TplStr s) -> _EString s
    (* An expression is just recursively desugared. *)
    | (_, TplExpr e) -> Expr.desugar e    

  (* When embedded into an expression, a string template is desugared
     by wrapping it in a join to convert the list into a string. *)
  let desugar_expr = function 
    | StrTmpl t -> join (desugar_template (TString, t))

  (* Finds the current template context in the type context. *)
  let ctx_tpl_ty ctx = List.find_map 
      (fun elem -> match elem with TplCtx t -> Some t | _ -> None) 
      ctx |> Option.get

  (* Typechecking is defined in a similar style as desugaring. *)
  let typecheck_template (ctx, tpl) = 
    let t_tcx = ctx_tpl_ty ctx in
    match tpl with 
    (* A template should desugar to a term of type `ty list` 
       where `ty` comes from the template context. *)
    | [] -> tylist t_tcx
    | p :: ps -> Template.typecheck_in_context (ctx, p, ps)      

  let typecheck_tpart (ctx, p) = 
    let t_tcx = ctx_tpl_ty ctx in
    match p with
    (* The type of template strings is determined by context. *)
    | TplStr _ -> t_tcx
    (* The type of interpolated expressions must match the context. *)
    | TplExpr e ->       
      if Type.eq (unbox (Expr.typecheck (ctx, e))) (unbox t_tcx) then t_tcx 
      else raise (Type_error "typecheck_tpart")

  (* Template parts should have the same type as the template list type. *)
  let typecheck_tpart_in_context (ctx, p, ps) =
    let t_tcx = ctx_tpl_ty ctx in
    if Type.eq (unbox (Template.typecheck_part (ctx, p))) (unbox t_tcx) then typecheck_template (ctx, ps)
    else raise (Type_error "typecheck_tpart_in_context")

  let typecheck (ctx, e) = match e with 
    (* String templates should desugar to terms of type `string list`. *)
    | StrTmpl tpl -> 
      let t = typecheck_template (TplCtx _TString :: ctx, tpl) in
      if Type.unbox_eq t (tylist _TString) then _TString
      else raise (Type_error "typecheck")

  (* Boring code. *)

  let lift_part = function
    | TplStr s -> _TplStr s
    | TplExpr e -> _TplExpr (Expr.lift e)

  let eval = function 
    | StrTmpl _ -> raise Not_desugared    

  let lift_expr = function 
    | StrTmpl _ -> raise Not_desugared

  let subst_expr (_, _, e2) = match e2 with 
    | StrTmpl _ -> raise Not_desugared    

  let show_ttext kt = (Stdlib.String.concat "" (List.map Template.show kt))

  let show_expr (_ctx, e) = match e with 
    | StrTmpl kt -> Printf.sprintf "`%s`" (show_ttext kt)

  let eq_expr = function
    | (StrTmpl _, _) | (_, StrTmpl _) -> raise Not_desugared

  let show_template = function
    | TplStr s -> s
    | TplExpr e -> Printf.sprintf "{%s}" (Expr.show e)    
end

let register_dstrtlit () =
  Expr.register (module DStrTLit);
  Template.register (module DStrTLit)

(* D^String_TProg level of the document calculus.
   Adds set, foreach, if, and splice as template parts.
   Implements the splicing-based approach to handling nested lists. *)
module DStrTProg = struct
  open DStrProg
  open DStrTLit
  open Prelude

  type Template.part +=
    (* Note that we cannot use a Bindlib binder for TplSet because the terms
       bound under the TplSet are adjacent to, not under, the set-binding. *)
    | TplSet of Expr.var * Expr.t
    (* But we can express the binding structure of TplForeach. *)
    | TplForeach of Expr.t * Type.t * Expr.t Template.binder   
    | TplIf of Expr.t * Template.t * Template.t
    | TplSplice of Expr.t 

  (* Smart constructors for Bindlib. *)
  let _TplSet : Expr.var -> Expr.t box -> Template.part box = 
    fun x -> box_apply (fun e -> TplSet (x, e))
  let _TplForeach : Expr.t box -> Type.t box -> Expr.var -> Template.t box -> Template.part box = 
    fun e xty x t -> box_apply3 (fun e xty t -> TplForeach (e, xty, t)) e xty (bind_var x t)
  let _TplIf : Expr.t box -> Template.t box -> Template.t box -> Template.part box = 
    box_apply3 (fun e t1 t2 -> TplIf (e, t1, t2))
  let _TplSplice : Expr.t box -> Template.part box =
    box_apply (fun e -> TplSplice e)

  (* The desugaring as described in Section 3.1.4 of the paper. *)
  let desugar_tpart_in_context (t_tcx, p, ps) = match p with 
    (* {| set x = e; ...ps |} --> let x = e in {| ps |} *)
    | TplSet (x, e) ->
      _Let x (Expr.desugar e) (desugar_template (t_tcx, ps))

    (* {| splice e; ...ps |} --> e @ {| ps |} *)
    | TplSplice e -> 
      append (Type.lift t_tcx) (Expr.desugar e) (desugar_template (t_tcx, ps))

    (* Note that foreach/if desugarings are context-insensitive *except* that they desugar
       to a splice, which *is* context-sensitive. *)

    (* {| T-foreach e : t . tpl |} --> splice (E-foreach e : t . splice {| tpl |}) *)
    | TplForeach (e, t, tpl) -> 
      let (x, tpl) = unbind tpl in
      let t' = 
        _TplSplice (
          flatten (Type.lift t_tcx)
            (foreach (Type.lift t) (tylist (Type.lift t_tcx))
               (lam1 x (Type.lift t) (desugar_template (t_tcx, tpl))) 
               (Expr.desugar e))) in
      Template.desugar_in_context (t_tcx, unbox t', ps)

    (* {| T-if e { tpl1 } else { tpl2 } |} --> E-if e { {| tpl1 |} else { {| tpl2 |} }*)
    | TplIf (e, tpl1, tpl2) ->
      let tpl' = _TplSplice (
          if_ (Expr.desugar e) 
            (desugar_template (t_tcx, tpl1))
            (desugar_template (t_tcx, tpl2))) in
      Template.desugar_in_context (t_tcx, unbox tpl', ps)

  (* The typing judgment as described in Section 5.1 of the paper. *)
  let typecheck_tpart_in_context (ctx, p, ps) = 
    let t_tcx = ctx_tpl_ty ctx in 
    match p with 
    | TplSet (x, e) ->      
      let ety = Expr.typecheck (ctx, e) in 
      typecheck_template (BoundVar (x, ety) :: ctx, ps)
    | TplSplice e ->
      let ety = Expr.typecheck (ctx, e) in 
      if Type.unbox_eq ety (tylist t_tcx) then typecheck_template (ctx, ps) 
      else raise (Type_error "typecheck_tpart_in_context")
    | TplForeach (e, t, tpl) ->
      let (x, tpl) = unbind tpl in
      let t_e = Expr.typecheck (ctx, e) in
      let t' = typecheck_template (BoundVar (x, (Type.lift t)) :: ctx, tpl) in
      if Type.unbox_eq t_e (tylist (Type.lift t)) && 
         Type.unbox_eq t' (tylist t_tcx)
      then typecheck_template (ctx, ps)
      else raise (Type_error "typecheck_tpart_in_context")
    | TplIf (e, tpl1, tpl2) ->
      let t_e = Expr.typecheck (ctx, e) in
      let t1' = typecheck_template (ctx, tpl1) in
      let t2' = typecheck_template (ctx, tpl2) in
      if Type.unbox_eq t_e tybool && 
         Type.unbox_eq t1' (tylist t_tcx) && 
         Type.unbox_eq t2' (tylist t_tcx)
      then typecheck_template (ctx, ps)
      else raise (Type_error "typecheck_tpart_in_context")

  (* Boring code. *)

  let show_template = function
    | TplForeach (e1, t, kt) -> 
      let (x, kt) = unbind kt in
      Printf.sprintf "{{ foreach (%s : %s) in %s }} %s {{ endforeach }}" (name_of x) (Type.show t) (Expr.show e1) (show_ttext kt)
    | TplSet (x, e) -> Printf.sprintf "{{ %s = %s }}" (name_of x) (Expr.show e)
    | TplSplice e -> Printf.sprintf ",@%s" (Expr.show e)

  let lift_part = function 
    | TplSet (x, e) -> _TplSet x (Expr.lift e)
    | TplForeach (e, t, kt) -> 
      let (x, kt) = unbind kt in
      _TplForeach (Expr.lift e) (Type.lift t) x (Template.lift kt)
    | TplIf (e, t1, t2) -> _TplIf (Expr.lift e) (Template.lift t1) (Template.lift t2)
    | TplSplice e -> _TplSplice (Expr.lift e)

  let typecheck_tpart = Open_func.noop

  let desugar_tpart = Open_func.noop
end

let register_dstrtprog () = 
  Template.register (module DStrTProg)