exception Undefined_behavior
exception Not_desugared
exception Type_error of string

let box_list l = List.fold_right 
    (Bindlib.box_apply2 (fun x xs -> x :: xs))
    l
    (Bindlib.box [])

module Type = struct
  type t = ..
  type ctx_elem = ..
  type ctx = ctx_elem list
  type var = t Bindlib.var
  type 'a binder = ('a, t) Bindlib.binder

  module Show = Open_func.Make(struct
      type input = Bindlib.ctxt * t
      type output = string
    end)

  module Eq = Open_func.Make(struct
      type input = t * t
      type output = bool
    end)

  module Lift = Open_func.Make(struct
      type input = t
      type output = t Bindlib.box
    end)

  module type Fragment = sig
    val eq_type : Eq.func    
    val lift_type : Lift.func
    val show_type : Show.func
  end

  let register (module F: Fragment) = 
    Eq.register F.eq_type;
    Lift.register F.lift_type;
    Show.register F.show_type

  let eq t1 t2 = Eq.call (t1, t2)
  let unbox_eq t1 t2 = eq (Bindlib.unbox t1) (Bindlib.unbox t2)
  let show_ctx = Show.call  
  let show t = Show.call (Bindlib.empty_ctxt, t)
  let lift = Lift.call
end

let () = Type.Eq.register (fun (_, _) -> false)

module Expr = struct
  type t = ..
  type var = t Bindlib.var
  type 'a binder = ('a, t) Bindlib.binder

  module Eval = Open_func.Make(struct
      type input = t
      type output = t
    end)

  module Desugar = Open_func.Make(struct
      type input = t
      type output = t Bindlib.box
    end)

  module Show = Open_func.Make(struct
      type input = Bindlib.ctxt * t
      type output = string
    end) 

  module Eq = Open_func.Make(struct
      type input = t * t
      type output = bool
    end)

  module Lift = Open_func.Make(struct
      type input = t
      type output = t Bindlib.box
    end)

  module Typecheck = Open_func.Make(struct
      type input = Type.ctx * t
      type output = Type.t Bindlib.box
    end)

  module type Fragment = sig
    val desugar_expr : Desugar.func
    val typecheck : Typecheck.func
    val lift_expr : Lift.func
    val eval : Eval.func
    val show_expr : Show.func
    val eq_expr : Eq.func
  end

  let register (module F: Fragment) = 
    Desugar.register F.desugar_expr;
    Typecheck.register F.typecheck;
    Lift.register F.lift_expr;
    Eval.register F.eval;    
    Show.register F.show_expr;
    Eq.register F.eq_expr

  let eval = Eval.call  
  let desugar = Desugar.call
  let show_ctx = Show.call  
  let show t = Show.call (Bindlib.empty_ctxt, t)
  let lift = Lift.call
  let typecheck = Typecheck.call
  let eq e1 e2 = Eq.call (e1, e2)

  let typecheck_top e = Bindlib.unbox (typecheck ([], Bindlib.unbox e))
  let eval_top e = eval (Bindlib.unbox e)
  let desugar_eval e = eval (Bindlib.unbox (desugar e) )
end

module Template = struct
  type part = ..
  type t = part list
  type 'a binder = ('a, t) Bindlib.binder

  module Desugar_part = Open_func.Make(struct
      type input = Type.t * part
      type output = Expr.t Bindlib.box
    end)

  module Desugar_in_context = Open_func.Make(struct
      type input = Type.t * part * t
      type output = Expr.t Bindlib.box
    end)

  module Typecheck_part = Open_func.Make(struct
      type input = Type.ctx * part
      type output = Type.t Bindlib.box
    end)

  module Typecheck_in_context = Open_func.Make(struct
      type input = Type.ctx * part * t
      type output = Type.t Bindlib.box
    end)

  module Lift_part = Open_func.Make(struct
      type input = part
      type output = part Bindlib.box
    end)  

  module Show = Open_func.Make(struct
      type input = part
      type output = string
    end)

  module type Fragment = sig
    val desugar_tpart : Desugar_part.func
    val desugar_tpart_in_context : Desugar_in_context.func
    val typecheck_tpart : Typecheck_part.func
    val typecheck_tpart_in_context : Typecheck_in_context.func
    val lift_part : Lift_part.func
    val show_template : Show.func
  end

  let register (module F: Fragment) = 
    Desugar_part.register F.desugar_tpart;
    Desugar_in_context.register F.desugar_tpart_in_context;
    Typecheck_part.register F.typecheck_tpart;
    Typecheck_in_context.register F.typecheck_tpart_in_context;    
    Lift_part.register F.lift_part;
    Show.register F.show_template

  let desugar_part = Desugar_part.call
  let desugar_in_context = Desugar_in_context.call
  let typecheck_part = Typecheck_part.call
  let typecheck_in_context = Typecheck_in_context.call
  let lift_part = Lift_part.call

  let _Template = box_list

  let lift ps = _Template (List.map lift_part ps)

  let show = Show.call
end


