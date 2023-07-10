type var = string

exception Undefined_behavior
exception Not_desugared
exception Type_error of string

module Type = struct
  type t = ..
  type ctx_elem = ..
  type ctx = ctx_elem list

  module Subst = Open_func.Make(struct
      type input = var * t * t
      type output = t
    end)

  module Show = Open_func.Make(struct
      type input = t
      type output = string
    end)

  module type Fragment = sig
    val subst_type : Subst.func
    val show_type : Show.func
  end

  let register (module F: Fragment) = 
    Subst.register F.subst_type;
    Show.register F.show_type

  let subst = Subst.call
  let show = Show.call
end


module Expr = struct
  type t = ..

  module Eval = Open_func.Make(struct
      type input = t
      type output = t
    end)

  module Subst = Open_func.Make(struct
      type input = var * t * t
      type output = t
    end)

  module Desugar = Open_func.Make(struct
      type input = t
      type output = t
    end)

  module Show = Open_func.Make(struct
      type input = t
      type output = string
    end) 

  module Typecheck = Open_func.Make(struct
      type input = Type.ctx * t
      type output = Type.t
    end)

  module type Fragment = sig
    val desugar_expr : Desugar.func
    val typecheck : Typecheck.func
    val subst_expr : Subst.func
    val eval : Eval.func
    val show_expr : Show.func
  end

  let register (module F: Fragment) = 
    Desugar.register F.desugar_expr;
    Typecheck.register F.typecheck;
    Subst.register F.subst_expr;
    Eval.register F.eval;    
    Show.register F.show_expr

  let eval = Eval.call
  let subst = Subst.call
  let desugar = Desugar.call
  let show = Show.call
  let typecheck = Typecheck.call
  let desugar_eval e = eval (desugar e)  
end


module Template = struct
  type part = ..
  type t = part list

  module Desugar_part = Open_func.Make(struct
      type input = Type.t * part
      type output = Expr.t
    end)

  module Desugar_in_context = Open_func.Make(struct
      type input = Type.t * part * t
      type output = Expr.t
    end)

  module Show = Open_func.Make(struct
      type input = part
      type output = string
    end)

  module type Fragment = sig
    val desugar_tpart : Desugar_part.func
    val desugar_tpart_in_context : Desugar_in_context.func
    val show_template : Show.func
  end

  let register (module F: Fragment) = 
    Desugar_part.register F.desugar_tpart;
    Desugar_in_context.register F.desugar_tpart_in_context;
    Show.register F.show_template

  let desugar_part = Desugar_part.call
  let desugar_in_context = Desugar_in_context.call

  let show = Show.call
end


