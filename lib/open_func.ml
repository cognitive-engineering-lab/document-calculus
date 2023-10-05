(* See open_func.mli for documentation.*)

exception Missing_case

module type FuncSig = sig 
  type input
  type output
end

module Make(F : FuncSig) = struct
  type func = F.input -> F.output

  let f_cell : func ref = ref (fun _ -> raise Missing_case)

  let register (f : func) : unit =
    let prev = !f_cell in
    f_cell := fun t -> try f t with Match_failure _ -> prev t

  let call (x : F.input) : F.output = !f_cell x
end

let noop _ = raise (Match_failure ("", 0, 0))