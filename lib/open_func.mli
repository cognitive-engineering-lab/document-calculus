(* This module provides an implementation of "open functions", or 
   functions whose behavior can be provided in pieces. *)

(* This describes the input and output types of the open function. *)
module type FuncSig = sig 
  type input
  type output
end

exception Missing_case

(* Creates a new open function for the given function signature. *)
module Make(F : FuncSig) : sig
  type func = F.input -> F.output

  (* Registers a new case for the open function. This is a mutating operation --
     you cannot undo it!
  
     The provided case should raise a Match_failure if it cannot handle
     a given input.

     The open function will call the cases in the order they are registered,
     so be careful to register them in the right order.
     
     Partial cases are most convenient to write with the -partial-match warning
     disabled, and leave OCaml to raise a Match_failure as normal. *)    
  val register : func -> unit

  (* Calls the open function on a given input. 
     
     This iterates through each registered case and returns its output
     if it does not raise a Match_failure.
      
     If no cases provide a value, then this raises the Missing_case exception. *)
  val call : F.input -> F.output
end

(* A convenient helper for not handling any cases. *)
val noop : 'a -> 'b