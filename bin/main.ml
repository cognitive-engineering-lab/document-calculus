[@@@warning "-unused-open"]

(* A testing ground. Fill me in and run: 
   $ dune exec bin/main.exe *)

open Document_calculus.Base
open Document_calculus.String
open Bindlib

let main () = 
  let open DStrLit in
  let open DStrProg in
  register_dstrlit ();
  register_dstrprog ();

  let e = _Concat (_EString "hello") (_EString " world") in
  assert (Type.eq (Expr.typecheck_top (_EString "sup")) TString);
  Printf.printf "A sample program:\n  %s\n\n" (Expr.show (unbox e));

  let e' = Expr.eval_top e in
  Printf.printf "It evaluates to:\n  %s\n" (Expr.show e')

let () = main ()