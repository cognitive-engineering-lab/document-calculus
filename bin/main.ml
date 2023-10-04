[@@@warning "-unused-open"]

open Document_calculus.Base
open Document_calculus.String

let main () = 
  (* Testing ground, fill me in and run: 
     $ dune exec bin/main.exe *)
  let open DStrLit in
  register_dstrlit ();
  assert (Expr.typecheck ([], EString "sup") = TString)

let () = main ()