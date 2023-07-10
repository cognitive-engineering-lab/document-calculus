open Model.Base
open Model.String
open Model.Article
open Model.Extensions

let main () =    
  (*** DStrLit tests ***)
  let open DStrLit in
  register_dstrlit ();
  assert (Expr.typecheck ([], EString "sup") = TString);
  assert (Expr.eval (EString "sup") = (EString "sup"));


  (*** DStrProg tests ***)
  let open DStrProg in
  let open Prelude in
  register_dstrprog() ;
  assert (Expr.eval (Concat (EString "hello", EString " world")) = (EString "hello world"));
  let e = Let("x", EString "a", Concat(Var "x", Concat(EString "b", Var "x"))) in
  assert (Expr.typecheck ([], e) = TString);
  assert (Expr.eval e = EString "aba");

  let e = with_prelude (EString "") in 
  assert (Expr.typecheck ([], e) = TString);


  (*** DStrTLit tests ***)
  let open DStrTLit in
  register_dstrtlit ();  
  let e = with_prelude (
      Let("world", EString " World", 
          StrTmpl [TStr "Hello"; TExpr (Var "world")])) in
  assert (Expr.typecheck ([], (Expr.desugar e)) = TString);
  assert (Expr.desugar_eval e = (EString "Hello World"));


  (*** DStrTProg tests ***)
  let open DStrTProg in
  register_dstrtprog ();  
  let e = with_prelude (StrTmpl [
      TForeach (
        list TString [EString "a"; EString "b"], "x", TString, 
        [TExpr (Var "x"); TStr "c"])]) in
  assert (Expr.typecheck ([], (Expr.desugar e)) = TString);
  assert (Expr.desugar_eval e = (EString "acbc"));


  (*** DTreeTProg tests ***)
  let open DTreeProg in
  let open DTreeTProg in
  register_dtreetprog ();
  let e = with_prelude (TreeTmpl [TNode ("p", [], [
      TStr "Hello";
      TSet ("world", text (EString "World"));
      TExpr (Var "world");
      TForeach (
        list TString [EString "?"; EString "!"], "x",  TString,
        [TNode ("bold", [], [TExpr (text (Var "x"))])]);    
    ])]) in
  let expected = Expr.eval (with_prelude (nodelist [node (EString "p") (nil tyattr) (nodelist [
      text (EString "Hello"); text (EString "World");
      node (EString "bold") (nil tyattr) (nodelist [text (EString "?")]);
      node (EString "bold") (nil tyattr) (nodelist [text (EString "!")])
    ])])) in
  assert (Expr.typecheck ([], Expr.desugar e) = tylist tynode);
  assert (Expr.desugar_eval e = expected);


  (*** DTreeTProgNested tests ***)
  let open DTreeTProgNested in
  register_dtreeprognested ();  
  let e = with_prelude (FragTpl [TNode ("p", [], [
    TStr "Hello";
    TSet ("world", ftext (EString "World"));
    TExpr (Var "world");
    TForeach (
      list TString [EString "?"; EString "!"], "x", TString,
      [TNode ("bold", [], [TExpr (ftext (Var "x"))])]);    
  ])]) in
  assert (Expr.typecheck ([], Expr.desugar e) = tylist tynode);
  assert (Expr.desugar_eval e = expected);


  (*** References extension tests ***)
  let mk_doc id = NNode("article", [], [
    NNode ("ref", [("target", id)], []);
    NNode ("section", [("id", "intro")], [
      NNode ("h1", [], [NText "Introduction"]);
      NNode ("section", [("id", "contributions")], []);
      NNode ("section", [("id", "caveats")], [])
    ]);
    NNode ("section", [("id", "discussion")], []);
  ]) in
  assert (section_ids (mk_doc "") = [
    ("intro", [1]); 
    ("contributions", [1; 1]); 
    ("caveats", [2; 1]);
    ("discussion", [2])
  ]);

  let d = mk_doc "intro" in
  assert (valid (section_ids d) d);
  let d = mk_doc "foobar" in 
  assert (not (valid (section_ids d) d));

  let d = mk_doc "caveats" in
  let d' = replace_refs (section_ids d) d in
  assert (match d' with NNode ("article", _, NText "1.2" :: _) -> true | _ -> false);              


  (*** Reforestation extension tests ***)
  let d = [
    NText "hello";
    NText "world";
    NText "\n\n";
    NText "middle";
    NNode ("h1", [], [NText "header"]);
    NText "postscript"
  ] in
  assert (reforest d [] = [
    NNode ("para", [], [NText "hello"; NText "world"]);
    NNode ("para", [], [NText "middle"]);
    NNode ("h1", [], [NNode ("para", [], [NText "header"])]);
    NNode ("para", [], [NText "postscript"])
  ]);


  (*** Reactive extension tests ***)
  let open React in  
  let counter child = 
    let id = gen_comp_id () in
    let init p = (List.assoc "mark" p, "") in
    let update s (p, c) = 
      if s = "click" then (p, p ^ c) else (p, c) in
    let view (_, c) = child c in
    {id; init; update; view} in  
  let v0 = 
    let inner_ctr = counter (fun c -> RText c) in
    RInstance 
    (instantiate (counter (fun c -> 
      RNode ("para", [], [
        RText c;
        RInstance (instantiate inner_ctr [("mark", "@")])
      ])))
    [("mark", "|")]) in

  let a0 = doc_view v0 in
  assert (a0 = NNode ("para", [], [NText ""; NText ""]));  

  let v1 = doc_step [(0, "click")] v0 in
  let a1 = doc_view v1 in
  assert (a1 = NNode ("para", [], [NText ""; NText "@"]));
  
  let v2 = doc_step [(1, "click")] v1 in
  let a2 = doc_view v2 in
  assert (a2 = NNode ("para", [], [NText "|"; NText "@"]));

  ()


let () = main ()