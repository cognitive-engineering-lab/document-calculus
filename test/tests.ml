open Document_calculus.Base
open Document_calculus.String
open Bindlib
open Document_calculus.Article
open Document_calculus.Extensions

let main () =    
  (*** DStrLit tests ***)
  let open DStrLit in
  register_dstrlit ();
  assert (Type.eq (Expr.typecheck_top (_EString "sup")) TString);
  assert (Expr.eq (Expr.eval (EString "sup")) (EString "sup"));


  (*** DStrProg tests ***)
  let open DStrProg in
  let open Prelude in
  register_dstrprog() ;
  assert (Expr.eval (Concat (EString "hello", EString " world")) = (EString "hello world"));
  let x = mkefree "x" in  
  let e = (
    _Let x (_EString "a")     
      (_Concat (_Var x) (_Concat (_EString "b") (_Var x)))) in
  assert (Type.eq (Expr.typecheck_top e) TString);
  assert (Expr.eq (Expr.eval_top e) (EString "aba"));

  let e = with_prelude (_EString "") in 
  assert (Type.eq (Expr.typecheck_top e) TString);


  (*** DStrTLit tests ***)
  let open DStrTLit in
  let open Template in
  register_dstrtlit ();  
  let world = mkefree "world" in
  let e = (
    _Let world (_EString " World")
      (_StrTmpl (_Template [_TplStr "Hello"; _TplExpr (_Var world)]))) in
  assert (Type.eq (Expr.typecheck_top (desugar_with_prelude e)) TString);
  assert (Type.eq (Expr.typecheck_top (with_prelude e)) TString);
  assert (Expr.eq (Expr.eval_top (desugar_with_prelude e)) (EString "Hello World"));


  (*** DStrTProg tests ***)
  let open DStrTProg in
  register_dstrtprog ();  
  let e = (
    _StrTmpl (_Template [
        _TplForeach 
          (list _TString [_EString "a"; _EString "b"])
          _TString
          x
          (_Template [_TplExpr (_Var x); _TplStr "c"])  
      ])
  ) in
  assert (Type.eq (Expr.typecheck_top (desugar_with_prelude e)) TString);
  assert (Type.eq (Expr.typecheck_top (with_prelude e)) TString);
  assert (Expr.eq (Expr.eval_top (desugar_with_prelude e)) (EString "acbc"));  


  (*** DArtTProg tests ***)
  let open DArtProg in
  let open DArtTProg in
  register_darttprog ();
  let mk_tpl textfn = _Template [_TplNode "p" [] (_Template [
      _TplStr "Hello";
      _TplSet world (textfn (_EString "World"));
      _TplExpr (_Var world);
      _TplForeach 
        (list _TString [_EString "?"; _EString "!"])         
        _TString
        x        
        (_Template [_TplNode "bold" [] (_Template [_TplExpr (textfn (_Var x))])]);    
    ])] in
  let e = _TreeTmpl (mk_tpl text) in
  let expected = Expr.eval_top (desugar_with_prelude (nodelist [node (_EString "p") (nil tyattr) (nodelist [
      text (_EString "Hello"); text (_EString "World");
      node (_EString "bold") (nil tyattr) (nodelist [text (_EString "?")]);
      node (_EString "bold") (nil tyattr) (nodelist [text (_EString "!")])
    ])])) in
  assert (Type.eq (Expr.typecheck_top (desugar_with_prelude e)) (unbox (tylist tynode)));
  assert (Type.eq (Expr.typecheck_top (with_prelude e)) (unbox (tylist tynode)));
  assert (Expr.eq (Expr.eval_top (desugar_with_prelude e)) expected);


  (*** DArtTProgNested tests ***)
  let open DArtTProgNested in
  register_dartprognested ();  
  let e = _FragTpl (mk_tpl ftext) in  
  assert (Type.eq (Expr.typecheck_top (desugar_with_prelude e)) (unbox (tylist tynode)));
  assert (Type.eq (Expr.typecheck_top (with_prelude e)) (unbox (tylist tynode)));
  assert (Expr.eq (Expr.eval_top (desugar_with_prelude e)) expected);


  (*** References extension tests ***)
  let open Node in 
  let open References in
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
  let open Reforestation in
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
  let open Reactivity in  
  let open T in
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