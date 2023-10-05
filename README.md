# A Core Calculus for Documents

This repository contains the accompanying artifact for our POPL'24 paper "A Core Calculus for Documents" (Crichton and Krishnamurthi). 

<!-- A complete list of claims made by your paper
Download, installation, and sanity-testing instructions
Evaluation instructions
Additional artifact description (file structure, extending the tool or adding your own examples, etc.) -->

## Overview

The core contribution of our paper is a formal model of document languages. This model extends System F with the concept of templates. We provide static and dynamic semantics for templates, and we also model various run-time extensions to the system such as reference labeling and reactivity.

This artifact implements each aspect of the model in OCaml. Our main goal in the implementation is to *correctly* and *clearly* implement the model. Then this model can facilitate authors of document languages to pick and choose ideas that are relevant to their setting, especially those less familiar with PL theory notation.

The mapping between the model (i.e., the claims) and the artifact is as follows:
* Section 3.1: `string.ml`
* Section 3.2: `article.ml`
* Section 4: `extensions.ml`
* Section 5.1: the `typecheck_template` functions in  `string.ml` and `article.ml`.
* Section 5.2: a proof, so no correspondent in the codebase.

Each of the source files has been liberally commented to explain the purpose of the code, and to point a reader to the relevant pieces.

## Installation

First, you need the OCaml package manager [opam]. This artifact was last tested with opam version 2.1.3.

Then, you need OCaml. This artifact was last tested with OCaml version 4.13.1. You can install the version by running:

```
opam switch create 4.13.1
```

Then install the project's dependencies by running:

```
opam install . --deps-only
```

Finally, make sure the tests pass by running:

```
opam exec -- dune test
```

If you're in a hurry, copy this script:

```
opam switch create 4.13.1 --yes
eval $(opam env --switch=4.13.1)
opam install . --deps-only --yes
opam exec -- dune test
```

[opam]: https://opam.ocaml.org/doc/Install.html