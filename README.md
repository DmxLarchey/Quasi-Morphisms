```
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)
```

# Quasi Morphisms for Almost Full relations (artifact)

This repository contains the artifact for a [TYPES 2024](https://types2024.itu.dk/Index.html) 
submission of the same name. The standalone Coq file [`af_morphism.v`](af_morphism.v)
contains the developement and is largely commented. It has minimal dependencies, only on the standard 
library (distributed with Coq), and only on the `List` and `Utf8` modules within the standard library. 
It is intented to be read and executed within an IDE for Coq such as eg [CoqIDE](https://coq.inria.fr/download) or 
[vscoq](https://github.com/coq-community/vscoq). 

Any version of Coq starting from `8.13.0` and 
upto at least `8.19.0` should be ok to compile and/or review the file [`af_morphism.v`](af_morphism.v).
Since this is a single file, there is no need to pre-compile before reviewing. 

For further information about Almost Full relations in Coq,
the following libraries may be of interest:
- [`Kruskal-AlmostFull`](https://github.com/DmxLarchey/Kruskal-AlmostFull):
  general tools and definitions for AF relations and inductive bar predicates,
  including _surjective relational morphisms_ and Coquand's constructivized
  Ramsey's theorem;
- [`Kruskal-Higman`](https://github.com/DmxLarchey/Kruskal-Higman):
  _quasi-morphisms_ then applied to the proof of Higman's lemma.

The artifact file [`af_morphism.v`](af_morphism.v) was designed by
extracting the necessary code from these libraries (so they are __not
needed__ for the review) and then cleaning up and commenting more specifically.
