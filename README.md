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

This repository contains the artifact for the submission
[_Quasi Morphisms for Almost Full relations_](https://members.loria.fr/DLarchey/files/papers/types2024.pdf)
to the [TYPES 2024](https://types2024.itu.dk/Index.html) conference.

The standalone Coq file [`af_morphism.v`](af_morphism.v)
contains the developement and is largely commented. It has minimal dependencies, only on the standard 
library (distributed with Coq), and only on the `List` and `Utf8` modules within the standard library. 
It is intented to be read and executed within an IDE for Coq such as eg [CoqIDE](https://coq.inria.fr/download) or 
[vscoq](https://github.com/coq-community/vscoq). 

Any version of Coq starting from `8.13.0` and 
upto at least `8.19.1` should be ok to compile and/or review the file [`af_morphism.v`](af_morphism.v).
Since this is a single file, there is no need to pre-compile before reviewing. 

For further information about Almost Full relations in Coq,
the following libraries may be of interest:
- [`Kruskal-AlmostFull`](https://github.com/DmxLarchey/Kruskal-AlmostFull):
  general tools and definitions for AF relations and inductive bar predicates,
  including _surjective relational morphisms_ and Coquand's constructivized
  Ramsey's theorem;
- [`Kruskal-Higman`](https://github.com/DmxLarchey/Kruskal-Higman):
  _quasi-morphisms_ then applied to the proof of Higman's lemma;
- [`Kruskal-Veldman`](https://github.com/DmxLarchey/Kruskal-Veldman):
  the proof of Wim Veldman's variant of Kruskal's tree theorem 
  adapted to type theory makes a central use of quasi-morphisms
  but in a more complicated setting compare to [`Kruskal-Higman`](https://github.com/DmxLarchey/Kruskal-Higman)
  above;
- [`Kruskal-Theorems`](https://github.com/DmxLarchey/Kruskal-Theorems):
  "easy" consequences of [`Kruskal-Veldman`](https://github.com/DmxLarchey/Kruskal-Veldman)
  derived using surjective relational morphisms.

The artifact file [`af_morphism.v`](af_morphism.v) was designed by
extracting the necessary code from these libraries (so they are __not
needed__ for the review) and then cleaning up and commenting more specifically.

# Remarks

Concerning the use of `Utf8` symbols in the code, we did not experience any display issues 
with CoqIDE in any of the `opam` installed versions from `8.13.0` and `8.19.1`. Similarly,
viewing the code in the Chrome browser directly on GitHub looks fine on our systems. 
Depending on the operating system, distribution or the IDE/browser, such issues might 
possibly arise if OS installed `Utf8` symbols are incomplete/inconsistent with the IDE/browser. 

Anyway, to possibly avoid such issues, we suggest the usage of an `opam` installed version 
of CoqIDE rather than the default OS version of the tool. This also allows to easily switch
between different versions of Coq when developping general purpose code.
