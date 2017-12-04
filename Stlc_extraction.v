Require Import Stlc_fun.

Cd "build".

Extraction Language Ocaml.


Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive prod => "(*)"  [ "(,)" ].

Extract Inlined Constant negb => "not".
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".

(* Recursive Extraction feval. *)
Recursive Extraction Library Stlc_fun.