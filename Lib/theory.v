From Vloc Require Export heaplang_notation core pure tactics heap util.

(* A notation to make proofmode look a little nicer *)
Notation "'Ref' c e" := (refines_right c e) (at level 100, only printing, format "'Ref'  c '//'    e").
