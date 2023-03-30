From Vloc Require Import theory.

(* Two different approaches we could take:
    - syntactical relation between predicates 
    - semantic relationship between C and HeapLang 
 *)

Open Scope bi_scope.

Axiom syn_relate : mpred.

Lemma syn_relate P e v Q P' c :
  syn_relate →
  {{ P }} e {{ v, Q }} 

  .
