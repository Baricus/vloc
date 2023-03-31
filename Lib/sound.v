From Vloc Require Import theory.

(* Two different approaches we could take:
    - syntactical relation between predicates 
    - semantic relationship between C and HeapLang 
 *)


Context `{!heapGS Σ}.

Axiom syn_relate : iProp Σ -> mpred -> Prop.

Lemma syn_relate_sound P e v Q P' Q' varspecs funspecs compspecs func ident argT retT:
  syn_relate P P' →
  syn_relate Q Q' →
  {{{ P }}} e {{{ RET v; Q }}} →
  (* -> VST triple *)
  (*semax compspecs Espec Δ *)
  semax_body varspecs funspecs func (
    ident,
    NDmk_funspec (argT, retT) 
  )
  
  .
