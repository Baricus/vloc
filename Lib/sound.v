From Vloc Require Import theory.

(* Two different approaches we could take:
    - syntactical relation between predicates 
    - semantic relationship between C and HeapLang 
 *)


Context `{!heapGS Σ}.

Axiom syn_relate : iProp Σ -> mpred -> Prop.

(*Definition semax_body*)
   (*(V: varspecs) (G: funspecs) {C: compspecs} (f: function) (spec: ident * funspec): Prop :=*)
(*match spec with (_, mk_funspec fsig cc A P Q _ _) =>*)
  (*fst fsig = map snd (fst (fn_funsig f)) /\*)
  (*snd fsig = snd (fn_funsig f) /\*)
(*forall Espec ts (x:dependent_type_functor_rec ts A mpred),*)
  (*semax Espec (func_tycontext f V G nil)*)
      (*(fun rho => close_precondition (map fst f.(fn_params)) (P ts x) rho * stackframe_of f rho)*)
       (*f.(fn_body)*)
      (*(frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts x)) (stackframe_of f))*)
(*end.*)

(*Notation "'WITH' x : tx 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=*)
  (*(NDmk_funspec (pair (cons u .. (cons v nil) ..) tz) cc_default tx*)
     (*(fun x => P) (fun x => Q)) : funspec_scope (default interpretation)*)

Lemma syn_relate_sound P e v Q P' Q' varspecs funspecs compspecs func ident argTs retT tx:
  syn_relate P P' →
  syn_relate Q Q' →
  {{{ P }}} e {{{ RET v; Q }}} →
  (* -> VST triple *)
  (*semax compspecs Espec Δ *)
  semax_body varspecs funspecs func (
    ident,
    NDmk_funspec (argTs, retT) cc_default tx (fun x y => P') (fun x y => Q') 
  )
  
  .
