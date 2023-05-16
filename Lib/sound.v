From Vloc Require Import theory.

From VST Require Import floyd.proofauto.

(* Two different approaches we could take:
    - syntactical relation between predicates 
    - semantic relationship between C and HeapLang 
 *)

(* Third approach:
    - use A as the relationship directly
 *)


Context `{!heapGS Σ}.

Context {cs: compspecs}.

Context `{refines_ctx}.

Axiom syn_relate : iProp Σ -> mpred -> Prop.

Definition refines varspecs funspecs func ident argTs retT with_type (P : with_type -> argsEnviron -> mpred) (ie : iexp) (rhs : sum iexp ref_id) (A : expr -> iexp -> mpred) :=
  semax_body (C:=cs) varspecs funspecs func
  (
    ident, 
    (*TODO: emp -> refines_right ctx *)
    NDmk_funspec (argTs, retT) cc_default with_type 
    (fun a b => P a b * 
      (∀ j : ref_id,
      match rhs with
      | inl e' => refines_right j e'
      | inr k => !! (j = k) && emp
      end
    ))%logic
    (fun wc environ => (EX Vres, EX Ires, (sepcon (A Vres Ires) (EX ctx, refines_right ctx (Ires)))))
    (*mk_funspec (argTs, retT) cc_default with_type *)
      (*(fun x y => P) *)
      (*(fun x y => ())*)
  ).


(*Definition refines_def (E : coPset)*)
  (*(e : expr) (e'k : rhs_t) (A : lrel Σ) : iProp Σ :=*)
  (*(∀ j : ref_id,*)
  (*match e'k with*)
    (*[> if it is an expression, it refines it to the right <]*)
  (*| inl e' => refines_right j e'*)
      (*[> if it is not, so it is a reference #, they are equal (pure fact) <]*)
  (*| inr k  => ⌜j = k⌝*)
  (*end -∗*)
 (*|={E,⊤}=> WP e {{ v, ∃ v', refines_right j (of_val v') ∗ A v v' }})%I.*)

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

(* Currently:
    - No restrictions on P, Q, P', Q'
      - it should have something!
      - Do we just have a 2nd triple for the VSTLoc version?
      - A needs to show up in the final triple (or just in the refinement triple?)
*)
Lemma syn_relate_sound 
  varspecs funspecs func ident argTs retT with_type
  (P : iProp Σ) e v (Q : iProp Σ) (P' : mpred) (Q' : mpred):
  (* VSTLoC Triple *)
  
  (* relationship between structures *)
  syn_relate P P' →
  syn_relate Q Q' →
  (* HeapLang triple *)
  {{{ P }}} e {{{ RET v; Q }}} →
  (* -> VST triple *)
  (*semax compspecs Espec Δ *)
  semax_body varspecs funspecs func (
    ident,
    (* x => WITH clauses, y => environment (args/return) *)
    NDmk_funspec (argTs, retT) cc_default with_type (fun x y => P') (fun x y => Q') 
  )
  .
