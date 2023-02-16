From Vloc Require Import core pure.

#[local] Ltac try_pures e' := first [
     apply pure_injrc 
   | apply pure_injlc 
   | apply pure_unop 
   | apply pure_binop 
   | apply pure_fst 
   | apply pure_snd 
   | apply pure_pairc 

   (* needed to ensure we can properly infer the true and false cases for some reason *)
   | match goal with
     | |- context [If (Val (LitV (LitBool ?b))) ?t ?f] => 
         subst e'; first [apply pure_if_false | apply pure_if_true]
     end
   (*| apply pure_if_true*)
   (*| apply pure_if_false*)
   | apply pure_case_inr 
   | apply pure_case_inl 
   (* Removes the goal created by pure_beta? *)
   | apply pure_beta; apply AsRecV_recv
   | apply pure_eqop
       (* since we're reshaping, this shouldn't be needed *)
   (*| apply pure_exec_fill *)
       (*I shouldn't need this one, I think?*)
   (*| apply pure_exec*)
   | apply (pure_recc _) (* allows inferrence? *)
   (* TODO: figure out how to actually fail with this *)
   | fail "Could not find a pure step to take (no pure_ tactic found)"
  ].

(* NOTE: this is obsolete; does not contain fixes for instruction level version *)
#[export] Ltac step_pure_r ctx :=
  let e' := fresh "e'" in
  let Hcond := fresh "Hcond" in
    lazymatch goal with
    (* if we have a decision, make it before we try to step further *)
    | |- context [ bool_decide ?cond ] => 
        destruct (bool_decide cond) eqn:Hcond;
        [apply bool_decide_eq_true in Hcond | apply bool_decide_eq_false in Hcond];
        try contradiction; try lia; 
        clear Hcond
    (* otherwise, try to step to the next instruction *)
    | |- context[refines_right ?ctx ?expr] => 
        reshape_expr expr ltac:(fun K e => 
          replace expr with (fill K e) by (by rewrite ? fill_app);
          evar (e' : iexp);
          viewshift_SEP 0 (refines_right ctx (fill K e'));
          first (
            go_lower; 
            eapply (refines_right_pure_r e e' _ _ _ K 1);
            [try_pures e' | auto | auto]
          );
          simpl in e';
          subst e';
          simpl 
          )
    | |- ?anything => fail "Could not isolate refines_right ctx [expr]. A definition may need to be unfolded!"
  end;
  simpl.


(* useful to have tactics that step a specific way *)
#[local] Ltac step_pure_r_instr tactic :=
  let e' := fresh "e'" in
  let Hcond := fresh "Hcond" in
    lazymatch goal with
    (* if we have a decision, make it before we try to step further *)
    | |- context [ bool_decide ?cond ] => 
        destruct (bool_decide cond) eqn:Hcond;
        [apply bool_decide_eq_true in Hcond | apply bool_decide_eq_false in Hcond];
        try contradiction; try lia; 
        clear Hcond
    (* anything else we carry on *)
    | |- ?anything => idtac (* do nothing tactic *)
    end;
    (* try to step to the next instruction *)
    lazymatch goal with
    | |- context[refines_right ?ctx ?expr] => 
        reshape_expr expr ltac:(fun K e => 
          replace expr with (fill K e) by (by rewrite ? fill_app);
          evar (e' : iexp);
          gather_SEP (refines_right _ _);
          viewshift_SEP 0 (refines_right ctx (fill K e'));
          first (
            go_lower; 
            eapply (refines_right_pure_r e e' _ _ _ K 1);
            [tactic e' | auto | auto]
          );
          simpl in e';
          subst e';
          simpl 
          )
    | |- ?anything => fail "Could not isolate refines_right ctx [expr]. A definition may need to be unfolded!"
  end;
  simpl.


#[export] Ltac SPR_injrc    := step_pure_r_instr  ltac:(fun _ => apply pure_injrc).
#[export] Ltac SPR_injlc    := step_pure_r_instr  ltac:(fun _ => apply pure_injlc).
#[export] Ltac SPR_unop     := step_pure_r_instr  ltac:(fun _ => apply pure_unop).
#[export] Ltac SPR_binop    := step_pure_r_instr  ltac:(fun _ => apply pure_binop).
#[export] Ltac SPR_fst      := step_pure_r_instr  ltac:(fun _ => apply pure_fst).
#[export] Ltac SPR_snd      := step_pure_r_instr  ltac:(fun _ => apply pure_snd).
#[export] Ltac SPR_pairrc   := step_pure_r_instr  ltac:(fun _ => apply pure_pairc).

(* NOTE: If requires that we know the branch we're going down in order to work *)
#[export] Ltac SPR_if_true  := step_pure_r_instr  ltac:(fun e' =>
  match goal with
  | |- context [If (Val (LitV (LitBool ?b))) ?t ?f] => 
      subst e'; apply pure_if_true
  end).
#[export] Ltac SPR_if_false  := step_pure_r_instr  ltac:(fun e' =>
  match goal with
  | |- context [If (Val (LitV (LitBool ?b))) ?t ?f] => 
      subst e'; apply pure_if_false
  end).

#[export] Ltac SPR_inr      := step_pure_r_instr  ltac:(fun _ => apply pure_case_inr).
#[export] Ltac SPR_inl      := step_pure_r_instr  ltac:(fun _ => apply pure_case_inl).

#[export] Ltac SPR_beta     := step_pure_r_instr  ltac:(fun _ => apply pure_beta; apply AsRecV_recv).
#[export] Ltac SPR_eqop     := step_pure_r_instr  ltac:(fun _ => apply pure_eqop).

#[export] Ltac SPR_recc     := step_pure_r_instr  ltac:(fun _ => apply (pure_recc _)).


(* helper stuff that isn't entirely related *)
#[export] Ltac print_goal := match goal with
                   | |- ?p => idtac "GOAL IS: " p
                   end.
  

