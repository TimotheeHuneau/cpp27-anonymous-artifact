Require Import FOL.Core.Models.
Require Import FOL.DLS.Retracts.
Require Import FOL.DLS.Defs.
Require Import FOL.DLS.Utils.

Section Defs.

  Context {s_f: funcs_signature} {s_P: preds_signature}.

  Definition interp_of_retract {A B: Type}:
  A ≤R B -> interp A -> interp B.
  Proof.
    intros [i s o] [A_func A_atom].
    pose (B_func := fun f v => i (A_func f (map s v))).
    pose (B_atom := fun p v => A_atom p (map s v)).
    apply (B_I B_func B_atom).
  Defined.

End Defs.

Section IntermediaryLemmas.

  Context {fff: falsity_flag} {s_f: funcs_signature} {s_P: preds_signature}.

  Lemma eval_comm_interp_of_retract' {A: model} {B: Type} (r: A ≤R B):
  forall (n: nat) (v: vec term n) (rho: env B),
    map (retr_s r) (map (eval B (interp_of_retract r (interp' A)) rho) v) =
    (map (eval A (interp' A) (fun n => (retr_s r) (rho n))) v).
  Proof.
    intros n v. induction v as [|hv n' tv ih]. all: intros rho.
    + reflexivity.
    + simpl. f_equal.
      - unfold interp_of_retract, eval. induction hv as [| f vv ihvv].
        * reflexivity.
        * destruct r as [i s o]. destruct (interp'). simpl in *.
          rewrite o. f_equal. rewrite map_map.
          apply map_ext_in. intros t ht. specialize (ihvv t ht). rewrite ihvv. reflexivity.
      - apply ih.
  Qed.

  Lemma elemsubm_of_retract {M A: model} {B: Type} (r: A ≤R B):
  A ⪳ M -> (Build_model (interp_of_retract r (interp' A))) ⪳ M.
  Proof.
    intros [h hh].
    exists (fun b => h (retr_s r b)).
    intros phi. induction phi as [|fff' p0 v|fff' b phi1 ih1 phi2 ih2|fff' q psi ih]. all: intros rho.
    - reflexivity.
    - unfold elementary_homomorphism, ">>" in *.
      rewrite <-(hh (atom p0 v)). simpl.
      rewrite <-(eval_comm_interp_of_retract' r).
      unfold i_atom. unfold eval. destruct r as [i s o]. destruct interp'. reflexivity.
    - destruct b. all: firstorder.
    - specialize (ih hh).
      assert (hhQ := hh (quant q psi)).
      assert (hh0 := hh psi).
      destruct q.
      all: split.
      + unfold ">>", ".:" in *; rewrite <-hhQ.
        intros H a; specialize (H (retr_i r a)).
        rewrite <-(retr_o r a), hh0, form_max_var_prop, <-ih.
        1: apply H.
        { intros [|i'] _. all: reflexivity. }
      + intros H a; specialize (H (h (retr_s r a))).
        rewrite ih.
        rewrite <-form_max_var_prop.
        1: apply H.
        { intros [|i'] _. all: reflexivity. }        
      + intros [a H]; exists (h ((retr_s r) a)).
        rewrite form_max_var_prop.
        rewrite <-ih .
        1: apply H.
        { intros [|i'] _. all: reflexivity. }
      + unfold ".:", ">>" in *; rewrite <-hhQ.
        intros [a H]; exists (retr_i r a).
        rewrite hh0, <-(retr_o r a), (form_max_var_prop), <-ih in H.
        1: apply H.
        { intros [|i'] _. all: reflexivity. }
  Qed.

End IntermediaryLemmas.

Lemma DLS_of_DLS' {fff: falsity_flag} {s_f: funcs_signature} {s_P: preds_signature}:
  forall (B: Type),
  DLS' B -> DLS B.
Proof.
  intros B dls M m0.
  destruct (dls M m0) as [N hN].
  exists (Build_model N).
  split.
  + apply hN.
  + exact (inhabits _).
Qed.

Lemma DLS'_of_DLS {fff: falsity_flag} {s_f: funcs_signature} {s_P: preds_signature}:
  forall (B: Type),
  DLS B -> DLS' B.
Proof.
  intros B dls M m0.
  destruct (dls M m0) as [N [hN [rN]]].
  exists (interp_of_retract rN (interp' N)).
  apply (elemsubm_of_retract rN hN).
Qed.

Theorem DLS_eqv_DLS'
  {fff: falsity_flag} {s_f: funcs_signature} {s_P: preds_signature}:
forall B, DLS B <-> DLS' B.
Proof.
  intros B; split; [apply DLS'_of_DLS | apply DLS_of_DLS'].
Qed.