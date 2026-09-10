
Require Import FOL.DLS.Defs.
Require Import FOL.DLS.DLSfw.
Require Import FOL.DLS.DLSbw.

Existing Instance falsity_on.

Theorem main_result: DLS_iff_BEP_BDP_BAC_DDC.
Proof.
  intros K [siK]. split.
  - intros [[bdp bep] [ddc bac]] s_f s_P p0 r.
    refine (DLS_of_BAC_DDC_BDP_BEP _ _ _ _ _ _).
    all: assumption.
  - intros H; repeat split.
    + refine (BDP_of_DLS1 (H _ _ _ _)).
    + refine (BEP_of_DLS1 (H _ _ _ _)).
    + refine (DDC_of_DLS1 (H _ _ _ _)).
    + refine (BAC_of_DLSK (H _ _ _ _)).
Qed.

Print Assumptions main_result.

Require Import FOL.DLS.Retracts.

Lemma is_Kirst_and_Zeng_generalisation:
DLS_iff_BEP_BDP_BAC_DDC ->
((BDP nat /\ BEP nat) /\ (DDC nat /\ BAC nat)) <->
  (forall (s_f: funcs_signature) (s_P: preds_signature), s_P ->
    s_f + s_P ≤R nat -> DLS nat).
Proof.
  intros H. 
  destruct (H nat (inhabits _)) as [Hl Hr].
  split.
  all: intros h.
  1: apply Hl.
  2: apply Hr.
  all: assumption.
Qed.
