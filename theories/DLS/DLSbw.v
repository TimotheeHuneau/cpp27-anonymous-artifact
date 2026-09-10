Require Import FOL.Core.Models.
Require Import FOL.DLS.Retracts.
Require Import FOL.DLS.Defs.
Require Import FOL.DLS.Utils.
Require Import FOL.DLS.Signatures.
Require Import FOL.DLS.DLSalt.

Existing Instance falsity_on.
Existing Instance s_0f.

Section Unification.

  Context {fff: falsity_flag}.
  Context {n: nat}.
  Context {T: Type}.

  (* Interpretation of function symbols when there are none *)
  Definition I_0f X: forall f: s_0f, vec X (ar_syms f) -> X :=
  fun f => match f: False with end.
  Arguments I_0f _: clear implicits.

  Definition s_TPn := (s_XPn T n).
  Existing Instance s_TPn.

  Definition relation_family X := T -> vec X n -> Prop.
  Definition I_TPn X (r: relation_family X): forall f, vec X (ar_preds f) -> Prop := fun t => r t.
  Arguments I_TPn {_} _.

  Definition canonModel {X} (r: relation_family X): model  :=
  (Build_model (B_I (I_0f X) (I_TPn r))).

  Lemma canonelemsubm {X} {r: relation_family X} {U: model} {h: U -> X}:
  (U ⪳[h] canonModel r) ->
  (canonModel (fun t v => r t (map h v))) ⪳[h] canonModel r.
  Proof.
    intros Hes.
    intros psi. induction psi as [|fff f v|fff b psi1 ih1 psi2 ih2|fff q phi IHphi].
    all: intros rho.
    - reflexivity.
    - simpl; unfold I_TPn.
      apply equiv_of_eq.
      rewrite map_map.
      apply map_ext.
      intros [j|[] _].
      unfold ">>". reflexivity.
    - destruct b.
      all: simpl in *.
      all: rewrite (ih1 Hes), (ih2 Hes).
      all: reflexivity.
    - rewrite <-(Hes (quant q phi) rho).
      specialize (IHphi Hes).
      destruct q; split; simpl in *.
      1,2: intros H x; specialize (H x).
      3,4: intros [x H]; exists x.
      all: destruct (IHphi (x .: rho)) as [IHl IHr].
      all: rewrite <-(Hes phi) in IHl, IHr.
      1,3: apply (IHl H). 
      all: apply (IHr H).
  Qed.

  Definition blurring X (psi: T -> form) :=
  forall Y (hY: inhabited Y),
  forall r, exists h: X -> Y,
  forall t rho,
  (sat (interp' (canonModel r)) (rho >> h) (psi t)) <-> 
  (sat (interp' (canonModel (fun t' v => r t' (map h v)))) rho (psi t)).

  Theorem blurring_of_DLS (X: Type):
  forall psi,
  DLS' X ->
  blurring X psi.
  Proof.
    intros psi dls Y [y] r.
    destruct (dls (canonModel r) y) as [IX [h HX]].
    exists h.
    intros t rho.
    symmetry.
    apply (canonelemsubm HX (psi t) rho).
  Qed.

End Unification.
Section Specific_forms.

  Import VectorNotations.

  Definition psi_DDC :=
  fun p: unit => ∀ (∀ (∃ (atom (p: s_1P2) ([$2; $0]) ∧ atom (p: s_1P2) ([$1; $0])))).
  (* We use de Bruijn indices: this exactly is ∀ x2 x1. ∃ x0. ((p x2 x0) ∧ (p x1 x0)) *)
  Lemma psi_DDC_prop {K} (x: K):
  blurring K psi_DDC -> DDC K.
  Proof.
    intros H Y y r hdr.
    destruct (H Y (inhabits y) (fun _ v => r (hd v) (hd (tl v)))) as [h Hb].
    exists h.
    destruct (Hb tt (fun _ => x)) as [Hb' _]; simpl in Hb'; unfold I_TPn in Hb'.
    exact (Hb' hdr).
  Qed.
  Theorem DDC_of_DLS1 {K} {x: inhab K}:
  DLS s_0f (s_1P2) K -> DDC K.
  Proof.
    rewrite DLS_eqv_DLS'.
    intros dls.
    apply (psi_DDC_prop x).
    apply blurring_of_DLS.
    apply dls.
  Qed.

  Definition psi_BEP := fun p: unit => ∃ (atom (p: s_1P1) ([$0])).
  Lemma psi_BEP_prop {K} (x: K):
  blurring K psi_BEP -> BEP K.
  Proof.
    intros H Y y r.
    destruct (H Y (inhabits y) (fun _ v => r (hd v))) as [h Hb].
    exists h.
    destruct (Hb tt (fun _ => x)) as [Hb' _]; simpl in Hb'; unfold I_TPn in Hb'.
    intros he.
    exact (Hb' he).
  Qed.
  Theorem BEP_of_DLS1 {K} {x: inhab K}:
  DLS s_0f s_1P1 K -> BEP K.
  Proof.

    rewrite DLS_eqv_DLS'.
    intros dls.
    apply (psi_BEP_prop x).
    apply blurring_of_DLS.
    apply dls.
  Qed.

  Definition psi_BDP := fun p: unit => ∀ (atom (p: s_1P1) ([$0])).
  Lemma psi_BDP_prop {K} (x: K):
  blurring K psi_BDP -> BDP K.
  Proof.
    intros H Y y r.
    destruct (H Y (inhabits y) (fun _ v => r (hd v))) as [h Hb].
    exists h.
    destruct (Hb tt (fun _ => x)) as [_ Hb']; simpl in Hb'; unfold I_TPn in Hb'.
    intros ha.
    exact (Hb' ha).
  Qed.
  Theorem BDP_of_DLS1 {K} {x: inhab K}:
  DLS s_0f s_1P1 K -> BDP K.
  Proof.
    rewrite DLS_eqv_DLS'.
    intros dls.
    apply (psi_BDP_prop x).
    apply blurring_of_DLS.
    apply dls.
  Qed.

  Definition psi_BAC K := fun x: K => ∃ (atom (x: s_XPn K 1) ([$0])).
  Lemma psi_BAC_prop {K} (x: K):
  blurring K (@psi_BAC K) -> BAC K.
  Proof.
    intros H Y y r htr.
    destruct (H Y (inhabits y) (fun x' v => r x' (hd v))) as [h Hb].
    exists h.
    intros x'.
    destruct (Hb x' (fun _ => x)) as [Hb' _]; simpl in Hb'; unfold I_TPn in Hb'.
    apply (Hb' (htr x')).
  Qed.
  Theorem BAC_of_DLSK {K} {x: inhab K}:
  DLS s_0f (s_XPn K 1) K -> BAC K.
  Proof.
    rewrite DLS_eqv_DLS'.
    intros dls.
    apply (psi_BAC_prop x).
    apply blurring_of_DLS.
    apply dls.
  Qed.

End Specific_forms.
