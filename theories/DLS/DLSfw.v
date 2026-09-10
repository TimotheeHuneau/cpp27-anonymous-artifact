From Stdlib Require Import Lia.
Require Import FOL.Core.Models.
Require Import FOL.DLS.Retracts.
Require Import FOL.DLS.Defs.
Require Import FOL.DLS.Utils.
Require Import FOL.DLS.Signatures.
Require Import FOL.DLS.SubsetsDefs.

Section TarskiVaught.

    Context {fff: falsity_flag}.
    Context {s_f: funcs_signature}.
    Context {s_P: preds_signature}.
    Context {M: model} (m0: M).

    Context {K: Type}.
    Context (siK: strongInf K).
    Context (r: s_f + s_P ≤R K).
    Abbreviation p := (X_add_X_retr_X_of_si_X siK).
    Abbreviation z := (X_mul_X_retr_X_of_si_X siK).
    Abbreviation k0 := (X_of_si_X siK).

    Definition TVall {ffff: falsity_flag} (A B: smallsubset M K) :=
    forall (phi: form) (va: vec (termK K) (form_max_var (∀ phi))),
    (forall b: K, (sat' m0 phi (cons _ (B b) _ (map (closure A) va)))) ->
    (sat' m0 (∀ phi) (map (closure A) va)).

    Definition TVex {ffff: falsity_flag} (A B: smallsubset M K) :=
    forall (phi: form) (va: vec (termK K) (form_max_var (∃ phi))),
    (sat' m0 (∃ phi) (map (closure A) va)) ->
    (exists b: K, (sat' m0 phi (cons _ (B b) _ (map (closure A) va)))).

    Definition TV {ffff: falsity_flag} (A B: smallsubset M K) :=
    included A B /\ (TVex A B /\ TVall A B).

    Lemma eval_comm_closure:
    forall (A: smallsubset M K) rho,
    feq
    (fun u => closure A (eval _ (interp_on_closure A) rho u))
    (eval M (interp' M) (fun n => (closure A) (rho n))).
    Proof.
      intros A rho u. induction u as [k|f v ih].
      - reflexivity.
      - simpl. f_equal.
        rewrite map_map. apply map_ext_in. exact ih.
    Qed.

    Lemma elemsubm_of_TV_fixpoint (A: smallsubset M K):
    TV A A ->
    Build_model (interp_on_closure A) ⪳[ closure A ] M.
    Proof.
      intros [_ [Hex Hall]] phi.
      induction phi as [| P0 v|f b phi1 ih1 phi2 ih2|f Q psi ih].
      all: intros rho.
      - reflexivity.
      - simpl. rewrite map_map.
        rewrite (map_ext _ _ _ _ (eval_comm_closure A rho)).
        reflexivity.
      - destruct b.
        all: simpl; rewrite (ih1 Hex Hall), (ih2 Hex Hall).
        all: reflexivity. 
      - destruct Q. all: split.
        + intros H.
          assert (Hall' := Hall psi (env2vec (form_max_var (∀ psi)) rho)).
          unfold sat' in Hall'.
          rewrite (form_max_var_prop ).
          1: apply Hall'.
          1: intros a; specialize (H (varK a)).
          1: rewrite (ih Hex Hall) in H.
          1: rewrite (form_max_var_prop).
          1: apply H.
          {
            rewrite map_env2vec_comm.
            apply (enveq_n_of_le _ (S (form_max_var psi))). { lia. }
            apply enveq_S.
            - reflexivity.
            - unfold ">>", ".:". symmetry.
              apply enveq_env2vec_vec2env.
          }{
            rewrite map_env2vec_comm.
            apply enveq_env2vec_vec2env.
          }
        + intros H a. rewrite (ih Hex Hall). specialize (H (closure A a)).
          rewrite form_max_var_prop.
          1: apply H.
          { intros [|i] _. all: reflexivity. }
        + intros [a H]. exists (closure A a). rewrite (ih Hex Hall) in H.
          rewrite <-form_max_var_prop.
          1: apply H.
          { intros [|i] _. all: reflexivity. }
        + intros [m H].
          assert (Hex' := Hex psi (env2vec (form_max_var (∃ psi)) rho)).
          unfold sat' in Hex'.
          rewrite form_max_var_prop in Hex'.
          1: destruct (Hex' (ex_intro _ m H)) as [w Hw].
          1: exists (varK w).
          1: rewrite (ih Hex Hall).
          1: rewrite form_max_var_prop.
          1: exact Hw.
          {
            apply (enveq_n_of_le _ (S (form_max_var psi))). { lia. }
            rewrite map_env2vec_comm.
            apply enveq_S.
            - reflexivity.
            - unfold ">>", ".:".
              apply enveq_env2vec_vec2env.
          }{
            rewrite map_env2vec_comm.
            symmetry. apply enveq_env2vec_vec2env. 
          }
    Qed.

    Lemma TVex_rightmono: rightmono TVex.
    Proof.
      intros A B C HTVexAB [iota hiota] phi v H.
      destruct (HTVexAB phi v H) as [b hb].
      exists (iota b).
      rewrite <-hiota.
      assumption.
    Qed.

    Lemma TVall_rightmono: rightmono TVall.
    Proof.
      intros A B C HTVallAB [iota hiota] phi v H.
      specialize (HTVallAB phi v). apply HTVallAB.
      intros b. specialize (H (iota b)).
      rewrite hiota.
      assumption.
    Qed.

    Lemma TV_rightmono: rightmono TV.
    Proof.
      unfold TV.
      refine (rightmono_inter _ (rightmono_inter _ _)).
      - exact included_rightmono.
      - exact TVex_rightmono.
      - exact TVall_rightmono.
    Qed.

End TarskiVaught.
#[global] Arguments TV_rightmono {_ _ _ _ _}.

Section Forward.

  Context {fff: falsity_flag}.
  Context {s_f: funcs_signature}.
  Context {s_P: preds_signature}.
  Context `{p0: inhab s_P}.

  Context {K: Type}.
  Context (r: s_f + s_P ≤R K).
  Context (siK: strongInf K).
  Abbreviation p := (X_add_X_retr_X_of_si_X siK).
  Abbreviation z := (X_mul_X_retr_X_of_si_X siK).
  Abbreviation k0 := (X_of_si_X siK).

  Section FixM.

    Context {M: model} {m0: M}.

    Lemma TV_fixpoint_of_directed_family:
    (exists F: K -> smallsubset M K, directedR (fun k1 k2 => TV m0 (F k1) (F k2))) ->
    exists A: smallsubset M K, TV m0 A A.
    Proof.
      intros [F HF].
      assert (Hincl: directedR (fun k1 k2 => included (F k1) (F k2))).
      {
        intros k1 k2. destruct (HF k1 k2) as [k0 [[H1 _] [H2 _]]].
        exists k0.
        split; assumption.
      }
      assert (HTVex: totalR (fun k1 k2 => TVex m0 (F k1) (F k2))).
      {
        intros k1. destruct (HF k1 k1) as [k0 [[_ [H1 _]] _]].
        exists k0.
        assumption.
      }
      assert (HTVall: totalR (fun k1 k2 => TVall m0 (F k1) (F k2))).
      {
        intros k1. destruct (HF k1 k1) as [k0 [[_ [_ H1]] _]].
        exists k0.
        assumption.
      }
      exists (union siK F).
      repeat split.
      1: reflexivity.
      all: intros phi v H.
      all: destruct (uniform_clos_vec siK Hincl (existT _ _ v)) as [j [v' hvj']].
      1: destruct (HTVex j) as [j' Hj'].
      2: destruct (HTVall j) as [j' Hj'].
      all: destruct (included_union siK F j') as [iota hiota].
      all: specialize (Hj' phi v').
      all: rewrite <-hvj' in Hj'. 
      - specialize (Hj' H).
        destruct Hj' as [b hb].
        exists (iota b).
        rewrite <-hiota.
        apply hb.
      - apply Hj'.
        intros b.
        specialize (H (iota b)).
        rewrite <-hiota in H.
        apply H.
    Qed.

    Lemma DLS_of_DDC_and_TV_total:
    DDC K ->
    totalR (TV m0 (K:=K)) ->
    DLS_on K M.
    Proof.
      intros ddc H.
      apply (directed_of_total_of_rightmono siK (TV_rightmono K)) in H.
      unfold DLS_on.
      destruct (TV_fixpoint_of_directed_family (ddc _ (fun _ => m0) (TV m0) H)) as [A HA].
      exists (Build_model (interp_on_closure A)).
      split.
      - exists (closure A).
        exact (elemsubm_of_TV_fixpoint _ _ HA).
      - exact (inhabits _).
    Qed.

    Definition Rex (A: smallsubset M K):
    (sigT (fun phi => vec (termK K) ((form_max_var (∃ phi))))) ->
    (K -> M) ->
    Prop :=
    fun p mu => match p with
    | existT _ phi v =>
      (sat' m0 (∃ phi) (map (closure A) v)) ->
      (exists b: K,
        sat' m0 phi (cons _ (mu b) _ (map (closure A) v)))
    end.

    Definition Rall (A: smallsubset M K):
    (sigT (fun phi => vec (termK K) ((form_max_var (∀ phi))))) ->
    (K -> M) ->
    Prop :=
    fun p mu => match p with
    | existT _ phi v =>
      (forall b: K,
        sat' m0 phi (cons _ (mu b) _ (map (closure A) v))) ->
      (sat' m0 (∀ phi) (map (closure A) v))
    end.

    Fact Rex_total_of_BEP {A: smallsubset M K}:
    BEP K ->
    totalR (Rex A).
    Proof.
      intros bep [phi v].
      destruct (bep
        M
        m0
        (fun m => sat' m0 phi (cons _ m _ (map (closure A) v))))
        as [mu H].
      exists mu.
      intros [m hm]. apply H. exists m.
      unfold sat'.
      rewrite form_max_var_prop.
      apply hm. reflexivity. 
    Qed.

    Fact Rall_total_of_BDP {A: smallsubset M K}:
    BDP K ->
    totalR (Rall A).
    Proof.
      intros bdp [phi v].
      destruct (bdp
        M
        m0
        (fun m => sat' m0 phi (cons _ m _ (map (closure A) v))))
        as [mu H].
      exists mu.
      intros hm m. specialize (H hm m).
      unfold sat' in H.
      rewrite form_max_var_prop.
      apply H. reflexivity. 
    Qed.

    Lemma TV_total_of_BAC_BEP_BDP:
    BAC K ->
    BEP K ->
    BDP K ->
    totalR (TV m0 (K:=K)).
    Proof.
      intros bac bep bdp A.
      pose proof (hte := Rex_total_of_BEP (A:=A) bep).
      pose proof (hta := Rall_total_of_BDP (A:=A) bdp).
      pose proof (R := _ : {phi: form s_f s_P & vec (termK K) (form_max_var phi)} ≤R K).

      pose (Rex' := fun k mu => Rex A (retr_s R k) mu).
      destruct (bac _ (fun _ => m0) Rex' (fun k => hte (retr_s R k))) as [gEx hgEx].
      pose (Be := union siK gEx).
      pose (Rall' := fun k mu => Rall A (retr_s R k) mu).
      destruct (bac _ (fun _ => m0) Rall' (fun k => hta (retr_s R k))) as [gAll hgAll].
      pose (Ba := union siK gAll).

      unfold Rex', Rex in hgEx.
      unfold Rall', Rall in hgAll.

      exists (bunion siK A (bunion siK Be Ba)).
      repeat split; [ apply l_included_bunion | | ].
      - refine (TVex_rightmono _ _ Be _ _ _).
        + intros phi v H.
          destruct (hgEx (retr_i R (existT _ phi v))) as [j hj].
          rewrite retr_o in hj.
          destruct (included_union siK gEx j) as [iota hiota].
          destruct (hj H) as [a' ha'].
          exists (iota a').
          rewrite hiota in ha'.
          assumption.
        + transitivity (bunion siK Be Ba); [ apply l_included_bunion | apply r_included_bunion ].
      - refine (TVall_rightmono _ _ Ba _ _ _).
        + intros phi v H.
          destruct (hgAll (retr_i R (existT _ phi v))) as [j hj].
          rewrite retr_o in hj.
          destruct (included_union siK gAll j) as [iota hiota].
          apply hj. intros a'.
          specialize (H (iota a')).
          rewrite hiota.
          assumption.
        + transitivity (bunion siK Be Ba); [ apply r_included_bunion | apply r_included_bunion ].
    Qed.

  End FixM.

  Theorem DLS_of_BAC_DDC_BDP_BEP:
  BAC K ->
  DDC K ->
  BDP K ->
  BEP K ->
  DLS K.
  Proof.
    intros bac ddc bdp bep M m0.
    refine (DLS_of_DDC_and_TV_total (m0:=m0) ddc _).
    refine (TV_total_of_BAC_BEP_BDP bac bep bdp).
  Qed.

End Forward.

