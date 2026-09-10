Require Import FOL.DLS.Defs.
Require Import FOL.DLS.Retracts.

Section BelowAC.

  Fact prv_BAC_K_K: forall K, inhab K -> BAC_on K K.
  Proof.
    intros K k0 R htR.
    exists id.
    exact htR.
  Qed.

  Fact prv_DDC_K_K: forall K, inhab K -> DDC_on K K.
  Proof.
    intros K k0 R hdR.
    exists id.
    exact hdR.
  Qed.

  Lemma AC_K_iff_AC_K_K_and_BAC_K: forall K, inhab K ->
  (AC K <->
  (BAC K /\ AC_on K K)).
  Proof.
    intros K siK. split.
    - intros ac. split.
      + intros Y y0 R htR.
        destruct (ac _ _ R htR) as [f hf].
        exists f.
        intros k. exists k. apply hf.
      + apply (ac _ _).
    - intros [bac ac] Y y0 R htR.
      destruct (bac _ _ R htR) as [f hf].
      destruct (ac (fun k k' => R k (f k')) hf) as [g hg].
      exists (fun k => f (g k)).
      exact hg.
  Qed.

  Lemma DC_of_DDC_K_and_AC_K {K} `{siK: strongInf K}:
  (DDC K /\ AC K) -> DC.
  Proof.
    intros [ddc ac] Y y0 R htR.
    pose proof (z := _ : K * K ≤R K).
    pose proof (p := _ : K + K ≤R K).
    pose (Q := fun (r r': K -> Y) => (forall n, exists m, r n = r' m) /\
      forall n, exists k, R (r n) (r' k)).
    assert (htQ: totalR Q).
    {
      intros r.
      pose (T := fun n x => R (r n) x).
      assert (htT: totalR T).
      {
        intros n. unfold T.
        destruct (htR (r n)) as [y hy].
        exists y. apply hy.
      }
      unfold Q.
      destruct (ac _ _ T htT) as [s hs].
      exists (fun n => match retr_s p n with
        | inl n' => r n'
        | inr n' => s n' end).
      split.
      + intros n.
        exists (retr_i p (inl n)). rewrite retr_o. reflexivity.
      + intros n. unfold T in hs.
        exists (retr_i p (inr n)). rewrite retr_o.
        apply hs.
    } 
    assert (hdQ: directedR Q).
    {
      intros r r'.
      destruct (htQ r) as [s [h1s h2s]].
      destruct (htQ r') as [s' [h1s' h2s']].
      exists (fun n => match retr_s p n with | inl n' => s n' | inr n' => s' n' end).
      repeat split.
      + intros n. destruct (h1s n) as [m hm].
        exists (retr_i p (inl m)). rewrite retr_o. apply hm.
      + intros n. destruct (h2s n) as [m hm].
        exists (retr_i p (inl m)). rewrite retr_o. apply hm.
      + intros n. destruct (h1s' n) as [m hm].
        exists (retr_i p (inr m)). rewrite retr_o. apply hm.
      + intros n. destruct (h2s' n) as [m hm].
        exists (retr_i p (inr m)). rewrite retr_o. apply hm.
    }
    destruct (ddc (K -> Y) (fun _ => y0) Q hdQ) as [F hF].
    pose (rho := fun n => let (m, k) := retr_s z n in F m k).
    assert (hrho: Q rho rho).
    {
      split.
      + intros n. exists n. reflexivity.
      + intros n. unfold Q in hF. unfold rho.
        destruct (retr_s z n) as [n1 n2] eqn: en.
        destruct (hF n1 n2) as [m1 [[_ hm1] _]].
        destruct (hm1 n2) as [m2 hm2].
        exists (retr_i z (m1, m2)). rewrite retr_o. apply hm2.
    }
    destruct (hrho) as [_ H'].
    pose (U := fun n n' => R (rho n) (rho n')).
    destruct (ac _ _ U H') as [g hg].
    pose (G := fix G n k0 := match n with | 0 => k0 | S n' => g (G n' k0) end).
    exists (fun n => rho (G n (_: inhab K))).
    intros n. apply (hg).
  Qed.

  Lemma DDC_mono {K K'} {r: K ≤R K'}:
  DDC K -> DDC K'.
  Proof.
    intros ddc Y y0 R hdR.
    destruct (ddc _ _ _ hdR) as [f hf].
    exists (fun k' => f (retr_s r k')).
    intros k1' k2'.
    destruct (hf (retr_s r k1') (retr_s r k2')) as [k0 hk0].
    exists (retr_i r k0).
    rewrite retr_o.
    exact hk0.
  Qed.

End BelowAC.
Section BelowLEM.

  Lemma EP_iff_BEP_unit:
  EP <-> BEP unit.
  Proof.
    split.
    all: intros lp X x0 P.
    all: destruct (lp _ _ P) as [w hw].
    - exists (fun _ => w); intros H. exists tt; apply hw, H.
    - exists (w tt); intros H. destruct (hw H) as [[] hw']; apply hw'.
  Qed.

  Lemma DP_iff_BDP_unit:
  DP <-> BDP unit.
  Proof.
    split.
    all: intros lp X x0 P.
    all: destruct (lp _ _ P) as [w hw].
    - exists (fun _ => w); intros H. apply hw, H, tt.
    - exists (w tt); intros H. apply hw; intros []; apply H.
  Qed.

  Lemma BEP_mono {K K'} {r: K ≤R K'}:
  BEP K -> BEP K'.
  Proof.
    intros lp X x0 P.
    destruct (lp _ _ P) as [w hw].
    exists (fun k' => w (retr_s r k')).
    intros H; destruct (hw H) as [k hk]; exists (retr_i r k); rewrite retr_o; apply hk.
  Qed. 

  Lemma BDP_mono {K K'} {r: K ≤R K'}:
  BDP K -> BDP K'.
  Proof.
    intros lp X x0 P.
    destruct (lp _ _ P) as [w hw].
    exists (fun k' => w (retr_s r k')).
    intros H; apply hw; intros k; specialize (H (retr_i r k)); rewrite retr_o in H; apply H.
  Qed. 


  Lemma LEM_of_BEP_and_MP: forall B, BEP B /\ GMP B -> LEM.
  Proof.
    intros B [bep mp] p.
    pose (A := {b: bool | b = false \/ (p \/ ~ p)}).
    pose (P := fun (a: A) => let (b, _) := a in match b with | true => p \/ ~ p | false => False end).
    destruct (bep A (exist _ false (or_introl (eq_refl))) P) as [f hf].
    pose (f' := fun b => let (a, _) := f b in a).
    assert (H: p \/ ~ p  <-> (exists c, P c)).
    {
      split.
      + intros e.
        * exists (exist _ true (or_intror e)). unfold P. exact e.
      + intros [[[|] hb] ha]. all: unfold P in ha.
      2: exfalso.
      all: exact ha.
    }
    assert (H': (exists b, f' b = true) <-> (exists a, P a)).
    {
      split.
      + intros [b hb]. exists (f b). unfold P. unfold f' in hb. destruct (f b) as [x [abs|e]].
        * rewrite hb in abs. inversion abs.
        * rewrite hb. exact e.
      + intros h. destruct (hf h) as [b hb]. unfold P in hb. 
        exists b. unfold f'. destruct (f b) as [[|] hb'].
        * reflexivity.
        * exfalso. apply hb.
    }
    rewrite H, <-H'. apply (mp f'). rewrite H', <-H.
    firstorder.
  Qed.
  
  Lemma prv_MP_option {K} `{k0: inhab K}: GMP K -> GMP (option K).
  Proof.
    intros mp f.
    destruct (f None) as [|] eqn: eN.
    - intros _. exists None. exact eN.
    - intros H.
      destruct (mp (fun k => f (Some k))) as [k hk].
      + intros abs. apply H. intros [[k|] hk].
        * apply abs. exists k; apply hk.
        * rewrite eN in hk; discriminate hk.
      + exists (Some k). exact hk.
  Qed.

End BelowLEM.
Section OmniscientChoiceAxiom.

  Fact AC_and_EP_of_OAC:
  forall K, inhab K ->
  OAC K -> (AC K /\ EP).
  Proof.
    intros K k0 oac.
    split.
    + intros Y y0 R htR.
      destruct (oac _ _ R) as [f hf].
      exists f.
      apply (hf htR).
    + intros X x0 P. unfold OAC, OAC_on in oac.
      destruct (oac X _ (fun _ z => P z)) as [w hw].
      exists (w k0).
      intros [x hx].
      apply hw.
      intros _.
      exists x. apply hx.
  Qed.

  Fact OBAC_iff_BAC_and_BEP: forall K, strongInf K ->
  (OBAC K) <->
  ((BAC K) /\
  (BEP K)).
  Proof.
    intros K siK. split.
    - intros obac.
      split.
      + intros Y y0 R htR.
        destruct (obac Y y0 R) as [f hf].
        exists f.
        apply (hf htR).
      + intros X x0 P.
        destruct (obac X _ (fun _ x => P x)) as [w hw].
        exists (w).
        intros [x hx].
        refine (hw _ (_: inhab K)).
        intros _. exists x; exact hx.
    - intros [bac bep] Y y0 R.
      pose proof (z:= _ : K * K ≤R K).
      destruct (bac _ y0 (fun _ _ => True) (fun _ => ex_intro _ y0 I)) as [dummy _].
      pose (P := fun f: K -> Y => totalR (fun k k' => R k (f k'))).
      destruct (bep _ dummy P) as [f hf].
      exists (fun k => let (k1, k2) := retr_s z k in f k1 k2).
      intros htR k.
      destruct (bac Y y0 R htR) as [g hg].
      assert (exists g, P g).
      { exists g. intros k'. apply (hg k'). }
      destruct (hf H) as [k1 hk1].
      destruct (hk1 k) as [k2 hk2].
      exists (retr_i z (k1, k2)). rewrite retr_o.
      apply hk2.
  Qed.

End OmniscientChoiceAxiom.
