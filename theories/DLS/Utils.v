From Stdlib Require Import Lia.
From Stdlib Require Import Classes.Morphisms.
Require Import FOL.Core.Models.
Require Import FOL.DLS.Defs.

Section Feq.

  Definition feq {X Y} (f g: X -> Y) :=
  forall x, f x = g x.

  #[export] Instance feq_refl {X Y: Type}: Reflexive (feq (X:=X) (Y:=Y)).
  Proof.
    exact (fun f x => eq_refl (f x)).
  Qed.

  #[export] Instance feq_sym {X Y: Type}: Symmetric (feq (X:=X) (Y:=Y)).
  Proof.
    exact (fun f g e x => eq_sym (e x)).
  Qed.

  #[export] Instance feq_trans {X Y: Type}: Transitive (feq (X:=X) (Y:=Y)).
  Proof.
    exact (fun f g h efg egh x => eq_trans (efg x) (egh x)).
  Qed.

  #[export] Instance feq_eq {X Y: Type}: Equivalence (feq (X:=X) (Y:=Y)).
  Proof.
    exact (Build_Equivalence feq feq_refl feq_sym feq_trans).
  Qed.
End Feq.

Section Enveq.

  Definition enveq {M: Type} (n: nat) (rho rho': env M) :=
    forall i, (i < n) -> rho i = rho' i.

  #[export] Instance enveq_Equivalence {X: Type} (n: nat): Equivalence (@enveq X n).
  Proof.
    apply Build_Equivalence.
    - intros rho i _. reflexivity.
    - intros rho rho' H i hi. symmetry. exact (H i hi).
    - intros rho0 rho1 rho2 H01 H12 i hi. transitivity (rho1 i); [apply (H01 i hi) | apply (H12 i hi)].
  Qed.

  Lemma enveq_0 {X} {rho rho': env X}: enveq 0 rho rho'.
  Proof.
    intros i hi. lia.
  Qed.

  Lemma enveq_S {X} {n} {rho rho': env X}:
  rho 0 = rho' 0 ->
  enveq n (S >> rho) (S >> rho') ->
  enveq (S n) rho rho'.
  Proof.
    intros h0 hS [|i'] hi.
    - apply h0.
    - apply hS. lia.
  Qed.

  Lemma enveq_n_of_le {X: Type}:
  forall n m, n <= m ->
  forall (rho rho': nat -> X), enveq m rho rho' -> enveq n rho rho'.
  Proof.
    intros n m hnm rho rho' H i hi.
    apply (H i).
    lia.
  Qed.

  Lemma map_In {A B: Type} (f: A -> B) {n} (v: vec A n) (a: A):
  In a v -> In (f a) (map f v).
  Proof.
    intros H.
    induction H as [n' t|n' h t H ih].
    all: simpl.
    - apply In_cons_hd. 
    - apply In_cons_tl, ih.
  Qed.

  Context {s_f: funcs_signature} {s_P:  preds_signature}.
  Context {M: model} {m0: M}.

  Fixpoint max_vec {n} (v: vec nat n): nat :=
  match v with
  | nil _ => 0
  | cons _ h _ t => max h (max_vec t)
  end.

  Fixpoint term_max_var (t: term):= match t with
  | var i => S i 
  | func f v => max_vec (map term_max_var v)
  end.

  Lemma max_vec_In {n}:
  forall (v: vec nat n) k,
  In k v -> k <= max_vec v.
  Proof.
    intros v k H. induction H.
    all: simpl; lia.
  Qed.

  Lemma term_max_var_le {n} (v: vec term n) (u: term):
  In u v ->
  (term_max_var u <= max_vec (map term_max_var v)).
  Proof.
    intros hu. induction hu. 
    all: simpl; lia.
  Qed.

  Lemma term_max_var_prop (t: term):
  forall rho rho', enveq (term_max_var t) rho rho' ->
  t ₜ[M] rho = t ₜ[M] rho'.
  Proof.
    induction t as [i|f v IH]. all: intros rho rho' heq.
    + simpl in *. apply heq. eauto.
    + simpl. f_equal. apply map_ext_in. intros st hst. apply (IH st hst).
      apply (@enveq_n_of_le _ (term_max_var st) (term_max_var (func f v))).
      - apply (term_max_var_le _ _ hst).
      - apply heq.
  Qed.

  Fixpoint form_max_var {fff: falsity_flag} (phi: form) := match phi with
    | falsity => 0
    | atom P v => max_vec (map term_max_var v)
    | bin b psi1 psi2 => max (form_max_var psi1) (form_max_var psi2)
    | quant Q psi => form_max_var psi
    end.

  Lemma equiv_of_eq (X: Type) (p: X -> Prop):
  forall x x', x = x' -> p x <-> p x'.
  Proof.
    intros x x' e. rewrite e. reflexivity.
  Qed.

  Lemma form_max_var_prop {fff: falsity_flag}:
  forall phi: form, forall rho rho' : env M,
  enveq (form_max_var phi) rho rho' ->
  sat (interp' M) rho phi <-> sat (interp' M) rho' phi.
  Proof.
    intros phi.
    induction phi as [|fff P v|fff bo phi IHphi psi IHpsi|fff Q psi IHpsi].
    + reflexivity.
    + intros rho rho' e. simpl.
      unfold i_atom.
      apply equiv_of_eq, map_ext_in.
      intros t0 ht0.
      apply (map_In term_max_var) in ht0.
      simpl in e. 
      apply
        term_max_var_prop,
        (enveq_n_of_le _ _ (max_vec_In _ _ ht0) _ _ e).
    + intros rho rho' e. destruct bo.
      all: cbn.
      all: rewrite (IHphi rho rho'), (IHpsi rho rho').
      1,4,7: reflexivity.
      5,6: refine (enveq_n_of_le _ (form_max_var (phi → psi)) _ _ _ e).
      3,4: refine (enveq_n_of_le _ (form_max_var (phi ∨ psi)) _ _ _ e).
      1,2: refine (enveq_n_of_le _ (form_max_var (phi ∧ psi)) _ _ _ e).
      all: simpl; lia.
    + intros rho rho' e.
      destruct Q.
      all: cbn.
      all: split.
      1,2: intros H m.
      3,4: intros [m H]; exists m.
      4: erewrite <-(IHpsi (m .: rho') (m .: rho) _); apply H.
      3: erewrite (IHpsi (m .: rho') (m .: rho) _); apply H.
      2: erewrite <-(IHpsi (m .: rho') (m .: rho) _); apply H.
      1: erewrite (IHpsi (m .: rho') (m .: rho) _); apply H.
      Unshelve. 
      all: symmetry; apply (enveq_n_of_le _ (S (form_max_var psi))). 
      all: try lia.
      all: refine (enveq_S _ e).
      all: reflexivity.
  Qed.

End Enveq.

Section FinEnv.

  Fixpoint vec2env {X} {n} (v: vec X n) (x0: X): env X :=
  match v with
  | nil _ => fun _ => x0
  | cons _ h _ t => h .: (vec2env t x0)
  end.
  
  Fixpoint env2vec {X} n (rho: env X): vec X n :=
  match n with
  | 0 => nil X 
  | S n' => cons X (rho 0) n' (env2vec n' (fun i => rho (S i)))
  end.

  Lemma enveq_env2vec_vec2env {X n} :
  forall (rho: env X) x,
  enveq n rho (vec2env (env2vec n rho) x).
  Proof.
    induction n as [|n' ihn].
    - intros rho x. apply enveq_0.
    - intros rho x. apply enveq_S.
      + reflexivity.
      + apply ihn.
  Qed.

  Lemma map_env2vec_comm: forall X Y (f: X -> Y),
  forall n, forall rho, map f (env2vec n rho) = env2vec n (fun n => f (rho n)).
  Proof.
    intros X Y f n. induction n as [|n' ihn].
    - intros rho. reflexivity.
    - intros rho. simpl. f_equal. apply ihn.
  Qed.

  Context {fff: falsity_flag}.
  Context {s_f: funcs_signature}.
  Context {s_P: preds_signature}.
  Context {M: model} (m0: M).

  Definition sat' {l} phi (v: vec M l) :=
  sat (interp' M) (vec2env v m0) phi.

End FinEnv.
