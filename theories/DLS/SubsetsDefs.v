From Stdlib Require Import Classes.Morphisms.
From Stdlib Require Import Lia.
Require Import FOL.Core.Models.
Require Import FOL.DLS.Retracts.
Require Import FOL.DLS.Defs.
Require Import FOL.DLS.Utils.
Require Import FOL.DLS.Signatures.

From Equations Require Import Equations.

Section Defs.

  Context {X K: Type}.
  Context (siK: strongInf K).
  Abbreviation p := (X_add_X_retr_X_of_si_X siK).
  Abbreviation z := (X_mul_X_retr_X_of_si_X siK).

  Definition smallsubset: Type :=  K -> X.

  Definition included: smallsubset -> smallsubset -> Prop :=
  fun A B => exists j: K -> K, feq A (fun a => (B (j a))).

  Definition bunion (A B: smallsubset): smallsubset :=
    (fun k =>
    match retr_s p k with
    | inl k' => A k'
    | inr k' => B k'
    end).

  Definition union (A: K -> smallsubset): smallsubset :=
  (fun k => let (k1, k2) := retr_s z k in A k1 k2).

  Definition rightmono (R: smallsubset -> smallsubset -> Prop) :=
  forall A B C, R A B -> included B C -> R A C.

End Defs.
Arguments smallsubset X K: clear implicits.

Section Lemmas.

  #[export] Instance included_refl {X K}: Reflexive (included (X:=X) (K:=K)).
  Proof.
    intros A. exists id.
    intros x; reflexivity.
  Qed.

  #[export] Instance included_trans {X K}: Transitive (included (X:=X) (K:=K)).
  Proof.
    intros A0 A1 A2 [iota1 hiota1] [iota2 hiota2].
    exists (fun a => iota2 (iota1 a)).
    intros a.
    rewrite hiota1, hiota2. reflexivity.
  Qed.

  Lemma l_included_bunion {X K} (siK: strongInf K) (A B: smallsubset X K):
  included A (bunion siK A B).
  Proof.
    exists (fun k => retr_i (X_add_X_retr_X_of_si_X siK) (inl k)).
    intros k. unfold bunion. rewrite retr_o. reflexivity.
  Qed.

  Lemma r_included_bunion {X K} (siK: strongInf K) (A B: smallsubset X K):
  included B (bunion siK A B).
  Proof.
    exists (fun k => retr_i (X_add_X_retr_X_of_si_X siK) (inr k)).
    intros k. unfold bunion. rewrite retr_o. reflexivity.
  Qed.

  Lemma included_union {X K} (siK: strongInf K) (F: K -> smallsubset X K):
  forall j, included (F j) (union siK F).
  Proof.
    intros j.
    exists (fun k' => retr_i (X_mul_X_retr_X_of_si_X siK) (j, k')).
    intros k'.
    unfold union.
    rewrite retr_o.
    reflexivity.
  Qed.

  Lemma find_index_in_union {X K} (siK: strongInf K) (F: K -> smallsubset X K):
  forall k, exists j kj, union siK F k = F j kj.
  Proof.
    intros k. destruct (retr_s (X_mul_X_retr_X_of_si_X siK) k) as [j kj] eqn: e.
    exists j, kj.
    unfold union. rewrite e.
    reflexivity.
  Qed.

  Lemma included_rightmono {X K}: rightmono (included (X:=X) (K:=K)).
  Proof.
    exact included_trans.
  Qed.

  Lemma rightmono_inter {X K} {R R': smallsubset X K -> smallsubset X K -> Prop}:
  rightmono R -> rightmono R' -> rightmono (fun A B => R A B /\ R' A B).
  Proof.
    intros H H' A B C [h h'] Hincl. split.
    - apply (H A B C h Hincl).
    - apply (H' A B C h' Hincl).
  Qed.

  Lemma directed_of_total_of_rightmono {X K} (siK: strongInf K) {R: smallsubset X K -> smallsubset X K -> Prop}:
  rightmono R -> totalR R -> directedR R.
  Proof.
    intros H Htot A1 A2.
    destruct (Htot A1) as [B1 h1].
    destruct (Htot A2) as [B2 h2].
    exists (bunion siK B1 B2).
    split.
    - apply (H A1 B1 _ h1), l_included_bunion.
    - apply (H A2 B2 _ h2), r_included_bunion.
  Qed.

End Lemmas.
#[global] Opaque union.
#[global] Opaque bunion.

Section Closure.

  Context {s_f: funcs_signature}.
  Context {s_P: preds_signature}.
  Context {M: model} (m0: M).
  Context {K: Type}.
  Context (siK: strongInf K).
  Abbreviation k0 := (X_of_si_X siK).

  Fixpoint closure (A: smallsubset M K) (u: termK K) :=
    match u with
    | varK a => A a
    | funcK f v => i_func M (interp' M) f (map (closure A) v)
    end.

  Definition interp_on_closure (A: smallsubset M K):
  interp (termK K) :=
  B_I
    (fun (f: s_f) v => funcK f v)
    (fun P v => (i_atom M (interp' M) P (map (closure A) v))).
  
  Fixpoint extend_to_closure (g: K -> K) (u: termK K): termK K := 
  match u with 
  | varK k => varK (g k)
  | funcK f v => funcK f (map (extend_to_closure g) v)
  end.

  Lemma extend_to_closure_prop
  (A B: smallsubset M K)
  (g: K -> K):
  feq B (fun k => A (g k)) ->
  feq (closure B) (fun u => closure A (extend_to_closure g u)).
  Proof.
    intros H u. induction u as [k|f v ih].
    - apply H.
    - simpl. f_equal. rewrite map_map.
      induction ih as [|h hh n t ht ih].
      + reflexivity.
      + simpl. f_equal; assumption.
  Qed.

  Equations size (u: termK K): nat :=
  size (varK a) := 1 ;
  size (funcK f v) := size_many v ;
  where size_many {n} (v: vec (termK K) n): nat :=
  size_many (nil _) := 0 ;
  size_many (cons _ h _ t) := 1 + (size h) + (size_many t).

  Lemma uniform_clos_vec {F: K -> smallsubset M K} 
  (H: directedR (fun j1 j2 => included ((F j1)) ((F j2)))):
  forall (w: sigT (vec (termK K))),
  let (n, v) := w in 
  exists j (v': vec (termK K) n),
  map (closure (union siK F)) v = map (closure (F j)) v'.
  Proof.
    intros w.
    induction w as [w' ih] using (well_founded_induction
    (Inverse_Image.wf_inverse_image _ _ _
      (fun w'': sigT (vec (termK K)) => let (n', v') := w'' in @size_many n' v')
      Wf_nat.lt_wf)).
    destruct w' as [_ [|h n' t]].
    - exists k0, (nil _).
      reflexivity.
    - destruct (ih (existT _ n' t)) as [jt [t' et]].
      { simpl. lia. }
      destruct h as [a|f vh] eqn: e.
      1: destruct (find_index_in_union siK F a) as [jh [a' eh]].
      1: pose (h' := varK a').
      2: destruct (ih (existT _ (ar_syms f) vh)) as [jh [vh' eh]]; [ simp size; lia | ].
      2: pose (h' := funcK f vh').
      all: destruct (H jh jt) as [j [[iotah hiotah] [iotat hiotat]]].
      all: exists j, (cons _ (extend_to_closure iotah h') _ (map (extend_to_closure iotat) t')).
      all: simpl.
      all: f_equal.
      2,4: rewrite et, map_map; apply map_ext, extend_to_closure_prop, hiotat. 
      + rewrite eh. apply hiotah.
      + f_equal.
        rewrite eh, map_map.
        apply map_ext, extend_to_closure_prop, hiotah.
  Qed.

End Closure.
