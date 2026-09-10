From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Vector.
Require Import FOL.Core.Models.
Require Import FOL.DLS.Retracts.
Require Import FOL.DLS.Utils.

From Equations Require Import Equations.
Unset Equations With Funext.
#[local] Obligation Tactic :=
  simpl in *;
  Tactics.program_simplify;
  CoreTactics.equations_simpl;
  try Tactics.program_solve_wf;
  try lia.

Import ListNotations.

Definition s_0f := Build_funcs_signature (fun devil: False => match devil with end).

Definition s_XPn X n := Build_preds_signature (fun p: X => n).
Definition s_1P2 := s_XPn unit 2.
Definition s_1P1 := s_XPn unit 1.

Section Form.

  Import ListNotations.

  Context {s_f: funcs_signature}.
  Context {s_P: preds_signature}.
  Context (p0: s_P).
  #[local] Definition psi00 {fff: falsity_flag} := atom p0 (const ($0) (ar_preds p0)).

  Equations sizef {fff: falsity_flag} (phi: form): nat :=
  sizef falsity := 0 ;
  sizef (atom _ v) := 0 ;
  sizef (bin b phi1 phi2) := 1 + sizef phi1 + sizef phi2 ;
  sizef (quant q phi1) := 1 + sizef phi1.

  Definition tradbinop b := match b with | Conj => 1 | Disj => 2 | Impl => 3 end.
  Definition tradquantop q := match q with | Ex => 4 | All => 5 end.

  Equations linearisef {fff: falsity_flag} (phi: form): list (nat + (sigT (fun p: s_P => vec term (ar_preds p)))) :=
  linearisef falsity := [inl 0] ;
  linearisef (atom P v) := [inr (existT _ P v)] ;
  linearisef (bin b phi1 phi2) := inl (tradbinop b) :: linearisef phi1 ++ linearisef phi2 ;
  linearisef (quant q psi) := inl (tradquantop q) :: linearisef psi.    

  Equations parsef' {fff: falsity_flag}
  (l: list (nat + (sigT (fun p: s_P => vec term (ar_preds p))))):
  form * {lo: list (nat + (sigT (fun p: s_P => vec term (ar_preds p)))) | length lo <= length l}
  by wf (length l) :=
  parsef' ([]) := (psi00, (exist _ ([]) _)) ;
  parsef' (inr (existT _ P v) :: ns) := (atom P v, (exist _ ns _)) ;
  parsef' (inl 0 :: ns) :=
    match fff with
    | falsity_on => (falsity, exist _ ns _)
    | falsity_off => (psi00, exist _ ns _)
    end ;
  parsef' (inl 1 :: ns) :=
    match parsef' ns with
    | pair phi1 (exist _ l1 _) =>
      match parsef' l1 with
      | pair phi2 (exist _ l2 _) => (phi1 ∧ phi2, exist _ l2 _)
      end
    end ;
  parsef' (inl 2 :: ns) :=
    match parsef' ns with
    | pair phi1 (exist _ l1 _) =>
      match parsef' l1 with
      | pair phi2 (exist _ l2 _) => (phi1 ∨ phi2, exist _ l2 _)
      end
    end;
  parsef' (inl 3 :: ns) :=
    match parsef' ns with
    | pair phi1 (exist _ l1 _) =>
      match parsef' l1 with
      | pair phi2 (exist _ l2 _) => (phi1 → phi2, exist _ l2 _)
      end
    end;
  parsef' (inl 4 :: ns) :=
    match parsef' ns with
    | pair psi (exist _ l1 _) => (∃ psi, exist _ l1 _)
    end;
  parsef' (inl 5 :: ns) :=
    match parsef' ns with
    | pair psi (exist _ l1 _) => (∀ psi, exist _ l1 _)
    end;
  parsef' (inl _ :: ns) := (psi00, exist _ ns _).
  Next Obligation.
      unfold parsef'.
      rewrite FixWf_unfold.
      1: unfold parsef'_unfold.
      all: unfold parsef'_functional at 1.
      1: destruct l as [|[[|[|[|[|[|[|]]]]]]|[]]]. all: try reflexivity.
      red. intros [] f g H.
      unfold parsef'_functional.
      destruct pr2 as [|[[|[|[|[|[|[|]]]]]]|[]]]. all: try reflexivity.
      all: rewrite H. all: destruct g as (? & ? & ?). all: try reflexivity.
      all: rewrite H. all: destruct g as (? & ? & ?). all: reflexivity.
  Defined.

  Context {fff: falsity_flag}.

  Definition parsef l: form * list (nat + (sigT (fun p: s_P => vec term (ar_preds p)))) :=
  match parsef' l with | pair phi (exist _ lo _) => (phi, lo) end.

  Lemma parsef'_prop {f: falsity_flag} (phi: form):
  forall (l: list (nat + (sigT (fun p: s_P => vec term (ar_preds p))))),
    exists H, parsef' (linearisef phi ++ l) = (phi, exist _ l H).
  Proof.
    induction phi as [phi ih] using (well_founded_induction
      (Inverse_Image.wf_inverse_image _ _ _ sizef Wf_nat.lt_wf)).
    destruct phi as [|ffff P v|ffff b phi1 phi2|ffff q psi].
    all: intros l; simp linearisef; cbn.
    - eexists. simp parsef'. reflexivity.
    - eexists. simp parsef'. reflexivity.
    - rewrite <-app_assoc.
      edestruct (ih phi1) as [? e1]. { simp sizef. lia. }
      edestruct (ih phi2) as [? e2]. { simp sizef. lia. }
      destruct b; simp parsef'.
      all :rewrite e1, e2; now eexists.
    - edestruct (ih psi) as [? e]. { simp sizef. }
      destruct q; simp parsef'; rewrite e.
      all: eexists; reflexivity.
  Qed.

  Lemma parsef_prop (phi: form):
    forall (l: list (nat + (sigT (fun p: s_P => vec term (ar_preds p))))),
    parsef (linearisef phi ++ l) = (phi, l).
  Proof.
    intros. unfold parsef.
    edestruct parsef'_prop as [H ->].
    reflexivity.
  Qed.

End Form.

Section TermK.

  Import ListNotations.

  Context {K: Type}.
  Context `{siK: strongInf K}.
  Abbreviation k0 := (X_of_si_X siK).
  Abbreviation z := (X_mul_X_retr_X_of_si_X siK).
  Abbreviation p := (X_add_X_retr_X_of_si_X siK).
  Abbreviation R := (nat_retr_X_of_si_X siK).

  Context (s_f: funcs_signature).

  Scheme All for vec.
  Inductive termK :=
  | varK (a: K)
  | funcK (f: s_f) (v: vec termK (ar_syms f)).
  #[global] Arguments funcK _ _: clear implicits.

  Equations sizeTK (t: termK): nat :=
  sizeTK (varK a) := 0 ;
  sizeTK (funcK f v) := 1 + sizeTK_many v ;
  where sizeTK_many {n} (v: vec (termK) n): nat :=
  sizeTK_many (nil _) := 0 ;
  sizeTK_many (cons _ t _ v) := 1 + sizeTK t + sizeTK_many v.

  Import ListNotations.

  Equations lineariseTK (t: termK): list (K + s_f) :=
  lineariseTK (varK a) := [inl a] ;
  lineariseTK (funcK f v) := (inr f) :: lineariseTK_many v ;
  where lineariseTK_many {n} (l: vec (termK) n): list (K + s_f) :=
  lineariseTK_many (nil _) := [] ;
  lineariseTK_many (cons _ t _ v) := lineariseTK t ++ lineariseTK_many v.

  Unset Equations With Funext.
  Equations parseTK' (k: nat) (l: list (K + s_f)): vec (termK) k * {lo: list (K + s_f) | length lo <= length l}
  by wf (length l) :=
    parseTK' 0 l := (nil _, (exist _ l _)) ;
    parseTK' (S k') ([]) := (const (varK k0) (S k'), (exist _ ([]) _)) ;
    parseTK' (S k') (inl a ::ns) :=
      match parseTK' k' ns with
      | pair vk (exist _ lk _) => (cons _ (varK a) _ vk, exist _ lk _)
      end ;
    parseTK' (S k') (inr f :: ns) :=
      match parseTK' (ar_syms f) ns with
      | pair v1 (exist _ l1 _) =>
        match parseTK' k' l1 with
        | pair vk (exist _ lk _) => (cons _ (funcK f v1) _ vk, exist _ lk _)
        end
      end.
  Next Obligation.
      unfold parseTK'.
      rewrite FixWf_unfold.
      1: unfold parseTK'_unfold.
      1: unfold parseTK'_functional at 1.
      1: destruct k. 1: reflexivity.
      1: destruct l as [|[|]]. 1-3: reflexivity.
      red. intros [] f g H.
      unfold parseTK'_functional.
      destruct pr1. reflexivity.
      destruct pr2 as [|[|]]. all: try reflexivity.
      all: rewrite H. all: destruct g as (? & ? & ?). 1: reflexivity.
      rewrite H. destruct g as (? & ? & ?). reflexivity.
  Defined.

  Definition parseTK k l: vec (termK) k * list (K + s_f) :=
      match parseTK' k l with
      | pair v (exist _ lo _) => (v, lo)
      end.

  Lemma parseTK_3 k a ns:
  parseTK (S k) (inl a :: ns) =
  ((cons _ (varK a) _ (fst (parseTK k ns))), snd (parseTK k ns)).
  Proof.
      unfold parseTK.
      simp parseTK'. 
      destruct (parseTK' k ns) as [vk [lk hk]].
      reflexivity.
  Qed.

  Lemma parseTK_4 k f ns:
  parseTK (S k) (inr f :: ns) =
  ((cons _ (funcK f (fst (parseTK (ar_syms f) ns))) _ (fst (parseTK k (snd (parseTK (ar_syms f) ns))))), snd (parseTK k (snd (parseTK (ar_syms f) ns)))).
  Proof.
      unfold parseTK.
      simp parseTK'.
      destruct (parseTK' (ar_syms f) ns) as [v1 [l1 h1]]; simpl. 
      destruct (parseTK' k l1) as [vk [lk hk]].
      reflexivity.
  Qed.

  Lemma parseTK_prop (v': sigT (vec termK)):
  forall (l: list (K + s_f)),
  let (n, v) := v' in 
  parseTK n (lineariseTK_many v ++ l) = (v, l).
  Proof.
    induction v' as [v' ih] using (well_founded_induction
    (Inverse_Image.wf_inverse_image _ _ _ (fun v'': sigT (vec termK) => let (n', v) := v'' in sizeTK_many v) Wf_nat.lt_wf)).
    destruct v' as [n [|u ns vs]].
    - reflexivity.
    - intros l.
    simpl.
    destruct u as [a|f vu].
    + simp lineariseTK. simpl.
      rewrite parseTK_3.
      rewrite (ih (existT _ _ vs)).
      * reflexivity.
      * simp sizeTK.
    + simp lineariseTK.
      rewrite <-app_assoc,
        <-app_comm_cons,
        parseTK_4.
      rewrite (ih (existT _ _ vu)); simpl.
      1: rewrite (ih (existT _ _ vs)).
      1: reflexivity.
      all: simp sizeTK.
      all: lia.
  Qed.

  #[global] Instance termK_retr_list':
  termK ≤R list (K + s_f).
  Proof.
    refine (Build_retract
      lineariseTK
      (fun l => hd (fst (parseTK 1 l)))
      _).
    intros u.
    destruct u as [a|f v].
    - reflexivity.
    - simp lineariseTK.
      rewrite parseTK_4. simpl.
      rewrite <-(app_nil_r (lineariseTK_many v)).
      assert (H := parseTK_prop (existT _ _ v) (List.nil)); simpl in H.
      rewrite H.
      reflexivity.
  Defined.

  #[global] Instance termK_retr_K
  {s_P: preds_signature}
  `{r: s_f + s_P ≤R K}:
  termK ≤R K.
  Proof.
      pose proof (rl := Build_retract
        (fun x => match x with | inl k => inl k | inr f => inr (inl f) end)
        (fun x => match x with | inl k => inl k | inr (inl f) => inr f | _ => inl k0 end)
        (fun x => match x with | inl k => eq_refl | inr f => eq_refl end) : K + s_f ≤R K + (s_f + s_P)).
      compose_retracts [ list (K + s_f) ; list (K + (s_f + s_P)) ].
  Qed.

End TermK.
#[global] Arguments varK {_ _} _.
#[global] Arguments funcK {_ _} _ _.
#[global] Arguments termK _ {_}.

Section TermForm.

  #[global] Instance term_retr_termK_nat
  {s_f: funcs_signature}:
  term ≤R termK nat.
  Proof.
    refine (Build_retract
      (fix i t := match t with | var j => varK j | func f v => funcK f (map i v) end)
      (fix s u := match u with | varK j => var j | funcK f v => func f (map s v) end)
      _).
    intros t. induction t as [j|f v ih].
    - reflexivity.
    - f_equal.
      rewrite map_map, (map_ext_in _ _ _ id _ _ ih). { apply map_id. }
  Qed.

  #[global] Instance form_retr_list'
  {fff: falsity_flag} {s_f: funcs_signature} {s_P: preds_signature} {p0: inhab s_P}:
  form ≤R list (nat + (sigT (fun p: s_P => vec term (ar_preds p)))).
  Proof.
    refine (Build_retract
      (linearisef (s_f:=s_f) (s_P:=s_P))
      (fun x => fst (parsef p0 x))
      _).
    intros x. 
    rewrite <-(app_nil_r (linearisef x)), parsef_prop.
    reflexivity.
  Qed.

  #[global] Instance termK_mono_retr {s_f: funcs_signature} {K K'} (r: K ≤R K'):
  termK K ≤R termK K'.
  Proof.
    refine (Build_retract
      (fix i u := match u with | varK k => varK (retr_i r k) | funcK f v => funcK f (map i v) end)
      (fix s u' := match u' with | varK k' => varK (retr_s r k') | funcK f v' => funcK f (map s v') end)
      _).
    intros u. induction u as [k|f v ih].
    all: f_equal.
    - apply retr_o.
    - rewrite map_map. induction ih as [|h hh n t _ iht].
      + reflexivity.
      + simpl; f_equal; assumption.
  Qed.

  Context {K: Type}.
  Context (siK: strongInf K).
  Abbreviation k0 := (X_of_si_X siK).
  Abbreviation p := (X_add_X_retr_X_of_si_X siK).
  Abbreviation z := (X_mul_X_retr_X_of_si_X siK).
  Abbreviation R := (nat_retr_X_of_si_X siK).

  #[global] Instance term_retr_K_of_sign_retr_K
  {s_f: funcs_signature} {s_P: preds_signature}
  `{Rs: s_f + s_P ≤R K}:
  term s_f ≤R K.
  Proof.
    compose_retracts [ termK nat ; termK K ].
  Qed.

  #[global] Instance form_retr_K_of_sign_retr_K
  {fff: falsity_flag} {s_f: funcs_signature} {s_P: preds_signature}
  `{p0: inhab s_P}
  `{Rs: s_f + s_P ≤R K}:
  form s_f s_P ≤R K.
  Proof.
    compose_retracts [ list (nat + {p : s_P & vec term (ar_preds p)}) ].
  Qed.

End TermForm.
