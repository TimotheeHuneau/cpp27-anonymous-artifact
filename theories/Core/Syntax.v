From Stdlib Require Import Vectors.Vector.
Local Abbreviation vec := t.

(* Some preliminary definitions for substitions  *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with
        | 0 => x
        | S n => xi n
        end.

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).

Class funcs_signature :=
  { syms : Type; ar_syms : syms -> nat }.

Coercion syms : funcs_signature >-> Sortclass.

Class preds_signature :=
  { preds : Type; ar_preds : preds -> nat }.

Coercion preds : preds_signature >-> Sortclass.

Arguments Build_funcs_signature {_} _.
Arguments Build_preds_signature {_} _.

Section fix_signature.

  Context {Σ_funcs : funcs_signature}.

  Unset Elimination Schemes.

  Inductive term  : Type :=
  | var : nat -> term
  | func : forall (f : syms), vec term (ar_syms f) -> term.
  Arguments func _ _ : clear implicits. (* Temporarily make it fully explicit *)

  Definition ForallT {X} (p : X -> Type) := fix ForallT {n} (v : t X n) :=
    match v with
    | nil _ => (unit : Type)
    | cons _ x _ v => (p x * ForallT v)%type
    end.

  Definition InT {X} (x:X) := fix InT {n} (v : t X n) :=
    match v with
    | nil _ => (False : Type)
    | cons _ y _ v => ((x=y) + InT v)%type
    end.
  
  Lemma term_rect' (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (ForallT p v) -> p (@func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. fix strong_term_ind' 1. destruct t as [n|F v].
    - apply f1.
    - apply f2. induction v.
      + econstructor.
      + econstructor. now eapply strong_term_ind'. eauto.
  Qed.

  Lemma term_rect (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (forall t, InT t v -> p t) -> p (@func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply term_rect'.
    - apply f1.
    - intros. apply f2. induction v.
      + intros t H; exfalso; apply H.
      + intros t [->|H]; cbn in *; destruct X; eauto. 
  Qed.

  Lemma term_ind (p : term -> Prop) :
    (forall x, p (var x)) -> (forall F v (IH : forall t, In t v -> p t), p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply term_rect'.
    - apply f1.
    - intros. apply f2. intros t. induction 1; inversion X; subst; eauto.
  Qed.

  Set Elimination Schemes.

  #[global] Register Scheme term_rect as rect_dep for term.
  #[global] Register Scheme term_ind as ind_dep for term.

  Context {Σ_preds : preds_signature}.

  (* We use a flag to switch on and off a constant for falisity *)

  Inductive falsity_flag := falsity_off | falsity_on.
  Existing Class falsity_flag.

  (* Syntax is parametrised in binary operators and quantifiers.
      Most developments will fix these types in the beginning and never change them.
   *)
  Class operators := {binop : Type ; quantop : Type}.
  Context {ops : operators}.

  Inductive form : falsity_flag -> Type :=
  | falsity : form falsity_on
  | atom {b} : forall (P : preds), vec term (ar_preds P) -> form b
  | bin {b} : binop -> form b -> form b -> form b
  | quant {b} : quantop -> form b -> form b.
  Arguments form {_}.
  Arguments atom {_} _ _, _ _ _.
  Arguments bin {_} _ _ _, _ _ _ _.
  Arguments quant {_} _ _, _ _ _.

End fix_signature.

(* Setting implicit arguments is crucial  *)
(* We can write term both with and without arguments, but printing is without. *)
Arguments term _, {_}.
Arguments var _ _, {_} _.
Arguments func _ _ _, {_} _ _.

(* Formulas can be written with the signatures explicit or not.
    If the operations are explicit, the signatures are too.
 *)
Arguments form  _ _ _ _, _ _ {_ _}, {_ _ _ _}, {_ _ _} _.
Arguments atom  _ _ _ _, _ _ {_ _}, {_ _ _ _}.
Arguments bin   _ _ _ _, _ _ {_ _}, {_ _ _ _}.
Arguments quant _ _ _ _, _ _ {_ _}, {_ _ _ _}.

(* Substitution Notation *)

Declare Scope subst_scope.
Open Scope subst_scope.

Notation "$ x" := (var x) (at level 3, format "$ '/' x") : subst_scope.
Notation "s .: sigma" := (scons s sigma) (at level 70, right associativity) : subst_scope.
Notation "f >> g" := (funcomp g f) (at level 50) : subst_scope.

(* Full syntax *)

Module FullSyntax.

  Inductive full_logic_sym : Type :=
  | Conj : full_logic_sym
  | Disj : full_logic_sym
  | Impl : full_logic_sym.

  Inductive full_logic_quant : Type :=
  | All : full_logic_quant
  | Ex : full_logic_quant.

  Definition full_operators : operators :=
    {| binop := full_logic_sym ; quantop := full_logic_quant |}.

  #[export] Hint Immediate full_operators : typeclass_instances.

  Declare Scope full_syntax.
  Delimit Scope full_syntax with Ffull.

  #[global] Open Scope full_syntax.
  Notation "∀ Phi" := (@quant _ _ full_operators _ All Phi) (at level 50) : full_syntax.
  Notation "∃ Phi" := (@quant _ _ full_operators _ Ex Phi) (at level 50) : full_syntax.
  Notation "A ∧ B" := (@bin _ _ full_operators _ Conj A B) (at level 41) : full_syntax.
  Notation "A ∨ B" := (@bin _ _ full_operators _ Disj A B) (at level 42) : full_syntax.
  Notation "A → B" := (@bin _ _ full_operators _ Impl A B) (at level 43, right associativity) : full_syntax.
  Notation "⊥" := (falsity) : full_syntax.
  Notation "¬ A" := (A → ⊥) (at level 42) : full_syntax.
  Notation "A ↔ B" := ((A → B) ∧ (B → A)) (at level 43) : full_syntax.

End FullSyntax.
