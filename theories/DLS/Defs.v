From Stdlib Require Import Classes.Morphisms.
Require Export FOL.Core.Models.

Existing Instance falsity_on.

Section Retracts.

  Class retract (A B: Type): Type := {
    retr_i: A -> B;
    retr_s: B -> A;
    retr_o: forall x, retr_s (retr_i x) = x;
  }.

  Class strongInf X := sinf:> (retract (list X) X).
  
  Class inhab (X: Type) := elem: X.

End Retracts.
Notation "A ≤R B" := (retract A B) (at level 80).

Section Properties.

  Definition totalR {X Y: Type} (R: X -> Y -> Prop) :=
    forall x, exists y, R x y.

  Definition directedR {X: Type} (R: X -> X -> Prop) :=
    forall x x', exists y, R x y /\ R x' y.

End Properties.
Section LogicalPrinciples.

  Definition LEM :=
    forall P, P \/ ~ P.

  Definition EP_on X :=
    forall (P: X -> Prop),
    exists w: X,
    (exists x, P x) -> P w.

  Definition DP_on X :=
    forall (P: X -> Prop),
    exists w: X,
    P w -> forall x, P x.

  Definition BEP_on K X :=
    forall (P: X -> Prop),
    exists f: K -> X,
    (exists x, P x) -> (exists k, P (f k)).

  Definition BDP_on K X :=
    forall (P: X -> Prop),
    exists f: K -> X,
    (forall k, P (f k)) -> (forall x, P x).

  Definition GMP K :=
    forall f: K -> bool,
    ~ ~ (exists k, f k = true) -> exists k, f k = true.

  Definition AC_on K Y :=
    forall R: K -> Y -> Prop, totalR R ->
    exists f: K -> Y,
    forall k, R k (f k).

  Definition DC_on Y :=
    forall R: Y -> Y -> Prop, totalR R ->
    exists f: nat -> Y,
    forall n, R (f n) (f (S n)).
    
  Definition OAC_on K Y :=
    forall R: K -> Y -> Prop,
    exists f: K -> Y,
    totalR R -> forall k, R k (f k).

  Definition BAC_on K Y :=
    forall R: K -> Y -> Prop, totalR R ->
    exists f: K -> Y,
    totalR (fun k0 k => R k0 (f k)).
  
  Definition DDC_on K Y :=
    forall R: Y -> Y -> Prop, directedR R ->
    exists f: K -> Y,
    directedR (fun k k' => R (f k) (f k')).

  Definition OBAC_on K Y :=
    forall R: K -> Y -> Prop,
    exists f: K -> Y,
    totalR R -> totalR (fun k0 k => R k0 (f k)).
  
  Definition ODDC_on K Y :=
    forall R: Y -> Y -> Prop,
    exists f: K -> Y,
    directedR R -> directedR (fun k k' => R (f k) (f k')).
  
  Definition EP := forall X, inhab X -> EP_on X.
  Definition DP := forall X, inhab X -> DP_on X.
  Definition BEP K := forall X, inhab X -> BEP_on K X.
  Definition BDP K := forall X, inhab X -> BDP_on K X.
  Definition AC K := forall Y, inhab Y -> AC_on K Y.
  Definition DC := forall Y, inhab Y -> DC_on Y.
  Definition OAC K := forall Y, inhab Y -> OAC_on K Y.
  Definition BAC K := forall Y, inhab Y -> BAC_on K Y.
  Definition DDC K := forall Y, inhab Y -> DDC_on K Y.
  Definition OBAC K := forall Y, inhab Y -> OBAC_on K Y.
  Definition ODDC K := forall Y, inhab Y -> ODDC_on K Y.

End LogicalPrinciples.
Section DLS.

  Context {fff: falsity_flag}.

  Definition DLS'_on
    {s_f: funcs_signature}
    {s_P: preds_signature}
    (K: Type)
    (M: model) :=
    exists (Is: interp K), Build_model Is ⪳ M.

  Definition DLS'
    {s_f: funcs_signature}
    {s_P: preds_signature}
    (K: Type) :=
    forall (M: model) (m0: M), DLS'_on K M.
  #[global] Arguments DLS' _ _ _, {_ _} _.

  Definition DLS_on
    {s_f: funcs_signature}
    {s_P: preds_signature}
    (K: Type)
    (M: model) :=
    exists (N: model), N ⪳ M /\ inhabited (N ≤R K).
    
  Definition DLS 
    {s_f: funcs_signature}
    {s_P: preds_signature}
    (K: Type) :=
    forall (M: model), M -> DLS_on K M.
   #[global] Arguments DLS  _ _ _, {_ _} _.

End DLS.
Section MainStatement.

  Definition DLS_iff_BEP_BDP_BAC_DDC := forall K, inhabited (strongInf K) ->
  ((BDP K /\ BEP K) /\ (DDC K /\ BAC K)) <->
  (forall (s_f: funcs_signature) (s_P: preds_signature), inhab s_P ->
    s_f + s_P ≤R K -> DLS K).

End MainStatement.
