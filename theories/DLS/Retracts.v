From Stdlib Require Import Classes.Morphisms.
From Stdlib Require Import List.
From Stdlib Require Import Vector.
From Stdlib Require Import Arith.Cantor.
Require Export FOL.DLS.Defs.

Arguments Build_retract _ _ _ _ _, {_ _} _ _ _.
Arguments retr_i {_ _} _ _.
Arguments retr_s {_ _} _ _.
Arguments retr_o {_ _} _ _.

Hint Mode retract ! ! : typeclass_instances.
Hint Mode strongInf + : typeclass_instances.
Hint Mode inhab + : typeclass_instances.

Section ElementaryOperations.
  (* These definitions are voluntarily ended with `Qed` rather than `Defined`. *)

  #[global] Instance id_retr A: A ≤R A.
  Proof.
    exact (Build_retract
      (@id A) 
      (@id A) 
      (@eq_refl A)).
  Qed.

  Instance comp_retr {A B C} (rAB: A ≤R B) (rBC: B ≤R C): A ≤R C.
  Proof.
    refine (Build_retract
      (fun a => retr_i rBC (retr_i rAB a))
      (fun c => retr_s rAB (retr_s rBC c))
      _).
    intros x. rewrite retr_o, retr_o. reflexivity.
  Qed.
  #[global] Arguments comp_retr {_ _ _} _ _, {A} B {C} _ _, _ _ _ _ _.

  #[global] Instance mul_retr {A B C D} `{rAB: A ≤R B} `{rCD: C ≤R D}:
  retract (A * C) (B * D).
  Proof.
    refine (Build_retract
      (fun p => match p with | pair a c => pair (retr_i rAB a) (retr_i rCD c) end)
      (fun p => match p with | pair b d => pair (retr_s rAB b) (retr_s rCD d) end)
      _).
    intros [a c]. rewrite retr_o, retr_o. reflexivity.
  Qed.

  #[global] Instance add_retr {A B C D} `{rAB: A ≤R B} `{rCD: C ≤R D}:
  retract (A + C) (B + D).
  Proof.
    refine (Build_retract
      (fun p => match p with | inl a => inl (retr_i rAB a) | inr c => inr (retr_i rCD c) end)
      (fun p => match p with | inl b => inl (retr_s rAB b) | inr d => inr (retr_s rCD d) end)
      _).
    intros [a|c]. all: rewrite retr_o. all: reflexivity.
  Qed.

  #[global] Instance distr_retr {J K: Type} {X: J -> Type}:
  (forall j, X j ≤R K) -> sigT X ≤R J * K.
  Proof.
    intros F.
    refine (Build_retract
      (fun p: sigT X => let (j, x) := p in pair j (retr_i (F j) x))
      (fun p: J * K => let (j, k) := p in existT X j (retr_s (F j) k))
      _).
    intros [j x]. rewrite retr_o. reflexivity.
  Qed.

  #[global] Instance inl_retr {A B} `{a0 : inhab A} : A ≤R A + B.
  Proof.
    exact (Build_retract
      (fun a => inl a)
      (fun x => match x with | inl a => a | inr _ => a0 end)
      (fun x => eq_refl _)).
  Qed.

  #[global] Instance inr_retr {A B} `{b0: inhab B} : B ≤R A + B.
  Proof.
    exact (Build_retract
      (fun b => inr b)
      (fun x => match x with | inl _ => b0 | inr b => b end)
      (fun x => eq_refl _)).
  Qed.

  #[global] Instance retr_inr {A B K} `{inhab B} (r: A + B ≤R K): B ≤R K.
  Proof.
    refine (Build_retract
              (fun b => retr_i r (inr b))
              (fun k => match retr_s r k with | inl _ => elem | inr b => b end)
              _).
    intros b. rewrite retr_o. reflexivity.
  Qed.

  #[global] Instance sum_0l_retr {A B} (R: A ≤R B): False + A ≤R B.
  Proof.
    exact (Build_retract
      (fun s =>
        match s with
        | inl devil => match devil: False with end
        | inr a => retr_i R a
      end)
      (fun b => inr (retr_s R b))
      (fun s =>
        match s with
        | inl devil => match devil: False with end
        | inr a => f_equal inr (retr_o R a)
        end)).
  Qed.

  #[global] Instance sum_0r_retr {A B} (R: A ≤R B): A + False ≤R B.
  Proof.
    exact (Build_retract
      (fun s =>
        match s with
        | inl a => retr_i R a
        | inr devil => match devil: False with end
        end)
      (fun b => inl (retr_s R b))
      (fun s =>
        match s with
        | inl a => f_equal inl (retr_o R a)
        | inr devil => match devil: False with end
        end)).
  Qed.

End ElementaryOperations.

#[global] Instance unit_retr_inhab {X} {x0: inhab X} : unit ≤R X.
Proof.
  exact (Build_retract
    (fun u => match u with | tt => x0 end)
    (fun _ => tt)
    (fun u => match u with | tt => eq_refl tt end)).
Qed.

#[global] Instance inhab_unit : inhab unit := tt.

Section List.  
  Import ListNotations.

  #[global] Instance list_mono_retr {X Y}
  `{R: X ≤R Y}:
  list X ≤R list Y.
  Proof.
    destruct R as [i s o].
    refine (Build_retract (List.map i) (List.map s) _).
    intros l. rewrite List.map_map. induction l as [|h t ih].
    - reflexivity.
    - simpl. rewrite ih, o. reflexivity.
  Qed.

  Lemma si_X_iff {X}:
  ((X * X ≤R X) * (nat ≤R X)) -> strongInf X.
  Proof.
    intros [[ip sp op] [i s o]].
    pose (x0:= i 0).
    pose (decode_x := fun x => match sp x with | pair h xt => (h, xt) end).
    pose (code_l := fix il_ l := match l with | [] => x0 | h :: t => ip (h, il_ t) end).
    assert (H: forall h t, (decode_x (code_l (h :: t))) = (h, code_l t)).
    { intros h t. unfold decode_x; simpl. rewrite op. reflexivity. }
    pose (sl_ := fix sl_ n x := match n with | 0 => [] | S n' => let (h, xt) := decode_x x in h :: sl_ n' xt end).
    refine (Build_retract
      (fun l => ip (i (length l), code_l l))
      (fun x => match sp x with | pair xn xl => sl_ (s xn) xl end)
      _).
    intros l. rewrite op, o. induction l as [|h t ih].
    - reflexivity.
    - simpl in *. destruct (decode_x (ip (h, code_l t))) eqn: e.
      congruence.
  Qed.

  #[global] Instance X_mul_X_retr_X_of_si_X {X}:
  strongInf X -> X * X ≤R X.
  Proof.
    intros [i s o].
    refine (Build_retract
      (fun p => match p with | pair x1 x2 => i (x1 :: x2 :: []) end)
      (fun x => match s x with | x1 :: x2 :: _ => pair x1 x2 | _ => pair x x end)
      _).
    intros [x1 x2]. rewrite o. reflexivity.
  Qed.

  #[global] Instance nat_retr_X_of_si_X {X}:
  strongInf X -> nat ≤R X.
  Proof.
    intros [i s o].
    refine (Build_retract
      (fun m => i (repeat (i []) m))
      (fun x => length (s x))
      _).
    intros n. rewrite o. exact (repeat_length _ _).
  Qed.

  #[global] Instance X_add_X_retr_X_of_si_X {X}:
  strongInf X -> X + X ≤R X.
  Proof.
    intros [i s o].
    refine (Build_retract
      (fun s => match s with | inl x => i (x :: []) | inr x => i (x :: x :: []) end)
      (fun x => match s x with | [] => inl (i []) | x :: [] => inl x | x :: _ :: _ => inr x end)
      _).
    intros [x|x].
    all: rewrite o. all: reflexivity.
  Qed.

  Definition X_of_si_X {X}:
  strongInf X -> X.
  Proof.
    intros [i _ _].
    exact (i []).
  Qed.

  #[global] Instance inhab_of_strongInf {K} `{siK: strongInf K}: inhab K := X_of_si_X siK.

End List.
Section Vector.

  #[local] Abbreviation vec := Vector.t.
  Import VectorNotations.
  
  #[global] Instance vec_mono_retr {X Y} n `{r: X ≤R Y}:
  vec X n ≤R vec Y n.
  Proof.
    refine (Build_retract
      (map (retr_i r))
      (map (retr_s r))
      _).
    intros x.
    rewrite <-map_id.
    rewrite map_map.
    exact (map_ext _ _ _ _ (retr_o r) _ _).
  Qed.

  Context {X: Type}.
  Context (siX: strongInf X).
  Abbreviation x0 := (X_of_si_X siX).
  Abbreviation z := (X_mul_X_retr_X_of_si_X siX).
  Abbreviation p := (X_add_X_retr_X_of_si_X siX).
  
  #[local] Definition vec_X_retr_i_X {n} (i: vec X n -> X):
  vec X (S n) -> X.
  Proof.
    intros v. exact (retr_i z ((hd v), i (tl v))).
  Defined.

  #[local] Definition vec_X_retr_s_X {n} (s: X -> vec X n) (x: X):
  vec X (S n).
  Proof.
    destruct (retr_s z x) as [xh xt].
    exact ( xh :: (s xt)).
  Defined.

  #[local] Lemma vec_X_retr_o_X
    {n}
    {i: vec X n -> X}
    {s: X -> vec X n}
    (o: forall v, s (i v) = v):
  forall v, vec_X_retr_s_X s (vec_X_retr_i_X i v) = v.
  Proof.
    intros v.
    unfold vec_X_retr_s_X, vec_X_retr_i_X.
    rewrite retr_o, o.
    rewrite <-(eta v).
    reflexivity.
  Qed.

  #[global] Instance vec_X_retr_X_of_si_X n: vec X n ≤R X.
  Proof.
    induction n as [|n' ihn].
    - refine (Build_retract
        (fun x => x0)
        (fun x => ([]))
        (case0 (eq _) (eq_refl _))).
    - destruct ihn as [i s o].
      refine (Build_retract
        (vec_X_retr_i_X i)
        (vec_X_retr_s_X s)
        (vec_X_retr_o_X o)).
  Qed.

End Vector.

Section Encodings.

  Context {K: Type}.
  Context `{siK: strongInf K}.

  #[global] Instance enc_prod {A B} `{A ≤R K} `{B ≤R K} : A * B ≤R K :=
    comp_retr (mul_retr) (X_mul_X_retr_X_of_si_X _).

  #[global] Instance enc_sum {A B} `{A ≤R K} `{rB: B ≤R K}: A + B ≤R K :=
    comp_retr (add_retr) (X_add_X_retr_X_of_si_X _).

  #[global] Instance enc_list {A} `{A ≤R K} : list A ≤R K :=
    comp_retr (list_mono_retr) siK.

  #[global] Instance enc_vec {A n} `{A ≤R K} : Vector.t A n ≤R K :=
    comp_retr (vec_mono_retr n) (vec_X_retr_X_of_si_X _ n).

  #[global] Instance enc_sigT {J} {X: J -> Type}
    `{J ≤R K} `{forall j, X j ≤R K}: sigT X ≤R K :=
    comp_retr (distr_retr _) (@enc_prod _ _ _ (id_retr K)).

End Encodings.

Instance Rcantor: nat * nat ≤R nat := Build_retract to_nat of_nat cancel_of_to.
#[global] Instance si_nat : strongInf nat := si_X_iff (_, _).

Ltac compose_retracts l :=
  lazymatch l with
  | @Datatypes.nil _ => exact _
  | @Datatypes.cons _ ?T ?l => 
      notypeclasses refine (comp_retr T _ _); [ exact _ | compose_retracts l ]
  end.
