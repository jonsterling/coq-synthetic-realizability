From synrl Require Import Preamble.

Module Coeq.
  Private Inductive T {A B} (f g : A → B) :=
  | intro : B → T f g.

  Arguments intro [A] [B] [f] [g] x.

  Section Operations.
    Context {A B} {f g : A → B}.

    Axiom glue : ∀ {x}, @intro A B f g (f x) = @intro A B f g (g x).

    Definition rec {C} (h : B → C) : (h ∘ f = h ∘ g) → T f g → C.
    Proof. by move=> ?; case. Defined.

    Definition ind (C : T f g → Type) (h : ∀ b, C (intro b)) : (∀ x, rew [C] glue in h (f x) = h (g x)) → ∀ x : T f g, C x.
    Proof. by move=> ?; case. Defined.

  End Operations.
End Coeq.

Module Quotient.
  Definition gph A (R : A → A → Prop) := {p : A * A | R p.1 p.2}.

  Definition pi1 {A} (R : A → A → Prop) : gph A R → A.
  Proof. by move/proj1_sig/fst. Defined.

  Definition pi2 {A} (R : A → A → Prop) : gph A R → A.
  Proof. by move/proj1_sig/snd. Defined.

  Definition T A (R : A → A → Prop) := Coeq.T (pi1 R) (pi2 R).

  Section Operations.
    Context {A} {R : A → A → Prop}.

    Definition intro : A → T A R.
    Proof. apply: Coeq.intro. Defined.

    Definition rec {C} (h : A → C) : (∀ x y : A, R x y → h x = h y) → T A R → C.
    Proof.
      move=> H.
      apply: (Coeq.rec h).
      abstract by apply: funext; case=> ? ?; rewrite /pi1 /pi2 //=; apply: H.
    Defined.

    Definition glue : ∀ {x y}, R x y → intro x = intro y.
    Proof.
      move=> x y h.
      rewrite /intro.
      pose xyh : gph A R := exist _ (x,y) h.
      rewrite (_ : x = pi1 _ xyh); first by [].
      rewrite (_ : y = pi2 _ xyh) ; first by [].
      apply Coeq.glue.
    Qed.

    Definition ind (C : T A R → Type) (h : ∀ x : A, C (intro x)) : (∀ (x y : A) (xy : R x y), rew [C] glue xy in h x = h y) → ∀ x : T A R, C x.
    Proof.
      move=> H.
      apply: (Coeq.ind C h); case; case=> x y xy.
      abstract by rewrite /pi1 /pi2 //= -(H x y xy); congr eq_rect.
    Defined.



    Definition indp (C : T A R → Prop) (h : ∀ x : A, C (intro x)) : ∀ x : T A R, C x.
    Proof. by apply: ind. Qed.

    Definition ind_eta (C : T A R → Type) (f1 f2 : ∀ x : T A R, C x) : (∀ x, f1 (intro x) = f2 (intro x)) → f1 = f2.
    Proof. by move=>?; apply: depfunext; apply: indp. Qed.


    Section Effectivity.
      Context `{RelationClasses.Equivalence A R}.

      Local Definition R' : T A R → A → Prop.
      Proof.
        apply: (rec R)=> x y xy.
        apply: funext=> z.
        apply: propext; split.
        - move=> ?.
          transitivity x=>//.
          by symmetry.
        - move=> ?.
          by transitivity y=>//.
      Defined.

      Definition eff {x y : A} : intro x = intro y → R x y.
      Proof.
        move=> h.
        symmetry.
        rewrite (_ : R y x = R x x); last by reflexivity.
        by move: (f_equal R' h) => //= ->.
      Qed.

      Definition glue_is_iso {x y : A} : is_isomorphism (@glue x y).
      Proof.
        move=> e.
        unshelve esplit=>//.
        by apply: eff.
      Qed.
    End Effectivity.
  End Operations.
End Quotient.
