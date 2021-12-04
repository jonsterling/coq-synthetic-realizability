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
  End Operations.
End Quotient.
