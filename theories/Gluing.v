From synrl Require Import Preamble Coequalizer.

Set Cumulative StrictProp.

Scheme eq_ind := Induction for eq Sort Type.

Set Primitive Projections.
Record strue : SProp := {}.
Record sand (A B : SProp) : SProp := { sfst : A; ssnd : B }.

Arguments sfst [A] [B].
Arguments ssnd [A] [B].

Definition L (A : Type) := {ϕ : SProp & ϕ -> A}.
Definition U := L Type.
Definition el (X : U) : Type :=
  forall z : projT1 X, projT2 X z.

Definition inU : Type -> U.
Proof.
  move=> A.
  exists strue=> _.
  apply: A.
Defined.


Definition extend (ϕ : SProp) (X : ϕ -> U) : U.
Proof.
  unshelve esplit.
  + refine (sand ϕ (∀ z : ϕ, projT1 (X z))).
  + move=> z.
    Check projT2 (X (sfst z)).
    apply: (projT2 (X (sfst z))).
    apply: (ssnd z).
Defined.

Axiom spropext : forall (ϕ ψ : SProp), (ϕ -> ψ) -> (ψ -> ϕ) → ϕ = ψ.
Axiom sdepfunext : forall (ϕ : SProp) (A : ϕ → Type) (u v : ∀ z, A z) (h : forall z, u z = v z), u = v.
Axiom sorry : forall P : Prop, P.


Lemma rew_partial {A} {ϕ : SProp} (f : ϕ → A) : forall (ψ : SProp) (H : ϕ = ψ) (x : _), (rew [fun z : SProp => z -> A] H in f) x = f (rew <- H in x).
Proof. by apply: eq_ind. Qed.

Lemma extend_restricts (ϕ : SProp) (X : ϕ → U) : forall z : ϕ, extend ϕ X = X z.
Proof.
  move=> z.
  apply: eq_sigT=>//=.
  - apply: spropext.
    + case=> h1; apply.
    + move=> h; split=>//.
  - move=> H.
    apply: sdepfunext=> z'.
    apply: rew_partial.
Qed.

Section iso.
  Context (ϕ : SProp) (X : ϕ → U).

  Definition fwd : (forall z, el (X z)) -> el (extend ϕ X).
  Proof.
    move=> x z.
    apply: x.
  Defined.

  Definition bwd (x : el (extend ϕ X)) : (∀ z, el (X z)).
  Proof. by refine (fun z z' => x (Build_sand _ _ _ _ )). Defined.

  Lemma fwd_bwd : ∀ u, fwd (bwd u) = u.
  Proof.
    move=> u.
    by apply: sdepfunext.
  Qed.

  Lemma bwd_fwd : forall u, bwd (fwd u) = u.
  Proof.
    move=> u.
    by apply: sdepfunext=> z.
  Qed.
End iso.
