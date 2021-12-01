Require Export ssreflect ssrfun Unicode.Utf8.
From HB Require Export structures.
Require Export Coq.Logic.Description Coq.Logic.PropExtensionality Coq.Logic.FunctionalExtensionality Program.Equality.

Set Primitive Projections.

(* NOTE: Universe Polymorphism must not be turned on, as this actually
causes axioms from Set to be lifted to Type!!! That's so messed
up!! *)
Unset Universe Polymorphism.

Export EqNotations.


Definition surjective {E B} (f : E → B) : Prop :=
  ∀ x : B, ∃ y : E, f y = x.


Arguments proj1_sig {A P}.
Notation sval := proj1_sig.

Definition iota {X : Type} (P : X → Prop) (h : exists! x, P x) : X :=
  proj1_sig (constructive_definite_description _ h).

Lemma iota_prop {X : Type} (P : X → Prop) (h : exists! x, P x) : P (iota P h).
Proof. rewrite /iota; apply proj2_sig. Qed.

Definition extract {X : Type} {P : X → Prop} : (∀ x y, P x → P y → x = y) → (∃ x, P x) → X.
Proof.
  move=> H J.
  apply: (@iota X P).
  case: J=> x xP.
  exists x; split=>//.
  by move=>?; apply: H.
Defined.

Definition extract_prop {X : Type} {P : X → Prop} : ∀ H J, P (@extract X P H J).
Proof.
  move=> ? ?.
  apply: iota_prop.
Qed.

Opaque extract.

Module Im.
  Section Im.
    Context {X Y : Type} (f : X → Y).

    Definition T : Type :=
      { y : Y | ∃ x, f x = y }.

    Definition surj : X → T.
    Proof. by move=> x; exists (f x); exists x. Defined.

    Definition inj : T → Y.
    Proof. by apply: proj1_sig. Defined.

    Lemma inj_injective : injective inj.
    Proof. by move=> x y h; apply/eq_sig/proof_irrelevance. Qed.

    Lemma surj_surjective : surjective surj.
    Proof. by move=> [y [x h]]; exists x; apply/eq_sig/proof_irrelevance. Qed.
  End Im.
End Im.

Notation Im := Im.T.

Notation propext := propositional_extensionality.
Notation funext := functional_extensionality.
Notation depfunext := functional_extensionality_dep.
Notation proofirr := proof_irrelevance.

#[global]
Hint Resolve proofirr : core.

Infix "∘" := comp (right associativity, at level 60).
Notation "𝟙" := True.


Definition projective (B : Type) : Prop :=
  ∀ E (r : E → B), surjective r → ∃ i : B → E, ∀ b : B, r (i b) = b.

Lemma bool_projective : projective bool.
Proof.
  move=> E p hp.
  case: (hp true)=> e0 he0.
  case: (hp false)=> e1 he1.
  unshelve esplit.
  - case; [exact: e0 | exact: e1].
  - by case.
Qed.
