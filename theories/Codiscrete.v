From synrl Require Import Preamble Orthogonality.

Axiom codiscrete : Type → Prop.
Class Codiscrete (A : Type) : Prop :=
  codisc : codiscrete A.

Axiom Codisc : Type → Type.
Notation "∇ A" := (Codisc A) (at level 60).

Module Codisc.
  Axiom ret : ∀ {A}, A → ∇ A.
  Axiom rec : ∀ {A B} `{Codiscrete B}, (A → B) → ∇ A → B.
  Axiom ind : ∀ {A B} `{∀ a, Codiscrete (B a)}, (∀ x : A, B (ret x)) → ∀ x : ∇ A, B x.
  Axiom rec_beta : ∀ {A B} `{Codiscrete B} (f : A → B) (a : A), rec f (ret a) = f a.
End Codisc.

Axiom codiscrete_def : ∀ A, is_isomorphism (@Codisc.ret A) → codiscrete A.

Instance Codiscrete_Codisc {A} : Codiscrete (∇ A).
Admitted.

Instance : ∀ A, Codiscrete A → ∀ x y : A, Codiscrete (x = y).
Admitted.

Instance Codiscrete_sigma : ∀ A B, Codiscrete A → (∀ x, Codiscrete (B x)) → Codiscrete {x : A & B x}.
Admitted.

Instance Codiscrete_and : ∀ P Q : Prop, Codiscrete P → Codiscrete Q → Codiscrete (P ∧ Q).
Admitted.

Instance Codiscrete_pi : ∀ A B, (∀ x : A, Codiscrete (B x)) → Codiscrete (∀ x : A, B x).
Admitted.

Instance Codiscrete_eq : ∀ A, Codiscrete A → ∀ x y : A, Codiscrete (x = y).
Admitted.


Lemma ex_uni_to_sigma (A : Type) (P : A → Prop) : (exists! x : A, P x) → {x : A & P x ∧ ∀ y, P y → x = y}.
Proof.
  move=> H.
  unshelve esplit.
  - by apply: (iota P).
  - split.
    + apply: iota_prop.
    + move=> a h.
      case: H=> b [h1 h2].
      rewrite -(h2 (iota P (ex_intro (unique [eta P]) b (conj h1 h2)))).
      * apply: iota_prop.
      * by rewrite -(h2 a).
Defined.

Lemma ex_uni_to_sigma_is_prop (A : Type) (P : A → Prop) : (exists! x : A, P x) → ∀ u v : {x : A & P x ∧ ∀ y, P y → x = y}, u = v.
Proof.
  move=> H u v.
  apply: eq_sigT=>//=.
  case: H=> a [h1 h2].
  rewrite -(h2 (projT1 u)).
  - apply: proj1.
    by apply: projT2 u.
  - rewrite -(h2 (projT1 v))//=.
    apply: proj1.
    by apply: projT2 v.
Qed.

Lemma ex_uni_to_sigma_iso A P : is_isomorphism (ex_uni_to_sigma A P).
Proof.
  move=> [a [h1a h2a]].
  unshelve esplit.
  - by exists a; split.
  - split=>//=.
    apply: eq_sigT=>//=.
    rewrite -(h2a (iota P _))//=.
    apply: iota_prop.
Qed.

Definition inverse {A B} (f : A → B) : is_isomorphism f → B → A.
Proof.
  move=> iso b.
  apply: (iota (λ a : A, f a = b)).
  apply: iso.
Defined.

Lemma codiscrete_closed_under_iso : ∀ A B (f : A → B), is_isomorphism f → Codiscrete B → Codiscrete A.
Admitted.


Instance : ∀ A (P : A → Prop), Codiscrete A → (∀ x, Codiscrete (P x)) → Codiscrete (exists! x : A, P x).
Proof.
  move=> A P ? ?.
  apply: (codiscrete_closed_under_iso _ _ _ (ex_uni_to_sigma_iso _ _)).
Qed.

Definition uniform (A : Type) : Prop :=
  ∃ A' : Type, Codiscrete A' ∧ (A' ⇾ A).

Class Uniform (A : Type) :=
  unif : uniform A.
