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

(* This holds because the constant objects functor for a realizability topos additionally preserves covers. *)
Instance Codiscrete_exists : ∀ A (P : A → Prop), Codiscrete A → (∀ x, Codiscrete (P x)) → Codiscrete (∃ x : A, P x).
Admitted.

Definition uniform (A : Type) : Prop :=
  ∃ A' : Type, Codiscrete A' ∧ (A' ⇾ A).

Class Uniform (A : Type) :=
  unif : uniform A.
