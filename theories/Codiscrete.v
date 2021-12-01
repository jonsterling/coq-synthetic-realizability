From synrl Require Import Preamble Orthogonality.

Axiom codiscrete : Type → Prop.
Class Codiscrete (A : Type) : Prop :=
  {codisc : codiscrete A}.

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

Instance : ∀ A B, Codiscrete A → (∀ x, Codiscrete (B x)) → Codiscrete {x : A & B x}.
Admitted.
