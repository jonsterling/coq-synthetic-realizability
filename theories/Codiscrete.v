From synrl Require Import Preamble Orthogonality.

Axiom codiscrete : Type → Prop.
Class Codiscrete (A : Type) : Prop :=
  codisc : codiscrete A.

Axiom Codisc : Type → Type.
Axiom CodiscProp : Prop → Prop.

Notation "∇ A" := (Codisc A) (at level 60).
Notation "∇-p A" := (CodiscProp A) (at level 60).

Module Codisc.
  Axiom ret : ∀ {A}, A → ∇ A.
  Axiom rec : ∀ {A B} `{Codiscrete B}, (A → B) → ∇ A → B.
  Axiom ind : ∀ {A} B `{∀ x, Codiscrete (B x)}, (∀ x : A, B (ret x)) → ∀ x : ∇ A, B x.
  Axiom rec_beta : ∀ {A B} `{Codiscrete B} (f : A → B) (a : A), rec f (ret a) = f a.
  Axiom ind_beta : ∀ {A B} `{∀ x, Codiscrete (B x)} (f : ∀ x, B (ret x)) (a : A), ind B f (ret a) = f a.
End Codisc.

Module CodiscProp.
  Axiom ret : ∀ {P : Prop}, P → ∇-p P.
  Axiom rec : ∀ {P : Prop} {B : Type} `{Codiscrete B}, (P → B) → ∇-p P → B.
  Axiom rec_beta : ∀ {P : Prop} {B : Type} `{Codiscrete B} (f : P → B) (u : P), rec f (ret u) = f u.
  Axiom ind : ∀ {P : Prop} (B : ∇-p P → Type) `{∀ x, Codiscrete (B (ret x))}, (∀ x : P, B (ret x)) → ∀ x : ∇-p P, B x.
  Axiom ind_beta : ∀ {P : Prop} {B : ∇-p P → Prop} `{∀ x, Codiscrete (B x)} (f : ∀ x, B (ret x)) (x : P), ind B f (ret x) = f x.
End CodiscProp.

Instance Codiscrete_Codisc {A} : Codiscrete (∇ A).
Admitted.

Instance Codiscrete_CodiscProp {A} : Codiscrete (∇-p A).
Admitted.

Instance Codiscrete_eq {A} `{Codiscrete A} {x y : A} : Codiscrete (x = y).
Admitted.

Instance Codiscrete_sigma {A B} `{Codiscrete A} `{∀ x : A, Codiscrete (B x)} : Codiscrete {x : A & B x}.
Admitted.

Instance Codiscrete_pi {A B} `{∀ x : A, Codiscrete (B x)} : Codiscrete (∀ x : A, B x).
Admitted.

Instance Codiscrete_subset {A} {P : A → Prop} `{Codiscrete A} `{∀ x : A, Codiscrete (P x)} : Codiscrete {x : A | P x}.
Admitted.

Instance Codiscrete_and {P Q : Prop} `{Codiscrete P} `{Codiscrete Q} : Codiscrete (P ∧ Q).
Admitted.

Instance Codiscrete_true : Codiscrete 𝟙.
Admitted.

(* This holds because the constant objects functor for a realizability topos additionally preserves the initial object, i.e. the subtopos is dense *)
Instance Codiscrete_false : Codiscrete False.
Admitted.

(* This holds because the constant objects functor for a realizability topos additionally preserves covers. *)
Instance Codiscrete_exists {A} {P : A → Prop} `{Codiscrete A} `{∀ x : A, Codiscrete (P x)} : Codiscrete (∃ x : A, P x).
Admitted.

Instance Codisc_not {P} : Codiscrete (¬ P).
Proof. by apply: Codiscrete_pi. Qed.

Definition uniform (A : Type) : Prop :=
  ∃ A' : Type, Codiscrete A' ∧ (A' ⇾ A).

Class Uniform (A : Type) :=
  unif : uniform A.

Definition codisc_or (P Q : Prop) `{Codiscrete P} `{Codiscrete Q} := ∇-p (P ∨ Q).

Infix "∇∨ " := codisc_or (at level 10).

Class CodiscretelyDecidable (A : Type) `{Codiscrete A} :=
  codisc_dcd : ∀ x y : A, (x = y) ∇∨ (¬ (x = y)).
