From synrl Require Import Preamble Modality Orthogonality Coequalizer.

Export Modality.

Axiom codiscrete : Type → Prop.

Declare Instance codiscrete_replete : RepleteSubuniverse codiscrete.
Declare Instance codiscrete_lex : LexSubuniverse codiscrete.
Declare Instance codiscrete_dense : DenseSubuniverse codiscrete.
Declare Instance codiscrete_regular : RegularSubuniverse codiscrete.
Declare Instance codiscrete_DepModality : Mod.DepModality codiscrete.

Notation Codiscrete := (Modal codiscrete).
Notation "∇ A" := (Mod.T codiscrete A) (at level 60).
Notation "∇-p P" := (ModP.T codiscrete (P <: Prop)) (at level 60).

Definition codisc_or (P Q : Prop) `{Codiscrete P} `{Codiscrete Q} := ∇-p (P ∨ Q).

Infix "∇∨ " := codisc_or (at level 10).

Class CodiscretelyDecidable (A : Type) `{Codiscrete A} :=
  codisc_dcd : ∀ x y : A, (x = y) ∇∨ ¬ (x = y).

Definition uniform (A : Type) : Prop :=
  ∃ A' : Type, Codiscrete A' ∧ (A' ⇾ A).

Class Uniform (A : Type) :=
  unif : uniform A.


Notation IsAssembly := (Separated codiscrete).
Notation Asm := (Sep codiscrete).
