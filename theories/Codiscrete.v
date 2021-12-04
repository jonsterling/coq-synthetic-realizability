From synrl Require Import Preamble Modality Orthogonality.

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


Definition is_assembly (A : Type) := ∀ x y : A, codiscrete (x = y).

Instance assemblies_replete : RepleteSubuniverse is_assembly.
Proof.
  move=> A B f iso asmA x y.
  pose g := iso_inv f iso.
  apply: (replete (g x = g y) (x = y)).
  - by apply/iso_injective/iso_inv_iso.
  - move=> ? h.
    unshelve esplit=>//.
    by rewrite h.
  - by apply: asmA.
Qed.

Declare Instance assemblies_DepModality : Mod.DepModality is_assembly.

Notation Asm := (Mod.T is_assembly).

Notation IsAssembly := (Modal is_assembly).


Instance Codiscrete_EqOfAssembly A `{IsAssembly A} {x y : A} : Codiscrete (x = y).
Proof. by apply: (mod x y). Qed.
