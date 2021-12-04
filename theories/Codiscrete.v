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

Definition codiscretely_eq (A : Type) (x y : A) : Prop :=
  ∇-p (x = y).

Instance Equivalence_codiscretely_eq {A} : RelationClasses.Equivalence (codiscretely_eq A).
Proof.
  split.
  - by move=> ?; apply: ModP.unit.
  - move=> u v.
    apply: ModP.rec=>->.
    by apply: ModP.unit.
  - move=> u v w.
    by apply: ModP.rec=>->.
Qed.

Notation IsAssembly := (Modal is_assembly).

Definition Asm_T (A : Type) := Quotient.T A (codiscretely_eq A).

Instance IsAssembly_Asm_T {A} : IsAssembly (Asm_T A).
Proof.
  apply: Quotient.indp=> x.
  apply: Quotient.indp=> y.
  apply: (replete _ _ Quotient.glue).
  - by apply: Quotient.glue_is_iso.
  - by apply: ModP.Modal_T.
Qed.

Instance assemblies_ModalOperator : Mod.ModalOperator is_assembly.
Proof.
  unshelve esplit.
  - by apply: Asm_T.
  - by move=>?; apply: IsAssembly_Asm_T.
  - by move=>?; apply: Quotient.intro.
Defined.

Instance assemblies_DepModality : Mod.DepModality is_assembly.
Proof.
  unshelve esplit.
  - typeclasses eauto.
  - move=> A B H f.
    unshelve esplit.
    + unshelve apply: Quotient.ind.
      * apply: f.
      * move=> x y.
        apply: ModP.ind.
        -- by move=> ?; apply: H.
        -- by move=> ?; simplify_eqs.
    + split=>//=.
      move=> h <-.
      by apply: depfunext; apply: Quotient.indp.
Defined.

Instance Codiscrete_EqOfAssembly A `{IsAssembly A} {x y : A} : Codiscrete (x = y).
Proof. by apply: (mod x y). Qed.
