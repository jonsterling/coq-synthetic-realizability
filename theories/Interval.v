From synrl Require Import Preamble Orthogonality Codiscrete.

Definition 𝕀 := ∇ 𝟚.

Instance : 𝕀 ⇾ 𝟙.
Proof. by exists (λ _, Logic.I)=> ?; exists (Codisc.ret true). Qed.


Section BipointedCodiscrete.

  (** HRR prove that Orth(𝕀) = Orth(S) for any strictly bipointed
  codiscrete object S. We generalize this result to realizability over
  a topos other than Set; to do so, we must assume that S is
  codiscretely decidable. In fact, a slightly weaker but somewhat
  unnatural assumption would suffice: that S has a basepoint whose
  equivalence class is decidable. *)


  Context {S} `{Codiscrete S} `{StrictlyBipointed S} `{CodiscretelyDecidable S}.

  Local Definition covering_map_graph (s0 : S) : S → 𝕀 → Prop :=
    λ s i, (s0 = s → i = Codisc.ret true) ∧ (∇¬(s0 = s) → i = Codisc.ret false).

  Local Lemma covering_graph_functional (s0 : S) : Functional (covering_map_graph s0).
  Proof.
    move=> s.
    generalize (codisc_dcd s s0); apply: CodiscProp.rec; case.
    - move=> ss0.
      exists (Codisc.ret true); split.
      + split=>//= h.
        by apply: CodiscProp.rec; last by apply: h.
      + by move=> ? [h _]; rewrite h.
    - move=> h.
      exists (Codisc.ret false); split.
      + split=>//= s0s.
        by apply: CodiscProp.rec; last by apply: h.
      + move=> i [h1 h2].
        rewrite h2//= => ?.
        by apply: h.
  Qed.

  #[global]
  Instance : S ⇾ 𝕀.
  Proof.
    case: sbptd => [s1 [s2 sdisj]].
    unshelve esplit.
    - apply: (funcompr (covering_map_graph s1)).
      by apply: covering_graph_functional.
    - move=> i; unshelve esplit; move: i.
      + by apply:Codisc.rec; case; [exact: s1 | exact: s2].
      + apply: Codisc.ind=> x.
        rewrite Codisc.rec_beta.
        apply: funcompr_compute.
        case: x; split=>//= h.
        by apply: CodiscProp.rec; last by apply: h.
  Qed.

  Instance to_orth_𝕀 {I} {X : I → Type} `{[S] ⫫ X} : [𝕀] ⫫ X.
  Proof. by apply: orth_cover. Qed.

  Instance from_orth_𝕀 {I} {X : I → Type} `{[𝕀] ⫫ X} : [S] ⫫ X.
  Proof.
    unshelve apply: orth_cover_converse =>//=.
    - exact: Codisc.ret.
    - move=> s.
      exists (Codisc.rec s).
      rewrite /precomp.
      apply: funext=>?.
      by apply: Codisc.rec_beta.
  Qed.

End BipointedCodiscrete.

(** The theorem of HRR that Orth(U) = Orth(∇2) for a uniform strictly
bipointed object U does *not* hold in generality. It seems to require
that all codiscrete objects are decidable. But this is needed to check
that Orth(Ω) = Orth(∇2). Of course, it may be that this is just not
the right definition of discreteness; I suspect that for defining the
correct notion of modest set, we would still want Orth(∇2). *)
