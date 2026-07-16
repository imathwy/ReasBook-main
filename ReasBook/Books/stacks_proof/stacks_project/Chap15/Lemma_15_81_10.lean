import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_81_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

section

/-
Domain-style sampling:
- primary domain: relative finite presentation of modules over a finite type algebra;
- sampled owner declarations:
  `Module.FinitePresentationRelativeTo`,
  `Module.finitePresentation_of_finitePresentationRelativeTo`,
  `Module.finitePresentation_of_split_exact`,
  `Module.FinitePresentation.prod`;
- best owner abstraction: the source-facing predicate `Module.FinitePresentationRelativeTo R A M`;
- primitive data: one surjective polynomial presentation of `A` over `R` together with finite
  presentation of the relevant module over that polynomial ring;
- derived API: stability of relative finite presentation under the split projections onto the two
  direct summands of a product.

Source/core/bridge triage:
- `source-facing`: the statement that relative finite presentation of `M × M'` forces the same
  property for both summands;
- `core/canonical`: `Module.FinitePresentationRelativeTo` and mathlib's split-exact theorem
  `Module.finitePresentation_of_split_exact`;
- `bridge/view`: the proof below unpacks one witness for the source-facing owner and applies the
  core split-exact result over that witness ring before repackaging the same presentation. -/
variable {R : Type u} {A : Type v} {M : Type w} {M' : Type x}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module A M]
variable [AddCommGroup M'] [Module A M']

namespace Module

-- Proof sketch: choose a surjective polynomial presentation of `A` over `R` witnessing that
-- `M × M'` is relatively finitely presented. Over the polynomial ring, finite presentation is
-- stable under split direct summands, so apply the projections `M × M' → M` and `M × M' → M'`
-- together with their standard sections, then repackage the same presentation witness.
/-- Lemma 15.81.10: if `M × M'` is finitely presented relative to `R` as an `A`-module, then both
`M` and `M'` are finitely presented relative to `R`. -/
@[stacks 0672]
theorem finitePresentationRelativeTo_summands_of_prod
    (h : Module.FinitePresentationRelativeTo R A (M × M')) :
    Module.FinitePresentationRelativeTo R A M ∧ Module.FinitePresentationRelativeTo R A M' := by
  rcases h with ⟨n, α, hα, hprod⟩
  let P := MvPolynomial (Fin n) R
  letI : Module P M := Module.compHom M α.toRingHom
  letI : Module P M' := Module.compHom M' α.toRingHom
  letI : Module P (M × M') := Module.compHom (M × M') α.toRingHom
  letI : Module.FinitePresentation P (M × M') := hprod
  constructor <;> refine ⟨n, α, hα, ?_⟩
  · exact Module.finitePresentation_of_split_exact
      (LinearMap.inl P M M') (LinearMap.snd P M M') (LinearMap.inr P M M')
      rfl LinearMap.inl_injective Function.Exact.inl_snd
  · exact Module.finitePresentation_of_split_exact
      (LinearMap.inr P M M') (LinearMap.fst P M M') (LinearMap.inl P M M')
      rfl LinearMap.inr_injective Function.Exact.inr_fst

-- Proof sketch: apply `finitePresentationRelativeTo_summands_of_prod` to `M × M'` and take the
-- first projection of the resulting conjunction.
/-- If `M × M'` is finitely presented relative to `R`, then `M` is finitely presented relative to
`R`. -/
theorem finitePresentationRelativeTo_left_of_prod
    (h : Module.FinitePresentationRelativeTo R A (M × M')) :
    Module.FinitePresentationRelativeTo R A M :=
  (finitePresentationRelativeTo_summands_of_prod h).1

-- Proof sketch: apply `finitePresentationRelativeTo_summands_of_prod` to `M × M'` and take the
-- second projection of the resulting conjunction.
/-- If `M × M'` is finitely presented relative to `R`, then `M'` is finitely presented relative to
`R`. -/
theorem finitePresentationRelativeTo_right_of_prod
    (h : Module.FinitePresentationRelativeTo R A (M × M')) :
    Module.FinitePresentationRelativeTo R A M' :=
  (finitePresentationRelativeTo_summands_of_prod h).2

end Module

end
