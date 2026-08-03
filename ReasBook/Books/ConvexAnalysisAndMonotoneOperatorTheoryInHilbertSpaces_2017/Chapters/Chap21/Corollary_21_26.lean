import BauschkeLean.Chap16.Proposition_16_27
import BauschkeLean.Chap20.Example_20_3
import BauschkeLean.Chap21.Corollary_21_19

open scoped InnerProductSpace SetValuedOperator

universe u

namespace ERealFunction

section SubdifferentialLocalBoundedness

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Source/core/bridge triage:
-- - `source-facing`: Corollary 21.26 is the boundedness of `∂ f(C)` for compact
--   `C ⊆ interior (effectiveDomain f)`.
-- - `core/canonical`: Chapter 21 packages the bounded-image conclusion for a monotone operator as
--   `Bornology.IsBounded (A.image C)`.
-- - `bridge/view`: Proposition 16.27 turns interior effective-domain points into
--   subdifferential domain points, and Example 20.3 supplies the primitive monotonicity owner
--   `IsMonotone (∂ f)` needed by Corollary 21.19.
--
-- Semantic recall: `lean_leansearch` returned only generic bounded-image facts, so the verified
-- local owners remain `Bornology.IsBounded ((∂ f).image C)` and `interior (effectiveDomain f)`.

/-- Corollary 21.26: if `f ∈ Γ₀(H)` and `C` is a compact subset of
`interior (effectiveDomain f)`, then `∂ f(C)` is bounded, formalized as
`Bornology.IsBounded ((∂ f).image C)`. -/
theorem subdifferential_image_bounded_of_isCompact_of_subset_interior_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (C : Set H)
    (hCcompact : IsCompact C) (hCsubset : C ⊆ interior (effectiveDomain f)) :
    Bornology.IsBounded ((∂ f).image C) := by
  have hinterior_subset :
      interior (effectiveDomain f) ⊆ interior (SetValuedOperator.dom (∂ f)) := by
    rw [IsOpen.subset_interior_iff isOpen_interior]
    intro x hx
    have hxcont : ContinuousPoint f x :=
      continuousPoint_of_mem_interior_effectiveDomain_of_mem_gammaZero hf hx
    exact continuitySet_subset_subdifferentialDomain_of_mem_gammaZero hf hxcont
  have hCsubset_dom : C ⊆ interior (SetValuedOperator.dom (∂ f)) := fun x hx ↦
    hinterior_subset (hCsubset hx)
  exact SetValuedOperator.image_bounded_of_isCompact_of_subset_interior_dom
    (∂ f) (subdifferential_isMonotone f hf.2.nonempty) C hCcompact hCsubset_dom

end SubdifferentialLocalBoundedness

end ERealFunction
