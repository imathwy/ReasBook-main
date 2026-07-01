import Mathlib.RingTheory.Valuation.ValuationSubring

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {K : Type u} [Field K]

/-- Lemma 10.50.5: a subring of a field containing either `x` or `x⁻¹` for every `x : K`
is a valuation ring with fraction field the ambient field `K`. -/
-- Layering:
-- * source-facing: the theorem speaks about the given subring `A`.
-- * core/canonical owner: `ValuationSubring K`.
-- * bridge: instantiate the canonical owner `ValuationSubring.ofSubring A hA` and reuse its
--   derived `ValuationRing` and `IsFractionRing` instances.
theorem valuationRing_and_isFractionRing_of_mem_or_inv_mem (A : Subring K)
    (hA : ∀ x : K, x ∈ A ∨ x⁻¹ ∈ A) :
    ValuationRing A ∧ IsFractionRing A K := by
  let V : ValuationSubring K := ValuationSubring.ofSubring A hA
  change ValuationRing V ∧ IsFractionRing V K
  exact ⟨inferInstance, inferInstance⟩

end
