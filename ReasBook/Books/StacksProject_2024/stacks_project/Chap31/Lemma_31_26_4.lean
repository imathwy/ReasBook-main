import Mathlib
import StacksProject_2024.Chap31.Definition_31_26_2
import StacksProject_2024.Chap31.Definition_31_26_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

section

attribute [local instance] Classical.propDecidable

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]

-- Semantic recall: `lean_leansearch` surfaced only analytic/meromorphic divisor owners, and local
-- Chapter 29 precedent (`Lemma_29_49_7`) already records generic-point stalks inside
-- `X.functionField` by `Set.range (algebraMap ...)`. This item therefore stays on the Chapter 31
-- owners `PrimeDivisor`, `LocallyFinite`, and `Scheme.primeDivisorOrder`.

/-- Lemma 31.26.4 (1): let `X` be a locally Noetherian integral scheme and let `f ∈ R(X)ˣ`. Then
the family of prime divisors `Z ⊆ X` such that `f` does not lie in the local ring
`\mathcal{O}_{X, \xi}` at the generic point `\xi` of `Z` is locally finite in `X`. -/
@[stacks 02RL]
theorem locallyFinite_primeDivisors_not_mem_genericPointStalk
    (f : X.functionFieldˣ) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      let eta : X := Z.genericPoint
      if (f : X.functionField) ∈
          Set.range (algebraMap (X.presheaf.stalk eta) ↥X.functionField) then
        (∅ : Set X)
      else
        (Z.support : Set X) := sorry

/-- Lemma 31.26.4 (2): let `X` be a locally Noetherian integral scheme and let `f ∈ R(X)ˣ`.
Assuming the order of vanishing along each prime divisor is defined through
`X.primeDivisorOrder`, the family of prime divisors `Z ⊆ X` with `ord_Z(f) ≠ 0` is locally finite
in `X`. -/
@[stacks 02RL]
theorem locallyFinite_primeDivisors_primeDivisorOrder_ne_zero
    (f : X.functionFieldˣ)
    [PrimeDivisorDiscreteValuationRings X] :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if X.primeDivisorOrder Z f = 0 then
        (∅ : Set X)
      else
        (Z.support : Set X) := sorry

end

end AlgebraicGeometry.Scheme
