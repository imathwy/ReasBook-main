import Mathlib
import stacks_project.Chap10.Lemma_10_155_1
import stacks_project.Chap15.Lemma_15_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open RingPairCat

universe u

noncomputable section

section

variable (A : Type u) [CommRing A] [IsLocalRing A]

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

-- Proof sketch: the henselization pair `(A, maximalIdeal A)` is henselian by construction. Lemma
-- `15.12.2` identifies its distinguished ideal with the image of `maximalIdeal A`, so the target
-- has the expected maximal ideal and residue field, and the filtered-colimit-of-etale condition is
-- the same one appearing in the pair-henselization construction of Lemma `15.12.1`.
/-- Lemma 15.12.3: the pair-henselization functor sends a local ring `A`, viewed as the pair
`(A, maximalIdeal A)`, to a henselization of `A` as a local ring. -/
theorem localRing_henselization_isHenselizationOf :
    IsHenselizationOf A (henselizationRing (pairOfIdeal (maximalIdeal A))) := sorry

/-- The pair-henselization of a local ring is available to typeclass search as a henselization. -/
instance localRing_henselization.instIsHenselizationOf :
    IsHenselizationOf A (henselizationRing (pairOfIdeal (maximalIdeal A))) :=
  localRing_henselization_isHenselizationOf A

end
