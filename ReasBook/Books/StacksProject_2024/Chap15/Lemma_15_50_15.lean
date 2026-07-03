import Mathlib
import StacksProject_2024.Chap15.Lemma_15_50_2
import StacksProject_2024.Chap15.Lemma_15_51_7

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open RingPairCat

universe u

section

variable {A : Type u} [CommRing A] [IsGRing A]
variable (I : Ideal A)

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

/- Domain triage:
- primary domain: `G`-rings and the canonical pair-henselization owner in Chapter 15;
- sampled owner declarations:
  `IsGRing`,
  `isGRing_iff_isPRing_isGeometricallyRegularProperty`,
  `RingPairCat.henselizationRing`,
  `isPRing_henselizationRing`;
- best owner abstraction: the source-facing `G`-ring statement should reuse the canonical
  `P`-ring permanence theorem `isPRing_henselizationRing`, specialized to
  `Algebra.IsGeometricallyRegularProperty` through its Chapter 15 owner instances, rather than
  carrying a parallel local proof shell;
- primitive data: a commutative ring `A`, an ideal `I`, and the owner hypothesis `[IsGRing A]`;
- derived API: the `G`-ring instance on `henselizationRing (pairOfIdeal I)`.

Source/core/bridge triage:
- `source-facing`: the `G`-ring permanence statement for pair henselizations;
- `core/canonical`: `IsGRing`, `IsPRing`, and the pair-henselization owner
  `henselizationRing (pairOfIdeal I)`;
- `bridge/view`: the equivalence
  `isGRing_iff_isPRing_isGeometricallyRegularProperty` together with the separable-base-field
  invariance `isGeometricallyRegular_iff_of_isSeparable`. -/
/-- Lemma 15.50.15: if `A` is a `G`-ring and `(A^h, I^h)` is the chosen henselization of the pair
`(A, I)`, then the henselization ring `A^h` is a `G`-ring. -/
instance pairHenselization_isGRing :
    IsGRing (henselizationRing (pairOfIdeal I)) := by
  refine
    (isGRing_iff_isPRing_isGeometricallyRegularProperty
      (henselizationRing (pairOfIdeal I))).2 ?_
  refine
    isPRing_henselizationRing
      I
      IsGeometricallyRegularProperty
      ((isGRing_iff_isPRing_isGeometricallyRegularProperty A).1 inferInstance)

end
