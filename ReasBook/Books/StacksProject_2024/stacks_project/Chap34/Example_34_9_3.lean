import StacksProject_2024.Chap26.Example_26_21_4
import StacksProject_2024.Chap34.Lemma_34_9_2
import StacksProject_2024.Chap34.Lemma_34_9_4

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

noncomputable section

universe u

-- Semantic recall: Example 34.9.3 uses the concrete doubled-origin counterexample from
-- Example 26.21.4. The Chapter 34 owner for the singleton-family neighborhood condition is
-- `HasPointwiseFiniteQuasiCompactNeighborhoodCover`, the singleton-family bridge is
-- `sigmaDescSingleton`, and the fpqc owner remains `IsFpqcCovering`.

variable (k : Type u) [Field k]

/-- The two-term family over the doubled-origin scheme `X` used in Example 34.9.3: the first
member is the inclusion `X_1 ⟶ X`, and the second member is the composite
`Spec(\mathcal O_{X_2, 0}) ⟶ X_2 ⟶ X`. -/
abbrev infiniteAffineSpaceWithZeroDoubledCounterexampleFamily
    {X : Scheme.{u}} (X1 X2 : X.Opens)
    (chart2Iso : X2.toScheme ≅ infiniteAffineSpectrum k) :
    Fin 2 → Over X
  | 0 => Over.mk X1.ι
  | 1 =>
      Over.mk
        ((X2.toScheme).fromSpecStalk
            (chart2Iso.inv.base (infiniteAffineOrigin k)) ≫
          X2.ι)

/-- The singleton family whose sole member is the coproduct morphism
`X_1 ⨿ Spec(\mathcal O_{X_2, 0}) ⟶ X` from Example 34.9.3. -/
abbrev infiniteAffineSpaceWithZeroDoubledCounterexampleSingletonFamily
    {X : Scheme.{u}} (X1 X2 : X.Opens)
    (chart2Iso : X2.toScheme ≅ infiniteAffineSpectrum k) :
    PUnit → Over X :=
  sigmaDescSingleton
    (infiniteAffineSpaceWithZeroDoubledCounterexampleFamily k X1 X2 chart2Iso)

/-- The geometric context realizing the infinite doubled-origin counterexample used in
Example 34.9.3. -/
structure InfiniteAffineSpaceWithZeroDoubledCounterexampleContext
    {X : Scheme.{u}} (X1 X2 : X.Opens)
    (chart1Iso : X1.toScheme ≅ infiniteAffineSpectrum k)
    (chart2Iso : X2.toScheme ≅ infiniteAffineSpectrum k) where
  cover : X1 ⊔ X2 = ⊤
  affineLeft : IsAffineOpen X1
  affineRight : IsAffineOpen X2
  overlapIso : (X1 ⊓ X2).toScheme ≅ (infiniteAffinePuncture k).toScheme

section InfiniteAffineSpaceWithZeroDoubledCounterexample

variable {X : Scheme.{u}}
variable (X1 X2 : X.Opens)
variable (chart1Iso : X1.toScheme ≅ infiniteAffineSpectrum k)
variable (chart2Iso : X2.toScheme ≅ infiniteAffineSpectrum k)
variable (h : InfiniteAffineSpaceWithZeroDoubledCounterexampleContext k X1 X2 chart1Iso chart2Iso)

/-- Example 34.9.3 (tag `0H7E`): for the concrete infinite doubled-origin counterexample from
Example 26.21.4, let `Y = X_1 ⨿ Spec(\mathcal O_{X_2, 0})` and let `Y ⟶ X` be the morphism whose
components are the inclusion `X_1 ⟶ X` and the composite `Spec(\mathcal O_{X_2, 0}) ⟶ X_2 ⟶ X`.
The associated singleton family satisfies the pointwise finite quasi-compact neighborhood
criterion from Lemma 34.9.2, but it is not an fpqc covering. -/
@[stacks 0H7E]
theorem infiniteAffineSpaceWithZeroDoubled_singleton_not_fpqcCovering
    (h : InfiniteAffineSpaceWithZeroDoubledCounterexampleContext k X1 X2 chart1Iso chart2Iso)
    :
    HasPointwiseFiniteQuasiCompactNeighborhoodCover
        (infiniteAffineSpaceWithZeroDoubledCounterexampleSingletonFamily k X1 X2 chart2Iso) ∧
      ¬ IsFpqcCovering
        (infiniteAffineSpaceWithZeroDoubledCounterexampleSingletonFamily k X1 X2 chart2Iso) := sorry

/-- In Example 34.9.3, the singleton family
`X_1 ⨿ Spec(\mathcal O_{X_2, 0}) ⟶ X` satisfies the pointwise finite quasi-compact neighborhood
criterion from Lemma 34.9.2. -/
theorem infiniteAffineSpaceWithZeroDoubled_counterexampleSingletonFamily_hasPointwiseFiniteQuasiCompactNeighborhoodCover
    (h : InfiniteAffineSpaceWithZeroDoubledCounterexampleContext k X1 X2 chart1Iso chart2Iso)
    :
    HasPointwiseFiniteQuasiCompactNeighborhoodCover
      (infiniteAffineSpaceWithZeroDoubledCounterexampleSingletonFamily k X1 X2 chart2Iso) :=
  let Y : PUnit → Over X :=
    infiniteAffineSpaceWithZeroDoubledCounterexampleSingletonFamily k X1 X2 chart2Iso
  let h' : HasPointwiseFiniteQuasiCompactNeighborhoodCover Y ∧ ¬ IsFpqcCovering Y :=
    infiniteAffineSpaceWithZeroDoubled_singleton_not_fpqcCovering k X1 X2 chart1Iso chart2Iso h
  h'.1

/-- In Example 34.9.3, the singleton family
`X_1 ⨿ Spec(\mathcal O_{X_2, 0}) ⟶ X` is not an fpqc covering. -/
theorem infiniteAffineSpaceWithZeroDoubled_counterexampleSingletonFamily_not_isFpqcCovering
    (h : InfiniteAffineSpaceWithZeroDoubledCounterexampleContext k X1 X2 chart1Iso chart2Iso)
    :
    ¬ IsFpqcCovering
      (infiniteAffineSpaceWithZeroDoubledCounterexampleSingletonFamily k X1 X2 chart2Iso) :=
  let Y : PUnit → Over X :=
    infiniteAffineSpaceWithZeroDoubledCounterexampleSingletonFamily k X1 X2 chart2Iso
  let h' : HasPointwiseFiniteQuasiCompactNeighborhoodCover Y ∧ ¬ IsFpqcCovering Y :=
    infiniteAffineSpaceWithZeroDoubled_singleton_not_fpqcCovering k X1 X2 chart1Iso chart2Iso h
  h'.2

end InfiniteAffineSpaceWithZeroDoubledCounterexample

end

end AlgebraicGeometry
