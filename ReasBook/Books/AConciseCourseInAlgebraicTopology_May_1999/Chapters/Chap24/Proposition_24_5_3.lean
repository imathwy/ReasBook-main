import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Theorem_24_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.ComplexKTheoryAdams

noncomputable section

universe u

open scoped ComplexKTheory ComplexKTheoryAdams

-- This file records the reduced action of a Chapter 24 Adams family on reduced complex
-- `K`-theory, keeping the source-facing `S²` Hopf/Bott class formula while deriving the reduced
-- endomorphism canonically from the ambient Adams operation.

instance sphereTwoCompactSpace : CompactSpace SphereTwo := by
  change CompactSpace (TopCat.diskBoundary 3)
  infer_instance

namespace IsComplexKTheoryAdams

/-- Adams operations preserve reduced complex `K`-theory. -/
theorem map_mem_reducedComplexKTheory
    {ψ : ComplexKTheoryAdamsFamily} (hψ : IsComplexKTheoryAdams ψ)
    (X : Type u) [TopologicalSpace X] [CompactSpace X] (x₀ : X)
    (k : NonzeroInt) (ξ : K̃(X, x₀)) :
    (ψ ^[k]) ξ ∈ K̃(X, x₀) := sorry

/-- The ambient Adams operation `ψ ^[k]` canonically restricts to an additive endomorphism of
reduced complex `K`-theory. -/
def reducedOp
    {ψ : ComplexKTheoryAdamsFamily} (hψ : IsComplexKTheoryAdams ψ)
    (X : Type u) [TopologicalSpace X] [CompactSpace X] (x₀ : X)
    (k : NonzeroInt) :
    K̃(X, x₀) →+ K̃(X, x₀) :=
  (((ψ ^[k]).toAddMonoidHom.restrict (K̃(X, x₀))).codRestrict (K̃(X, x₀))
    fun ξ ↦ hψ.map_mem_reducedComplexKTheory X x₀ k ξ)

@[simp] theorem reducedOp_apply
    {ψ : ComplexKTheoryAdamsFamily} (hψ : IsComplexKTheoryAdams ψ)
    (X : Type u) [TopologicalSpace X] [CompactSpace X] {x₀ : X}
    (k : NonzeroInt) (ξ : K̃(X, x₀)) :
    hψ.reducedOp X x₀ k ξ =
      ⟨(ψ ^[k]) ξ, hψ.map_mem_reducedComplexKTheory X x₀ k ξ⟩ := rfl

@[simp] theorem reducedOp_coe_apply
    {ψ : ComplexKTheoryAdamsFamily} (hψ : IsComplexKTheoryAdams ψ)
    (X : Type u) [TopologicalSpace X] [CompactSpace X] {x₀ : X}
    (k : NonzeroInt) (ξ : K̃(X, x₀)) :
    ((hψ.reducedOp X x₀ k ξ : K̃(X, x₀)) : complexKTheory X) = (ψ ^[k]) ξ := rfl

end IsComplexKTheoryAdams

/-- Proposition 24.5.3. Relative to the reduced Bott class from Theorem 24.2.4, Adams operations
do not commute with Bott periodicity in the naive way: on the canonical reduced Hopf/Bott class
`sphereTwoReducedHopfLineClass x₀ ∈ K̃(S², x₀)`, the induced reduced Adams endomorphism acts by
multiplication by `k`. -/
theorem sphereTwoReducedHopfLineClass_adams
    {ψ : ComplexKTheoryAdamsFamily} (hψ : IsComplexKTheoryAdams ψ)
    (x₀ : SphereTwo)
    (k : NonzeroInt) :
    hψ.reducedOp SphereTwo x₀ k (sphereTwoReducedHopfLineClass x₀) =
      ((k : ℤ) • sphereTwoReducedHopfLineClass x₀ : K̃(SphereTwo, x₀)) := sorry

/-- Coercing Proposition 24.5.3 to `K(S²)` recovers the ambient Adams-operation formula. -/
theorem sphereTwoReducedHopfLineClass_adams_coe
    {ψ : ComplexKTheoryAdamsFamily} (hψ : IsComplexKTheoryAdams ψ)
    (x₀ : SphereTwo)
    (k : NonzeroInt) :
    (ψ ^[k]) (sphereTwoReducedHopfLineClass x₀) =
      ((k : ℤ) • sphereTwoReducedHopfLineClass x₀ : complexKTheory SphereTwo) := by
  simpa using congrArg (fun η : K̃(SphereTwo, x₀) ↦ (η : complexKTheory SphereTwo))
    (sphereTwoReducedHopfLineClass_adams hψ x₀ k)

/-- Any reduced class identified with the canonical reduced Hopf/Bott class satisfies the same
Adams-operation formula. -/
theorem sphereTwoReducedBottClass_adams
    {ψ : ComplexKTheoryAdamsFamily} (hψ : IsComplexKTheoryAdams ψ)
    (x₀ : SphereTwo) (η : K̃(SphereTwo, x₀))
    (hη : η = sphereTwoReducedHopfLineClass x₀)
    (k : NonzeroInt) :
    hψ.reducedOp SphereTwo x₀ k η = ((k : ℤ) • η : K̃(SphereTwo, x₀)) := by
  simpa [hη] using sphereTwoReducedHopfLineClass_adams hψ x₀ k

/-- Coercing the reduced companion theorem to `K(S²)` yields the ambient Adams-operation
formula. -/
theorem sphereTwoReducedBottClass_adams_coe
    {ψ : ComplexKTheoryAdamsFamily} (hψ : IsComplexKTheoryAdams ψ)
    (x₀ : SphereTwo) (η : K̃(SphereTwo, x₀))
    (hη : η = sphereTwoReducedHopfLineClass x₀)
    (k : NonzeroInt) :
    (ψ ^[k]) η = ((k : ℤ) • η : complexKTheory SphereTwo) := by
  simpa using congrArg (fun ξ : K̃(SphereTwo, x₀) ↦ (ξ : complexKTheory SphereTwo))
    (sphereTwoReducedBottClass_adams hψ x₀ η hη k)
