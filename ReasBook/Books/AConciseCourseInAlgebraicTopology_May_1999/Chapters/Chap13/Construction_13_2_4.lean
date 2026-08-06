import Mathlib.Topology.CWComplex.Classical.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_4.Quotient
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_4.Comparison
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_4.Suspension

universe u

noncomputable section

/-- Helper for Construction 13.2.4: a CW structure on `Set.univ` supplies the Hausdorffness
needed by `Topology.CWComplex.skeleton`. -/
private instance instT2SpaceOfUnivCWComplex
    {X : Type u} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] : T2Space X :=
  sorry

/-- Helper for Construction 13.2.4: the chosen copy of `X^(n - 1)` inside the `n`-skeleton
`X^n`. -/
private abbrev cellularBoundaryPreviousSkeleton
    (X : Type u) [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] (n : ℕ+) :
    Set (Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ)) :=
  { x | x.1 ∈ Topology.CWComplex.skeleton (Set.univ : Set X) ((n : ℕ) - 1) }

/-- Helper for Construction 13.2.4: the chosen copy of `X^(n - 2)` inside the same ambient
`n`-skeleton `X^n`. -/
private abbrev cellularBoundarySecondPreviousSkeleton
    (X : Type u) [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] (n : ℕ+) :
    Set (Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ)) :=
  { x | x.1 ∈ Topology.CWComplex.skeleton (Set.univ : Set X) ((n : ℕ) - 2) }

/-- Construction 13.2.4. For a CW complex `X` and `n : ℕ+`, the topological boundary map
`∂ₙ : X^n / X^(n - 1) ⟶ Σ(X^(n - 1) / X^(n - 2))` is obtained from chosen quotient/cofiber
comparison data for `X^(n - 1) ↪ X^n`, followed by the canonical cofiber-model map to the
chosen suspension-model owner of `Σ(X^(n - 1) / X^(n - 2))`. The comparison to the repository's
reduced suspension is companion bridge API rather than the primary labeled target. -/
noncomputable abbrev topologicalBoundaryMap
    (X : Type u) [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] (n : ℕ+)
    (comparison : TopologicalBoundaryComparison (cellularBoundaryPreviousSkeleton X n)) :
    C(collapseSubsetType
        (Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ))
        (cellularBoundaryPreviousSkeleton X n),
      previousSkeletonQuotientSuspension
        (cellularBoundarySecondPreviousSkeleton X n)
        (cellularBoundaryPreviousSkeleton X n)) :=
  topologicalBoundaryMapModel
    (cellularBoundarySecondPreviousSkeleton X n)
    (cellularBoundaryPreviousSkeleton X n)
    comparison.quotientToCofiber

/-- Source-facing companion theorem for Construction 13.2.4: the boundary map is the chosen
quotient/cofiber comparison followed by the cofiber-model map into the chosen
suspension-model owner. -/
theorem topologicalBoundaryMap_def
    (X : Type u) [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] (n : ℕ+)
    (comparison : TopologicalBoundaryComparison (cellularBoundaryPreviousSkeleton X n)) :
    topologicalBoundaryMap X n comparison =
      topologicalBoundaryMapModel
        (cellularBoundarySecondPreviousSkeleton X n)
        (cellularBoundaryPreviousSkeleton X n)
        comparison.quotientToCofiber := sorry

/-- Choosing a point of `Xⁿ⁻²` compares the source-facing boundary map with a map into the
repository's canonical reduced-suspension owner. -/
noncomputable abbrev topologicalBoundaryMapToReducedSuspension {X : Type u} [TopologicalSpace X]
    {Xnm2 Xnm1 : Set X} (h : Xnm2 ⊆ Xnm1) (x0 : Xnm2)
    (comparison : TopologicalBoundaryComparison Xnm1) :
    C(collapseSubsetType X Xnm1,
      (suspensionSpace (previousSkeletonQuotientPointed h x0)).toCompactlyGenerated) :=
  (previousSkeletonQuotientSuspensionComparison h x0).comp
    (topologicalBoundaryMapModel Xnm2 Xnm1 comparison.quotientToCofiber)
