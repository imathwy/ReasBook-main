import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

noncomputable section

universe u

-- Semantic search tooling was unavailable in this environment; this file follows the local
-- `LeeBoundaryModelSpace` precedent already used in Proposition 1.38.

/-- Lee's model upper half-space `H^n`: in dimension `0` this is `ℝ^0`, and in positive
dimensions it is mathlib's Euclidean half-space. -/
abbrev LeeBoundaryModelSpace : ℕ → Type
  | 0 => EuclideanSpace ℝ (Fin 0)
  | n + 1 => EuclideanHalfSpace (n + 1)

scoped[Manifold] notation "ℍ^{" n:max "}" => LeeBoundaryModelSpace n

/-- The source's model upper half-space carries the natural topology inherited from its
two cases. -/
instance leeBoundaryModelSpaceTopologicalSpace (n : ℕ) :
    TopologicalSpace (ℍ^{n}) := by
  cases n with
  | zero => infer_instance
  | succ n =>
      let _ : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
      change TopologicalSpace (EuclideanHalfSpace (n + 1))
      infer_instance

/-- Lee's model with corners for a topological manifold with boundary: in dimension `0` this is
the Euclidean model `𝓡 0`, and in positive dimensions it is the half-space model `𝓡∂ (n + 1)`. -/
abbrev leeBoundaryModelWithCorners :
    (n : ℕ) → ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (LeeBoundaryModelSpace n)
  | 0 => 𝓡 0
  | n + 1 => 𝓡∂ (n + 1)

/-- Lee's model upper half-space is Hausdorff in every dimension. -/
instance leeBoundaryModelSpaceT2Space (n : ℕ) :
    T2Space (ℍ^{n}) := by
  cases n with
  | zero =>
      simpa [LeeBoundaryModelSpace] using
        (inferInstance : T2Space (EuclideanSpace ℝ (Fin 0)))
  | succ n =>
      let _ : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
      simpa [LeeBoundaryModelSpace, EuclideanHalfSpace] using
        (inferInstance : T2Space { x : EuclideanSpace ℝ (Fin (n + 1)) // 0 ≤ x 0 })

/-- Lee's model upper half-space is second countable in every dimension. -/
instance leeBoundaryModelSpaceSecondCountableTopology (n : ℕ) :
    SecondCountableTopology (ℍ^{n}) := by
  cases n with
  | zero =>
      simpa [LeeBoundaryModelSpace] using
        (inferInstance : SecondCountableTopology (EuclideanSpace ℝ (Fin 0)))
  | succ n =>
      let _ : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
      simpa [LeeBoundaryModelSpace, EuclideanHalfSpace] using
        (inferInstance :
          SecondCountableTopology { x : EuclideanSpace ℝ (Fin (n + 1)) // 0 ≤ x 0 })

/-- Lee's model upper half-space carries its canonical self-charted-space structure. -/
instance leeBoundaryModelSpaceChartedSpace (n : ℕ) :
    ChartedSpace (ℍ^{n}) (ℍ^{n}) :=
  chartedSpaceSelf _

/-- Definition 1.5-extra-1: An `n`-dimensional topological manifold with boundary is a
second-countable Hausdorff charted space modelled on Lee's upper half-space `ℍ^n`, together with
the corresponding canonical `C^0` manifold structure. -/
class TopologicalManifoldWithBoundary (n : ℕ) (M : Type u)
    [TopologicalSpace M] extends
    T2Space M, SecondCountableTopology M, ChartedSpace (ℍ^{n}) M,
    IsManifold (leeBoundaryModelWithCorners n) 0 M

attribute [instance] TopologicalManifoldWithBoundary.toT2Space
attribute [instance] TopologicalManifoldWithBoundary.toSecondCountableTopology
attribute [instance] TopologicalManifoldWithBoundary.toIsManifold

instance instChartedSpaceOfTopologicalManifoldWithBoundaryZero (M : Type u)
    [TopologicalSpace M] [h : TopologicalManifoldWithBoundary 0 M] :
    ChartedSpace (ℍ^{0}) M :=
  h.toChartedSpace

instance instChartedSpaceOfTopologicalManifoldWithBoundarySucc (n : ℕ) (M : Type u)
    [TopologicalSpace M] [h : TopologicalManifoldWithBoundary (n + 1) M] :
    ChartedSpace (LeeBoundaryModelSpace (n + 1)) M :=
  h.toChartedSpace

instance instChartedSpaceEuclideanHalfSpaceOfTopologicalManifoldWithBoundarySucc
    (n : ℕ) (M : Type u) [TopologicalSpace M]
    [h : TopologicalManifoldWithBoundary (n + 1) M] :
    ChartedSpace (EuclideanHalfSpace (n + 1)) M := by
  simpa [LeeBoundaryModelSpace] using
    (h.toChartedSpace : ChartedSpace (LeeBoundaryModelSpace (n + 1)) M)

/-- The model upper half-space is itself a topological manifold with boundary. -/
instance instTopologicalManifoldWithBoundaryLeeBoundaryModelSpace (n : ℕ) :
    TopologicalManifoldWithBoundary n (ℍ^{n}) where
  toT2Space := leeBoundaryModelSpaceT2Space n
  toSecondCountableTopology := leeBoundaryModelSpaceSecondCountableTopology n
  toChartedSpace := leeBoundaryModelSpaceChartedSpace n
  toIsManifold := inferInstance
