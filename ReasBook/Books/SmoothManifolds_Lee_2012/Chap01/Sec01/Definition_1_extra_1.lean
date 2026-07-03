import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Manifold

/-- Definition 1-extra-1: A topological manifold of dimension `n` is a topological space that is
Hausdorff, second-countable, and equipped with charts to open subsets of `ℝ^n`. -/
class TopologicalManifold (n : ℕ) (M : Type u) [TopologicalSpace M] extends T2Space M,
    SecondCountableTopology M, ChartedSpace (EuclideanSpace ℝ (Fin n)) M

/-- A Hausdorff second-countable charted space modelled on `ℝ^n` carries the chapter's canonical
topological-manifold structure. -/
@[reducible] def topologicalManifoldOfChartedSpace (n : ℕ) (M : Type u) [TopologicalSpace M]
    [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    TopologicalManifold n M where
  toT2Space := inferInstance
  toSecondCountableTopology := inferInstance
  toChartedSpace := inferInstance

/-- Euclidean space is a topological manifold of its own dimension. -/
instance euclideanSpace_topologicalManifold (n : ℕ) :
    TopologicalManifold n (EuclideanSpace ℝ (Fin n)) :=
  topologicalManifoldOfChartedSpace n (EuclideanSpace ℝ (Fin n))

noncomputable section

namespace TopologicalManifold

open ChartedSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [TopologicalManifold n M]

/-- A homeomorphism transports a topological manifold structure across the source. -/
@[reducible] noncomputable def of_homeomorph (n : ℕ) {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalManifold n N]
    (h : M ≃ₜ N) : TopologicalManifold n M := by
  let _ : T2Space M := h.symm.t2Space
  let _ : SecondCountableTopology M := h.secondCountableTopology
  let hs := h.symm.isLocalHomeomorph
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M :=
    hs.chartedSpace h.symm.surjective
  exact topologicalManifoldOfChartedSpace n M

theorem locallyCompactSpace_of_topologicalManifold (n : ℕ) (M : Type u) [TopologicalSpace M]
    [TopologicalManifold n M] : LocallyCompactSpace M := by
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  infer_instance

-- Proof sketch: use the preferred chart at `p`; by definition its source contains `p`.
/-- A topological manifold has, at each point, a chart to `ℝ^n`, i.e. an open partial
homeomorphism whose source contains that point. -/
theorem exists_open_homeomorph (p : M) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)), p ∈ e.source :=
  ⟨chartAt (EuclideanSpace ℝ (Fin n)) p, mem_chart_source _ p⟩

/-- A nonempty space cannot carry topological manifold structures of two different dimensions. -/
theorem dimension_eq (n m : ℕ) (M : Type u) [TopologicalSpace M] [Nonempty M]
    [TopologicalManifold n M] [TopologicalManifold m M] :
    m = n := sorry

/-- Homeomorphic nonempty topological manifolds have the same dimension. -/
theorem dimension_eq_of_homeomorph (n m : ℕ) (M : Type u) (N : Type v)
    [TopologicalSpace M] [Nonempty M] [TopologicalManifold n M]
    [TopologicalSpace N] [TopologicalManifold m N] (h : M ≃ₜ N) :
    m = n := by
  letI : TopologicalManifold m M := of_homeomorph m h
  simpa using dimension_eq n m M

end TopologicalManifold

namespace TopologicalSpace.Opens

open ChartedSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [TopologicalManifold n M] (U : Opens M)

/-- An open subset of a topological manifold is canonically a topological manifold of the same
dimension. -/
noncomputable instance topologicalManifold : TopologicalManifold n U :=
  topologicalManifoldOfChartedSpace n U

end TopologicalSpace.Opens

end
