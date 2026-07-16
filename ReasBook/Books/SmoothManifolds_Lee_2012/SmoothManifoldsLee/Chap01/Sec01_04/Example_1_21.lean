import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01.Definition_1_extra_1

open scoped Manifold ContDiff
open ChartedSpace

universe u

variable {M : Type u} [TopologicalSpace M]

-- Proof sketch: a `0`-dimensional chart has target an open subset of `ℝ^0`, hence a singleton,
-- so every point is open and the space is discrete; second countability of the manifold then
-- forces the underlying discrete space to be countable.
/-- A `0`-dimensional topological manifold has the discrete topology. -/
instance topologicalManifold_zero_discreteTopology [TopologicalManifold 0 M] :
    DiscreteTopology M := by
  refine ⟨eq_bot_of_singletons_open fun p ↦ ?_⟩
  let e := chartAt (EuclideanSpace ℝ (Fin 0)) p
  have hsource : Set.Subsingleton e.source := by
    have hsub : Subsingleton e.source := by
      let h := e.toHomeomorphSourceTarget.toEquiv
      let _ : Subsingleton e.target := inferInstance
      exact h.subsingleton
    intro x hx y hy
    exact congrArg Subtype.val (show (⟨x, hx⟩ : e.source) = ⟨y, hy⟩ from Subsingleton.elim _ _)
  have hsource_eq : e.source = {p} :=
    hsource.eq_singleton_of_mem (mem_chart_source _ p)
  simpa [e, hsource_eq] using e.open_source

/-- A `0`-dimensional topological manifold is countable. -/
theorem topologicalManifold_zero_countable [TopologicalManifold 0 M] : Countable M :=
  countable_of_Lindelof_of_discrete

/-- Example 1.21: a `0`-dimensional topological manifold is a countable discrete space. -/
theorem topologicalManifold_zero_countable_and_discrete [TopologicalManifold 0 M] :
    Countable M ∧ DiscreteTopology M :=
  ⟨topologicalManifold_zero_countable, inferInstance⟩

/-- A countable discrete space carries the natural `0`-dimensional topological manifold
structure. -/
instance countable_discrete_topologicalManifold_zero [Countable M] [DiscreteTopology M] :
    TopologicalManifold 0 M where
  toT2Space := inferInstance
  toSecondCountableTopology := inferInstance
  toChartedSpace :=
    ChartedSpace.of_discreteTopology

-- Proof sketch: every chart target in dimension `0` is a subsingleton, so each transition map is
-- automatically smooth on its source.
/-- Every `0`-dimensional topological manifold carries the canonical smooth structure modeled on
`ℝ^0`. -/
theorem topologicalManifold_zero_isManifold [TopologicalManifold 0 M] :
    IsManifold (𝓡 0) ∞ M := by
  apply isManifold_of_contDiffOn
  intro e e' _ _
  exact contDiff_of_subsingleton.contDiffOn
