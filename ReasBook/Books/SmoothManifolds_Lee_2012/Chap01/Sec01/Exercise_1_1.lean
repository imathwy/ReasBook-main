import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Basic
import SmoothManifolds_Lee_2012.Chap01.Sec01.Definition_1_extra_1
import SmoothManifolds_Lee_2012.Chap01.Sec01.Definition_1_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open ChartedSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M]

/-- A space has coordinate-ball charts if every point belongs to the source of some chart whose
target is an open Euclidean ball. -/
def HasCoordinateBallCharts (n : ℕ) (M : Type u) [TopologicalSpace M] : Prop :=
  ∀ p : M, ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
    p ∈ e.source ∧ e.IsCoordinateBall

/-- A space has Euclidean-target charts if every point belongs to the source of some chart whose
target is all of `ℝ^n`. -/
def HasEuclideanTargetCharts (n : ℕ) (M : Type u) [TopologicalSpace M] : Prop :=
  ∀ p : M, ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
    p ∈ e.source ∧ e.target = Set.univ

namespace HasCoordinateBallCharts

@[implicit_reducible] private noncomputable def toChartedSpace
    (h : HasCoordinateBallCharts n M) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) M where
  atlas := Set.range fun p : M ↦ Classical.choose (h p)
  chartAt := fun p ↦ Classical.choose (h p)
  mem_chart_source := fun p ↦ (Classical.choose_spec (h p)).1
  chart_mem_atlas := fun p ↦ ⟨p, rfl⟩

@[reducible] private noncomputable def toTopologicalManifold
    [T2Space M] [SecondCountableTopology M]
    (h : HasCoordinateBallCharts n M) : TopologicalManifold n M :=
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M := h.toChartedSpace
  topologicalManifoldOfChartedSpace n M

private theorem chartAt_isCoordinateBall [T2Space M] [SecondCountableTopology M]
    (h : HasCoordinateBallCharts n M) (p : M) :
    let _ : TopologicalManifold n M := h.toTopologicalManifold
    (chartAt (EuclideanSpace ℝ (Fin n)) p).IsCoordinateBall := by
  -- The induced manifold structure uses the chart chosen by `h p` as its preferred chart.
  simpa [HasCoordinateBallCharts.toTopologicalManifold, HasCoordinateBallCharts.toChartedSpace,
    topologicalManifoldOfChartedSpace] using (Classical.choose_spec (h p)).2

/-- On a Hausdorff second-countable space, coordinate-ball charts yield some topological-manifold
structure whose preferred charts are coordinate-ball charts. -/
theorem exists_topologicalManifold [T2Space M] [SecondCountableTopology M]
    (h : HasCoordinateBallCharts n M) :
    ∃ tm : TopologicalManifold n M,
      let _ : TopologicalManifold n M := tm
      ∀ p : M, (chartAt (EuclideanSpace ℝ (Fin n)) p).IsCoordinateBall := by
  -- Take the charted-space/manifold structure assembled from the chosen coordinate-ball charts.
  refine ⟨h.toTopologicalManifold, ?_⟩
  -- The preferred chart at `p` is definitionally the chosen witness from `h p`.
  simpa using fun p : M ↦ h.chartAt_isCoordinateBall p

end HasCoordinateBallCharts

namespace HasEuclideanTargetCharts

@[implicit_reducible] private noncomputable def toChartedSpace
    (h : HasEuclideanTargetCharts n M) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) M where
  atlas := Set.range fun p : M ↦ Classical.choose (h p)
  chartAt := fun p ↦ Classical.choose (h p)
  mem_chart_source := fun p ↦ (Classical.choose_spec (h p)).1
  chart_mem_atlas := fun p ↦ ⟨p, rfl⟩

@[reducible] private noncomputable def toTopologicalManifold
    [T2Space M] [SecondCountableTopology M]
    (h : HasEuclideanTargetCharts n M) : TopologicalManifold n M :=
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M := h.toChartedSpace
  topologicalManifoldOfChartedSpace n M

private theorem chartAt_target_eq_univ [T2Space M] [SecondCountableTopology M]
    (h : HasEuclideanTargetCharts n M) (p : M) :
    let _ : TopologicalManifold n M := h.toTopologicalManifold
    (chartAt (EuclideanSpace ℝ (Fin n)) p).target = Set.univ := by
  -- The induced manifold structure again uses the chosen local witness as `chartAt`.
  simpa [HasEuclideanTargetCharts.toTopologicalManifold, HasEuclideanTargetCharts.toChartedSpace,
    topologicalManifoldOfChartedSpace] using (Classical.choose_spec (h p)).2

/-- On a Hausdorff second-countable space, Euclidean-target charts yield some topological-manifold
structure whose preferred charts have target all of `ℝ^n`. -/
theorem exists_topologicalManifold [T2Space M] [SecondCountableTopology M]
    (h : HasEuclideanTargetCharts n M) :
    ∃ tm : TopologicalManifold n M,
      let _ : TopologicalManifold n M := tm
      ∀ p : M, (chartAt (EuclideanSpace ℝ (Fin n)) p).target = Set.univ := by
  -- Use the manifold structure built from the chosen Euclidean-target charts.
  refine ⟨h.toTopologicalManifold, ?_⟩
  -- The preferred chart is the chart chosen by `h p`, so its target is `univ`.
  simpa using fun p : M ↦ h.chartAt_target_eq_univ p

end HasEuclideanTargetCharts

/-- Helper for Exercise 1.1: restricting a chart to a smaller open ball in its target keeps the
chosen point in the source and makes the new target exactly that ball. -/
private theorem chart_restrict_target_to_ball
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) {p : M} {r : ℝ}
    (hp : p ∈ e.source) (hr : 0 < r) (hball : Metric.ball (e p) r ⊆ e.target) :
    ∃ e' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      p ∈ e'.source ∧ e'.target = Metric.ball (e p) r := by
  let e' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    e.trans (OpenPartialHomeomorph.ofSet (Metric.ball (e p) r) Metric.isOpen_ball)
  -- The chosen point stays in the source because its image lies in the smaller ball.
  have hp_source : p ∈ e'.source := by
    simp [e', hp, hr]
  -- The new target is the chosen ball since that ball was contained in the old target.
  have htarget : e'.target = Metric.ball (e p) r := by
    ext y
    simp [e', Set.inter_eq_left.mpr hball]
  exact ⟨e', hp_source, htarget⟩

-- Proof sketch: compose a ball-target chart with the inverse of the standard chart
-- `OpenPartialHomeomorph.univBall` from `ℝ^n` onto that ball.
/-- Helper for Exercise 1.1: a chart whose target is a Euclidean ball can be straightened to one
whose target is all of `ℝ^n`. -/
private theorem chart_straighten_ball_target
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hr : 0 < r) (hball : e.target = Metric.ball c r) :
    ∃ e' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      e'.source = e.source ∧ e'.target = Set.univ := by
  -- Match the target of `e` with the source of the inverse ball chart.
  have hsource :
      e.target = (OpenPartialHomeomorph.univBall c r).symm.source := by
    simp [OpenPartialHomeomorph.univBall_target, hr, hball]
  let e' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    OpenPartialHomeomorph.trans' e (OpenPartialHomeomorph.univBall c r).symm hsource
  -- Exact composition preserves the original source.
  have hsource_eq : e'.source = e.source := by
    simp [e', OpenPartialHomeomorph.trans']
  -- The inverse ball chart has source equal to the ball and target equal to `univ`.
  have htarget_eq : e'.target = Set.univ := by
    simp [e', OpenPartialHomeomorph.trans', OpenPartialHomeomorph.univBall_source]
  exact ⟨e', hsource_eq, htarget_eq⟩

-- Proof sketch: starting from a topological-manifold chart, shrink its target to a small
-- Euclidean ball around the image of the chosen point.
/-- Exercise 1.1 (1): a topological manifold has coordinate-ball charts. -/
theorem hasCoordinateBallCharts_of_topologicalManifold
    [TopologicalManifold n M] :
    HasCoordinateBallCharts n M := by
  intro p
  let e := chartAt (EuclideanSpace ℝ (Fin n)) p
  -- Start with the preferred manifold chart through `p`.
  have hp : p ∈ e.source := mem_chart_source (EuclideanSpace ℝ (Fin n)) p
  have hep : e p ∈ e.target := e.map_source hp
  -- Shrink the open target around `e p` to an actual metric ball.
  rcases Metric.isOpen_iff.mp e.open_target (e p) hep with ⟨r, hr, hrball⟩
  rcases chart_restrict_target_to_ball e hp hr hrball with ⟨e', hp', htarget⟩
  have hcoord : e'.IsCoordinateBall :=
    OpenPartialHomeomorph.isCoordinateBall_of_target_eq_ball e' (e p) r hr htarget
  exact ⟨e', hp', hcoord⟩

-- Proof sketch: choose preferred coordinate-ball charts, use them to define a charted-space
-- structure, and then apply `topologicalManifoldOfChartedSpace`.
/-- Exercise 1.1 (2): for a Hausdorff second-countable space, coordinate-ball charts are
equivalent to admitting a topological-manifold structure with those charts. -/
theorem hasCoordinateBallCharts_iff_exists_topologicalManifold
    [T2Space M] [SecondCountableTopology M] :
    HasCoordinateBallCharts n M ↔
      ∃ tm : TopologicalManifold n M,
        let _ : TopologicalManifold n M := tm
        ∀ p : M, (chartAt (EuclideanSpace ℝ (Fin n)) p).IsCoordinateBall :=
  by
  constructor
  · -- Preferred coordinate-ball charts build a manifold structure.
    intro h
    exact h.exists_topologicalManifold
  · rintro ⟨tm, htm⟩
    let _ : TopologicalManifold n M := tm
    intro p
    -- In the given manifold structure, take the preferred chart at `p`.
    exact ⟨chartAt (EuclideanSpace ℝ (Fin n)) p, mem_chart_source _ p, htm p⟩

-- Proof sketch: compose each coordinate-ball chart with `OpenPartialHomeomorph.univBall` to
-- obtain Euclidean-target charts, and conversely restrict a Euclidean-target chart to a small ball
-- around the image of the chosen point.
/-- Exercise 1.1 (3): for a Hausdorff second-countable space, Euclidean-target charts are
equivalent to admitting a topological-manifold structure with those charts. -/
theorem hasEuclideanTargetCharts_iff_exists_topologicalManifold
    [T2Space M] [SecondCountableTopology M] :
    HasEuclideanTargetCharts n M ↔
      ∃ tm : TopologicalManifold n M,
        let _ : TopologicalManifold n M := tm
        ∀ p : M, (chartAt (EuclideanSpace ℝ (Fin n)) p).target = Set.univ :=
  by
  constructor
  · -- Preferred Euclidean-target charts also build a manifold structure.
    intro h
    exact h.exists_topologicalManifold
  · rintro ⟨tm, htm⟩
    let _ : TopologicalManifold n M := tm
    intro p
    -- Use the preferred chart supplied by the given manifold structure.
    exact ⟨chartAt (EuclideanSpace ℝ (Fin n)) p, mem_chart_source _ p, htm p⟩

/-- Exercise 1.1 (4): coordinate-ball charts and Euclidean-target charts are equivalent local
formulations. -/
theorem hasCoordinateBallCharts_iff_hasEuclideanTargetCharts :
    HasCoordinateBallCharts n M ↔ HasEuclideanTargetCharts n M := by
  constructor
  · intro h p
    rcases h p with ⟨e, hp, ⟨c, r, hr, hball⟩⟩
    -- Straighten the chosen ball-target chart to one whose target is all of `ℝ^n`.
    rcases chart_straighten_ball_target e hr hball with ⟨e', hsource, htarget⟩
    have hp' : p ∈ e'.source := by
      rw [hsource]
      exact hp
    exact ⟨e', hp', htarget⟩
  · intro h p
    rcases h p with ⟨e, hp, htarget⟩
    -- Restrict a Euclidean-target chart to the unit ball around `e p`.
    have hsubset : Metric.ball (e p) 1 ⊆ e.target := by
      simp [htarget]
    rcases chart_restrict_target_to_ball e hp zero_lt_one hsubset with ⟨e', hp', hball⟩
    have hcoord : e'.IsCoordinateBall :=
      OpenPartialHomeomorph.isCoordinateBall_of_target_eq_ball e' (e p) 1 zero_lt_one hball
    exact ⟨e', hp', hcoord⟩

end
