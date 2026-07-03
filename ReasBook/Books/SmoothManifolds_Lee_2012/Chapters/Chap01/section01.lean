import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_extra_1 (from Chap01/Sec01) -/
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

/-! ### Exercise_1_1 (from Chap01/Sec01) -/
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

/-! ### Problem_1_1 (from Chap01/Sec01_07) -/
/-- The subset `X ⊆ ℝ²` consisting of the two horizontal lines `y = 1` and `y = -1`. -/
def problem1LineWithTwoOriginsPoints : Set (ℝ × ℝ) :=
  { p | p.2 = 1 ∨ p.2 = -1 }

/-- The point space `X` before taking the quotient in the line-with-two-origins construction. -/
abbrev problem1LineWithTwoOriginsPoint : Type :=
  ↥problem1LineWithTwoOriginsPoints

/-- The upper point `(0, 1)` in the two-line model `X`. -/
def problem1LineWithTwoOriginsUpperPoint : problem1LineWithTwoOriginsPoint :=
  ⟨(0, 1), Or.inl rfl⟩

/-- The lower point `(0, -1)` in the two-line model `X`. -/
def problem1LineWithTwoOriginsLowerPoint : problem1LineWithTwoOriginsPoint :=
  ⟨(0, -1), Or.inr rfl⟩

/-- Two points of `X` are equivalent when they have the same `x`-coordinate, and the
`y`-coordinate is remembered only over `x = 0`. This is the quotient relation that identifies
`(x, -1)` with `(x, 1)` for every nonzero `x`. -/
def problem1LineWithTwoOriginsRel (p q : problem1LineWithTwoOriginsPoint) : Prop :=
  p.1.1 = q.1.1 ∧ (p.1.1 ≠ 0 ∨ p.1.2 = q.1.2)

/- The next three lemmas provide the equivalence-relation axioms for the quotient relation. -/

/-- The line-with-two-origins relation is reflexive. -/
-- Proof sketch: the `x`-coordinates agree by reflexivity, and the `y`-coordinates agree
-- tautologically.
theorem problem1LineWithTwoOriginsRel_refl (p : problem1LineWithTwoOriginsPoint) :
    problem1LineWithTwoOriginsRel p p := by
  -- Both coordinates agree with themselves, so the remembered `y`-coordinate matches trivially.
  exact ⟨rfl, Or.inr rfl⟩

/-- The line-with-two-origins relation is symmetric. -/
-- Proof sketch: symmetry preserves equality of `x`-coordinates, and the second clause is symmetric
-- because either the common `x`-coordinate is nonzero or the `y`-coordinates are equal.
theorem problem1LineWithTwoOriginsRel_symm {p q : problem1LineWithTwoOriginsPoint}
    (hpq : problem1LineWithTwoOriginsRel p q) : problem1LineWithTwoOriginsRel q p := by
  rcases hpq with ⟨hxy, hbranch⟩
  -- Reversing the pair keeps the common `x`-coordinate and flips the `y`-equality.
  refine ⟨hxy.symm, ?_⟩
  rcases hbranch with hx | hy
  · exact Or.inl fun hq => hx (hxy.trans hq)
  · exact Or.inr hy.symm

/-- The line-with-two-origins relation is transitive. -/
-- Proof sketch: equality of `x`-coordinates is transitive. If the common `x`-coordinate is
-- nonzero, the second clause is automatic; if it is `0`, the intermediate equalities of
-- `y`-coordinates force the endpoints to have the same `y`-coordinate.
theorem problem1LineWithTwoOriginsRel_trans {p q r : problem1LineWithTwoOriginsPoint}
    (hpq : problem1LineWithTwoOriginsRel p q) (hqr : problem1LineWithTwoOriginsRel q r) :
    problem1LineWithTwoOriginsRel p r := by
  rcases hpq with ⟨hpq_x, hpq_branch⟩
  rcases hqr with ⟨hqr_x, hqr_branch⟩
  -- The `x`-coordinate is the global invariant carried through the quotient.
  refine ⟨hpq_x.trans hqr_x, ?_⟩
  by_cases hx : p.1.1 = 0
  · -- Over `x = 0`, both relation hypotheses must come from equal `y`-coordinates.
    right
    have hq0 : q.1.1 = 0 := by exact hpq_x ▸ hx
    have hr0 : r.1.1 = 0 := by exact hqr_x ▸ hq0
    have hpq_y : p.1.2 = q.1.2 := by
      rcases hpq_branch with hp0 | hy
      · exact False.elim (hp0 hx)
      · exact hy
    have hqr_y : q.1.2 = r.1.2 := by
      rcases hqr_branch with hq0' | hy
      · exact False.elim (hq0' hq0)
      · exact hy
    exact hpq_y.trans hqr_y
  · -- Away from `x = 0`, the quotient forgets the `y`-coordinate entirely.
    exact Or.inl hx

/-- The setoid on `X` defining Lee's line with two origins. -/
def problem1LineWithTwoOriginsSetoid : Setoid problem1LineWithTwoOriginsPoint where
  r := problem1LineWithTwoOriginsRel
  iseqv :=
    ⟨problem1LineWithTwoOriginsRel_refl, problem1LineWithTwoOriginsRel_symm,
      problem1LineWithTwoOriginsRel_trans⟩

/-- Helper for Problem 1-1: expose the quotient relation as the ambient setoid on `X`. -/
instance : Setoid problem1LineWithTwoOriginsPoint :=
  problem1LineWithTwoOriginsSetoid

/-- The quotient space `M` obtained from the two horizontal lines by identifying the points with
the same nonzero `x`-coordinate. -/
abbrev problem1LineWithTwoOrigins : Type :=
  Quotient problem1LineWithTwoOriginsSetoid

/-- The upper origin of the line with two origins. -/
def problem1LineWithTwoOriginsUpperOrigin : problem1LineWithTwoOrigins :=
  ⟦problem1LineWithTwoOriginsUpperPoint⟧

/-- The lower origin of the line with two origins. -/
def problem1LineWithTwoOriginsLowerOrigin : problem1LineWithTwoOrigins :=
  ⟦problem1LineWithTwoOriginsLowerPoint⟧

/-- Helper for Problem 1-1: the quotient remembers only the `x`-coordinate of a class. -/
def problem1LineWithTwoOriginsXCoord : problem1LineWithTwoOrigins → ℝ :=
  Quotient.lift (fun p => p.1.1) fun _ _ h => h.1

/-- Helper for Problem 1-1: the upper branch parametrizes the quotient by classes of `(x, 1)`. -/
def problem1LineWithTwoOriginsUpperBranch (x : ℝ) : problem1LineWithTwoOrigins :=
  ⟦⟨(x, 1), Or.inl rfl⟩⟧

/-- Helper for Problem 1-1: the lower branch parametrizes the quotient by classes of `(x, -1)`. -/
def problem1LineWithTwoOriginsLowerBranch (x : ℝ) : problem1LineWithTwoOrigins :=
  ⟦⟨(x, -1), Or.inr rfl⟩⟧

/-- Helper for Problem 1-1: the quotient `x`-coordinate of the upper branch is the parameter. -/
lemma problem1LineWithTwoOrigins_xCoord_upper_branch (x : ℝ) :
    problem1LineWithTwoOriginsXCoord (problem1LineWithTwoOriginsUpperBranch x) = x := by
  rfl

/-- Helper for Problem 1-1: the quotient `x`-coordinate of the lower branch is the parameter. -/
lemma problem1LineWithTwoOrigins_xCoord_lower_branch (x : ℝ) :
    problem1LineWithTwoOriginsXCoord (problem1LineWithTwoOriginsLowerBranch x) = x := by
  rfl

/-- Helper for Problem 1-1: the two branches are identified away from `x = 0`. -/
lemma problem1LineWithTwoOrigins_upper_eq_lower_branch {x : ℝ} (hx : x ≠ 0) :
    problem1LineWithTwoOriginsUpperBranch x = problem1LineWithTwoOriginsLowerBranch x := by
  -- The quotient relation identifies the two points with the same nonzero `x`-coordinate.
  exact Quotient.sound ⟨rfl, Or.inl hx⟩

/-- Helper for Problem 1-1: the two origins represent distinct quotient classes. -/
lemma problem1LineWithTwoOriginsUpperOrigin_ne_lowerOrigin :
    problem1LineWithTwoOriginsUpperOrigin ≠ problem1LineWithTwoOriginsLowerOrigin := by
  intro h
  -- If the origins were equal, the quotient relation would force `1 = -1`.
  have hrel :
      problem1LineWithTwoOriginsRel problem1LineWithTwoOriginsUpperPoint
        problem1LineWithTwoOriginsLowerPoint :=
    Quotient.exact h
  rcases hrel with ⟨_, hbranch⟩
  rcases hbranch with hzero | hy
  · exact hzero rfl
  · have hy' : (1 : ℝ) = -1 := by
        simpa [problem1LineWithTwoOriginsUpperPoint, problem1LineWithTwoOriginsLowerPoint] using hy
    norm_num at hy'

/-- Helper for Problem 1-1: every upper-branch point avoids the lower origin. -/
lemma problem1LineWithTwoOrigins_upper_branch_ne_lower_origin (x : ℝ) :
    problem1LineWithTwoOriginsUpperBranch x ≠ problem1LineWithTwoOriginsLowerOrigin := by
  intro h
  -- Equality with the lower origin would force the representative `(x, 1)` to have `y = -1`.
  have hrel :
      problem1LineWithTwoOriginsRel ⟨(x, 1), Or.inl rfl⟩ problem1LineWithTwoOriginsLowerPoint :=
    Quotient.exact h
  rcases hrel with ⟨hx, hbranch⟩
  rcases hbranch with hne | hy
  · exact hne hx
  · have hy' : (1 : ℝ) = -1 := by
        simpa [problem1LineWithTwoOriginsLowerPoint] using hy
    norm_num at hy'

/-- Helper for Problem 1-1: every lower-branch point avoids the upper origin. -/
lemma problem1LineWithTwoOrigins_lower_branch_ne_upper_origin (x : ℝ) :
    problem1LineWithTwoOriginsLowerBranch x ≠ problem1LineWithTwoOriginsUpperOrigin := by
  intro h
  -- Equality with the upper origin would force the representative `(x, -1)` to have `y = 1`.
  have hrel :
      problem1LineWithTwoOriginsRel ⟨(x, -1), Or.inr rfl⟩ problem1LineWithTwoOriginsUpperPoint :=
    Quotient.exact h
  rcases hrel with ⟨hx, hbranch⟩
  rcases hbranch with hne | hy
  · exact hne hx
  · have hy' : (-1 : ℝ) = 1 := by
        simpa [problem1LineWithTwoOriginsUpperPoint] using hy
    norm_num at hy'

/-- Helper for Problem 1-1: a class different from the lower origin is represented on the upper
branch by its common `x`-coordinate. -/
lemma problem1LineWithTwoOrigins_upper_branch_eq_of_ne_lower_origin
    (p : problem1LineWithTwoOriginsPoint)
    (hp : ⟦p⟧ ≠ problem1LineWithTwoOriginsLowerOrigin) :
    problem1LineWithTwoOriginsUpperBranch p.1.1 = ⟦p⟧ := by
  rcases p.2 with hp_y | hp_y
  · -- On the upper branch the representative already has the desired form.
    exact Quotient.sound ⟨rfl, Or.inr hp_y.symm⟩
  · -- On the lower branch, being different from the lower origin forces `x ≠ 0`.
    have hx : p.1.1 ≠ 0 := by
      intro hx0
      apply hp
      exact Quotient.sound ⟨hx0, Or.inr hp_y⟩
    calc
      problem1LineWithTwoOriginsUpperBranch p.1.1 =
          problem1LineWithTwoOriginsLowerBranch p.1.1 :=
        problem1LineWithTwoOrigins_upper_eq_lower_branch hx
      _ = ⟦p⟧ := by
        exact Quotient.sound ⟨rfl, Or.inr hp_y.symm⟩

/-- Helper for Problem 1-1: a class different from the upper origin is represented on the lower
branch by its common `x`-coordinate. -/
lemma problem1LineWithTwoOrigins_lower_branch_eq_of_ne_upper_origin
    (p : problem1LineWithTwoOriginsPoint)
    (hp : ⟦p⟧ ≠ problem1LineWithTwoOriginsUpperOrigin) :
    problem1LineWithTwoOriginsLowerBranch p.1.1 = ⟦p⟧ := by
  rcases p.2 with hp_y | hp_y
  · -- On the upper branch, being different from the upper origin forces `x ≠ 0`.
    have hx : p.1.1 ≠ 0 := by
      intro hx0
      apply hp
      exact Quotient.sound ⟨hx0, Or.inr hp_y⟩
    calc
      problem1LineWithTwoOriginsLowerBranch p.1.1 =
          problem1LineWithTwoOriginsUpperBranch p.1.1 := by
        symm
        exact problem1LineWithTwoOrigins_upper_eq_lower_branch hx
      _ = ⟦p⟧ := by
        exact Quotient.sound ⟨rfl, Or.inr hp_y.symm⟩
  · -- On the lower branch the representative already has the desired form.
    exact Quotient.sound ⟨rfl, Or.inr hp_y.symm⟩

/-- Helper for Problem 1-1: the upper branch recovers every class except the lower origin. -/
lemma problem1LineWithTwoOrigins_upper_branch_xCoord
    {q : problem1LineWithTwoOrigins} (hq : q ≠ problem1LineWithTwoOriginsLowerOrigin) :
    problem1LineWithTwoOriginsUpperBranch (problem1LineWithTwoOriginsXCoord q) = q := by
  -- Prove the statement by quotient induction, carrying the non-lower-origin hypothesis along.
  refine Quotient.inductionOn q ?_ hq
  intro p hp
  simpa [problem1LineWithTwoOriginsXCoord] using
    problem1LineWithTwoOrigins_upper_branch_eq_of_ne_lower_origin p hp

/-- Helper for Problem 1-1: the lower branch recovers every class except the upper origin. -/
lemma problem1LineWithTwoOrigins_lower_branch_xCoord
    {q : problem1LineWithTwoOrigins} (hq : q ≠ problem1LineWithTwoOriginsUpperOrigin) :
    problem1LineWithTwoOriginsLowerBranch (problem1LineWithTwoOriginsXCoord q) = q := by
  -- Prove the statement by quotient induction, carrying the non-upper-origin hypothesis along.
  refine Quotient.inductionOn q ?_ hq
  intro p hp
  simpa [problem1LineWithTwoOriginsXCoord] using
    problem1LineWithTwoOrigins_lower_branch_eq_of_ne_upper_origin p hp

/-- Helper for Problem 1-1: the quotient coordinate descends continuously to the quotient. -/
lemma problem1LineWithTwoOrigins_continuous_xCoord :
    Continuous problem1LineWithTwoOriginsXCoord := by
  -- The prequotient coordinate map is continuous and constant on equivalence classes.
  have hf : Continuous (fun p : problem1LineWithTwoOriginsPoint => p.1.1) := by
    simpa using (continuous_fst.comp continuous_subtype_val)
  simpa [problem1LineWithTwoOriginsXCoord] using
    (Continuous.quotient_liftOn' (s := problem1LineWithTwoOriginsSetoid)
      (f := fun p : problem1LineWithTwoOriginsPoint => p.1.1) hf fun _ _ h => h.1)

/-- Helper for Problem 1-1: the upper branch is a continuous map into the quotient. -/
lemma problem1LineWithTwoOrigins_continuous_upper_branch :
    Continuous problem1LineWithTwoOriginsUpperBranch := by
  -- The upper branch is the quotient projection composed with the continuous inclusion
  -- `x ↦ (x, 1)`.
  have hinc :
      Continuous
        (fun x : ℝ => (⟨((x, 1) : ℝ × ℝ), Or.inl rfl⟩ : problem1LineWithTwoOriginsPoint)) := by
    exact
      (show Continuous fun x : ℝ => ((x, (1 : ℝ)) : ℝ × ℝ) by continuity).subtype_mk
        fun _ => Or.inl rfl
  simpa [problem1LineWithTwoOriginsUpperBranch] using continuous_quotient_mk'.comp hinc

/-- Helper for Problem 1-1: the lower branch is a continuous map into the quotient. -/
lemma problem1LineWithTwoOrigins_continuous_lower_branch :
    Continuous problem1LineWithTwoOriginsLowerBranch := by
  -- The lower branch is the quotient projection composed with the continuous inclusion
  -- `x ↦ (x, -1)`.
  have hinc :
      Continuous
        (fun x : ℝ => (⟨((x, -1) : ℝ × ℝ), Or.inr rfl⟩ : problem1LineWithTwoOriginsPoint)) := by
    exact
      (show Continuous fun x : ℝ => ((x, (-1 : ℝ)) : ℝ × ℝ) by continuity).subtype_mk
        fun _ => Or.inr rfl
  simpa [problem1LineWithTwoOriginsLowerBranch] using continuous_quotient_mk'.comp hinc

/-- Helper for Problem 1-1: the quotient preimage of the upper chart domain is an elementary
open subset of the two-line model. -/
lemma problem1LineWithTwoOrigins_preimage_upper_chart_domain :
    (Quotient.mk' : problem1LineWithTwoOriginsPoint → problem1LineWithTwoOrigins) ⁻¹'
        {q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsLowerOrigin} =
      {p : problem1LineWithTwoOriginsPoint | 0 < p.1.2 ∨ p.1.1 ≠ 0} := by
  ext p
  rcases p.2 with hp_y | hp_y
  · -- Points on the upper branch never map to the lower origin.
    constructor
    · intro _
      left
      simp [hp_y]
    · intro _ hq
      apply problem1LineWithTwoOrigins_upper_branch_ne_lower_origin p.1.1
      have hp_eq : problem1LineWithTwoOriginsUpperBranch p.1.1 = ⟦p⟧ := by
        exact Quotient.sound ⟨rfl, Or.inr hp_y.symm⟩
      exact hp_eq.trans hq
  · -- Points on the lower branch avoid the lower origin exactly when `x ≠ 0`.
    constructor
    · intro hp
      right
      intro hx
      apply hp
      exact Quotient.sound ⟨hx, Or.inr hp_y⟩
    · intro hp
      rcases hp with hp_pos | hx
      · linarith [hp_y]
      · intro hq
        have hrel :
            problem1LineWithTwoOriginsRel p problem1LineWithTwoOriginsLowerPoint :=
          Quotient.exact hq
        exact hx hrel.1

/-- Helper for Problem 1-1: the quotient preimage of the lower chart domain is an elementary
open subset of the two-line model. -/
lemma problem1LineWithTwoOrigins_preimage_lower_chart_domain :
    (Quotient.mk' : problem1LineWithTwoOriginsPoint → problem1LineWithTwoOrigins) ⁻¹'
        {q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsUpperOrigin} =
      {p : problem1LineWithTwoOriginsPoint | p.1.2 < 0 ∨ p.1.1 ≠ 0} := by
  ext p
  rcases p.2 with hp_y | hp_y
  · -- Points on the upper branch avoid the upper origin exactly when `x ≠ 0`.
    constructor
    · intro hp
      right
      intro hx
      apply hp
      exact Quotient.sound ⟨hx, Or.inr hp_y⟩
    · intro hp
      rcases hp with hp_neg | hx
      · linarith [hp_y]
      · intro hq
        have hrel :
            problem1LineWithTwoOriginsRel p problem1LineWithTwoOriginsUpperPoint :=
          Quotient.exact hq
        exact hx hrel.1
  · -- Points on the lower branch never map to the upper origin.
    constructor
    · intro _
      left
      simp [hp_y]
    · intro _ hq
      apply problem1LineWithTwoOrigins_lower_branch_ne_upper_origin p.1.1
      have hp_eq : problem1LineWithTwoOriginsLowerBranch p.1.1 = ⟦p⟧ := by
        exact Quotient.sound ⟨rfl, Or.inr hp_y.symm⟩
      exact hp_eq.trans hq

/-- Helper for Problem 1-1: the complement of the lower origin is open. -/
lemma problem1LineWithTwoOrigins_upper_chart_domain_isOpen :
    IsOpen {q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsLowerOrigin} := by
  -- Route correction: prove openness through the quotient preimage, where the set becomes a
  -- simple union of open branch conditions.
  change
    IsOpen
      ((Quotient.mk' : problem1LineWithTwoOriginsPoint → problem1LineWithTwoOrigins) ⁻¹'
        {q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsLowerOrigin})
  rw [problem1LineWithTwoOrigins_preimage_upper_chart_domain]
  have hy :
      IsOpen {p : problem1LineWithTwoOriginsPoint | 0 < p.1.2} := by
    simpa using
      isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val)
  have hx :
      IsOpen {p : problem1LineWithTwoOriginsPoint | p.1.1 ≠ 0} := by
    simpa using isOpen_ne.preimage (continuous_fst.comp continuous_subtype_val)
  exact hy.union hx

/-- Helper for Problem 1-1: the complement of the upper origin is open. -/
lemma problem1LineWithTwoOrigins_lower_chart_domain_isOpen :
    IsOpen {q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsUpperOrigin} := by
  -- Route correction: as above, the quotient preimage is a union of open half-branch conditions.
  change
    IsOpen
      ((Quotient.mk' : problem1LineWithTwoOriginsPoint → problem1LineWithTwoOrigins) ⁻¹'
        {q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsUpperOrigin})
  rw [problem1LineWithTwoOrigins_preimage_lower_chart_domain]
  have hy :
      IsOpen {p : problem1LineWithTwoOriginsPoint | p.1.2 < 0} := by
    simpa using
      isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const
  have hx :
      IsOpen {p : problem1LineWithTwoOriginsPoint | p.1.1 ≠ 0} := by
    simpa using isOpen_ne.preimage (continuous_fst.comp continuous_subtype_val)
  exact hy.union hx

/-- Helper for Problem 1-1: the complement of the lower origin is globally parameterized by the
upper branch. -/
lemma problem1LineWithTwoOrigins_upper_chart_homeomorph :
    Nonempty ({q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsLowerOrigin} ≃ₜ
      (Set.univ : Set ℝ)) := by
  refine ⟨
    { toFun := fun q => ⟨problem1LineWithTwoOriginsXCoord q.1, by simp⟩
      invFun := fun x =>
        ⟨problem1LineWithTwoOriginsUpperBranch x.1,
          problem1LineWithTwoOrigins_upper_branch_ne_lower_origin x.1⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }⟩
  · intro q
    -- Every class in the upper chart is recovered by following its `x`-coordinate back up
    -- the upper branch.
    apply Subtype.ext
    exact problem1LineWithTwoOrigins_upper_branch_xCoord q.2
  · intro x
    -- On the upper branch the quotient coordinate is visibly the original parameter.
    apply Subtype.ext
    simp [problem1LineWithTwoOrigins_xCoord_upper_branch]
  · -- Continuity of the chart map is continuity of `xCoord`, with a trivial subtype target.
    exact
      (problem1LineWithTwoOrigins_continuous_xCoord.comp continuous_subtype_val).subtype_mk
        fun _ => by simp
  · -- Continuity of the inverse is continuity of the upper branch, again with a trivial subtype
    -- target.
    exact
      (problem1LineWithTwoOrigins_continuous_upper_branch.comp continuous_subtype_val).subtype_mk
        fun x => problem1LineWithTwoOrigins_upper_branch_ne_lower_origin x.1

/-- Helper for Problem 1-1: the complement of the upper origin is globally parameterized by the
lower branch. -/
lemma problem1LineWithTwoOrigins_lower_chart_homeomorph :
    Nonempty ({q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsUpperOrigin} ≃ₜ
      (Set.univ : Set ℝ)) := by
  refine ⟨
    { toFun := fun q => ⟨problem1LineWithTwoOriginsXCoord q.1, by simp⟩
      invFun := fun x =>
        ⟨problem1LineWithTwoOriginsLowerBranch x.1,
          problem1LineWithTwoOrigins_lower_branch_ne_upper_origin x.1⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }⟩
  · intro q
    -- Every class in the lower chart is recovered by following its `x`-coordinate back down
    -- the lower branch.
    apply Subtype.ext
    exact problem1LineWithTwoOrigins_lower_branch_xCoord q.2
  · intro x
    -- On the lower branch the quotient coordinate is the original parameter.
    apply Subtype.ext
    rfl
  · -- Continuity of the chart map is continuity of `xCoord`, with a trivial subtype target.
    exact
      (problem1LineWithTwoOrigins_continuous_xCoord.comp continuous_subtype_val).subtype_mk
        fun _ => by simp
  · -- Continuity of the inverse is continuity of the lower branch.
    exact
      (problem1LineWithTwoOrigins_continuous_lower_branch.comp continuous_subtype_val).subtype_mk
        fun x => problem1LineWithTwoOrigins_lower_branch_ne_upper_origin x.1

/-- Problem 1-1 (1): every point of the line with two origins has an open neighborhood
homeomorphic to an open subset of `ℝ`, so the quotient is locally Euclidean of dimension `1`. -/
-- Proof sketch: away from the two origins, the quotient map is locally a homeomorphism onto an
-- open interval in one of the two copies of `ℝ`. At either origin, take a small interval around
-- `0` in the chosen branch; its image in the quotient is still homeomorphic to an open interval.
theorem problem1LineWithTwoOrigins_exists_open_homeomorph (x : problem1LineWithTwoOrigins) :
    ∃ (U : Set problem1LineWithTwoOrigins) (hU : IsOpen U) (hx : x ∈ U) (V : Set ℝ)
      (hV : IsOpen V), Nonempty (U ≃ₜ V) := by
  by_cases hx : x = problem1LineWithTwoOriginsLowerOrigin
  · -- At the lower origin, use the lower chart.
    refine ⟨{q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsUpperOrigin},
      problem1LineWithTwoOrigins_lower_chart_domain_isOpen, ?_,
      Set.univ, isOpen_univ, problem1LineWithTwoOrigins_lower_chart_homeomorph⟩
    simpa [hx] using problem1LineWithTwoOriginsUpperOrigin_ne_lowerOrigin.symm
  · -- Every other point lies in the upper chart.
    refine ⟨{q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsLowerOrigin},
      problem1LineWithTwoOrigins_upper_chart_domain_isOpen, hx,
      Set.univ, isOpen_univ, problem1LineWithTwoOrigins_upper_chart_homeomorph⟩

/-- Problem 1-1 (2): the line with two origins is second-countable. -/
-- Proof sketch: the prequotient `X` is a subspace of `ℝ²`, hence second-countable. Show that the
-- quotient map `X → M` is an open quotient map, then transfer second countability to the
-- quotient.
theorem problem1LineWithTwoOrigins_secondCountableTopology :
    SecondCountableTopology problem1LineWithTwoOrigins := by
  -- The quotient is covered by the two open global charts, each homeomorphic to `ℝ`.
  let U : Bool → Set problem1LineWithTwoOrigins := fun b =>
    cond b
      {q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsUpperOrigin}
      {q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsLowerOrigin}
  have hU_sc : ∀ b, SecondCountableTopology (U b) := by
    intro b
    cases b
    · rcases problem1LineWithTwoOrigins_upper_chart_homeomorph with ⟨e⟩
      simpa [U] using e.secondCountableTopology
    · rcases problem1LineWithTwoOrigins_lower_chart_homeomorph with ⟨e⟩
      simpa [U] using e.secondCountableTopology
  letI : ∀ b, SecondCountableTopology (U b) := hU_sc
  have hU_open : ∀ b, IsOpen (U b) := by
    intro b
    cases b
    · simpa [U] using problem1LineWithTwoOrigins_upper_chart_domain_isOpen
    · simpa [U] using problem1LineWithTwoOrigins_lower_chart_domain_isOpen
  have hcover : ⋃ b, U b = Set.univ := by
    ext q
    constructor
    · intro _
      simp
    · intro _
      by_cases hq : q = problem1LineWithTwoOriginsLowerOrigin
      · refine Set.mem_iUnion.2 ?_
        refine ⟨true, ?_⟩
        simpa [U, hq] using problem1LineWithTwoOriginsUpperOrigin_ne_lowerOrigin.symm
      · refine Set.mem_iUnion.2 ?_
        exact ⟨false, hq⟩
  exact TopologicalSpace.secondCountableTopology_of_countable_cover hU_open hcover

/-- Helper for Problem 1-1: any open neighborhoods of the two origins contain a common nonzero
branch parameter, so they meet in the quotient. -/
lemma problem1LineWithTwoOrigins_origins_nhds_inter
    (U V : Set problem1LineWithTwoOrigins) (hU : IsOpen U) (hV : IsOpen V)
    (hUpper : problem1LineWithTwoOriginsUpperOrigin ∈ U)
    (hLower : problem1LineWithTwoOriginsLowerOrigin ∈ V) :
    (U ∩ V).Nonempty := by
  let U' : Set ℝ := problem1LineWithTwoOriginsUpperBranch ⁻¹' U
  let V' : Set ℝ := problem1LineWithTwoOriginsLowerBranch ⁻¹' V
  have hU' : IsOpen U' := by
    simpa [U'] using hU.preimage problem1LineWithTwoOrigins_continuous_upper_branch
  have hV' : IsOpen V' := by
    simpa [V'] using hV.preimage problem1LineWithTwoOrigins_continuous_lower_branch
  have h0U : (0 : ℝ) ∈ U' := by
    simpa [U', problem1LineWithTwoOriginsUpperBranch, problem1LineWithTwoOriginsUpperOrigin]
      using hUpper
  have h0V : (0 : ℝ) ∈ V' := by
    simpa [V', problem1LineWithTwoOriginsLowerBranch, problem1LineWithTwoOriginsLowerOrigin]
      using hLower
  -- Open neighborhoods of `0` contain metric balls around `0`.
  obtain ⟨εU, hεU_pos, hεU⟩ := Metric.mem_nhds_iff.1 (hU'.mem_nhds h0U)
  obtain ⟨εV, hεV_pos, hεV⟩ := Metric.mem_nhds_iff.1 (hV'.mem_nhds h0V)
  let t : ℝ := min εU εV / 2
  have ht_pos : 0 < t := by
    dsimp [t]
    have hmin_pos : 0 < min εU εV := lt_min hεU_pos hεV_pos
    linarith
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have htU : t ∈ U' := by
    apply hεU
    dsimp [t]
    have hnonneg : 0 ≤ min εU εV / 2 := by
      have hmin_nonneg : 0 ≤ min εU εV := le_of_lt (lt_min hεU_pos hεV_pos)
      nlinarith
    have hlt : min εU εV / 2 < εU := by
      have hmin_le : min εU εV ≤ εU := min_le_left _ _
      nlinarith [hεU_pos]
    simpa [Metric.ball, Real.dist_eq, abs_of_nonneg hnonneg] using hlt
  have htV : t ∈ V' := by
    apply hεV
    dsimp [t]
    have hnonneg : 0 ≤ min εU εV / 2 := by
      have hmin_nonneg : 0 ≤ min εU εV := le_of_lt (lt_min hεU_pos hεV_pos)
      nlinarith
    have hlt : min εU εV / 2 < εV := by
      have hmin_le : min εU εV ≤ εV := min_le_right _ _
      nlinarith [hεV_pos]
    simpa [Metric.ball, Real.dist_eq, abs_of_nonneg hnonneg] using hlt
  -- The same nonzero parameter gives the same quotient point on the two branches.
  refine ⟨problem1LineWithTwoOriginsUpperBranch t, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [U'] using htU
  · have hLowerMem : problem1LineWithTwoOriginsLowerBranch t ∈ V := by
      simpa [V'] using htV
    exact problem1LineWithTwoOrigins_upper_eq_lower_branch ht_ne ▸ hLowerMem

/-- Problem 1-1 (3): the line with two origins is not Hausdorff. -/
-- Proof sketch: the upper and lower origins are distinct quotient classes, but every open
-- neighborhood of one meets every open neighborhood of the other because both contain the image of
-- some punctured interval around `0`, whose nonzero points have been identified in the quotient.
theorem problem1LineWithTwoOrigins_not_t2Space :
    ¬ T2Space problem1LineWithTwoOrigins := by
  intro hT2
  letI : T2Space problem1LineWithTwoOrigins := hT2
  -- In a Hausdorff space, distinct points admit disjoint open neighborhoods.
  rcases t2_separation problem1LineWithTwoOriginsUpperOrigin_ne_lowerOrigin with
    ⟨U, V, hU, hV, hUpper, hLower, hDisj⟩
  rcases
      problem1LineWithTwoOrigins_origins_nhds_inter U V hU hV hUpper hLower with
    ⟨x, hxU, hxV⟩
  exact Set.disjoint_left.1 hDisj hxU hxV
