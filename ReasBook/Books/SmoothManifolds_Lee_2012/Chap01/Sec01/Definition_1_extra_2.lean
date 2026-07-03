import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Basic

universe u

section

variable {H : Type*} [PseudoMetricSpace H]
variable {n : ℕ} {M : Type u} [TopologicalSpace M]

/- Definition 1-extra-2: a coordinate chart on a topological `n`-manifold is an open partial
homeomorphism from `M` to `EuclideanSpace ℝ (Fin n)`. -/
#check OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))

namespace OpenPartialHomeomorph

/-- A chart has coordinate-ball image if its target is an open metric ball. -/
def IsCoordinateBall (e : OpenPartialHomeomorph M H) : Prop :=
  ∃ c : H, ∃ r : ℝ, 0 < r ∧ e.target = Metric.ball c r

/-- A chart with target equal to an open Euclidean ball is a coordinate ball. -/
-- Proof sketch: unfold `IsCoordinateBall` and use the specified center and radius.
theorem isCoordinateBall_of_target_eq_ball
    (e : OpenPartialHomeomorph M H) (c : H) (r : ℝ) (hr : 0 < r)
    (h : e.target = Metric.ball c r) : e.IsCoordinateBall :=
  ⟨c, r, hr, h⟩

variable (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))

/-- A chart is centered at `p` if `p` lies in its source and the chart sends `p` to `0`. -/
def IsCenteredAt (p : M) : Prop :=
  p ∈ e.source ∧ e p = 0

/-- A chart has coordinate-box image if its target is a product of open intervals. -/
def IsCoordinateBox : Prop :=
  ∃ a b : EuclideanSpace ℝ (Fin n),
    (∀ i, a i < b i) ∧ e.target = { x | ∀ i : Fin n, x i ∈ Set.Ioo (a i) (b i) }

/-- A chart with target equal to an open coordinate box is a coordinate box. -/
-- Proof sketch: unfold `IsCoordinateBox` and use the specified interval endpoints.
theorem isCoordinateBox_of_target_eq
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (a b : EuclideanSpace ℝ (Fin n))
    (hab : ∀ i, a i < b i)
    (h : e.target = { x | ∀ i : Fin n, x i ∈ Set.Ioo (a i) (b i) }) : e.IsCoordinateBox :=
  ⟨a, b, hab, h⟩

/-- Center a chart at a source point `p` by translating its coordinates so that `p` maps to `0`.
-/
def centerAt (p : e.source) : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
  e.transHomeomorph (Homeomorph.addRight (-e p))

@[simp] theorem centerAt_source (p : e.source) : (e.centerAt p).source = e.source :=
  rfl

/-- The centered chart at a source point `p` is centered at `p`. -/
theorem centerAt_isCenteredAt (p : e.source) : (e.centerAt p).IsCenteredAt p := by
  exact ⟨p.2, by simp [centerAt]⟩

end OpenPartialHomeomorph

/- A charted topological manifold provides the preferred chart `chartAt`, whose source contains
the chosen point by `mem_chart_source`. -/
#check chartAt (EuclideanSpace ℝ (Fin n))
#check mem_chart_source (EuclideanSpace ℝ (Fin n))

end
