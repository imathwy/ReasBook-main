import Mathlib

open scoped Manifold

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the canonical chart-expression API was verified directly in
-- `Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean` and
-- `Mathlib/Analysis/Analytic/Order.lean`.

-- Declarations for this item will be appended below by the statement pipeline.

section Ramification

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]

/-- The preferred local coordinate expression of `φ` at `a`, translated so that the image point is
sent to `0`. -/
noncomputable def centered_chart_expression_at (φ : X → Y) (a : X) : ℂ → ℂ :=
  fun z ↦
    writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a φ z - (extChartAt 𝓘(ℂ) (φ a)) (φ a)

/-- Definition VI.4-extra-11: a holomorphic map `φ : X → Y` has ramification index `p` at `a`
when the centered preferred local coordinate expression of `φ` at `a` has vanishing order `p`. -/
class has_ramification_index_at (φ : X → Y) (a : X) (p : ℕ) : Prop where
  /-- The centered preferred local coordinate expression is analytic at the chart-center. -/
  analyticAt :
    AnalyticAt ℂ (centered_chart_expression_at φ a) ((extChartAt 𝓘(ℂ) a) a)
  /-- The centered preferred local coordinate expression has vanishing order `p`. -/
  analyticOrder_eq :
    analyticOrderAt (centered_chart_expression_at φ a) ((extChartAt 𝓘(ℂ) a) a) = p

/-- A map is unramified at `a` exactly when its ramification index there is `1`. -/
def unramified_at (φ : X → Y) (a : X) : Prop :=
  has_ramification_index_at φ a 1

end Ramification

section Ramification

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- The centered preferred local coordinate expression vanishes at the chart-center of `a`. -/
theorem centered_chart_expression_at_self (φ : X → Y) (a : X) :
    centered_chart_expression_at φ a ((extChartAt 𝓘(ℂ) a) a) = 0 := by
  simp [centered_chart_expression_at]

/-- Being unramified is the specialization of the ramification-index condition to `p = 1`. -/
theorem unramified_at_iff_has_ramification_index_at_one {φ : X → Y} {a : X} :
    unramified_at φ a ↔ has_ramification_index_at φ a 1 :=
  Iff.rfl

end Ramification
