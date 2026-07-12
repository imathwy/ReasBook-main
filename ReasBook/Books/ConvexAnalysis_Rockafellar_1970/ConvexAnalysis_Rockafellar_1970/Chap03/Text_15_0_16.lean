import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

open AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-!
Source/core/bridge triage:
- `source-facing`: Text 15.0.16 defines a special class of metrics on `R^n` by adding translation
  invariance and affine-segment scaling to the metric axioms. The source specialization to `R^n`
  is recovered by taking `E = EuclideanSpace ℝ (Fin n)`.
- `core/canonical`: the owner abstraction for the metric axioms is mathlib's `MetricSpace`, while
  the translation-invariance clause is already owned by `IsIsometricVAdd Eᵃᵒᵖ E`.
- `bridge/view`: the affine-segment formula is most naturally expressed using the canonical affine
  owner `AffineMap.lineMap`, while the source coordinate formula `((1 - t) • x) + t • y` is a
  companion view.
- Domain-style sampling used here: `MetricSpace`, `IsIsometricVAdd Eᵃᵒᵖ E` with its theorem
  `dist_add_right`, `AffineMap.lineMap`, and the normed-space theorem `dist_left_lineMap` as the
  canonical affine-segment distance pattern; on the chapter side, `IsGaugeNorm.map_smul_eq_abs`
  is the matching radial-homogeneity owner.
- Primitive data vs derived API: the metric owner `ρ : MetricSpace E` is primitive data; the only
  primitive extra axiom beyond the translation-invariant owner is radial scaling from the origin,
  while the affine-segment identities are derived API.
- Layer target: `source-facing`, implemented as a `Prop`-valued refinement of a fixed
  `MetricSpace E`.
-/

namespace MetricSpace

/-- Text 15.0.16: a Minkowski metric on a real vector space is a metric whose distance is
translation invariant and whose distance from `0` to `t • x` equals `t` times the distance from
`0` to `x` for every `t ∈ [0, 1]`. Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers the
textbook `R^n` formulation. -/
class IsMinkowskiMetric (ρ : MetricSpace E) : Prop extends (letI := ρ; IsIsometricVAdd Eᵃᵒᵖ E) where
  dist_zero_smul (x : E) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ρ.dist (0 : E) (t • x) = t * ρ.dist (0 : E) x

attribute [instance] IsMinkowskiMetric.toIsIsometricVAdd

namespace IsMinkowskiMetric

variable {ρ : MetricSpace E} [hρ : ρ.IsMinkowskiMetric]

/-- In a Minkowski metric, the affine-segment point is at distance `t * dist x y` from the left
endpoint for every `t ∈ [0, 1]`. -/
theorem dist_left_lineMap (x y : E) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ρ.dist x (lineMap x y t) = t * ρ.dist x y := by
  letI := ρ
  have hxy : ρ.dist (0 : E) (y - x) = ρ.dist x y := by
    simpa using (dist_add_right (0 : E) (y - x) x).symm
  calc
    ρ.dist x (lineMap x y t) = ρ.dist (0 : E) (t • (y - x)) := by
      rw [lineMap_apply]
      simpa using (dist_add_right (0 : E) (t • (y - x)) x)
    _ = t * ρ.dist (0 : E) (y - x) := hρ.dist_zero_smul (y - x) ht
    _ = t * ρ.dist x y := by rw [hxy]

/-- Text 15.0.16: in a Minkowski metric, the distance from `x` to the affine-segment point
`(1 - t) • x + t • y` is `t` times the distance from `x` to `y` for every `t ∈ [0, 1]`. -/
theorem dist_affineCombination (x y : E) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ρ.dist x (((1 - t) • x) + t • y) = t * ρ.dist x y := by
  simpa [lineMap_apply_module] using dist_left_lineMap x y ht

end IsMinkowskiMetric

end MetricSpace

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The standard norm metric on a real normed space is a Minkowski metric. -/
instance : (inferInstance : MetricSpace E).IsMinkowskiMetric := by
  refine { dist_zero_smul := ?_ }
  intro x t ht
  rw [dist_zero_left, dist_zero_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]

end
