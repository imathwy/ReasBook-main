import AchimKlenkeLean.Items.Chap15.Theorem_15_12

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

/-- The slope of the linear interpolant on the `k`th interval `[a_k, a_{k+1}]`. -/
noncomputable def polygonalSegmentSlope (a y : ℕ → ℝ) (k : ℕ) : ℝ :=
  (y (k + 1) - y k) / (a (k + 1) - a k)

/-- The coefficient `p_{k+1} = a_{k+1}(m_{k+2} - m_{k+1})` used in Example 15.15, with the terminal
slope interpreted as `0`. -/
noncomputable def polygonalWeight (a y : ℕ → ℝ) (n k : ℕ) : ℝ :=
  a (k + 1) *
    ((if _ : k + 1 < n then polygonalSegmentSlope a y (k + 1) else 0) -
      polygonalSegmentSlope a y k)

/-- A real-valued function is the polygonal interpolant from this example if it takes the
prescribed nodal values, is affine on each interpolation interval, vanishes outside `[-a_n, a_n]`,
and is even. -/
def IsEvenPolygonalInterpolant (n : ℕ) (a y : ℕ → ℝ) (φ : ℝ → ℝ) : Prop :=
  (∀ k ≤ n, φ (a k) = y k) ∧
    (∀ k < n,
      EqOn φ (fun x ↦ y k + polygonalSegmentSlope a y k * (x - a k)) (Icc (a k) (a (k + 1)))) ∧
    (∀ ⦃x : ℝ⦄, a n < |x| → φ x = 0) ∧
    Function.Even φ

-- Proof sketch: read off the first field of `IsEvenPolygonalInterpolant`.
/-- A polygonal interpolant takes the prescribed values at the interpolation nodes. -/
theorem isEvenPolygonalInterpolant_apply_nodes {n : ℕ} {a y : ℕ → ℝ} {φ : ℝ → ℝ}
    (hφ : IsEvenPolygonalInterpolant n a y φ) {k : ℕ} (hk : k ≤ n) :
    φ (a k) = y k :=
  hφ.1 k hk

/-- The explicit convex combination of the triangular measures appearing in Example 15.15. -/
noncomputable def polygonalCharacteristicMeasure (n : ℕ) (a y : ℕ → ℝ) : Measure ℝ :=
  Finset.sum (Finset.range n) fun k ↦
    ENNReal.ofReal (polygonalWeight a y n k) • triangularCharacteristicMeasure (a (k + 1))

-- Proof sketch: first show from convexity on `[0, ∞)` that the slopes
-- `polygonalSegmentSlope a y k` are nondecreasing, so the coefficients `polygonalWeight a y n k`
-- are nonnegative and sum to `1`. Then apply `charFun_triangularCharacteristicMeasure` to each
-- summand, evaluate the finite weighted sum at the interpolation nodes by partial summation, and
-- conclude by linearity on each interval, evenness, and the compact support condition.
/-- The explicit polygonal measure from Example 15.15 is a probability measure. -/
theorem isProbabilityMeasure_polygonalCharacteristicMeasure
    (n : ℕ) (a y : ℕ → ℝ) (φ : ℝ → ℝ)
    (ha0 : a 0 = 0) (ha_strict : ∀ ⦃k : ℕ⦄, k < n → a k < a (k + 1))
    (hy0 : y 0 = 1) (hyn : y n = 0)
    (hφ : IsEvenPolygonalInterpolant n a y φ) (hconvex : ConvexOn ℝ (Ici 0) φ) :
    IsProbabilityMeasure (polygonalCharacteristicMeasure n a y) := sorry

/-- The characteristic function of the explicit polygonal measure from Example 15.15 is the
polygonal interpolant `φ`. -/
theorem charFun_polygonalCharacteristicMeasure_eq
    (n : ℕ) (a y : ℕ → ℝ) (φ : ℝ → ℝ)
    (ha0 : a 0 = 0) (ha_strict : ∀ ⦃k : ℕ⦄, k < n → a k < a (k + 1))
    (hy0 : y 0 = 1) (hyn : y n = 0)
    (hφ : IsEvenPolygonalInterpolant n a y φ) (hconvex : ConvexOn ℝ (Ici 0) φ) :
    ∀ t : ℝ, charFun (polygonalCharacteristicMeasure n a y) t = (φ t : ℂ) := sorry

/-- Example 15.15: an even compactly supported polygonal function on `ℝ` with vertices
`(a_k, y_k)`, linear interpolation on each interval, and convexity on `[0, ∞)` is the
characteristic function of the explicitly constructed probability measure
`polygonalCharacteristicMeasure n a y`. -/
theorem convexPolygonalInterpolant_isCharacteristicFunction
    (n : ℕ) (a y : ℕ → ℝ) (φ : ℝ → ℝ)
    (ha0 : a 0 = 0) (ha_strict : ∀ ⦃k : ℕ⦄, k < n → a k < a (k + 1))
    (hy0 : y 0 = 1) (hyn : y n = 0)
    (hφ : IsEvenPolygonalInterpolant n a y φ) (hconvex : ConvexOn ℝ (Ici 0) φ) :
    IsProbabilityMeasure (polygonalCharacteristicMeasure n a y) ∧
      ∀ t : ℝ, charFun (polygonalCharacteristicMeasure n a y) t = (φ t : ℂ) := by
  exact ⟨
    isProbabilityMeasure_polygonalCharacteristicMeasure n a y φ ha0 ha_strict hy0 hyn hφ hconvex,
    charFun_polygonalCharacteristicMeasure_eq n a y φ ha0 ha_strict hy0 hyn hφ hconvex
  ⟩
