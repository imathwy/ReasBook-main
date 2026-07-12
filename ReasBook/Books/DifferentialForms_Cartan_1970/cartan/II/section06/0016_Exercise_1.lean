import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0001_Definition_II_1_extra_1»
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»

open scoped ComplexConjugate

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for Cartan section06 0016_Exercise_1: complex conjugation commutes with complex-valued
interval integrals. -/
private lemma conjIntervalIntegral {g : ℝ → ℂ} {a b : ℝ} :
    conj (∫ t in a..b, g t) = ∫ t in a..b, conj (g t) := by
  -- Expand the interval integral into set integrals and conjugate each term separately.
  simp [intervalIntegral, integral_conj, map_sub]

namespace Path

-- Proof sketch: compose `f` with complex conjugation on the source and target; continuity of
-- complex conjugation on `ℂ` and continuity of `f` along the image of `γ` imply continuity on the
-- reflected path image.
/-- Exercise 1 (1): if `f` is continuous on the image of a path `γ`, then
`z ↦ conj (f (conj z))` is continuous on the reflected path `γ.map Complex.continuous_conj`. -/
theorem continuousOn_conj_comp_conj_reflected
    {a b : ℂ} {γ : Path a b} {f : ℂ → ℂ} (hf : ContinuousOn f (Set.range γ)) :
    ContinuousOn (fun z ↦ conj (f (conj z)))
      (Set.range (γ.map Complex.continuous_conj)) := by
  -- First move points from the reflected path back to the original path by conjugating again.
  have hmaps : Set.MapsTo (fun z : ℂ ↦ conj z)
      (Set.range (γ.map Complex.continuous_conj)) (Set.range γ) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    simp [Path.map_coe]
  -- Then compose the original continuity with the source and target conjugations.
  have hcomp : ContinuousOn (fun z : ℂ ↦ f (conj z))
      (Set.range (γ.map Complex.continuous_conj)) :=
    hf.comp Complex.continuous_conj.continuousOn hmaps
  simpa [Function.comp] using Complex.continuous_conj.comp_continuousOn hcomp

/-- Helper for Cartan section06 0016_Exercise_1: reflecting a path and then extending it to `ℝ`
is the same as conjugating the original extension pointwise. -/
private lemma extend_mapConj {a b : ℂ} (γ : Path a b) :
    (γ.map Complex.continuous_conj).extend = fun t : ℝ ↦ conj (γ.extend t) := by
  ext t
  by_cases ht0 : t ≤ 0
  · -- To the left of the unit interval, both extensions are the reflected initial point.
    simp [Path.extend_of_le_zero, ht0]
  · by_cases ht1 : 1 ≤ t
    · -- To the right of the unit interval, both extensions are the reflected endpoint.
      simp [Path.extend_of_one_le, ht1]
    · -- On `[0,1]`, both paths are evaluated at the same parameter and then conjugated.
      have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_not_ge ht0, le_of_not_ge ht1⟩
      simp [Path.extend_apply, htI, Path.map_coe]

/-- Helper for Cartan section06 0016_Exercise_1: the derivative of the reflected path extension is
the conjugate of the derivative of the original extension. -/
private lemma deriv_extend_mapConj {a b : ℂ} (γ : Path a b) (t : ℝ) :
    deriv ((γ.map Complex.continuous_conj).extend) t = conj (deriv γ.extend t) := by
  -- Route correction: rewrite the reflected extension globally before applying `deriv.star`.
  simpa [extend_mapConj γ] using (deriv.star (f := fun s : ℝ ↦ γ.extend s) (x := t))

-- Proof sketch: parametrize the reflected path by `t ↦ conj (γ t)`, use the piecewise
-- differentiability of `γ` to justify taking derivatives on each smooth piece, and observe that
-- the reflected integrand is the complex conjugate of the original integrand.
/-- Helper for Cartan section06 0016_Exercise_1: reflecting a piecewise differentiable path across
the real axis and replacing `f` by `z ↦ conj (f (conj z))` conjugates the complex path
integral. -/
theorem conj_curveIntegral_eq_curveIntegral_reflected
    {a b : ℂ} {γ : Path a b} (hγ : γ.IsPiecewiseDifferentiable) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.range γ)) :
    conj (∫ᶜ z in γ, (1 : ℂ →L[ℂ] ℂ).smulRight (f z)) =
      ∫ᶜ z in γ.map Complex.continuous_conj,
        (1 : ℂ →L[ℂ] ℂ).smulRight (conj (f (conj z))) := by
  let _ := hγ
  let _ := hf
  -- Rewrite both curve integrals as interval integrals so conjugation acts on the scalar
  -- pullback integrand.
  rw [curveIntegral_eq_intervalIntegral_deriv, curveIntegral_eq_intervalIntegral_deriv,
    conjIntervalIntegral]
  refine intervalIntegral.integral_congr ?_
  intro t ht
  -- The reflected integrand is the conjugate of the original one after rewriting the reflected
  -- extension and its derivative.
  calc
    conj (((1 : ℂ →L[ℂ] ℂ).smulRight (f (γ.extend t))) (deriv γ.extend t)) =
        conj (deriv γ.extend t) * conj (f (γ.extend t)) := by
      simp [map_mul]
    _ = ((1 : ℂ →L[ℂ] ℂ).smulRight (conj (f (conj (((γ.map Complex.continuous_conj).extend) t)))))
          (deriv ((γ.map Complex.continuous_conj).extend) t) := by
      rw [deriv_extend_mapConj γ t]
      rw [extend_mapConj γ]
      simp

end Path

/-- Helper for Cartan section06 0016_Exercise_1: on the unit circle, complex conjugation equals
inversion. -/
private lemma unitCircleConjEqInv (θ : ℝ) :
    conj (circleMap 0 1 θ) = (circleMap 0 1 θ)⁻¹ := by
  -- This is the standard unit-circle identity specialized to `circleMap 0 1`.
  simpa [circleMap_zero_inv] using conj_circleMap_zero 1 θ

/-- Helper for Cartan section06 0016_Exercise_1: conjugating the unit-circle pullback integrand
produces the factor `-z⁻²`. -/
private lemma unitCircleConjIntegrand (f : ℂ → ℂ) (θ : ℝ) :
    conj (deriv (circleMap 0 1) θ * f (circleMap 0 1 θ)) =
      -(deriv (circleMap 0 1) θ *
        (conj (f (circleMap 0 1 θ)) / (circleMap 0 1 θ) ^ (2 : ℕ))) := by
  have hz : circleMap 0 1 θ ≠ 0 := by
    exact circleMap_ne_center (c := 0) (R := 1) (θ := θ) (one_ne_zero : (1 : ℝ) ≠ 0)
  have hunit : conj (circleMap 0 1 θ) = (circleMap 0 1 θ)⁻¹ := unitCircleConjEqInv θ
  have hderiv :
      conj (deriv (circleMap 0 1) θ) =
        -(deriv (circleMap 0 1) θ / (circleMap 0 1 θ) ^ (2 : ℕ)) := by
    -- Conjugate the tangent vector explicitly and rewrite `conj z` as `z⁻¹` on the unit circle.
    rw [deriv_circleMap, map_mul, Complex.conj_I, hunit]
    simp [div_eq_mul_inv, pow_two, hz, mul_assoc, mul_comm]
  -- The remaining algebra is a commutative rearrangement of the conjugated scalar pullback.
  calc
    conj (deriv (circleMap 0 1) θ * f (circleMap 0 1 θ)) =
        conj (deriv (circleMap 0 1) θ) * conj (f (circleMap 0 1 θ)) := by
      simp
    _ = (-(deriv (circleMap 0 1) θ / (circleMap 0 1 θ) ^ (2 : ℕ))) *
          conj (f (circleMap 0 1 θ)) := by
      rw [hderiv]
    _ = -(deriv (circleMap 0 1) θ *
          (conj (f (circleMap 0 1 θ)) / (circleMap 0 1 θ) ^ (2 : ℕ))) := by
      simp [div_eq_mul_inv, mul_assoc, mul_comm]

-- Proof sketch: identify the reflected positively oriented unit circle with the negatively
-- oriented original circle, use `conj z = z⁻¹` on `|z| = 1`, and rewrite the reflected integrand
-- in terms of `dz / z^2`.
/-- Cartan section06 0016_Exercise_1: on the positively oriented unit circle, conjugating the
circle integral of `f` produces the integral of `-conj (f z) / z^2`. -/
theorem conj_circleIntegral_unitCircle_eq_neg_circleIntegral_conj_div_zsq
    {f : ℂ → ℂ} (hf : ContinuousOn f (Metric.sphere (0 : ℂ) 1)) :
    conj (∮ z in C(0, 1), f z) =
      -(∮ z in C(0, 1), conj (f z) / z ^ (2 : ℕ)) := by
  let _ := hf
  -- Rewrite the circle integral in its interval parametrization and conjugate the pullback
  -- integrand pointwise.
  rw [circleIntegral, conjIntervalIntegral]
  calc
    ∫ θ in (0 : ℝ)..2 * Real.pi, conj (deriv (circleMap 0 1) θ • f (circleMap 0 1 θ)) =
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          -(deriv (circleMap 0 1) θ •
            (conj (f (circleMap 0 1 θ)) / (circleMap 0 1 θ) ^ (2 : ℕ))) := by
      refine intervalIntegral.integral_congr ?_
      intro θ hθ
      simpa [smul_eq_mul] using unitCircleConjIntegrand f θ
    _ = -∫ θ in (0 : ℝ)..2 * Real.pi,
          deriv (circleMap 0 1) θ •
            (conj (f (circleMap 0 1 θ)) / (circleMap 0 1 θ) ^ (2 : ℕ)) := by
      rw [intervalIntegral.integral_neg]
    _ = -(∮ z in C(0, 1), conj (f z) / z ^ (2 : ℕ)) := by
      rfl
