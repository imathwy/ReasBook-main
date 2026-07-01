import Mathlib
import cartan.III.section10.«0001_Definition_III_4_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology unitInterval
open Metric

/-
This file is `source-facing`: its primitive data is a Laurent coefficient family `a : ℤ → R`.
The core/canonical meromorphic owner for residues of actual functions remains
`meromorphicTrailingCoeffAt`, while this file records the textbook coefficient-level formulas
directly. Clause `(2)` is a `bridge/view` specialization of the path-level contour-integral owner
from Proposition `2.1` to positively oriented circles strictly inside the annulus.
-/

section Coefficients

variable {R : Type*}

/-- Definition III.5-extra-1 (1): for Laurent coefficients at a finite point, the residue term is
the `(-1)`st Laurent coefficient. -/
def laurentResidue (a : ℤ → R) : R :=
  a (-1 : ℤ)

@[simp] theorem laurentResidue_eq_laurentCoeff_neg_one (a : ℤ → R) :
    laurentResidue a = a (-1 : ℤ) :=
  rfl

end Coefficients

/-- Helper for Definition III.5-extra-1: the radius-`r` circle is contained in the closed annulus
with both radii equal to `r`. -/
lemma sphere_subset_complexClosedAnnulus_self (r : NNReal) :
    Metric.sphere (0 : ℂ) (r : ℝ) ⊆ complexClosedAnnulus r r := by
  -- Points on this circle have norm exactly `r`, so both closed-annulus inequalities are
  -- equalities.
  intro z hz
  have hzR : ‖z‖ = (r : ℝ) := by
    simpa using mem_sphere_iff_norm.mp hz
  have hzR' : ‖z‖₊ = r := by
    exact NNReal.coe_injective (by simp [hzR])
  simp [complexClosedAnnulus, hzR']

/-- Helper for Definition III.5-extra-1: a positive-radius circle lies in the punctured annulus
`ρ₂ < ‖z‖ < ρ₁` whenever its radius lies strictly between `ρ₂` and `ρ₁`. -/
lemma sphere_subset_complexOpenAnnulus_of_lt_lt
    {ρ₂ ρ₁ R : NNReal} (hρ₂ : ρ₂ < R) (hρ₁ : R < ρ₁) :
    Metric.sphere (0 : ℂ) (R : ℝ) ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
  -- Points on the radius-`R` circle satisfy the annulus inequalities because their norm is
  -- exactly `R`.
  intro z hz
  have hzR : ‖z‖ = (R : ℝ) := by
    simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz
  have hzR' : ‖z‖₊ = R := by
    exact NNReal.coe_injective (by simp [hzR])
  change (ρ₂ : ENNReal) < ‖z‖₊ ∧ ‖z‖₊ < (ρ₁ : ENNReal)
  constructor
  · simpa [hzR'] using (show (ρ₂ : ENNReal) < (R : ENNReal) by exact_mod_cast hρ₂)
  · simpa [hzR'] using (show (R : ENNReal) < (ρ₁ : ENNReal) by exact_mod_cast hρ₁)

/-- Helper for Definition III.5-extra-1: points on a positive-radius circle are nonzero. -/
lemma ne_zero_of_mem_sphere_zero_of_pos {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ Metric.sphere (0 : ℂ) R) : z ≠ 0 := by
  -- A point on `sphere 0 R` has norm `R`, so for `R > 0` it cannot be the origin.
  have hzR : ‖z‖ = R := by
    simpa using mem_sphere_iff_norm.mp hz
  exact fun hz0 ↦ (ne_of_gt hR) <| by simpa [hz0] using hzR.symm

/-- Helper for Definition III.5-extra-1: the circle integral of `z ^ k` detects exactly the
residue exponent `k = -1`. -/
lemma circleIntegral_zpow_eq_residue {R : ℝ} (hR : 0 < R) (k : ℤ) :
    (∮ z in C(0, R), z ^ k) = if k = -1 then 2 * Real.pi * Complex.I else 0 := by
  by_cases hk : k = -1
  · subst hk
    have hzero_mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hR
    simpa using
      (circleIntegral.integral_sub_inv_of_mem_ball (c := (0 : ℂ)) (w := (0 : ℂ)) (R := R)
        hzero_mem)
  · rw [if_neg hk]
    simpa using
      (circleIntegral.integral_sub_zpow_of_ne hk (c := (0 : ℂ)) (w := (0 : ℂ)) (R := R))

/-- Helper for Definition III.5-extra-1: each Laurent monomial is continuous on a positive-radius
circle. -/
lemma laurentTerm_continuousOn_sphere
    {a : ℤ → ℂ} {R : NNReal} (hR : 0 < (R : ℝ)) (m : ℤ) :
    ContinuousOn (laurentTerm a m) (Metric.sphere (0 : ℂ) (R : ℝ)) := by
  -- The only issue for a `zpow` monomial is the origin, and a positive-radius circle avoids it.
  refine (continuousOn_const.mul (continuousOn_zpow₀ (m := m))).mono ?_
  intro z hz
  exact ne_zero_of_mem_sphere_zero_of_pos hR hz

/-- Helper for Definition III.5-extra-1: uniform convergence of a Laurent family on a circle
allows termwise circle integration. -/
lemma circleIntegral_tsum_of_summableUniformlyOn_sphere
    {F : ℤ → ℂ → ℂ} {R : NNReal}
    (hcont : ∀ m, ContinuousOn (F m) (Metric.sphere (0 : ℂ) (R : ℝ)))
    (hsum : SummableUniformlyOn F (Metric.sphere (0 : ℂ) (R : ℝ))) :
    (∮ z in C(0, (R : ℝ)), ∑' m : ℤ, F m z) = ∑' m : ℤ, ∮ z in C(0, (R : ℝ)), F m z := by
  have hhas :
      HasSumUniformlyOn F (fun z ↦ ∑' m : ℤ, F m z) (Metric.sphere (0 : ℂ) (R : ℝ)) :=
    hsum.hasSumUniformlyOn
  have hcont_partial :
      ∀ s : Finset ℤ,
        ContinuousOn (fun z : ℂ ↦ ∑ m ∈ s, F m z) (Metric.sphere (0 : ℂ) (R : ℝ)) := by
    -- Finite partial sums preserve continuity on the circle.
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (0 : ℂ)) _)
    · intro m s hm hs
      simpa [Finset.sum_insert, hm] using (hcont m).add hs
  have htendsto :
      Filter.Tendsto (fun s : Finset ℤ ↦ ∮ z in C(0, (R : ℝ)), ∑ m ∈ s, F m z) Filter.atTop
        (𝓝 (∮ z in C(0, (R : ℝ)), ∑' m : ℤ, F m z)) :=
    hhas.tendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn R.2
      (Filter.Eventually.of_forall hcont_partial)
  have hsum_int :
      HasSum (fun m : ℤ ↦ ∮ z in C(0, (R : ℝ)), F m z)
        (∮ z in C(0, (R : ℝ)), ∑' m : ℤ, F m z) := by
    rw [HasSum]
    convert htendsto using 1
    ext s
    symm
    exact circleIntegral.integral_fun_sum fun m _ ↦ (hcont m).circleIntegrable R.2
  exact hsum_int.tsum_eq.symm

/-- Helper for Definition III.5-extra-1: integrating one Laurent monomial around a positive circle
detects only the residue exponent `-1`. -/
lemma circleIntegral_laurentTerm_eq_residue
    {a : ℤ → ℂ} {r : ℝ} (hr : 0 < r) (m : ℤ) :
    (∮ z in C(0, r), laurentTerm a m z) =
      if m = -1 then (2 * Real.pi * Complex.I : ℂ) * a (-1 : ℤ) else 0 := by
  calc
    (∮ z in C(0, r), laurentTerm a m z) = ∮ z in C(0, r), a m * z ^ m := by
      refine circleIntegral.integral_congr hr.le ?_
      intro z hz
      simp [laurentTerm]
    _ = a m * (∮ z in C(0, r), z ^ m) := by
          rw [circleIntegral.integral_const_mul]
    _ = a m * (if m = -1 then 2 * Real.pi * Complex.I else 0) := by
          rw [circleIntegral_zpow_eq_residue hr]
    _ = if m = -1 then (2 * Real.pi * Complex.I : ℂ) * a (-1 : ℤ) else 0 := by
          by_cases hm : m = -1
          · subst hm
            simp [mul_comm]
          · simp [hm]

/-- Definition III.5-extra-1 (2): if `f` agrees on the punctured disk `0 < |z| < R` with the
Laurent series `∑' n : ℤ, a n * z ^ n`, then the positively oriented circle integral on any
intermediate circle `|z| = r` with `0 < r < R` is `2 π i` times the residue. -/
theorem circleIntegral_eq_two_pi_I_mul_laurentCoeff_neg_one
    {f : ℂ → ℂ} {a : ℤ → ℂ} {r R : NNReal} (hr0 : 0 < r) (hrR : r < R)
    (ha : IsLaurentSeriesOnAnnulus a 0 R)
    (hf : Set.EqOn f (fun z ↦ ∑' n : ℤ, a n * z ^ n) (complexOpenAnnulus 0 R)) :
    (∮ z in C(0, (r : ℝ)), f z) =
      (2 * Real.pi * Complex.I : ℂ) * laurentResidue a := by
  have hr0' : 0 < (r : ℝ) := by
    exact_mod_cast hr0
  have hsphere :
      Metric.sphere (0 : ℂ) (r : ℝ) ⊆ complexOpenAnnulus 0 R :=
    sphere_subset_complexOpenAnnulus_of_lt_lt (R := r) hr0 hrR
  have hsum_closed :
      SummableUniformlyOn (laurentTerm a) (complexClosedAnnulus r r) :=
    ha.summableUniformlyOn_closedAnnulus
      (show (0 : ENNReal) < (r : ENNReal) by exact_mod_cast hr0)
      (show (r : ENNReal) < (R : ENNReal) by exact_mod_cast hrR)
  have hsum :
      SummableUniformlyOn (laurentTerm a) (Metric.sphere (0 : ℂ) (r : ℝ)) :=
    hsum_closed.mono (sphere_subset_complexClosedAnnulus_self r)
  have hseries :
      (∮ z in C(0, (r : ℝ)), ∑' m : ℤ, laurentTerm a m z) =
        ∑' m : ℤ, ∮ z in C(0, (r : ℝ)), laurentTerm a m z := by
    -- Uniform convergence on the circle allows termwise contour integration of the Laurent sum.
    exact circleIntegral_tsum_of_summableUniformlyOn_sphere
      (R := r) (F := laurentTerm a)
      (fun m ↦ laurentTerm_continuousOn_sphere (a := a) hr0' m) hsum
  have hterm_sum :
      (∑' m : ℤ, ∮ z in C(0, (r : ℝ)), laurentTerm a m z) =
        (2 * Real.pi * Complex.I : ℂ) * a (-1 : ℤ) := by
    -- Every Laurent term integrates to zero except the unique residue exponent `m = -1`.
    calc
      (∑' m : ℤ, ∮ z in C(0, (r : ℝ)), laurentTerm a m z)
        = ∑' m : ℤ,
            if m = -1 then (2 * Real.pi * Complex.I : ℂ) * a (-1 : ℤ) else 0 := by
              refine tsum_congr ?_
              intro m
              simpa using circleIntegral_laurentTerm_eq_residue (a := a) (r := (r : ℝ)) hr0' m
      _ = (2 * Real.pi * Complex.I : ℂ) * a (-1 : ℤ) := by
            rw [tsum_ite_eq]
  -- Route correction: rewrite `f` to the Laurent sum on the circle, then integrate termwise and
  -- isolate the single surviving residue term.
  calc
    (∮ z in C(0, (r : ℝ)), f z) = ∮ z in C(0, (r : ℝ)), ∑' m : ℤ, laurentTerm a m z := by
      refine circleIntegral.integral_congr hr0.le ?_
      intro z hz
      simpa [laurentTerm] using hf (hsphere hz)
    _ = ∑' m : ℤ, ∮ z in C(0, (r : ℝ)), laurentTerm a m z := hseries
    _ = (2 * Real.pi * Complex.I : ℂ) * a (-1 : ℤ) := hterm_sum
    _ = (2 * Real.pi * Complex.I : ℂ) * laurentResidue a := by
      simp

section Coefficients

variable {R : Type*} [Neg R]

/-- Definition III.5-extra-1 (3): for Laurent coefficients in the chart at infinity, the residue
at infinity is the negative of the finite-point residue coefficient. -/
def laurentResidueAtInfinity (a : ℤ → R) : R :=
  -laurentResidue a

@[simp] theorem laurentResidueAtInfinity_eq_neg_laurentCoeff_neg_one (a : ℤ → R) :
    laurentResidueAtInfinity a = -a (-1 : ℤ) :=
  rfl

end Coefficients
