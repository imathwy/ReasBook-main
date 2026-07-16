import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Lemma_6_5
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Proposition_6_2_1
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Theorem_6_18

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E]

attribute [local instance] Classical.propDecidable

/- Example 6.20 is `source-facing`: the textbook object is the cubic norm penalty
`x ↦ λ ‖x‖^3`, stated on the chapter owner `prox[...]` from Definition 6.1. Domain sampling
against Definition 6.1, Lemma 6.5 (3), Theorem 6.18, and Example 6.19 shows the owner split
here:

- `source-facing`: the vector penalty `cubic_norm_penalty`,
- `core/canonical`: the chapter radial proximal owner `prox_norm_composition_eq_piecewise`,
- `bridge/view`: the scalar positive-ray owner `nonnegative_cubic_penalty`.

The primitive data are only `lam` and the norm-based penalty itself; the scalar cubic profile and
its properness are derived bridge data and should not remain as parallel public owners in this
file. -/

/-- The cubic norm penalty `x ↦ λ ‖x‖^3`. -/
def cubic_norm_penalty (lam : ℝ) : E → EReal :=
  nonnegative_cubic_penalty lam ∘ (norm : E → ℝ)

/-- Evaluating the cubic norm penalty gives the value `λ ‖x‖^3`. -/
@[simp] theorem cubic_norm_penalty_apply (lam : ℝ) (x : E) :
    cubic_norm_penalty lam x = ((lam * ‖x‖ ^ (3 : ℕ) : ℝ) : EReal) := by
  simp [cubic_norm_penalty, nonnegative_cubic_penalty_apply, norm_nonneg x]

-- Proof sketch: if `lam = 0`, the penalty is the zero function, so the proximal singleton is
-- `{x}` by the chapter constant-function owner. For `lam > 0`, identify the scalar radial profile
-- with `nonnegative_cubic_penalty lam`, apply the chapter radial proximal theorem, and substitute
-- Lemma 6.5 (3). At `x = 0`, this gives `{0}`. Away from the origin, the scalar radius is
-- `(-1 + √(1 + 12 λ ‖x‖)) / (6 λ)`, and dividing by `‖x‖` simplifies to the textbook shrinkage
-- factor `2 / (1 + √(1 + 12 λ ‖x‖))`.
section ProximalFormula

variable [InnerProductSpace ℝ E] [Nontrivial E]

/-- Example 6.20: for the cubic norm penalty `f(x) = λ ‖x‖^3` with `0 ≤ λ`, the
proximal mapping is the singleton obtained by shrinking `x` by the scalar factor
`2 / (1 + √(1 + 12 λ ‖x‖))`. -/
theorem prox_cubic_norm_penalty_eq_singleton (lam : ℝ) (hlam : 0 ≤ lam) (x : E) :
    prox[cubic_norm_penalty lam] x =
      {(((2 : ℝ) / (1 + Real.sqrt (1 + 12 * lam * ‖x‖))) • x)} := by
  have hdom : ∀ t : ℝ, t < 0 → nonnegative_cubic_penalty lam t = ⊤ := by
    intro t ht
    simp [nonnegative_cubic_penalty_apply, not_le.mpr ht]
  by_cases hlam_zero : lam = 0
  · subst hlam_zero
    calc
      prox[cubic_norm_penalty 0] x = prox[fun _ : E ↦ (0 : EReal)] x := by
        congr 1
        ext y
        simp [cubic_norm_penalty, nonnegative_cubic_penalty_apply, norm_nonneg y]
      _ = {x} := prox_zero_eq_singleton x
      _ = {(((2 : ℝ) / (1 + Real.sqrt (1 + 12 * 0 * ‖x‖))) • x)} := by
        congr 1
        norm_num
  · have hlam_pos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hlam_zero)
    by_cases hx : x = 0
    · subst x
      have hradial :
          prox[cubic_norm_penalty lam] (0 : E) =
            {u : E | ‖u‖ ∈ prox[nonnegative_cubic_penalty lam] 0} := by
        simpa [cubic_norm_penalty] using
          prox_norm_composition_at_zero
            (nonnegative_cubic_penalty lam)
            (isProper_nonnegative_cubic_penalty lam)
            (by sorry)
            (by sorry)
            hdom
      have hscalar :
          prox[nonnegative_cubic_penalty lam] 0 = ({0} : Set ℝ) := by
        simpa [hlam_pos] using prox_nonnegative_cubic_penalty_eq_singleton lam hlam_pos 0
      simp [hradial, hscalar]
    · have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hradial :
          prox[cubic_norm_penalty lam] x =
            (fun t : ℝ ↦ (t / ‖x‖) • x) '' prox[nonnegative_cubic_penalty lam] ‖x‖ := by
        simpa [cubic_norm_penalty] using
          prox_norm_composition_of_ne_zero
            (nonnegative_cubic_penalty lam)
            (isProper_nonnegative_cubic_penalty lam)
            (by sorry)
            (by sorry)
            hdom
            hx
      have hscalar :
          prox[nonnegative_cubic_penalty lam] ‖x‖ =
            ({(-1 + Real.sqrt (1 + 12 * lam * ‖x‖)) / (6 * lam)} : Set ℝ) := by
        simpa [hxnorm] using prox_nonnegative_cubic_penalty_eq_singleton lam hlam_pos ‖x‖
      have hcoeff :
          (((-1 + Real.sqrt (1 + 12 * lam * ‖x‖)) / (6 * lam)) / ‖x‖ : ℝ) =
            (2 : ℝ) / (1 + Real.sqrt (1 + 12 * lam * ‖x‖)) := by
        have harg_nonneg : 0 ≤ 1 + 12 * lam * ‖x‖ := by positivity
        have hsq : Real.sqrt (1 + 12 * lam * ‖x‖) ^ (2 : ℕ) = 1 + 12 * lam * ‖x‖ :=
          Real.sq_sqrt harg_nonneg
        have hden1 : 6 * lam ≠ 0 := by nlinarith
        have hden2 : ‖x‖ ≠ 0 := by linarith
        have hden3 : 1 + Real.sqrt (1 + 12 * lam * ‖x‖) ≠ 0 := by
          have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + 12 * lam * ‖x‖) := Real.sqrt_nonneg _
          nlinarith
        field_simp [hden1, hden2, hden3]
        nlinarith [hsq]
      simp [hradial, hscalar, Set.image_singleton, hcoeff]

end ProximalFormula

end
