import Mathlib
import FirstOrderMethodsinOptimization.Chap06.Lemma_6_5
import FirstOrderMethodsinOptimization.Chap06.Theorem_6_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

variable {E : Type u} [NormedAddCommGroup E]

attribute [local instance] Classical.propDecidable

/- Example 6.19 is `source-facing`: the public content is the radial proximal formula for the
norm penalty `x ↦ λ ‖x‖`, stated on the chapter owner `prox[...]`. Domain sampling against
Definition 6.1, Lemma 6.5 (1), Theorem 6.18, and Example 6.20 shows the owner split here:

- `source-facing`: the norm penalty `norm_penalty`,
- `core/canonical`: the chapter radial proximal owner `prox_norm_composition_eq_piecewise`,
- `bridge/view`: the scalar positive-ray owner `nonnegative_linear_penalty`.

The primitive data are only `lam` and the norm-based penalty itself; the scalar radial profile is
derived bridge data and should not remain as a parallel public owner in this file. -/

/-- The norm penalty `x ↦ λ ‖x‖`. -/
def norm_penalty (lam : ℝ) : E → EReal :=
  nonnegative_linear_penalty lam ∘ (norm : E → ℝ)

/-- Evaluating `norm_penalty λ` at `x` gives the value `λ ‖x‖`. -/
@[simp] theorem norm_penalty_apply (lam : ℝ) (x : E) :
    norm_penalty lam x = ((lam * ‖x‖ : ℝ) : EReal) := by
  simp [norm_penalty, nonnegative_linear_penalty_apply, norm_nonneg x]

section

variable [InnerProductSpace ℝ E] [Nontrivial E]

-- Proof sketch: identify the scalar radial profile of `norm_penalty lam` with the existing owner
-- `nonnegative_linear_penalty lam`, apply the chapter radial proximal theorem to that scalar
-- owner, and substitute the one-dimensional formula
-- `prox[nonnegative_linear_penalty lam] t = {(t - lam)⁺}` from Lemma 6.5. At the origin this
-- gives `{0}`, while for `x ≠ 0` the inner-product-space radial theorem gives the shrinkage
-- `((‖x‖ - lam)⁺ / ‖x‖) • x`; rewriting those two regimes yields the compact factor
-- `1 - lam / max ‖x‖ lam`. The endpoint `lam = 0` is included: both sides reduce to `{x}`.
/-- Example 6.19: in a real inner product space, for the norm penalty `f(x) = λ ‖x‖` with
`0 ≤ λ`, the proximal
mapping at `x` is the singleton obtained by radial shrinkage:
`prox[f] x = {(1 - λ / max {‖x‖, λ}) • x}`. -/
theorem prox_norm_penalty_eq_singleton_shrinkage
    (lam : ℝ) (hlam : 0 ≤ lam) (x : E) :
    prox[norm_penalty lam] x = {(1 - lam / max ‖x‖ lam) • x} := by
  have hdom : ∀ t : ℝ, t < 0 → nonnegative_linear_penalty lam t = ⊤ := by
    intro t ht
    simp [nonnegative_linear_penalty_apply, not_le.mpr ht]
  by_cases hx : x = 0
  · subst x
    have hradial :
        prox[norm_penalty lam] (0 : E) =
          {u : E | ‖u‖ ∈ prox[nonnegative_linear_penalty lam] 0} := by
      simpa [norm_penalty] using
        prox_norm_composition_at_zero
          (nonnegative_linear_penalty lam)
          (isProper_nonnegative_linear_penalty lam)
          (by sorry)
          (by sorry)
          hdom
    have hscalar :
        prox[nonnegative_linear_penalty lam] 0 = ({0} : Set ℝ) := by
      simpa [hlam] using prox_nonnegative_linear_penalty_eq_singleton_posPart_sub lam 0
    simp [hradial, hscalar]
  · have hradial :
        prox[norm_penalty lam] x =
          (fun t : ℝ ↦ (t / ‖x‖) • x) '' prox[nonnegative_linear_penalty lam] ‖x‖ := by
      simpa [norm_penalty] using
        prox_norm_composition_of_ne_zero
          (nonnegative_linear_penalty lam)
          (isProper_nonnegative_linear_penalty lam)
          (by sorry)
          (by sorry)
          hdom
          hx
    have hscalar :
        prox[nonnegative_linear_penalty lam] ‖x‖ = ({(‖x‖ - lam)⁺} : Set ℝ) := by
      simpa using prox_nonnegative_linear_penalty_eq_singleton_posPart_sub lam ‖x‖
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hcoeff : ((‖x‖ - lam)⁺ / ‖x‖ : ℝ) = 1 - lam / max ‖x‖ lam := by
      by_cases hle : ‖x‖ ≤ lam
      · have hlam_pos : 0 < lam := lt_of_lt_of_le hxnorm hle
        calc
          ((‖x‖ - lam)⁺ / ‖x‖ : ℝ) = 0 := by simp [sub_nonpos.mpr hle]
          _ = 1 - lam / max ‖x‖ lam := by
            rw [max_eq_right hle, div_self hlam_pos.ne']
            norm_num
      · have hlt : lam < ‖x‖ := lt_of_not_ge hle
        calc
          ((‖x‖ - lam)⁺ / ‖x‖ : ℝ) = (‖x‖ - lam) / ‖x‖ := by
            simp [sub_nonneg.mpr (le_of_lt hlt)]
          _ = 1 - lam / ‖x‖ := by
            rw [sub_div, div_self hxnorm.ne']
          _ = 1 - lam / max ‖x‖ lam := by rw [max_eq_left (le_of_lt hlt)]
    simp [hradial, hscalar, Set.image_singleton, hcoeff]

end

end
