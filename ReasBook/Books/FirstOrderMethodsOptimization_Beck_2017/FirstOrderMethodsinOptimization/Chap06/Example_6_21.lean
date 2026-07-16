import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Example_6_19

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]

attribute [local instance] Classical.propDecidable

/- Example 6.21 is `source-facing` in the Chapter 6 proximal-operator domain. Domain sampling
against the chapter owner `prox[...]` from Definition 6.1, the source-facing penalty owner
`norm_penalty` from Example 6.19, the radial owner theorem
`prox_norm_composition_eq_piecewise` from Theorem 6.18, and the scalar proximal formula
`prox_nonnegative_linear_penalty_eq_singleton_posPart_sub` from Lemma 6.5 shows that the
primitive data here is already fixed upstream: the penalty is exactly `norm_penalty (-lam)`.
The sphere/singleton description is derived API for that owner. Its singleton branch is Euclidean,
so the statement belongs in the inner-product owner layer rather than in an arbitrary real normed
space. -/

-- Proof sketch: in a real inner product space, minimize
-- `u ↦ -λ ‖u‖ + (1 / 2) ‖u - x‖^2` by reducing to the radial variable `r = ‖u‖`. For `x ≠ 0`,
-- equality in the triangle inequality forces any minimizer to lie on the ray through `x`, where
-- the scalar problem becomes the proximal problem for `t ↦ -λ t` on `[0, ∞)`, giving the radius
-- `‖x‖ + λ` and hence the unique point `(1 + λ / ‖x‖) • x`. For `x = 0`, the objective depends
-- only on `‖u‖`, so every point with norm `λ` is a minimizer.
/-- Example 6.21: in a real inner product space, for the norm penalty with negative parameter
`norm_penalty (-λ) = (fun x ↦ -λ ‖x‖)` and `0 ≤ λ`, the proximal mapping is the sphere
`Metric.sphere 0 λ` at the origin and the singleton `{(1 + λ / ‖x‖) • x}` away from the
origin. -/
theorem prox_norm_penalty_neg_eq_piecewise (lam : ℝ) (hlam : 0 ≤ lam) (x : E) :
    prox[norm_penalty (-lam)] x =
      if x = 0 then Metric.sphere 0 lam else {(1 + lam / ‖x‖) • x} := by
  have hproper : IsProperExtendedRealFunction (nonnegative_linear_penalty (-lam)) :=
    isProper_nonnegative_linear_penalty (-lam)
  have hdom : ∀ t : ℝ, t < 0 → nonnegative_linear_penalty (-lam) t = ⊤ := by
    intro t ht
    simp [nonnegative_linear_penalty_apply, not_le.mpr ht]
  by_cases hx : x = 0
  · subst x
    have hradial :
        prox[norm_penalty (-lam)] (0 : E) =
          {u : E | ‖u‖ ∈ prox[nonnegative_linear_penalty (-lam)] 0} := by
      simpa [norm_penalty] using
        prox_norm_composition_at_zero
          (nonnegative_linear_penalty (-lam))
          hproper
          (by sorry)
          (by sorry)
          hdom
    have hscalar :
        prox[nonnegative_linear_penalty (-lam)] 0 = ({lam} : Set ℝ) := by
      simpa [sub_eq_add_neg, hlam] using
        prox_nonnegative_linear_penalty_eq_singleton_posPart_sub (-lam) 0
    ext u
    simp [Metric.sphere, hradial, hscalar]
  · have hradial :
        prox[norm_penalty (-lam)] x =
          (fun t : ℝ ↦ (t / ‖x‖) • x) '' prox[nonnegative_linear_penalty (-lam)] ‖x‖ := by
      simpa [norm_penalty] using
        prox_norm_composition_of_ne_zero
          (nonnegative_linear_penalty (-lam))
          hproper
          (by sorry)
          (by sorry)
          hdom
          hx
    have hscalar :
        prox[nonnegative_linear_penalty (-lam)] ‖x‖ = ({‖x‖ + lam} : Set ℝ) := by
      simpa [sub_eq_add_neg, posPart_eq_self.2 (add_nonneg (norm_nonneg x) hlam)] using
        prox_nonnegative_linear_penalty_eq_singleton_posPart_sub (-lam) ‖x‖
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hcoeff : ((‖x‖ + lam) / ‖x‖ : ℝ) = 1 + lam / ‖x‖ := by
      rw [add_div, div_self hxnorm.ne']
    simp [hradial, hx, hscalar, Set.image_singleton, hcoeff]

end
