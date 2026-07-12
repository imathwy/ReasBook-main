import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_3
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Lemma_6_5
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Remark_6_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open WithLp (toLp)
open scoped BigOperators
open scoped SoftThreshold

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/- Example 6.8 is `source-facing`: the source object is the Euclidean `ℓ¹` regularizer on a
finite-dimensional Euclidean product, specializing to `ℝ^n` when `ι = Fin n`. Domain sampling
against Proposition 3.17, Definition 6.3, Lemma 6.5, and Theorem 6.6 shows that the right owner
split is:

- `source-facing`: the regularizer `x ↦ λ ‖x‖₁`,
- `core/canonical`: mathlib's `WithLp 1` norm on the finite product, together with the Chapter 6
  owners `absolute_value_penalty`, `PiLp.separableSum`, and
  `prox_separableSum_eq_singleton_iff_coordinatewise`,
- `bridge/view`: the coordinate formula `‖x‖₁ = ∑ i, |x i|`.

Accordingly, this file keeps the source-facing notation `‖x‖₁`, with the raw owner exposed as the
short canonical name `EuclideanSpace.l1Norm`. Its coordinate sum formula is derived API. -/

namespace EuclideanSpace

/-- The Euclidean `ℓ¹` norm on a finite product, specializing to `ℝ^n` when `ι = Fin n`. -/
abbrev l1Norm (x : E) : ℝ :=
  ‖toLp 1 fun i ↦ x i‖

/-- The Euclidean `ℓ¹` norm is the finite sum of the coordinate absolute values. -/
@[simp] theorem l1Norm_eq_sum_abs (x : E) :
    l1Norm x = ∑ i, |x i| := by
  rw [l1Norm, PiLp.norm_eq_sum]
  · simp
  · norm_num

end EuclideanSpace

/-- Textbook notation for the Euclidean `ℓ¹` norm on a finite product. -/
notation "‖" x "‖₁" => EuclideanSpace.l1Norm x

-- Proof sketch: unfold `separableSum` and `absolute_value_penalty`, then identify the resulting
-- finite sum of absolute values with the `ℓ¹` norm in Euclidean coordinates.
/-- Bridge theorem: the canonical separable-sum owner for the scalar penalty `t ↦ λ |t|` is the
Euclidean `ℓ¹` regularizer `x ↦ λ ‖x‖₁` on a finite product, specializing to `ℝ^n` when
`ι = Fin n`. -/
theorem separableSum_absolute_value_penalty_eq_l1_norm_penalty
    (lam : ℝ) (x : E) :
    separableSum (fun _ : ι ↦ absolute_value_penalty lam) x = ((lam * ‖x‖₁ : ℝ) : EReal) := by
  rw [separableSum, EuclideanSpace.l1Norm_eq_sum_abs]
  simp only [absolute_value_penalty_apply]
  have hsum :
      (∑ i, ((lam * |x i| : ℝ) : EReal)) = ((∑ i, lam * |x i| : ℝ) : EReal) := by
    classical
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
        simpa [hi, EReal.coe_add] using
          congrArg (fun t : EReal ↦ (((lam * |x i| : ℝ) : EReal) + t)) ih
  calc
    (∑ i, ((lam * |x i| : ℝ) : EReal)) = ((∑ i, lam * |x i| : ℝ) : EReal) := hsum
    _ = ((lam * ∑ i, |x i| : ℝ) : EReal) := by
      congr 1
      simpa using (Finset.mul_sum Finset.univ (fun i : ι ↦ |x i|) lam).symm

-- Proof sketch: rewrite the Euclidean `ℓ¹` penalty using
-- `separableSum_absolute_value_penalty_eq_l1_norm_penalty`, apply
-- `prox_separableSum_eq_singleton_iff_coordinatewise` to the constant family
-- `absolute_value_penalty lam`, use
-- `prox_absolute_value_penalty_eq_singleton_soft_thresholding` in each coordinate, and
-- reassemble the unique minimizer as the Euclidean vector `T_[λ] x`.
-- The source's strict
-- positivity assumption is redundant for the minimizer-set identity itself, so the canonical Lean
-- statement keeps only `0 ≤ λ`.
/-- Example 6.8: for the Euclidean `ℓ¹` regularizer `x ↦ λ ‖x‖₁` on a finite Euclidean product,
specializing to `ℝ^n` when `ι = Fin n`, the proximal mapping at `x` is the singleton obtained by
coordinatewise soft-thresholding. -/
theorem prox_euclidean_l1_eq_singleton_softThreshold
    {lam : ℝ} (hlam : 0 ≤ lam) (x : E) :
    prox[fun y : E ↦ ((lam * ‖y‖₁ : ℝ) : EReal)] x =
      {T_[lam] x} := by
  have hproper_abs : IsProperExtendedRealFunction (absolute_value_penalty lam) := by
    refine ⟨?_, ?_⟩
    · intro t
      simpa [absolute_value_penalty_apply, EReal.coe_mul] using EReal.coe_ne_bot (lam * |t|)
    · refine ⟨0, ?_⟩
      rw [mem_effective_domain]
      simp [absolute_value_penalty_apply]
  have hpen :
      (PiLp.separableSum (fun _ : ι ↦ absolute_value_penalty lam) : E → EReal) =
        fun y : E ↦ ((lam * ‖y‖₁ : ℝ) : EReal) :=
    funext (separableSum_absolute_value_penalty_eq_l1_norm_penalty lam)
  simpa [hpen] using
    (prox_separableSum_eq_singleton_iff_coordinatewise
      (fun _ : ι ↦ absolute_value_penalty lam)
      (fun _ ↦ hproper_abs)
      x
      (T_[lam] x)).2
      (fun i ↦ by
        simpa using prox_absolute_value_penalty_eq_singleton_soft_thresholding lam hlam (x i))

end
