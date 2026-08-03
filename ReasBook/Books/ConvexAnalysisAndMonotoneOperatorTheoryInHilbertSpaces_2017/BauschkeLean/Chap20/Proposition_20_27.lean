import Mathlib
import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap20.Definition_20_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace Function

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A single-valued operator is hemicontinuous when every scalar slice
`α ↦ ⟪z, A (x + α • y)⟫_ℝ` is right-continuous at `0`. -/
def IsHemicontinuous (A : H → H) : Prop :=
  ∀ x y z : H,
    ContinuousWithinAt (fun α : ℝ ↦ ⟪z, A (x + α • y)⟫_ℝ) (Set.Ioi 0) 0

-- Proof sketch: unfold `Function.IsHemicontinuous` and `ContinuousWithinAt`; this rewrites the
-- right-continuity condition exactly as the textbook right-limit formula along `α ↓ 0`.
/-- The hemicontinuity condition is equivalent to the textbook right-limit formulation
`lim_{α ↓ 0} ⟪z, A (x + α • y)⟫ = ⟪z, A x⟫`. -/
theorem isHemicontinuous_iff_tendsto (A : H → H) :
    A.IsHemicontinuous ↔
      ∀ x y z : H,
        Filter.Tendsto (fun α : ℝ ↦ ⟪z, A (x + α • y)⟫_ℝ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ⟪z, A x⟫_ℝ) :=
by
  constructor
  · intro h x y z
    simpa [ContinuousWithinAt, zero_smul] using h x y z
  · intro h x y z
    simpa [ContinuousWithinAt, zero_smul] using h x y z

/-- Helper for Proposition 20.27: the Minty inequality tested on the ray
`x + α • (u - A x)` forces the residual inner product to be nonpositive. -/
private lemma residualInner_nonpos_of_mintyRay
    (A : H → H) {x u : H}
    (hrel : ∀ y : H, 0 ≤ ⟪x - y, u - A y⟫_ℝ) {α : ℝ} (hα : 0 < α) :
    ⟪u - A x, u - A (x + α • (u - A x))⟫_ℝ ≤ 0 := by
  -- Test the Minty relation at the textbook ray point.
  have hray := hrel (x + α • (u - A x))
  have hrewrite :
      ⟪x - (x + α • (u - A x)), u - A (x + α • (u - A x))⟫_ℝ =
        (-α) * ⟪u - A x, u - A (x + α • (u - A x))⟫_ℝ := by
    calc
      ⟪x - (x + α • (u - A x)), u - A (x + α • (u - A x))⟫_ℝ
          = ⟪-(α • (u - A x)), u - A (x + α • (u - A x))⟫_ℝ := by
              congr 1
              abel_nf
      _ = ⟪(-α) • (u - A x), u - A (x + α • (u - A x))⟫_ℝ := by
            rw [← neg_smul]
      _ = (-α) * ⟪u - A x, u - A (x + α • (u - A x))⟫_ℝ := by
            rw [real_inner_smul_left]
  rw [hrewrite] at hray
  nlinarith

/-- Helper for Proposition 20.27: hemicontinuity gives the right-limit of the residual inner
product along the Minty ray. -/
private lemma residualInner_tendsto_of_hemicontinuous
    (A : H → H) (hA_hemi : A.IsHemicontinuous) (x d u : H) :
    Filter.Tendsto (fun α : ℝ ↦ ⟪d, u - A (x + α • d)⟫_ℝ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ⟪d, u - A x⟫_ℝ) := by
  -- First obtain the textbook right-limit for `α ↦ ⟪d, A (x + α • d)⟫`.
  have hslice :
      Filter.Tendsto (fun α : ℝ ↦ ⟪d, A (x + α • d)⟫_ℝ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ⟪d, A x⟫_ℝ) :=
    (isHemicontinuous_iff_tendsto A).1 hA_hemi x d d
  -- Then subtract that slice from the constant `⟪d, u⟫`.
  simpa [inner_sub_right] using hslice.const_sub ⟪d, u⟫_ℝ

/-- Helper for Proposition 20.27: the Minty relation against every graph point of a monotone
hemicontinuous singleton-valued operator forces `u = A x`. -/
private lemma eq_of_mintyRelated
    (A : H → H) (hA_hemi : A.IsHemicontinuous) {x u : H}
    (hrel : ∀ y : H, 0 ≤ ⟪x - y, u - A y⟫_ℝ) :
    u = A x := by
  let d : H := u - A x
  -- The Minty ray gives a nonpositive residual for every `α > 0`.
  have hnonpos : ∀ {α : ℝ}, 0 < α → ⟪d, u - A (x + α • d)⟫_ℝ ≤ 0 := by
    intro α hα
    simpa [d] using residualInner_nonpos_of_mintyRay A hrel hα
  -- Hemicontinuity identifies the right-limit of that residual.
  have hlim :
      Filter.Tendsto (fun α : ℝ ↦ ⟪d, u - A (x + α • d)⟫_ℝ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ⟪d, u - A x⟫_ℝ) := by
    simpa [d] using residualInner_tendsto_of_hemicontinuous A hA_hemi x d u
  have hEventually :
      ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ⟪d, u - A (x + α • d)⟫_ℝ ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    exact hnonpos hα
  -- Passing to the limit forces the residual norm square to vanish.
  have hlimit_nonpos : ⟪d, u - A x⟫_ℝ ≤ 0 :=
    le_of_tendsto_of_frequently hlim hEventually.frequently
  have hnorm_sq_nonpos : ‖d‖ ^ 2 ≤ 0 := by
    simpa [d, real_inner_self_eq_norm_sq] using hlimit_nonpos
  have hnorm_zero : ‖d‖ = 0 := by
    nlinarith [sq_nonneg ‖d‖, hnorm_sq_nonpos]
  have hd_zero : d = 0 := norm_eq_zero.mp hnorm_zero
  have hux : u - A x = 0 := by
    simpa [d] using hd_zero
  exact sub_eq_zero.mp hux

-- Proof sketch: use the characterization of maximal monotonicity from Definition 20.20. If
-- `(x, u)` is monotonically related to the singleton-valued graph of `A`, test the inequality at
-- points `x + α • (u - A x)` for `α > 0`; monotonicity gives the sign condition, and
-- hemicontinuity lets `α ↓ 0` to deduce `‖u - A x‖² ≤ 0`, hence `u = A x`.
/-- Proposition 20.27: a monotone hemicontinuous single-valued operator on a real Hilbert space is
maximally monotone when viewed as its associated singleton-valued set-valued operator. -/
theorem toSetValuedOperator_isMaximallyMonotone_of_monotone_hemicontinuous
    (A : H → H) (hA_mono : A.toSetValuedOperator.IsMonotone) (hA_hemi : A.IsHemicontinuous) :
    Maximal SetValuedOperator.IsMonotone A.toSetValuedOperator := by
  -- Rewrite maximality into the Minty graph-membership criterion.
  rw [SetValuedOperator.maximal_iff_mem_iff]
  intro x u
  constructor
  · intro hu y v hv
    -- Singleton membership reduces the forward direction to monotonicity of `A`.
    rw [SetValuedOperator.isMonotone_iff] at hA_mono
    simpa [Function.toSetValuedOperator_apply] using hA_mono hu hv
  · intro hrel
    -- After removing singleton memberships, the reverse direction is exactly the Minty ray lemma.
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
    apply eq_of_mintyRelated A hA_hemi
    intro y
    exact hrel (y := y) (v := A y) (by simp [Function.toSetValuedOperator_apply])

end Function
