import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_26 (from Chap02) -/
/- Definition 2.26 is a source-facing recall in the convex-geometry domain of epigraphs in `ℝ²`.

Primary domain:
- the epigraph of the reciprocal map `x ↦ 1 / x` on the positive ray.

Sampled owner-style declarations:
- `reciprocalEpigraphOnPositiveRay`, the Chapter 2 owner set for the textbook region `Q`;
- `mem_reciprocalEpigraphOnPositiveRay_iff`, the owner membership criterion;
- `ConvexOn.convex_epigraph`, the mathlib owner theorem expressing the general epigraph style;
- `convexOn_iff_convex_epigraph`, the canonical bridge between convexity and epigraph convexity.

Best owner abstraction:
- `reciprocalEpigraphOnPositiveRay : Set (ℝ × ℝ)`

Primitive data:
- the positivity condition `0 < x.1`;
- the epigraph inequality `x.2 ≥ 1 / x.1`.

Derived API:
- the additional displayed condition `0 ≤ x.2`, since `0 < x.1` implies `0 < 1 / x.1`.

Source/core/bridge triage:
- source-facing: the textbook set `Q = {(x₁, x₂) | 0 < x₁, x₂ ≥ 1 / x₁}`;
- core/canonical: `reciprocalEpigraphOnPositiveRay`;
- bridge/view: `mem_reciprocalEpigraphOnPositiveRay_iff`.

This recall file therefore introduces no parallel local definition such as
`positiveReciprocalEpigraph`; downstream use should refer directly to the owner set and its
companion membership theorem. -/

recall reciprocalEpigraphOnPositiveRay : Set (ℝ × ℝ)

recall mem_reciprocalEpigraphOnPositiveRay_iff
    (x : ℝ × ℝ) :
    x ∈ reciprocalEpigraphOnPositiveRay ↔ 0 < x.1 ∧ x.2 ≥ 1 / x.1

/-! ### Lemma_2_26 (from Chap02) -/
noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type v} [Fintype ι] [Nonempty ι]
variable {m : ℕ} {μ L : ℝ}

namespace SmoothMinimaxProblem

section

variable (problem : SmoothMinimaxProblem E ι μ L)

local notation "modelValue" =>
  fun xBar γ ↦
    sInf
      ((quadraticallyRegularizedObjective
          (problem.affineApproximation xBar)
          γ
          xBar) '' problem.feasibleSet)

local notation "valueFunction" =>
  sInf (problem '' problem.feasibleSet)

local notation "relativeGap" =>
  fun xBar ↦ problem xBar - valueFunction

/-
Primary domain: the scalar stopping inequality for regularized local-model values on the owner
smooth minimax problem.

Owner abstractions sampled before refining:
- `SmoothMinimaxProblem` from `Definition_2_38.lean`, the owner fixed-feasible-set minimax
  problem;
- `SmoothMinimaxProblem.affineApproximation`, the owner local affine model at `xBar`;
- `quadraticallyRegularizedObjective` from `Definition_1_4_17.lean`, the owner quadratic
  regularization of that affine model;
- `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` from
  `Definition_2_47.lean`, the later bridge/view which will reuse this owner theorem.

Best owner abstraction:
- `problem : SmoothMinimaxProblem E ι μ L`.

Source/core/bridge triage:
- source-facing in this namespace: the stopping comparison for a smooth minimax problem;
- core/canonical: the owner regularized model values built from `problem.affineApproximation`;
- bridge/view: the fixed-`t` constrained problem in the second half of this file.

Primitive data:
- the owner minimax problem `problem`;
- the base point `xBar`;
- the scalars `α` and `Qf`.

Derived API:
- the regularized model values `modelValue xBar γ`;
- the optimal value `valueFunction`;
- the relative gap `relativeGap xBar`.
-/
/-- On the canonical smooth-minimax owner layer, if the `μ`-regularized model value at `xBar` is
bounded below by the `L`-regularized model value minus `(Q_f - 1)` times the current relative
gap, and if that relative gap is at most `(α / (Q_f - 1))` times the `L`-model value, then
`f^*(xBar; μ) ≥ (1 - α) f^*(xBar; L)`. -/
theorem stopping_condition_of_relativeGapBound
    {α Qf : ℝ} {xBar : E}
    (hQf : 1 < Qf)
    (hModelComparison :
      modelValue xBar μ ≥
        modelValue xBar L - (Qf - 1) * relativeGap xBar)
    (hRelativeGap :
      relativeGap xBar ≤
        (α / (Qf - 1)) * modelValue xBar L) :
    (1 - α) * modelValue xBar L ≤ modelValue xBar μ := by
  have hQf_sub : 0 < Qf - 1 := sub_pos.mpr hQf
  have hRelativeGap' :
      (Qf - 1) * relativeGap xBar ≤ α * modelValue xBar L := by
    have h :=
      mul_le_mul_of_nonneg_left hRelativeGap (le_of_lt hQf_sub)
    calc
      (Qf - 1) * relativeGap xBar ≤
          (Qf - 1) * ((α / (Qf - 1)) * modelValue xBar L) := h
      _ = α * modelValue xBar L := by
        field_simp [hQf_sub.ne']
  nlinarith [hModelComparison, hRelativeGap']

end

end SmoothMinimaxProblem

section

variable (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L) (t : ℝ)

local notation "parametricProblem" => problem.toParametricSmoothMinimaxProblem t

local notation "modelValue" => problem.regularizedModelValue t

local notation "valueFunction" =>
  sInf (parametricProblem '' (SmoothMinimaxProblem.feasibleSet parametricProblem))

local notation "relativeGap" => fun xBar ↦ parametricProblem xBar - valueFunction

/-
Primary domain: fixed-`t` regularized local-model values for the constrained max-type problem
attached to a smooth functional-constraint problem.

Owner abstractions sampled before refining:
- `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` from
  `Definition_2_47.lean`, the owner fixed-`t` smooth minimax problem;
- `SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue` from
  `Definition_2_47.lean`, the owner fixed-`t` regularized model value;
- `SmoothMinimaxProblem.stopping_condition_of_relativeGapBound` from this file, the owner
  minimax comparison theorem reused below;
- `ConstrainedMinimizationMethod.step1a` from `Algorithm_2_11.lean`, the later bridge/view
  packaging the same stopping inequality along the algorithmic trajectory.

Best owner abstraction:
- `parametricProblem : SmoothMinimaxProblem E (Fin (m + 1)) μ L`.

Source/core/bridge triage:
- source-facing: Lemma 2.26 for the fixed parameter `t` in the constrained problem;
- core/canonical: the owner smooth minimax problem `parametricProblem` and its theorem
  `parametricProblem.stopping_condition_of_relativeGapBound`;
- bridge/view: `ConstrainedMinimizationMethod.step1a`, which later reuses the same comparison.

Primitive data:
- the constrained problem `problem`;
- the scalar parameter `t`;
- the base point `xBar`;
- the scalars `α` and `Qf`.

Derived API:
- the owner local-model values `modelValue xBar γ`, recalled from
  `SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue`;
- the owner constrained optimal value `valueFunction`;
- the relative gap `relativeGap xBar`.

The refinement therefore keeps the public lemma at the source-facing fixed-`t` layer, recalls the
owner declaration `problem.regularizedModelValue t` for the local-model values, and reuses the
canonical smooth-minimax owner theorem instead of keeping a parallel local proof on the bridge
layer.
-/

/-- Lemma 2.26: for the fixed-`t` parametric minimax problem attached to a smooth functional
constraints problem, if the regularized `μ`-model value is bounded below by the regularized `L`
model value minus `(Q_f - 1)` times the current relative gap, and that relative gap is at most
`(α / (Q_f - 1)) f^*(t; xBar; L)`, then the stopping comparison
`f^*(t; xBar; μ) ≥ (1 - α) f^*(t; xBar; L)` holds. -/
-- Proof sketch: apply the owner minimax version of the same inequality to the fixed-`t` bridge
-- problem `parametricProblem`.
theorem stopping_condition_of_relativeGapBound
    {α Qf : ℝ} {xBar : E}
    (hQf : 1 < Qf)
    (hModelComparison :
      modelValue xBar μ ≥
        modelValue xBar L - (Qf - 1) * relativeGap xBar)
    (hRelativeGap :
      relativeGap xBar ≤
        (α / (Qf - 1)) * modelValue xBar L) :
    (1 - α) * modelValue xBar L ≤ modelValue xBar μ := by
  simpa [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue] using
    (problem.toParametricSmoothMinimaxProblem t).stopping_condition_of_relativeGapBound
      hQf hModelComparison hRelativeGap

end

/-! ### Proposition_2_26 (from Chap02) -/
open scoped ConvexAnalysis

/- 
Primary domain: one-variable secant estimates for convex value functions.

Owner abstractions sampled before refining:
* mathlib `ConvexOn`
* mathlib `ConvexOn.slope_mono_adjacent`
* mathlib `ConvexOn.secant_mono`
* chapter `extendedRealEffectiveDomain`
* chapter `extendedRealRealPart`

Best owner abstraction:
* `ConvexOn 𝕜 s f` on the ordered-field line

Primitive data:
* a function on the scalar line
* convexity on the ambient owner set

Derived API:
* the left-shifted secant lower bound below on the canonical ordered-field owner
* the finite-value `EReal` bridge via `extendedRealEffectiveDomain` and `extendedRealRealPart`

Source/core/bridge triage:
* source-facing: Proposition 2.26 for an extended-real value function with finite comparison points
* core/canonical: `ConvexOn 𝕜 s f` and `ConvexOn.secant_mono`
* bridge/view: restricting an `EReal`-valued function to its finite real part

The public file therefore keeps the source-facing finite-value statement and the owner scalar-line
secant theorem, but no parallel wrapper structure. The midpoint finite-value condition is derived
from convexity of the finite-value domain rather than stored as primitive data.
-/

namespace ConvexOn

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {s : Set 𝕜} {f : 𝕜 → 𝕜}

/-- A convex function on a convex subset of a linearly ordered field satisfies the left-shifted
secant lower bound obtained by comparing the secants over `[t₁ - Δ, t₁]` and `[t₁, t₂]`. -/
-- Proof sketch: if `Δ = 0`, the claim is immediate. For `Δ > 0`, apply
-- `ConvexOn.secant_mono` with base point `t₁`, after deriving `t₁ ∈ s` from convexity of `s`,
-- and rearrange the resulting secant inequality.
theorem secant_lower_bound_left_shift (hf : ConvexOn 𝕜 s f)
    {t1 t2 Delta : 𝕜} (hleft : t1 - Delta ∈ s) (ht2 : t2 ∈ s)
    (hDelta : 0 ≤ Delta) (ht : t1 < t2) :
    f (t1 - Delta) ≥
      f t1 + (Delta / (t2 - t1)) * (f t1 - f t2) := by
  rcases eq_or_lt_of_le hDelta with rfl | hDelta
  · simp
  have ht1 : t1 ∈ s := by
    exact hf.1.ordConnected.out hleft ht2 ⟨by linarith, ht.le⟩
  have hslope :
      (f t1 - f (t1 - Delta)) / Delta ≤ (f t2 - f t1) / (t2 - t1) := by
    have hsecant :=
      hf.secant_mono ht1 hleft ht2 (by linarith) ht.ne' (by linarith)
    convert hsecant using 1
    ring
  have hstep :
      f t1 - f (t1 - Delta) ≤
        ((f t2 - f t1) / (t2 - t1)) * Delta := by
    exact (div_le_iff₀ hDelta).1 hslope
  have hbound :
      f t1 - f (t1 - Delta) ≤
        (Delta / (t2 - t1)) * (f t2 - f t1) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hstep
  linarith

/-- If a convex function on a convex subset of a linearly ordered field is positive at `t₁` and
nonpositive at a right endpoint `t₂`, then necessarily `t₁ < t₂`, and the left-shifted secant
lower bound specialized to `t₂` gives a lower estimate at every `t₀ < t₁`. -/
theorem strict_lt_and_secant_lower_bound_of_nonpos_right
    (hf : ConvexOn 𝕜 s f) {t0 t1 t2 : 𝕜} (ht0 : t0 ∈ s) (ht2 : t2 ∈ s)
    (ht0t1 : t0 < t1) (ht1t2 : t1 ≤ t2)
    (hpos : 0 < f t1) (ht2_nonpos : f t2 ≤ 0) :
    t1 < t2 ∧
      f t0 ≥ f t1 + ((t1 - t0) / (t2 - t1)) * f t1 := by
  have ht1_ne_t2 : t1 ≠ t2 := by
    intro h
    exact not_le_of_gt hpos (by simpa [h] using ht2_nonpos)
  have ht1t2' : t1 < t2 :=
    lt_of_le_of_ne ht1t2 ht1_ne_t2
  let coeff : 𝕜 := (t1 - t0) / (t2 - t1)
  have hcoeff_nonneg : 0 ≤ coeff := by
    dsimp [coeff]
    exact div_nonneg (sub_nonneg.mpr ht0t1.le) (sub_nonneg.mpr ht1t2'.le)
  have hshift : t1 - (t1 - t0) = t0 := by
    ring
  have hleft : t1 - (t1 - t0) ∈ s := by
    simpa [hshift] using ht0
  have hsecant :
      f t1 + coeff * (f t1 - f t2) ≤ f t0 := by
    dsimp [coeff]
    simpa [hshift] using
      (hf.secant_lower_bound_left_shift
        hleft
        ht2
        (sub_nonneg.mpr ht0t1.le)
        ht1t2')
  have hdrop_term :
      coeff * f t1 ≤ coeff * (f t1 - f t2) := by
    refine mul_le_mul_of_nonneg_left ?_ hcoeff_nonneg
    linarith
  have hdrop :
      f t1 + coeff * f t1 ≤
        f t1 + coeff * (f t1 - f t2) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_left hdrop_term (f t1)
  refine ⟨ht1t2', ?_⟩
  simpa [coeff] using hdrop.trans hsecant

end

end ConvexOn

/-- Proposition 2.26: if an extended-real convex value function is finite at the secant endpoints,
then the same left-shifted secant lower bound holds for its finite real values. This is the
source-facing finite-value form used for functions such as `t ↦ f^*(t; x̄; γ)`. -/
theorem secant_lower_bound_left_shift_of_finite_values
    {f : ℝ → EReal}
    (hf : ConvexOn ℝ (dom f) (extendedRealRealPart f))
    {t1 t2 Delta : ℝ}
    (hleft : t1 - Delta ∈ dom f)
    (ht2 : t2 ∈ dom f)
    (hDelta : 0 ≤ Delta) (ht : t1 < t2) :
    extendedRealRealPart f (t1 - Delta) ≥
      extendedRealRealPart f t1 +
        (Delta / (t2 - t1)) * (extendedRealRealPart f t1 - extendedRealRealPart f t2) := by
  simpa using hf.secant_lower_bound_left_shift hleft ht2 hDelta ht
