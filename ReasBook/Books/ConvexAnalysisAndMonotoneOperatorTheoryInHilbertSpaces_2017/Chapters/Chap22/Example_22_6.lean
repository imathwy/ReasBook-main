import Mathlib
import BauschkeLean.Chap04.Definition_4_1
import BauschkeLean.Chap22.Definition_22_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace SetValuedOperator

-- Semantic recall: `lean_leansearch` did not surface a monotone-operator owner for this affine
-- perturbation statement. Local Chapter 20/22 precedent records single-valued monotonicity via
-- `SetValuedOperator.ofFunction`, with the target owners `IsStrictlyMonotone` and
-- `IsStronglyMonotone`.

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Example 22.6: normalize the affine perturbation difference into the
`identity + perturbation` form used by both monotonicity estimates. -/
lemma perturbedDifference_eq (x y tx ty : H) (α : ℝ) :
    (x + α • tx) - (y + α • ty) = (x - y) + α • (tx - ty) := by
  -- Rearranging the two affine terms exposes the common displacement and perturbation pieces.
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

omit [InnerProductSpace ℝ H] in
/-- Helper for Example 22.6: a strict contraction perturbation leaves a positive identity margin. -/
lemma strictMargin_pos_of_strictContraction (dx dT : H) {α : ℝ}
    (hdx_pos : 0 < ‖dx‖) (hdT_lt : ‖dT‖ < ‖dx‖) (hα_abs : |α| ≤ 1) :
    0 < ‖dx‖ ^ 2 - |α| * ‖dx‖ * ‖dT‖ := by
  -- Bounding `|α|` by `1` keeps the perturbation strictly smaller than the identity term.
  have hscaled_le : |α| * ‖dT‖ ≤ ‖dT‖ := by
    have : |α| * ‖dT‖ ≤ 1 * ‖dT‖ :=
      mul_le_mul_of_nonneg_right hα_abs (norm_nonneg dT)
    simpa using this
  have hscaled_lt : |α| * ‖dT‖ < ‖dx‖ := lt_of_le_of_lt hscaled_le hdT_lt
  have hgap_pos : 0 < ‖dx‖ - |α| * ‖dT‖ := by
    nlinarith
  nlinarith

/-- Helper for Example 22.6: an absolute bound on the perturbation term yields the desired
lower bound for the affine inner product. -/
lemma perturbationLowerBound_of_abs_bound (dx dT : H) {α M : ℝ}
    (hbound : abs (α * inner ℝ dx dT) ≤ M) :
    ‖dx‖ ^ 2 - M ≤ inner ℝ dx (dx + α • dT) := by
  -- The inner product splits into the identity contribution plus the controlled perturbation.
  have hperturb_lower : -M ≤ α * inner ℝ dx dT := (abs_le.mp hbound).1
  rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  nlinarith

/-- Helper for Example 22.6: a Lipschitz bound on the perturbation controls the scalar error term
by `|α| * β * ‖dx‖^2`. -/
lemma lipschitzPerturbationAbsBound (dx dT : H) {α β : ℝ}
    (hβ_nonneg : 0 ≤ β) (hdT_le : ‖dT‖ ≤ β * ‖dx‖) :
    abs (α * inner ℝ dx dT) ≤ |α| * β * ‖dx‖ ^ 2 := by
  -- Cauchy-Schwarz turns the geometric bound on `dT` into the scalar estimate needed downstream.
  have hβdx_nonneg : 0 ≤ β * ‖dx‖ := mul_nonneg hβ_nonneg (norm_nonneg dx)
  calc
    abs (α * inner ℝ dx dT) = |α| * abs (inner ℝ dx dT) := by
      rw [abs_mul]
    _ ≤ |α| * (‖dx‖ * ‖dT‖) := by
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm dx dT) (abs_nonneg α)
    _ ≤ |α| * (‖dx‖ * (β * ‖dx‖)) := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg α)
      exact mul_le_mul_of_nonneg_left hdT_le (norm_nonneg dx)
    _ = |α| * β * ‖dx‖ ^ 2 := by
      nlinarith [norm_nonneg dx, hβ_nonneg, hβdx_nonneg]

/-- Helper for Example 22.6: if `D` is a nonempty subset of `ℋ`,
`T : D → H`,
let
`α ∈ [-1, 1]`, and set `A = Id + α T`. If `T` is strictly nonexpansive, then the singleton-valued
operator attached to `A` is strictly monotone. The source's nonempty-domain hypothesis is
redundant for this owner-level conclusion, so it is omitted. -/
theorem ofFunction_id_add_smul_isStrictlyMonotone_of_isStrictlyNonexpansiveOn
    {D : Set H} {T : D → H} (hT : IsStrictlyNonexpansiveOn T) {α : ℝ}
    (hα : α ∈ Set.Icc (-1 : ℝ) 1) :
    (ofFunction D (fun x : D ↦ x + α • T x)).IsStrictlyMonotone := by
  have hα_abs : |α| ≤ 1 := by
    simpa [abs_le] using hα
  intro x u y v hu hv hxy
  -- Unpack the singleton graph witnesses so the argument runs on ambient vectors.
  rcases hu with ⟨hx, rfl⟩
  rcases hv with ⟨hy, rfl⟩
  let dx : H := x - y
  let dT : H := T ⟨x, hx⟩ - T ⟨y, hy⟩
  have hxy' : (⟨x, hx⟩ : D) ≠ ⟨y, hy⟩ := fun h ↦ hxy (congrArg Subtype.val h)
  have hdT_lt : ‖dT‖ < ‖dx‖ := by
    simpa [dx, dT] using hT ⟨x, hx⟩ ⟨y, hy⟩ hxy'
  have hdx_pos : 0 < ‖dx‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hstrict_margin : 0 < ‖dx‖ ^ 2 - |α| * ‖dx‖ * ‖dT‖ := by
    -- The strict nonexpansive hypothesis keeps the perturbation strictly smaller than the identity.
    exact strictMargin_pos_of_strictContraction dx dT hdx_pos hdT_lt hα_abs
  have hperturb_abs :
      abs (α * inner ℝ dx dT) ≤ |α| * ‖dx‖ * ‖dT‖ := by
    -- Cauchy-Schwarz bounds the perturbation by the product of the two norm gaps.
    calc
      abs (α * inner ℝ dx dT) = |α| * abs (inner ℝ dx dT) := by rw [abs_mul]
      _ ≤ |α| * (‖dx‖ * ‖dT‖) := by
        exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm dx dT) (abs_nonneg α)
      _ = |α| * ‖dx‖ * ‖dT‖ := by ring
  have hnormalize :
      (x + α • T ⟨x, hx⟩) - (y + α • T ⟨y, hy⟩) = dx + α • dT := by
    -- Route correction: use one reusable normalization lemma instead of an inline `show` rewrite.
    simpa [dx, dT] using perturbedDifference_eq x y (T ⟨x, hx⟩) (T ⟨y, hy⟩) α
  have hlower :
      ‖dx‖ ^ 2 - |α| * ‖dx‖ * ‖dT‖ ≤
        inner ℝ dx ((x + α • T ⟨x, hx⟩) - (y + α • T ⟨y, hy⟩)) := by
    -- The generic lower-bound lemma now packages the inner-product algebra in one place.
    simpa [hnormalize] using
      perturbationLowerBound_of_abs_bound dx dT
        (α := α) (M := |α| * ‖dx‖ * ‖dT‖) hperturb_abs
  exact lt_of_lt_of_le hstrict_margin hlower

/-- Helper for Example 22.6: if `D` is a nonempty subset of `ℋ`,
`T : D → H`,
let
`α ∈ [-1, 1]`, and set `A = Id + α T`. If `T` is `β`-Lipschitz continuous with `β ∈ [0,1[`,
then the singleton-valued operator attached to `A` is strongly monotone with modulus
`1 - |α| β`. The source's nonempty-domain hypothesis is redundant for this owner-level
conclusion, so it is omitted. -/
theorem ofFunction_id_add_smul_isStronglyMonotone_of_lipschitzWith
    {D : Set H} {T : D → H} {β : ℝ}
    (hT : LipschitzWith (Real.toNNReal β) T) (hβ : β ∈ Set.Ico (0 : ℝ) 1) {α : ℝ}
    (hα : α ∈ Set.Icc (-1 : ℝ) 1) :
    (ofFunction D (fun x : D ↦ x + α • T x)).IsStronglyMonotone (1 - |α| * β) := by
  have hβ_nonneg : 0 ≤ β := hβ.1
  have hβ_lt_one : β < 1 := hβ.2
  have hα_abs : |α| ≤ 1 := by
    simpa [abs_le] using hα
  refine ⟨by nlinarith, ?_⟩
  intro x u y v hu hv
  -- Unpack the singleton graph witnesses so the strong monotonicity estimate is pointwise.
  rcases hu with ⟨hx, rfl⟩
  rcases hv with ⟨hy, rfl⟩
  let dx : H := x - y
  let dT : H := T ⟨x, hx⟩ - T ⟨y, hy⟩
  have hdT_le : ‖dT‖ ≤ β * ‖dx‖ := by
    -- Translate the Lipschitz hypothesis on the subtype back to the ambient norm difference.
    simpa [dx, dT, Subtype.dist_eq, dist_eq_norm, Real.toNNReal_of_nonneg hβ_nonneg,
      mul_comm, mul_left_comm, mul_assoc] using hT.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩
  have hperturb_abs :
      abs (α * inner ℝ dx dT) ≤ |α| * β * ‖dx‖ ^ 2 := by
    exact lipschitzPerturbationAbsBound dx dT hβ_nonneg hdT_le
  have hnormalize :
      (x + α • T ⟨x, hx⟩) - (y + α • T ⟨y, hy⟩) = dx + α • dT := by
    -- Reuse the same affine normalization as in the strict-monotonicity proof.
    simpa [dx, dT] using perturbedDifference_eq x y (T ⟨x, hx⟩) (T ⟨y, hy⟩) α
  have hbase :
      ‖dx‖ ^ 2 - |α| * β * ‖dx‖ ^ 2 ≤
        inner ℝ dx ((x + α • T ⟨x, hx⟩) - (y + α • T ⟨y, hy⟩)) := by
    -- The generic lower-bound lemma reduces the final step to scalar arithmetic.
    simpa [hnormalize] using
      perturbationLowerBound_of_abs_bound dx dT
        (α := α) (M := |α| * β * ‖dx‖ ^ 2) hperturb_abs
  have hlower :
      (1 - |α| * β) * ‖dx‖ ^ 2 ≤
        inner ℝ dx ((x + α • T ⟨x, hx⟩) - (y + α • T ⟨y, hy⟩)) := by
    nlinarith
  simpa [dx] using hlower

/-- Example 22.6: if `D` is a nonempty subset of `ℋ`, `T : D → H`, `α ∈ [-1, 1]`, and
`A = Id + α T`, then strict nonexpansiveness of `T` implies strict monotonicity of `A`,
while `β`-Lipschitz continuity of `T` for `β ∈ [0,1[` implies strong monotonicity of `A`
with modulus `1 - |α| β`. The source's nonempty-domain hypothesis is redundant for this
owner-level conjunction, so it is omitted. -/
theorem ofFunction_id_add_smul_strictAndStrongMonotonicity
    {D : Set H} {T : D → H} :
    ( (∀ {α : ℝ}, IsStrictlyNonexpansiveOn T →
          α ∈ Set.Icc (-1 : ℝ) 1 →
            (ofFunction D (fun x : D ↦ x + α • T x)).IsStrictlyMonotone) ∧
      (∀ {β : ℝ}, LipschitzWith (Real.toNNReal β) T →
          β ∈ Set.Ico (0 : ℝ) 1 → ∀ {α : ℝ}, α ∈ Set.Icc (-1 : ℝ) 1 →
            (ofFunction D (fun x : D ↦ x + α • T x)).IsStronglyMonotone (1 - |α| * β)) ) := by
  constructor
  · intro α hT hα
    exact ofFunction_id_add_smul_isStrictlyMonotone_of_isStrictlyNonexpansiveOn hT hα
  · intro β hT hβ α hα
    exact ofFunction_id_add_smul_isStronglyMonotone_of_lipschitzWith hT hβ hα

end SetValuedOperator
