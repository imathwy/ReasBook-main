import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

section

variable {ι 𝕜 E : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [AddCommMonoid E] [MulActionWithZero 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.2.1 says that a finite linear combination of proper convex functions with
  nonnegative coefficients is convex.
- `core/canonical`: the chapter owner abstractions are `Function.IsProper`,
  `Function.IsConvex`, the properness consequence `Function.IsProper.bot_lt`, and the
  finite-sum bridge theorem `Function.isConvex_sum_of_bot_lt`.
- `bridge/view`: the owner-level bridge uses scalar coefficients `w : ι → 𝕜` with primitive
  nonnegativity assumptions `0 ≤ w i`, while the textbook positive-coefficient form appears as the
  source-facing companion.
- Primitive data vs derived API: the source-facing theorem uses the support `s`, the family `f`,
  the coefficient function `w`, and properness only on positively weighted summands. The
  owner bridge replaces properness by the derived pointwise `⊥`-exclusion needed only for
  nonzero-weight summands.

Domain-style sampling used here:
- the owner predicates `Function.IsProper` and `Function.IsConvex` from the earlier Section 4
  items `Definition_4_6` and `Theorem_4_2`;
- the owner companion `Function.IsProper.bot_lt` from `Definition_4_6`;
- the chapter owner bridge theorem `Function.isConvex_sum_of_bot_lt` from `Theorem_5_2`;
- the owner constructor `Function.IsConvex.smul_nonneg` from `Theorem_5_2`;
- the chapter `WithBotTop` multiplication boundary behavior from `EOrder/Mul`.
- mathlib's real-valued owner theorem `ConvexOn.smul` as the matching scalar-multiple pattern.

Layer target: owner-first. The canonical public bridge is the primitive nonnegative-weight
finite-sum theorem with nonzero-weight `⊥`-exclusion, while the textbook positive-coefficient
properness form remains as a source-facing companion.
-/

omit [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜] in
private theorem bot_lt_smul_of_nonneg {a : 𝕜} (ha : 0 ≤ a) {b : WithBotTop 𝕜} (hb : ⊥ < b) :
    ⊥ < a • b := by
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simp
  · cases b using WithBotTop.rec with
    | bot =>
        exact (not_lt_of_ge bot_le hb).elim
    | coe x =>
        simpa [WithBotTop.smul_def, WithBotTop.coe_mul] using (WithBotTop.bot_lt_coe (a * x))
    | top =>
        simp [WithBotTop.smul_def, WithBotTop.coe_mul_top_of_pos ha_pos]

private theorem isConvex_sum_smul_nonneg_core
    (s : Finset ι) (f : ι → E → WithBotTop 𝕜) (w : ι → 𝕜)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hf_bot : ∀ i ∈ s, w i ≠ 0 → ∀ x : E, ⊥ < f i x)
    (hf_convex : ∀ i ∈ s, Function.IsConvex 𝕜 (f i)) :
    Function.IsConvex 𝕜 (s.sum (fun i ↦ w i • f i)) := by
  refine Function.isConvex_sum_of_bot_lt s (fun i ↦ w i • f i) ?_ ?_
  · intro i hi x
    by_cases hwi : w i = 0
    · simp [hwi, Pi.smul_apply, WithBotTop.smul_def]
    · simpa [Pi.smul_apply] using bot_lt_smul_of_nonneg (hw i hi) (hf_bot i hi hwi x)
  · intro i hi
    exact (hf_convex i hi).smul_nonneg (hw i hi)

namespace Function

-- Proof sketch: finite weighted sums are handled directly at the scalar layer `𝕜`: nonnegative
-- coefficients preserve convexity via `IsConvex.smul_nonneg`, and only nonzero coefficients need
-- pointwise `⊥`-exclusion for the finite-sum bridge.
/-- Owner-level weighted-sum bridge: a finite sum of nonnegative scalar multiples of convex
`WithBotTop 𝕜`-valued functions is convex provided every nonzero-weight summand is everywhere
strictly above `⊥`. -/
theorem isConvex_sum_smul_nonneg
    (s : Finset ι) (f : ι → E → WithBotTop 𝕜) (w : ι → 𝕜)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hf_bot : ∀ i ∈ s, w i ≠ 0 → ∀ x : E, ⊥ < f i x)
    (hf_convex : ∀ i ∈ s, IsConvex 𝕜 (f i)) :
    IsConvex 𝕜 (s.sum (fun i ↦ w i • f i)) :=
  isConvex_sum_smul_nonneg_core s f w hw hf_bot hf_convex

/-- Text 5.2.1: a finite nonnegative-weighted sum of proper convex `WithBotTop 𝕜`-valued functions
is convex. Only the positively weighted summands need be proper; zero coefficients add no
mathematical content. The source `R^n` formulation is the specialization to `𝕜 = ℝ`,
`s = Finset.univ`, and `E = EuclideanSpace ℝ (Fin n)`. -/
theorem isConvex_weighted_sum_of_nonnegative
    (s : Finset ι) (f : ι → E → WithBotTop 𝕜) (w : ι → 𝕜)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hf_proper : ∀ i ∈ s, 0 < w i → IsProper (f i))
    (hf_convex : ∀ i ∈ s, IsConvex 𝕜 (f i)) :
    IsConvex 𝕜 (s.sum (fun i ↦ w i • f i)) := by
  exact isConvex_sum_smul_nonneg s f w hw
    (fun i hi hwi x ↦
      (hf_proper i hi (lt_of_le_of_ne (hw i hi) (by simpa using hwi.symm))).bot_lt x)
    hf_convex

/-- A finite nonnegative-weighted sum of convex `WithBotTop 𝕜`-valued functions is convex as soon
as every positively weighted summand is everywhere strictly above `⊥`. This is the owner-near
source-facing bridge behind `Function.isConvex_weighted_sum_of_nonnegative`. -/
theorem isConvex_weighted_sum_of_nonnegative_of_bot_lt
    (s : Finset ι) (f : ι → E → WithBotTop 𝕜) (w : ι → 𝕜)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hf_bot : ∀ i ∈ s, 0 < w i → ∀ x : E, ⊥ < f i x)
    (hf_convex : ∀ i ∈ s, IsConvex 𝕜 (f i)) :
    IsConvex 𝕜 (s.sum (fun i ↦ w i • f i)) :=
  isConvex_sum_smul_nonneg s f w hw
    (fun i hi hwi x ↦ hf_bot i hi (lt_of_le_of_ne (hw i hi) (by simpa using hwi.symm)) x)
    hf_convex

end Function

end
