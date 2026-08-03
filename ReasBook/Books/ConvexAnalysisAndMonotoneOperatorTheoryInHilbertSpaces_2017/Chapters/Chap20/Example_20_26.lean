import BauschkeLean.Chap01.Text_1_0_57
import BauschkeLean.Chap16.Example_16_13
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap20.Theorem_20_25

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise
open ERealFunction
open SetValuedOperator

universe u

namespace Set

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}

omit [CompleteSpace H] in
/-- Helper for Example 20.26: the indicator of a nonempty closed convex set belongs to `Γ₀(H)`. -/
private theorem setIndicator_mem_gammaZero_of_nonempty_isClosed_convex
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ι[C] ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  -- Closedness identifies the indicator as a lower semicontinuous `EReal`-valued function.
  have hindicator_lsc :
      LowerSemicontinuous (fun y ↦ ((ι[C]) y : EReal)) := by
    simpa using (lowerSemicontinuous_indicator_compl_top_iff_isClosed C).2 hC_closed
  -- The effective domain of the indicator is exactly the underlying set `C`.
  have hindicator_dom : effectiveDomain (ι[C]) = C := by
    ext y
    by_cases hy : y ∈ C <;> simp [ERealFunction.effectiveDomain, ERealFunction.indicator, hy]
  refine ⟨hindicator_lsc, ?_⟩
  -- Convexity of `C` transfers directly to convexity of the indicator on its effective domain.
  refine ⟨by simpa [hindicator_dom] using hC_nonempty, fun _ hy ↦ hy, ?_⟩
  intro y hy z hz a ha0 ha1
  have hyC : y ∈ C := by
    simpa [hindicator_dom] using hy
  have hzC : z ∈ C := by
    simpa [hindicator_dom] using hz
  have hayzC : a • y + (1 - a) • z ∈ C :=
    hC_convex hyC hzC ha0.le (sub_nonneg.mpr ha1.le) (by ring)
  simp [ERealFunction.indicator, hyC, hzC, hayzC]

/- Source/core/bridge triage:
- `source-facing`: Example 20.26 states maximal monotonicity for the normal cone operator `N[C]`.
- `core/canonical`: the owner abstraction is maximality for the standard monotonicity predicate on
  the normal cone operator `N[C]`.
- `bridge/view`: the proof passes through the indicator-function subdifferential theorem and the
  canonical identification `∂ ι[C] = N[C]`.

Primitive data: a nonempty closed convex set `C`, viewed canonically through the indicator
function `ι[C] ∈ Γ₀(H)`.
Derived API: maximal monotonicity of the normal cone operator `N[C]`, obtained by rewriting the
canonical owner theorem for `∂ ι[C]`. -/
-- Semantic recall note: `lean_leansearch` returned no direct mathlib owner for this example, and
-- the verified local canonical bridge is `subdifferential_setIndicator_eq_normalCone` together
-- with `subdifferential_isMaximallyMonotone_of_mem_gammaZero`.

-- Proof sketch: show that the indicator `ι_C` belongs to `Γ₀(H)` for a nonempty closed convex set
-- `C`, apply Moreau's theorem `subdifferential_isMaximallyMonotone_of_mem_gammaZero` to `ι_C`, and
-- then rewrite the resulting operator with `subdifferential_setIndicator_eq_normalCone`.
/-- Example 20.26: for a nonempty closed convex subset `C` of a real Hilbert space, the normal
cone operator `N[C]` is maximally monotone. -/
theorem normalCone_isMaximallyMonotone
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    Maximal IsMonotone (N[C]) := by
  -- First show that the indicator of `C` lies in `Γ₀(H)`, which is the hypothesis needed by
  -- Moreau's maximal-monotonicity theorem for subdifferentials.
  have hindicator : ι[C] ∈ Γ₀(H) :=
    setIndicator_mem_gammaZero_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  -- Then apply the owner theorem to `ι[C]` and transport the resulting operator through the
  -- canonical identification `∂ ι[C] = N[C]`.
  simpa [subdifferential_setIndicator_eq_normalCone C hC_nonempty] using
    subdifferential_isMaximallyMonotone_of_mem_gammaZero hindicator

end

end Set
