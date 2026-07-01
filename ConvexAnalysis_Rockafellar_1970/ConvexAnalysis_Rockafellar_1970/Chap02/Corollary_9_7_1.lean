import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_0_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise ENNReal NNReal Rockafellar

universe u v

section

variable {𝕜 : Type v} [NNNorm 𝕜]
variable {E : Type u} [SMul 𝕜 E]
variable {C : Set E} {a : 𝕜} {x : E}

/-- Generic bridge: any owner-level equality identifying a gauge sublevel set with a dilate yields
the corresponding pointwise membership equivalence. -/
theorem egauge_le_iff_mem_smul_of_sublevel_eq
    (hsublevel : {y : E | γ[𝕜](y | C) ≤ ‖a‖ₑ} = a • C) :
    γ[𝕜](x | C) ≤ ‖a‖ₑ ↔ x ∈ a • C := by
  simpa using congrArg (fun S : Set E ↦ x ∈ S) hsublevel

/-- Generic bridge: any owner-level equality identifying the gauge zero-level set with the
recession cone yields the corresponding pointwise membership equivalence. -/
theorem egauge_eq_zero_iff_mem_recessionCone_of_zeroLevel_eq
    [Zero 𝕜] [LE 𝕜] [HAdd E E E]
    (hzero : {y : E | γ[𝕜](y | C) = 0} = 0⁺[𝕜]C) :
    γ[𝕜](x | C) = 0 ↔ x ∈ 0⁺[𝕜] C := by
  simpa using congrArg (fun S : Set E ↦ x ∈ S) hzero

end

section

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [NNNorm 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 9.7.1 states that for a closed convex set `C ⊆ R^n` containing `0`,
  the gauge is closed, its positive sublevel sets are exactly the positive dilates `λ C`, and its
  zero set is the recession cone `0⁺ C`.
- `core/canonical`: the faithful owner for this corollary is the extended gauge
  `egauge 𝕜 C : E → ℝ≥0∞` on an additive ambient space with scalar action and ordered scalar
  layer, because the source allows nonabsorbent closed convex sets and the
  zero-level statement is false for the real-valued `gauge` on arbitrary sets. The chapter owner
  for the recession cone is `recessionCone`.
- `bridge/view`: the scalar-parameterized textbook notation `γ[𝕜](· | C)` is rendered by
  `egauge 𝕜 C`, while the recession notation is rendered by `0⁺[𝕜] C` on the owner side; on this
  ordered-field layer, specializing `𝕜 = ℝ` recovers the source scalar.

Domain-style sampling used here:
- `egauge`;
- `gauge_eq_sInf_dilates`;
- `egauge_lt_iff`;
- `egauge_le_of_mem_smul`;
- `Convex.mem_recessionCone_iff_forall_pos_inv_smul_mem`.

Primitive data vs derived API:
- primitive inputs: the set `C`; for the source-faithful `≤`-sublevel clause and the zero-level
  clause, closedness/convexity and `0 ∈ C` are all mathematically active owner hypotheses;
- derived outputs: lower semicontinuity of the gauge, the owner-level positive-sublevel and
  zero-level set equalities, and their pointwise bridge characterizations. The pointwise bridges
  are also exported in generic equality-driven form so they stay at the intrinsic set-owner layer
  instead of carrying closed/convex assumptions.

Layer target: this item stays `source-facing`, written directly in terms of the canonical extended
gauge and the existing chapter owner `recessionCone`, with the sublevel and zero-level clauses
first exposed as owner-level set equalities and then bridged to pointwise forms.

Ambient-space refinement: the recession-side bridge used in this item
(`Convex.mem_recessionCone_iff_forall_pos_inv_smul_mem`) and the Chapter 9 closure bridge layer
both live on an ordered-field topological-module interface. To keep the public API mathematically
credible without over-weakening assumptions, the three corollary clauses are stated on that same
owner-supported layer (field/order plus compatible topological module structure), while still
avoiding any finite-dimensional or coordinate-model specialization such as
`EuclideanSpace ℝ (Fin n)`.
-/

variable {C : Set E}

-- Proof sketch: apply the preceding closedness criterion from Section 9 to the indicator-plus-one
-- function of `C`, whose recession function is the gauge `γ(· | C)`. In Lean this is recorded as
-- lower semicontinuity of the canonical extended gauge `egauge 𝕜 C`.
/-- Corollary 9.7.1 (1): if `C` is a closed convex subset of `R^n`, then its gauge function
`γ[𝕜](· | C)`, formalized here as `egauge 𝕜 C`, is closed, expressed as lower
semicontinuity. -/
theorem egauge_lowerSemicontinuous (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C) :
    LowerSemicontinuous (γ[𝕜](· | C)) := sorry

-- Proof sketch: specialize the theorem cited in the textbook proof to
-- `f(x) = δ(x | C) + 1`. For closed convex `C` containing `0`, this gives the source-faithful
-- `≤`-sublevel description `{x | γ(x | C) ≤ λ} = λ C` for positive `λ`.
/-- Corollary 9.7.1 (2), owner-level set form: for every positive scalar `a : 𝕜`, the
`‖a‖ₑ`-sublevel set of the gauge of `C` is exactly the positive dilate `a • C`. -/
theorem egauge_sublevel_eq_smul
    (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C) (h0C : (0 : E) ∈ C)
    (a : 𝕜) (ha : 0 < a) :
    {x : E | γ[𝕜](x | C) ≤ ‖a‖ₑ} = a • C := sorry

/-- Corollary 9.7.1 (2), pointwise bridge form: for every positive scalar `a : 𝕜`, a point belongs
to the `‖a‖ₑ`-sublevel set of the gauge of `C` if and only if it belongs to the dilate `a • C`. -/
theorem egauge_le_iff_mem_smul
    (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C) (h0C : (0 : E) ∈ C)
    (a : 𝕜) (ha : 0 < a) (x : E) :
    γ[𝕜](x | C) ≤ ‖a‖ₑ ↔ x ∈ a • C := by
  exact egauge_le_iff_mem_smul_of_sublevel_eq
    (x := x)
    (egauge_sublevel_eq_smul hC_closed hC_convex h0C a ha)

-- Proof sketch: use the Chapter 8 owner theorem
-- `Convex.mem_recessionCone_iff_forall_pos_inv_smul_mem` (with scalar `𝕜`) to rewrite
-- recession-cone membership in the textbook inverse-scaling form. If the gauge is `0`, then for
-- every `ε > 0` one has
-- `egauge 𝕜 C x < ‖ε‖ₑ`, so `egauge_lt_iff` gives a smaller positive dilate containing `x`;
-- convexity and `0 ∈ C` then contract that witness to show `ε⁻¹ • x ∈ C`. Conversely, recession
-- membership gives `x ∈ ε • C` for every `ε > 0`, and `egauge_le_of_mem_smul` forces the gauge
-- to be bounded above by every positive `ε`, hence equal to `0`.
/-- Corollary 9.7.1 (3), owner-level set form: the zero-level set of the gauge of `C` is exactly
the recession cone `0⁺[𝕜] C`. -/
theorem egauge_zeroLevel_eq_recessionCone
    (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C) (h0C : (0 : E) ∈ C) :
    {x : E | γ[𝕜](x | C) = 0} = 0⁺[𝕜] C := sorry

/-- Corollary 9.7.1 (3), pointwise bridge form: a vector has gauge `0` with respect to `C`
if and only if it belongs to the recession cone `0⁺[𝕜] C`. -/
theorem egauge_eq_zero_iff_mem_recessionCone
    (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C) (h0C : (0 : E) ∈ C) (x : E) :
    γ[𝕜](x | C) = 0 ↔ x ∈ 0⁺[𝕜] C := by
  exact egauge_eq_zero_iff_mem_recessionCone_of_zeroLevel_eq
    (x := x)
    (egauge_zeroLevel_eq_recessionCone hC_closed hC_convex h0C)

namespace Convex

/-- Canonical owner-surface form of Corollary 9.7.1 (1): closedness of the gauge is attached
to the convex owner `hC_convex : Convex 𝕜 C`. -/
theorem egauge_lowerSemicontinuous
    {C : Set E} (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) :
    LowerSemicontinuous (γ[𝕜](· | C)) := by
  exact _root_.egauge_lowerSemicontinuous (C := C) hC_closed hC_convex

/-- Canonical owner-surface form of Corollary 9.7.1 (2), owner-level set equality. -/
theorem egauge_sublevel_eq_smul
    {C : Set E} (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C)
    (h0C : (0 : E) ∈ C) (a : 𝕜) (ha : 0 < a) :
    {x : E | γ[𝕜](x | C) ≤ ‖a‖ₑ} = a • C := by
  exact _root_.egauge_sublevel_eq_smul (C := C) hC_closed hC_convex h0C a ha

/-- Canonical owner-surface form of Corollary 9.7.1 (2), pointwise bridge. -/
theorem egauge_le_iff_mem_smul
    {C : Set E} (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C)
    (h0C : (0 : E) ∈ C) (a : 𝕜) (ha : 0 < a) (x : E) :
    γ[𝕜](x | C) ≤ ‖a‖ₑ ↔ x ∈ a • C := by
  exact _root_.egauge_le_iff_mem_smul (C := C) hC_closed hC_convex h0C a ha x

/-- Canonical owner-surface form of Corollary 9.7.1 (3), owner-level set equality. -/
theorem egauge_zeroLevel_eq_recessionCone
    {C : Set E} (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C)
    (h0C : (0 : E) ∈ C) :
    {x : E | γ[𝕜](x | C) = 0} = 0⁺[𝕜] C := by
  exact _root_.egauge_zeroLevel_eq_recessionCone (C := C) hC_closed hC_convex h0C

/-- Canonical owner-surface form of Corollary 9.7.1 (3), pointwise bridge. -/
theorem egauge_eq_zero_iff_mem_recessionCone
    {C : Set E} (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C)
    (h0C : (0 : E) ∈ C) (x : E) :
    γ[𝕜](x | C) = 0 ↔ x ∈ 0⁺[𝕜] C := by
  exact _root_.egauge_eq_zero_iff_mem_recessionCone (C := C) hC_closed hC_convex h0C x

end Convex

end
