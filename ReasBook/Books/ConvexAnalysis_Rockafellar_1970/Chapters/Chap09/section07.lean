import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_9_7_1 (from Chap02) -/
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

/-! ### Theorem_9_7 (from Chap02) -/
noncomputable section

open scoped Rockafellar
open Function (sublinearHull)

section

variable {E : Type*} {𝕜 : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 9.7 studies the positively homogeneous convex function generated by a
  closed convex function `f` with no `⊥` values and `f 0 > 0`, identifies its closure as the
  infimum of the right scalar multiples `f_λ` together with the recession value `f0⁺`, proves
  attainment of that infimum, and records the closed-case simplification when `0 ∈ dom f`.
- `core/canonical`: the owner abstractions already present in the chapter are
  `Function.sublinearHull`, `rightScalarMul`,
  `Function.recessionFunction`, and `lowerSemicontinuousHull`.
  closure `cl k` is the chapter owner `lowerSemicontinuousHull`, and the family
  `f_λ` is rendered by the canonical owner `(a •ʳ f)` indexed over the intrinsic
  positive nonnegative-scalar ray `𝕜≥0ˣ`.

Domain-style sampling used here:
- `Function.sublinearHull_eq_iInf_rightScalarMul`;
- `Function.sublinearHull_eq_iInf_pos_rightScalarMul`;
- `recessionFunction_lowerSemicontinuous`;
- `tendsto_rightScalarMul_to_recessionFunction_of_zero_mem_dom_of_ne_bot`;
- `lowerSemicontinuousHull`.

Primitive data vs derived API:
- primitive input: the function `f : E → WithTopBot 𝕜`;
- owner hypotheses: convexity and closedness of `f`, the primitive codomain condition
  `∀ z, f z ≠ ⊥`, and the source-visible positivity hypothesis `(0 : WithTopBot 𝕜) < f 0`;
- derived API: the closure formula, attainment of that infimum, and the closed-case simplification
  when `f 0 < ⊤`, together with source-facing wrappers that recover the same statements from
  `f.IsProper`.

Layer target: `source-facing`, attached to the canonical owner namespace
`Function`, and stated directly with the existing owner declarations instead of
introducing a parallel wrapper for the generated function, its closure, or the scalar family.

Ambient-space refinement: every owner declaration used here already lives on an arbitrary
topological module over an ordered scalar field `𝕜`, and the only additional structure
needed here is the topological-order layer required by the closure owner `cl(·)` and the
recession-limit theorem from Corollary 8.5.2. The induced topological-order structure on
`WithTopBot 𝕜` is taken from typeclass inference, so no extra codomain-topology binders are
exposed on theorem surfaces. In particular, this file introduces no extra finite-dimensional,
inner-product, or concrete-model assumptions beyond those upstream owner theorems. Thus the
file stays on arbitrary scalar topological modules rather than the concrete display model
`EuclideanSpace ℝ (Fin n)`.
-/

namespace Function

section

variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)
local notation "𝕜≥0ˣ" => {a : 𝕜≥0 // (0 : 𝕜) < (a : 𝕜)}

variable {f : E → WithTopBot 𝕜}

/-- Primitive owner form of Theorem 9.7: if `f` is closed convex with no `⊥` values and
`f 0 > 0`, then the closure of the generated positively homogeneous convex function is the infimum
of the recession value `(f)₀⁺ x` and the positive right scalar multiples of `f`. -/
-- Proof sketch: apply Text 5.4.9 to express the generated function as the infimum of the
-- right scalar multiples `f_λ` for `λ ≥ 0`, then use Corollary 8.5.2 to identify the `λ → 0+`
-- boundary value with `recessionFunction f`. Lower semicontinuous closure converts this
-- pointwise infimum-with-limit description into the displayed closure formula
-- for `lowerSemicontinuousHull`.
theorem lowerSemicontinuousHull_sublinearHull_eq_inf_recession_iInf_pos_rightScalarMul_of_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z, f z ≠ (⊥ : WithTopBot 𝕜))
    (hf_closed : LowerSemicontinuous f)
    (h0 : 0 < f 0) :
    cl(sublinearHull f) =
      fun x : E ↦ (((f)₀⁺) x) ⊓ (⨅ a : 𝕜≥0ˣ, (a •ʳ f) x) := sorry

/-- Derived source-facing form of Theorem 9.7 using `f.IsProper`. -/
theorem lowerSemicontinuousHull_sublinearHull_eq_inf_recession_iInf_pos_rightScalarMul
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f)
    (h0 : 0 < f 0) :
    cl(sublinearHull f) =
      fun x : E ↦ (((f)₀⁺) x) ⊓ (⨅ a : 𝕜≥0ˣ, (a •ʳ f) x) := by
  simpa using
    lowerSemicontinuousHull_sublinearHull_eq_inf_recession_iInf_pos_rightScalarMul_of_ne_bot
      (f := f) hf_convex (fun z ↦ hf_proper.ne_bot z) hf_closed h0

/-- Set-indexed bridge form of Theorem 9.7, kept for source-facing compatibility with
`sInf (insert · (range ·))`. -/
theorem lowerSemicontinuousHull_sublinearHull_eq_sInf_insert_recessionFunction
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f)
    (h0 : 0 < f 0) :
    cl(sublinearHull f) =
      fun x : E ↦
        sInf (Set.insert (((f)₀⁺) x) (Set.range fun a : 𝕜≥0ˣ ↦ (a •ʳ f) x)) := by
  -- Bridge from the canonical `⊓`/`iInf` owner form.
  sorry

/-- The candidate values in Theorem 9.7 have least element
`cl(sublinearHull f) x`, so the infimum there is attained either by the recession value or
by a positive right scalar multiple. -/
-- Proof sketch: the right scalar multiples converge to `recessionFunction f x` as `λ → 0+`, so
-- the candidate values consist exactly of a convergent positive-scalar family together with its
-- limit. Closedness of the hull then ensures that the infimum is realized either by
-- `recessionFunction f x` itself or by some `(a •ʳ f) x` with `a > 0`.
theorem isLeast_lowerSemicontinuousHull_sublinearHull_of_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z, f z ≠ (⊥ : WithTopBot 𝕜))
    (hf_closed : LowerSemicontinuous f)
    (h0 : 0 < f 0) (x : E) :
    IsLeast (Set.insert (((f)₀⁺) x) (Set.range fun a : 𝕜≥0ˣ ↦ (a •ʳ f) x))
      (cl(sublinearHull f) x) := sorry

/-- Derived source-facing form of attainment in Theorem 9.7 using `f.IsProper`. -/
theorem isLeast_lowerSemicontinuousHull_sublinearHull
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f)
    (h0 : 0 < f 0) (x : E) :
    IsLeast (Set.insert (((f)₀⁺) x) (Set.range fun a : 𝕜≥0ˣ ↦ (a •ʳ f) x))
      (cl(sublinearHull f) x) := by
  simpa using
    isLeast_lowerSemicontinuousHull_sublinearHull_of_ne_bot
      (f := f) hf_convex (fun z ↦ hf_proper.ne_bot z) hf_closed h0 x

/-- If `0 ∈ dom f`, then the generated positively homogeneous convex function is fixed by
Rockafellar's closure owner `cl(·)`. -/
theorem lowerSemicontinuousHull_sublinearHull_eq_sublinearHull_of_zero_mem_dom_of_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z, f z ≠ (⊥ : WithTopBot 𝕜))
    (hf_closed : LowerSemicontinuous f)
    (h0 : (0 : E) ∈ dom(f)) :
    cl(sublinearHull f) = sublinearHull f := sorry

/-- Derived source-facing closed-case simplification using `f.IsProper`. -/
theorem lowerSemicontinuousHull_sublinearHull_eq_sublinearHull_of_zero_mem_dom
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f)
    (h0 : (0 : E) ∈ dom(f)) :
    cl(sublinearHull f) = sublinearHull f := by
  simpa using
    lowerSemicontinuousHull_sublinearHull_eq_sublinearHull_of_zero_mem_dom_of_ne_bot
      (f := f) hf_convex (fun z ↦ hf_proper.ne_bot z) hf_closed h0

/-- If `0 ∈ dom f`, then the generated positively homogeneous convex function is already closed. -/
-- Proof sketch: under `h0 : (0 : E) ∈ dom(f)`, Corollary 8.5.2 identifies the missing
-- `λ = 0⁺` boundary term with the actual limit of the positive right scalar multiples at every
-- point. The closure formula above therefore agrees pointwise with the generated function itself,
-- giving lower semicontinuity.
theorem lowerSemicontinuous_sublinearHull_of_zero_mem_dom_of_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z, f z ≠ (⊥ : WithTopBot 𝕜))
    (hf_closed : LowerSemicontinuous f)
    (h0 : (0 : E) ∈ dom(f)) :
    LowerSemicontinuous (sublinearHull f) := sorry

/-- Derived source-facing closedness of `sublinearHull f` under `0 ∈ dom f` and `f.IsProper`. -/
theorem lowerSemicontinuous_sublinearHull_of_zero_mem_dom
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f)
    (h0 : (0 : E) ∈ dom(f)) :
    LowerSemicontinuous (sublinearHull f) := by
  simpa using
    lowerSemicontinuous_sublinearHull_of_zero_mem_dom_of_ne_bot
      (f := f) hf_convex (fun z ↦ hf_proper.ne_bot z) hf_closed h0

end

end Function

end
