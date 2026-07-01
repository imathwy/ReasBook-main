import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open Filter
open scoped Rockafellar

variable {E : Type*} {𝕜 : Type*}

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 8.5.2 states that the right scalar multiples `f_λ` converge to the
  recession function `(f)₀⁺` as `λ → 0+`, first at points of `dom f` and then, under
  `0 ∈ dom f`, at every point of the ambient scalar topological module.
- `core/canonical`: the owner abstractions already present upstream are the canonical `Function`
  owner `recessionFunction` on codomain `WithBotTop 𝕜`, the scaled-epigraph owner
  `rightScalarMul`, the convexity predicate `f.IsConvex`, the primitive codomain condition
  `∀ z, f z ≠ ⊥`, the effective-domain owner `dom(·)`, and the closedness hypothesis
  `LowerSemicontinuous`; source-facing properness forms are derived wrappers.
- `bridge/view`: the second clause is proved from the closed-case quotient limit in Theorem 8.5
  together with the positive-scalar rescaling identity for `rightScalarMul`.

Domain-style sampling used here:
- `rightScalarMul`;
- `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos`;
- `Function.recessionFunction`;
- `Function.tendsto_differenceQuotient_atTop_recessionFunction`.
- `dom(·)` and `mem_effectiveDomain`.

Primitive data vs derived API:
- primitive inputs: the function `f`, the closed/convex hypotheses, the primitive no-`⊥`
  condition `∀ z, f z ≠ ⊥`, and the owner-domain memberships `y ∈ dom f` and `0 ∈ dom f`;
- derived API: source-facing `f.IsProper` wrappers and the one-sided limit formula for right
  scalar multiples at `0`.

Layer target: this item stays `source-facing`, but its public API is placed directly on the
canonical owner namespace `Function` and uses the existing notation `(f)₀⁺`.

Ambient-space refinement: although the source states the corollary on `R^n`, the supporting owner
API from Text 5.4.3 and Theorem 8.5 already lives on arbitrary scalar topological modules, and no
coordinate-level argument is used here.
-/

namespace Function

section MemDom

variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [DenselyOrdered 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [ContinuousAdd 𝕜] [ContinuousMul 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddTorsor E] [ContinuousSMul 𝕜 E]
variable {f : E → WithBotTop 𝕜}

-- Proof sketch: apply the boundary-limit statement from Corollary 7.5.1 to the closed convex
-- perspective function whose positive slices are the right scalar multiples `f_λ`. The hypotheses
-- `hf_convex`, `hf_ne_bot`, and `hf_closed` provide the primitive closed convex setup at this
-- layer, while `hy : y ∈ dom f` supplies a finite base point. The boundary value at `λ = 0`
-- is exactly the recession value `((f)₀⁺) y`.
/-- Primitive boundary-limit form of Corollary 8.5.2 (1): for a closed convex function with no
`⊥` values, the right scalar multiples `f_λ` converge to the recession function `(f)₀⁺` at every
point `y` of `dom f`. -/
theorem tendsto_rightScalarMul_to_recessionFunction_of_mem_dom_of_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z, f z ≠ (⊥ : WithBotTop 𝕜))
    (hf_closed : LowerSemicontinuous f)
    {y : E} (hy : y ∈ dom(f)) :
    Tendsto (fun lam : 𝕜≥0 ↦ (lam •ʳ f) y)
      (nhdsWithin (⟨0, le_rfl⟩ : 𝕜≥0) (Set.Ioi (⟨0, le_rfl⟩ : 𝕜≥0)))
      (nhds (((f)₀⁺) y)) := sorry

/-- Corollary 8.5.2 (1): derived source-facing form with properness. -/
theorem tendsto_rightScalarMul_to_recessionFunction_of_mem_dom
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f)
    {y : E} (hy : y ∈ dom(f)) :
    Tendsto (fun lam : 𝕜≥0 ↦ (lam •ʳ f) y)
      (nhdsWithin (⟨0, le_rfl⟩ : 𝕜≥0) (Set.Ioi (⟨0, le_rfl⟩ : 𝕜≥0)))
      (nhds (((f)₀⁺) y)) := by
  simpa using tendsto_rightScalarMul_to_recessionFunction_of_mem_dom_of_ne_bot
    (f := f) hf_convex (fun z ↦ hf_proper.ne_bot z) hf_closed hy

end MemDom

section ZeroMemDom

variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable {f : E → WithBotTop 𝕜}

-- Proof sketch: specialize the closed-case quotient-limit formula from Theorem 8.5 at the base
-- point `x = 0`, using `h0 : (0 : E) ∈ dom f`. Rewrite the quotient
-- `(f (t • y) - f 0) / t` as the value of `rightScalarMul` at `t⁻¹` via
-- `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos`, then change variables `λ = t⁻¹` to
-- obtain the limit of `f_λ(y)` as `λ → 0+`.
/-- Primitive boundary-limit form of Corollary 8.5.2 (2): if `0 ∈ dom f` and `f` has no `⊥`
values, then the same limit formula for `f_λ(y)` and `((f)₀⁺) y` holds for every `y` in the
ambient scalar topological module. -/
theorem tendsto_rightScalarMul_to_recessionFunction_of_zero_mem_dom_of_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z, f z ≠ (⊥ : WithBotTop 𝕜))
    (hf_closed : LowerSemicontinuous f)
    (h0 : (0 : E) ∈ dom(f)) (y : E) :
    Tendsto (fun lam : 𝕜≥0 ↦ (lam •ʳ f) y)
      (nhdsWithin (⟨0, le_rfl⟩ : 𝕜≥0) (Set.Ioi (⟨0, le_rfl⟩ : 𝕜≥0)))
      (nhds (((f)₀⁺) y)) := sorry

/-- Corollary 8.5.2 (2): derived source-facing form with properness. -/
theorem tendsto_rightScalarMul_to_recessionFunction_of_zero_mem_dom
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f)
    (h0 : (0 : E) ∈ dom(f)) (y : E) :
    Tendsto (fun lam : 𝕜≥0 ↦ (lam •ʳ f) y)
      (nhdsWithin (⟨0, le_rfl⟩ : 𝕜≥0) (Set.Ioi (⟨0, le_rfl⟩ : 𝕜≥0)))
      (nhds (((f)₀⁺) y)) := by
  simpa using tendsto_rightScalarMul_to_recessionFunction_of_zero_mem_dom_of_ne_bot
    (f := f) hf_convex (fun z ↦ hf_proper.ne_bot z) hf_closed h0 y

end ZeroMemDom

end Function

end
