import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_6
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_4_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Definiton_8_7_0

noncomputable section

attribute [local instance] Classical.propDecidable

section

variable {E : Type*}
variable [AddCommGroup E]

open scoped Rockafellar
open scoped Pointwise

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 8.7 says that every nonempty scalar sublevel set of a closed proper
  convex function has the same recession cone and the same lineal set.
- `core/canonical`: the owner declarations already present upstream are
  `Function.IsConvex`, `Function.recessionFunction`, and
  `Function.constancySpace`, together with the imported Chapter 8 owners `recessionCone`,
  `Set.lineal`, and `Function.recessionCone`.
- `bridge/view`: the textbook phrase "the recession cone and the constancy space of `f`" is
  rendered directly as `Function.recessionCone ((f)₀⁺)` and
  `Function.constancySpace ((f)₀⁺)`.

Domain-style sampling used here:
- the chapter owner `Function.IsConvex`;
- the nearby chapter owner `Function.recessionFunction`;
- `Function.forall_antitone_translate_iff_mem_recessionCone` and
  `Function.forall_antitone_translate_of_closed_of_antitone_translate` from
  Theorem 8.6;
- the imported owner pairs `recessionCone` / `Set.mem_recessionCone_iff`,
  `lineal` / `mem_lineal_iff`, and
  `Function.recessionCone` / `Function.mem_recessionCone_iff`;
- the upstream owner `Function.constancySpace` from Definition 8.7.0.

Primitive data vs derived API:
- primitive inputs: the function `f`, the level `μ`, and the owner hypotheses
  `Function.IsConvex f`, `f.IsProper`, `LowerSemicontinuous f`;
- derived API: the common recession-cone equality and the induced lineality/constancy equality for
  each nonempty scalar sublevel set.

Layer target: the item stays `source-facing`, stated directly with the chapter's existing owner
objects and split into atomic clauses for the cone and lineality conclusions.
- Ambient-space refinement: although the source states the theorem on `R^n`, the surrounding
  owner API already lives on intrinsic topological vector spaces, so this file is refined to that
  layer instead of a fixed Euclidean coordinate model.
- Scalar/codomain refinement: this item follows the generalized scalar/codomain owner chain from
  Theorems 8.5 and 8.6, keeping codomain `WithBotTop 𝕜` and exposing scalar `𝕜` on set-valued
  owners (`0⁺[𝕜]`, `lin[𝕜]`) where it is mathematically essential.
-/

open Set

section

variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
variable [IsOrderedAddMonoid α]

/-- For a nonempty set `C`, membership in the recession cone of the indicator recession function
is equivalent to one-step intrinsic translation invariance `y +ᵥ C ⊆ C`. -/
theorem mem_functionRecessionCone_indicatorFunction_iff_vadd_subset_self
    {C : Set E} (hC_nonempty : C.Nonempty) :
    ∀ y : E, y ∈ (δ[α](· | C) )₀⁺.recessionCone  ↔ y +ᵥ C ⊆ C := by
  intro y
  let f : E → WithBotTop α := fun x ↦ δ[α](x | C)
  have hdom : dom(f) = C := by
    simpa [f] using (effectiveDomain_indicator (α := α) C)
  have hf_proper : f.IsProper := by
    rw [Function.isProper_iff]
    constructor
    · exact hdom.symm ▸ hC_nonempty
    · intro x
      by_cases hx : x ∈ C
      · have hx0 : f x = (0 : WithBotTop α) := by
          simpa [f, hx] using (indicator_def (α := α) C x)
        exact hx0.symm ▸ WithBotTop.zero_ne_bot
      · have hxtop : f x = (⊤ : WithBotTop α) := by
          simpa [f, hx] using (indicator_def (α := α) C x)
        exact hxtop.symm ▸ top_ne_bot
  constructor
  · intro hy
    rw [Function.mem_recessionCone_iff] at hy
    intro z hz
    rcases Set.mem_vadd_set.mp hz with ⟨x, hxC, rfl⟩
    have hxdom : x ∈ dom(f) := by simpa [hdom] using hxC
    have hxy : f (x + y) ≤ f x + ((f)₀⁺) y :=
      Function.recessionFunction_translationUpperBound (f := f) hf_proper x hxdom y
    have hyf : ((f)₀⁺) y ≤ (0 : WithBotTop α) := by
      simpa [f] using hy
    have hxy' : f (x + y) ≤ f x := by
      calc
        f (x + y) ≤ f x + ((f)₀⁺) y := hxy
        _ ≤ f x + 0 := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hyf (f x)
        _ = f x := by simp
    have hx0 : f x = (0 : WithBotTop α) := by
      simpa [f, hxC] using (indicator_def (α := α) C x)
    have hxy_le_zero : f (x + y) ≤ (0 : WithBotTop α) := by
      simpa [hx0] using hxy'
    have hxpyC : x + y ∈ C := by
      by_contra hxpyC
      have hxpy_top : f (x + y) = (⊤ : WithBotTop α) := by
        simpa [f, hxpyC] using (indicator_def (α := α) C (x + y))
      have htop_le_zero : (⊤ : WithBotTop α) ≤ (0 : WithBotTop α) := by
        simpa [hxpy_top] using hxy_le_zero
      exact (WithBotTop.coe_ne_top (0 : α)) (top_le_iff.mp htop_le_zero)
    simpa [vadd_eq_add, add_comm] using hxpyC
  · intro hy
    let h : E → WithBotTop α := fun z ↦ if z = y then 0 else ⊤
    have hh : Function.TranslationUpperBound f h := by
      intro x hxdom z
      by_cases hz : z = y
      · subst z
        have hxC : x ∈ C := by simpa [hdom] using hxdom
        have hxpyC : x + y ∈ C := by
          have hyxC : y +ᵥ x ∈ C := hy (Set.mem_vadd_set.mpr ⟨x, hxC, rfl⟩)
          simpa [vadd_eq_add, add_comm] using hyxC
        have hx0 : f x = (0 : WithBotTop α) := by
          simpa [f, hxC] using (indicator_def (α := α) C x)
        have hxpy0 : f (x + y) = (0 : WithBotTop α) := by
          simpa [f, hxpyC] using (indicator_def (α := α) C (x + y))
        simp [h, hx0, hxpy0]
      · have hfx_top : f x + (⊤ : WithBotTop α) = ⊤ :=
          WithBotTop.add_top_of_ne_bot (hf_proper.ne_bot x)
        have hz_top : f (x + z) ≤ f x + (⊤ : WithBotTop α) := by
          rw [hfx_top]
          exact le_top
        have hh_top : h z = (⊤ : WithBotTop α) := by simp [h, hz]
        rw [hh_top]
        exact hz_top
    have hle : ((f)₀⁺) y ≤ h y :=
      Function.recessionFunction_le_of_translationUpperBound (f := f) hf_proper hh y
    rw [Function.mem_recessionCone_iff]
    simpa [h, f] using hle

/-- For a convex set `C`, the recession cone of its indicator function in any
`WithBotTop α` codomain coincides with the recession cone of `C`. -/
@[simp] theorem functionRecessionCone_indicatorFunction_eq_recessionCone
    {𝕜 : Type*} [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [FloorSemiring 𝕜]
    [Module 𝕜 E]
    {C : Set E} (hC_convex : Convex 𝕜 C) :
    (δ[α](· | C))₀⁺.recessionCone = 0⁺[𝕜] C := by
  by_cases hC_nonempty : C.Nonempty
  · ext y
    rw [mem_functionRecessionCone_indicatorFunction_iff_vadd_subset_self
      (α := α) hC_nonempty y,
      Convex.mem_recessionCone_iff_vadd_subset_self hC_convex y]
  · have hC_empty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC_nonempty
    ext y
    rw [Function.mem_recessionCone_iff, hC_empty, Set.recessionCone_empty]
    simp [Function.recessionFunction]

/-- For a convex set `C`, the constancy space of the recession function of
`δ[α](· | C)` coincides with the lineal set of `C`. -/
theorem constancySpace_indicatorFunction_eq_lineal
    {𝕜 : Type*} [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [FloorSemiring 𝕜]
    [Module 𝕜 E]
    {C : Set E} (hC_convex : Convex 𝕜 C) :
    (δ[α](· | C))₀⁺.constancySpace = lin[𝕜](C) := by
  ext y
  rw [Function.mem_constancySpace_iff_mem_recessionCone, Set.mem_lineal_iff,
    functionRecessionCone_indicatorFunction_eq_recessionCone hC_convex]
  constructor <;> intro h <;> exact h

/-- Canonical owner bridge: for a convex set `C`, the function-side lineal owner of the
indicator equals the set-side lineal owner of `C`. -/
theorem lineal_indicator_eq_lineal
    {𝕜 : Type*} [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [FloorSemiring 𝕜]
    [Module 𝕜 E]
    {C : Set E} (hC_convex : Convex 𝕜 C) :
    lin(δ[α](· | C)) = lin[𝕜](C) := by
  simpa [Function.lineal] using
    (constancySpace_indicatorFunction_eq_lineal (α := α) (𝕜 := 𝕜) (C := C) hC_convex)

end

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable [Module 𝕜 E]

variable {f : E → WithBotTop 𝕜}

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

namespace Function.IsConvex

/-- Theorem 8.7 (1): for a closed proper convex function, every nonempty scalar sublevel set
`{x | f x ≤ μ}` has recession cone equal to the recession cone of `f`, expressed as the
nonpositive sublevel set of `(f)₀⁺`. -/
-- Proof sketch: use `Set.mem_recessionCone_iff` to rewrite membership in the recession cone of the
-- sublevel set as preservation of the inequality `f (x + t • y) ≤ λ` along every forward ray from
-- a point with `f x ≤ λ`. Because the sublevel set is nonempty, choose one such base point; the
-- resulting antitonicity on that line upgrades by the closed case of Theorem 8.6 to antitonicity
-- on every parallel line. The equivalence in Theorem 8.6 then identifies this with
-- `((f)₀⁺) y ≤ 0`, which is exactly membership in `Function.recessionCone ((f)₀⁺)`.
theorem recessionCone_sublevelSet_eq_functionRecessionCone
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f) (μ : WithBotTop 𝕜)
    (hμ_nonempty : ({x : E | f x ≤ μ}).Nonempty) :
    0⁺[𝕜] ({x : E | f x ≤ μ}) = f ₀⁺.recessionCone := sorry

/-- Theorem 8.7 (2): for a closed proper convex function, every nonempty scalar sublevel set
`{x | f x ≤ μ}` has lineal set equal to the constancy space of `f`, expressed as the
constancy space of `(f)₀⁺`. -/
-- Proof sketch: unfold membership in the lineal set of the sublevel set using `mem_lineal_iff`;
-- this requires both `y` and `-y` to lie in the recession cone of that
-- sublevel set. Part (1) rewrites those two cone-membership conditions as
-- `((f)₀⁺) y ≤ 0` and `((f)₀⁺) (-y) ≤ 0`, which is exactly the defining condition from
-- `Function.mem_constancySpace_iff` for `Function.constancySpace ((f)₀⁺)`.
theorem lineal_sublevelSet_eq_constancySpace
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f) (μ : WithBotTop 𝕜)
    (hμ_nonempty : ({x : E | f x ≤ μ}).Nonempty) :
    lin[𝕜]({x : E | f x ≤ μ}) = f ₀⁺.constancySpace := sorry

end Function.IsConvex

end
