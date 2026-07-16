import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

/-
Source/core/bridge triage for this item.

- `source-facing`: Text 5.1.5 says that the affine value transform `(λ f + α)` of a proper convex
  function is again proper convex when `0 ≤ λ`.
- `core/canonical`: the owner predicates are `Function.IsProper` and `Function.IsConvex`, and the
  boundary-preserving affine value transform is expressed directly by the canonical owners
  `Function.toWithTopBot` and `Function.extendBotTop`, applied to the finite affine branch
  `t ↦ λ • t + α`.
- `bridge/view`: `extendBotTop` is essential here because the textbook convention at `+∞` is not
  the raw `WithTopBot` scalar-multiplication convention when `λ = 0`.

Domain-style sampling used here:
- `Function.IsProper` and `Function.IsProper.bot_lt` from `Definition_4_6`;
- `Function.IsConvex` from `Theorem_4_2`, imported through `Theorem_5_1`;
- `Function.IsConvex.comp_toWithTopBot_extendBotTop_of_monotone` from `Theorem_5_1`;
- `Function.toWithTopBot` and `Function.extendBotTop` from `EOrder.Basic`.

Primitive data vs derived API:
- primitive data: the finite affine branch `t ↦ λ • t + α`;
- core/canonical realization: the canonical codomain lift `.toWithTopBot` of the finite affine
  branch together with its boundary-preserving extension `extendBotTop`;
- derived API: the properness/convexity preservation theorem below, stated directly on that
  canonical composite rather than through a local wrapper owner.
-/

variable {𝕜 : Type v} {E : Type u}

namespace Function

private theorem affineBranch_convexOn_univ_of_nonneg
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (lam α : 𝕜) (hlam : 0 ≤ lam) :
    ConvexOn 𝕜 (Set.univ : Set 𝕜) (fun t : 𝕜 ↦ lam • t + α) := by
  have hAffineConvexOn : ConvexOn 𝕜 (Set.univ : Set 𝕜) (fun t : 𝕜 ↦ lam • t + α) := by
    have hId : ConvexOn 𝕜 (Set.univ : Set 𝕜) (fun t : 𝕜 ↦ t) := convexOn_id convex_univ
    have hSmul : ConvexOn 𝕜 (Set.univ : Set 𝕜) (fun t : 𝕜 ↦ lam • t) := hId.smul hlam
    simpa using hSmul.add_const α
  exact hAffineConvexOn

private theorem monotone_affineBranch_of_nonneg
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (lam α : 𝕜) (hlam : 0 ≤ lam) :
    Monotone (fun t : 𝕜 ↦ lam • t + α) := by
  intro x y hxy
  simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using
    (add_le_add_right (mul_le_mul_of_nonneg_left hxy hlam) α)

/- Properness branch for Text 5.1.5 on the canonical owner surface. -/
theorem IsProper.comp_affineValueTransform
    {β : Type*} [SMul 𝕜 β] [Add β] [Preorder β]
    {f : E → WithTopBot β} (hf : f.IsProper) (lam : 𝕜) (a : β) :
    ((((fun t : β ↦ lam • t + a).toWithTopBot).extendBotTop) ∘ f).IsProper := by
  simpa using hf.comp_extendBotTop (fun t : β ↦ lam • t + a)

set_option maxHeartbeats 800000 in
/-- Convexity branch for Text 5.1.5 on the canonical owner surface. -/
theorem IsConvex.comp_affineValueTransform_of_nonneg
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommMonoid E] [Module 𝕜 E]
    {f : E → WithTopBot 𝕜} (hf : f.IsConvex 𝕜)
    (lam α : 𝕜) (hlam : 0 ≤ lam) :
    ((((fun t : 𝕜 ↦ lam • t + α).toWithTopBot).extendBotTop) ∘ f).IsConvex 𝕜 := by
  simpa using hf.comp_toWithTopBot_extendBotTop_of_monotone
    (affineBranch_convexOn_univ_of_nonneg lam α hlam)
    (monotone_affineBranch_of_nonneg lam α hlam)

/-- Text 5.1.5: if `f` is proper convex and `0 ≤ λ`, then the canonical affine value composite
`((fun t ↦ λ • t + α).toWithTopBot).extendBotTop ∘ f` preserves both owners `IsProper` and
`IsConvex`. -/
theorem affineValueTransform_comp_isProper_and_isConvex_of_nonneg
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommMonoid E] [Module 𝕜 E]
    {f : E → WithTopBot 𝕜} (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜)
    (lam α : 𝕜) (hlam : 0 ≤ lam) :
    ((((fun t : 𝕜 ↦ lam • t + α).toWithTopBot).extendBotTop) ∘ f).IsProper ∧
      ((((fun t : 𝕜 ↦ lam • t + α).toWithTopBot).extendBotTop) ∘ f).IsConvex 𝕜 := by
  exact ⟨hf_proper.comp_affineValueTransform lam α,
    hf_convex.comp_affineValueTransform_of_nonneg lam α hlam⟩

end Function

end
