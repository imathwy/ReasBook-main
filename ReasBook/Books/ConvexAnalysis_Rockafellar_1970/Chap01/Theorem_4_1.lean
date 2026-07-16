import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_2

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:
- `source-facing`: Theorem 4.1 is Rockafellar's Jensen inequality criterion for convexity on a
  convex set `C`.
- `core/canonical`: the owner surface is the canonical `ConvexOn 𝕜 C f` predicate.
- `bridge/view`: the displayed two-point inequality uses the same codomain scalar action as
  `ConvexOn`; no strict finite-height slack is part of this theorem.
-/

universe u v w

section

attribute [local instance] Classical.propDecidable

variable {𝕜 : Type w} {E : Type u} {α : Type v}
variable [Ring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid (WithTopBot α)] [PartialOrder (WithTopBot α)]
variable [IsOrderedAddMonoid (WithTopBot α)]
variable [SMul 𝕜 (WithTopBot α)] [PosSMulMono 𝕜 (WithTopBot α)]
variable {C : Set E}

/-- Theorem 4.1, forward direction: a convex function satisfies the displayed Jensen inequality
on every open segment in its convex domain. -/
theorem ConvexOn.le_affine_combination {f : E → WithTopBot α}
    (hf : ConvexOn 𝕜 C f)
    {x y : E} (hxC : x ∈ C) (hyC : y ∈ C)
    {t : 𝕜} (ht0 : 0 < t) (ht1 : t < 1) :
    f ((1 - t) • x + t • y) ≤ (1 - t) • f x + t • f y := by
  sorry

/-- Theorem 4.1: on a convex domain, convexity is equivalent to the two-point Jensen inequality
for every `0 < t < 1`. -/
theorem convexOn_iff_jensen_open_segment {f : E → WithTopBot α}
    (hC : Convex 𝕜 C) :
    ConvexOn 𝕜 C f ↔
      ∀ x y : E, x ∈ C → y ∈ C → ∀ t : 𝕜, 0 < t → t < 1 →
        f ((1 - t) • x + t • y) ≤ (1 - t) • f x + t • f y := by
  sorry

end
