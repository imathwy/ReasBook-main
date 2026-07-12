import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_32_4

noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [CommRing 𝕜] [Preorder 𝕜] [AddLeftMono 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable {f : E → WithTopBot 𝕜}

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 32.4.1 says that if a convex function attains its supremum on an
  arbitrary set `S` at a point `x ∈ ri(dom f)`, then every subgradient at `x` defines a linear
  functional whose supremum on `S` is attained at the same point `x`.
- `core/canonical`: the owner-level mechanism is the normal-cone theorem
  `mem_normalCone_of_mem_subdifferentialAt_of_isMaxOn` from Theorem 32.4 together with the
  owner bridge `isMaxOn_pairing_of_mem_normalCone` from `Chap01.Definition_2_7_10`.
- `bridge/view`: the source phrase “yields a linear functional attaining its supremum over `S`
  at `x`” is represented directly by `IsMaxOn (fun y ↦ (⟪y, xStar⟫ₚ : 𝕜)) S x`.

Domain-style sampling used here:
- `mem_normalCone_of_mem_subdifferentialAt_of_isMaxOn` from `Chap06.Theorem_32_4`;
- `isMaxOn_pairing_of_mem_normalCone` from `Chap01.Definition_2_7_10`;
- `riDom[𝕜](·)` from `Chap01.Definition_4_4`;
- `IsMaxOn` from mathlib's extrema API.

Primitive data vs derived API:
- primitive inputs on the source theorem surface: `x ∈ riDom[𝕜](f)`, `f x ≠ ⊥`, the maximizing
  point data `x ∈ S` and `IsMaxOn f S x`, and a chosen subgradient
  `xStar ∈ ∂[Y]f(x)`;
- derived API: `intrinsicInterior_subset` supplies the owner-level finiteness datum
  `x ∈ dom(f)`, and the two upstream owner theorems compose to the linear-maximizer conclusion for
  the pairing functional
  `y ↦ (⟪y, xStar⟫ₚ : 𝕜)` on `S`.

Layer target: `source-facing`, as a thin direct corollary on `riDom[𝕜](f)` with no extra local
owner-layer wrapper theorem.
-/

-- Proof sketch: `x ∈ riDom[𝕜](f)` implies `x ∈ dom(f)` by `intrinsicInterior_subset`, then apply
-- the two canonical owner theorems directly.
/-- Source-facing `riDom[𝕜]` specialization of Corollary 32.4.1. -/
theorem isMaxOn_pairing_of_mem_subdifferentialAt_of_mem_riDom
    {S : Set E} {x : E} (hxri : x ∈ riDom[𝕜](f)) (hx_bot : f x ≠ ⊥)
    (hxS : x ∈ S) (hmax : IsMaxOn f S x)
    {Y : Type (max u v)} [AddCommMonoid Y] [Module 𝕜 Y]
    [HasLinearPairing E Y 𝕜] [HasPairingSubLeft E Y 𝕜] {xStar : Y}
    (hxStar : xStar ∈ ∂[Y]f(x)) :
    IsMaxOn (fun y : E ↦ (⟪y, xStar⟫ₚ : 𝕜)) S x := by
  have hx : x ∈ dom(f) := intrinsicInterior_subset hxri
  exact isMaxOn_pairing_of_mem_normalCone
    (mem_normalCone_of_mem_subdifferentialAt_of_isMaxOn hxStar hxS hmax hx hx_bot)

end
