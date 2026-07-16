import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_19_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 19.3.2 says that the Minkowski sum of two polyhedral convex subsets
  of a finite-dimensional topological `𝕜`-module is again polyhedral.
- `core/canonical`: the owner abstraction is the pairing-parametric `Set.IsPolyhedral 𝕜 Y`,
  together with the canonical product-space owner `E × E`, the product theorem
  `Set.IsPolyhedral.prod`, and the image theorem `Set.IsPolyhedral.linear_image` from
  Theorem 19.3.
- `bridge/view`: the textbook sum is exactly Lean's pointwise-set addition. The pair-space points
  whose first and second coordinates lie in `C₁` and `C₂` form the product set `C₁ ×ˢ C₂`, and
  the addition map on that product owner has image `C₁ + C₂`.

Domain-style sampling used here:
- `Set.IsPolyhedral`;
- `Set.IsPolyhedral.prod`;
- `Set.IsPolyhedral.linear_image`;
- `LinearMap.fst`;
- `LinearMap.snd`;
- `Set.add_image_prod`.

Primitive data vs derived API:
- primitive inputs: the two polyhedral convex sets `C₁` and `C₂`;
- derived API: polyhedrality of their pointwise sum `C₁ + C₂`.

Layer target: `source-facing`, stated directly on the canonical owner `Set.IsPolyhedral`.
-/

namespace Set.IsPolyhedral

section Add

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
variable {Y : Type*} [HasPairing E Y 𝕜]

/-- Corollary 19.3.2: the Minkowski sum of two polyhedral convex sets is polyhedral. -/
theorem add {C₁ C₂ : Set E} (hC₁ : C₁.IsPolyhedral 𝕜 Y)
    (hC₂ : C₂.IsPolyhedral 𝕜 Y) : (C₁ + C₂).IsPolyhedral 𝕜 Y := by
  let addMap : E × E →ₗ[𝕜] E := LinearMap.fst 𝕜 E E + LinearMap.snd 𝕜 E E
  have hprod : (C₁ ×ˢ C₂).IsPolyhedral 𝕜 (Y × Y) := hC₁.prod hC₂
  simpa [Set.add_image_prod, addMap, LinearMap.add_apply] using hprod.linear_image addMap

/-- Corollary 19.3.2, difference form: the pointwise difference of two polyhedral convex sets is
polyhedral. -/
theorem sub {C₁ C₂ : Set E} (hC₁ : C₁.IsPolyhedral 𝕜 Y)
    (hC₂ : C₂.IsPolyhedral 𝕜 Y) : (C₁ - C₂).IsPolyhedral 𝕜 Y := by
  simpa [sub_eq_add_neg] using
    hC₁.add (hC₂.linear_image (LinearMap.lsmul 𝕜 E (-1 : 𝕜)))

end Add

end Set.IsPolyhedral

end
