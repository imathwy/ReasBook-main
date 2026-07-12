import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Proposition_2_6_12

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.13 fixes convex sets `C₁` and `C₂`, forms their homogenization sets
  `K₁ = homogenizationSet C₁` and `K₂ = homogenizationSet C₂`, then defines `K` as the set of
  points lying in both and asserts that `K` is convex.
- `core/canonical`: the owner theorem is `Convex.homogenizationSet_inter`, now upstream in
  Proposition 2.6.12 next to `Convex.homogenizationSet`.
- `bridge/view`: the displayed set `K` is exactly `homogenizationSet C₁ ∩ homogenizationSet C₂`;
  this text item is exact owner reuse.
- Primitive data vs derived API: the source-facing construction `homogenizationSet` is already
  available from Text 3.5.5; this item adds only the derived convexity statement for the
  intersection of two such sets.
- Domain-style sampling: this item reuses the existing owner/data split given by
  `homogenizationSet`, `mem_homogenizationSet_iff`, `Convex.homogenizationSet`, and
  `Convex.inter`.
- Layer target: `core/canonical`; this numbered text is exact reuse of an owner theorem, so the
  entry point should be `recall` rather than a parallel local declaration.

Abstraction audit (canonicalize):
- Codomain/ambient layer more concrete than needed? `No`: this is already an intrinsic set-convexity
  statement over `Set (R × E)`.
- Scalar or ambient structure really essential? `Partially`: this file introduces no stronger local
  assumptions; it reuses exactly the upstream assumptions of `Convex.homogenizationSet`.
- Owner tied to a concrete model? `No`: owner surfaces are `Convex` and `homogenizationSet`.
- Ambient vs intrinsic topology language? `N/A` (non-topological item).
- Owner naming too concrete/long? `No`: owner-facing names are short and canonical.
- Notation needed on theorem surfaces? `Yes`; this file uses and extends the `K[R | _]` surface.
- Concrete arity over-specialization? `Yes` before normalization: binary intersection is the
  textbook instance, but the API should expose indexed-family convexity as the intrinsic layer.
-/

open scoped Rockafellar

section

universe u

variable {R : Type*} {E : Type u}
variable [Semifield R] [PartialOrder R] [IsOrderedRing R] [PosMulReflectLT R]
  [AddCommMonoid E] [Module R E]

namespace Convex

/-- Indexed-family canonical form: if each `C i` is convex, then the intersection of their
homogenization sets is convex. The binary Text 3.6.13 statement is the arity-2 specialization. -/
theorem iInter_homogenizationSet {ι : Sort*} {C : ι → Set E}
    (hC : ∀ i, Convex R (C i)) :
    Convex R (⋂ i, K[R | C i]) := by
  exact convex_iInter fun i => (hC i).homogenizationSet

/-- Intrinsic-family set form: for a set of convex sets `𝒞`, the intersection of the image family
`{K[R | C] | C ∈ 𝒞}` is convex. -/
theorem sInter_image_homogenizationSet {𝒞 : Set (Set E)}
    (h𝒞 : ∀ C ∈ 𝒞, Convex R C) :
    Convex R (⋂₀ ((fun C : Set E => K[R | C]) '' 𝒞)) := by
  refine convex_sInter ?_
  intro S hS
  rcases hS with ⟨C, hC, rfl⟩
  exact (h𝒞 C hC).homogenizationSet

end Convex

end

/-- Text 3.6.13: for convex sets `C₁` and `C₂`, the set of pairs `(λ, x)` belonging to both
homogenization sets is convex at the canonical scalar/module layer, with concrete coordinate
specializations handled downstream as needed. -/
recall Convex.homogenizationSet_inter
