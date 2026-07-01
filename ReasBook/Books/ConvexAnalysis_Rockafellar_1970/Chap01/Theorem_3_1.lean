import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

/-
Source/core/bridge triage:
- `source-facing`: Theorem 3.1 states that the sum of two convex subsets is again convex.
- `core/canonical`: the owner abstraction is the intrinsic predicate `Convex 𝕜 s` on sets. The
  chapter owner theorem should live at the primitive additive scalar-action layer.
- `bridge/view`: the textbook sum
  `C₁ + C₂ = {x₁ + x₂ | x₁ ∈ C₁, x₂ ∈ C₂}`
  is exactly mathlib's pointwise set addition notation `C₁ + C₂`.
- Primitive data vs derived API: the sets `C₁` and `C₂` are primitive; the convexity of their
  pointwise sum is the whole statement.
- Domain-style sampling: Chapter 1 already fixes the owner notion in `Definition_2_0_1` by
  recalling `Convex`; this file provides the weak-layer additive closure bridge used directly by
  downstream finite-sum items.
- Layer target: `core/canonical`; expose the binary closure owner at the primitive layer
  `[DistribSMul 𝕜 E]`, with mathlib's `Convex.add` as a stronger specialization.

Abstraction audit (canonicalize):
- Codomain/ambient layer over-concrete? `No`: this item is codomain-free.
- Scalar/ambient structure stronger than needed? `Yes` in the old `Convex.add`-only surface:
  binary convex-sum closure does not require a full module structure.
- Owner tied to a concrete model? `No`: owner is the intrinsic set predicate `Convex 𝕜`.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: this is a convexity-closure theorem,
  not a topological closure/interior statement.
- Owner name/notation too heavy or too concrete? `No`: the theorem stays on the short owner
  namespace `Convex` and pointwise sum notation `A + B`.
- Upstream over-specialization to repair first? `Yes`: provide the weak binary bridge here and
  reuse it downstream instead of duplicating local private replacements.
-/

section

variable {𝕜 E : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [DistribSMul 𝕜 E]

/- Theorem 3.1 at the canonical mathlib owner layer (module specialization). -/
recall Convex.add

/-- Theorem 3.1 at the primitive additive scalar-action layer: if `A` and `B` are convex, then
their pointwise sum `A + B` is convex. This is the chapter-level owner bridge; mathlib's
`Convex.add` is the stronger `[Module 𝕜 E]` specialization. -/
theorem Convex.add_set {A B : Set E} (hA : Convex 𝕜 A) (hB : Convex 𝕜 B) :
    Convex 𝕜 (A + B) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨xA, hxA, xB, hxB, rfl⟩
  rcases hy with ⟨yA, hyA, yB, hyB, rfl⟩
  refine ⟨a • xA + b • yA, hA hxA hyA ha hb hab, a • xB + b • yB, hB hxB hyB ha hb hab, ?_⟩
  simp [smul_add, add_assoc, add_left_comm]

end
