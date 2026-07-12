import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

/-
Source/core/bridge triage:
- `source-facing`: Theorem 3.0.2 says that if a set `C` is convex, then its scalar image
  `c C = {c x | x ∈ C}` is also convex.
- `core/canonical`: mathlib's owner theorem `Convex.smul` is canonical at module level; this file
  also exposes the chapter's weaker scalar-action bridge used downstream.
- `bridge/view`: the textbook notation `c C = {c x | x ∈ C}` is exactly the pointwise set scalar
  action `c • C`.
- Primitive data vs derived API: convexity of `C` is primitive; closure under scalar image is a
  canonical derived theorem. At the chapter abstraction layer, this closure should only require a
  scalar action that distributes over `+` and commutes with convex-combination scaling.
- Domain-style sampling: this item aligns with `Convex.smul`, pointwise set scalar action, and the
  weak-layer bridge pattern used by `Convex.add_set`.
- Layer target: `core/canonical`; keep canonical owner reuse while exposing the weak bridge once
  upstream for direct downstream reuse.

Abstraction audit (canonicalize):
- Codomain/ambient layer over-concrete? `No`: this item is codomain-free.
- Scalar/ambient structure stronger than needed? `Yes` for chapter-wide reuse if only
  `Convex.smul` is exposed, because it forces `[Module 𝕜 E]` and `CommSemiring`.
- Owner tied to a concrete model? `No`: owner stays intrinsic (`Convex` + `•` on sets).
- Ambient-vs-intrinsic topology mismatch? `Not applicable`.
- Owner name/notation too heavy or too concrete? `Yes` for the bridge theorem's old
  implementation-shaped suffix; expose a short owner-facing set surface while keeping textbook `•`.
- Upstream over-specialization to repair first? `Yes`: add one weak-layer chapter bridge here so
  downstream finite-sum items do not rebuild it locally.
-/

/- Theorem 3.0.2: scalar images of convex sets are convex. This item is exactly the canonical
owner theorem `Convex.smul`. -/
recall Convex.smul

section

variable {𝕜 R E : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [DistribSMul R E] [SMulCommClass R 𝕜 E]

/-- Weak-layer chapter bridge for Theorem 3.0.2: scalar images of convex sets are convex at the
primitive scalar-action layer, without forcing a full module structure or requiring the image
scalar to be the same type as the convex-combination scalar. The scalar is implicit so the theorem
composes on theorem surfaces without manual parameter passing. -/
theorem Convex.smul_set {C : Set E} (hC : Convex 𝕜 C) {c : R} :
    Convex 𝕜 (c • C) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨x', hx', rfl⟩
  rcases hy with ⟨y', hy', rfl⟩
  refine ⟨a • x' + b • y', hC hx' hy' ha hb hab, ?_⟩
  change c • (a • x' + b • y') = a • (c • x') + b • (c • y')
  simp [smul_add, smul_comm c a x', smul_comm c b y']

end
