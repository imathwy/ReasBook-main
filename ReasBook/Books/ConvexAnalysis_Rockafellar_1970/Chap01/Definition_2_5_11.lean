import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

namespace Rockafellar

/- Source notation for the canonical nonnegative orthant as a set in an ordered module. -/
scoped notation:max "orthant[" 𝕜 "](" M ")" => (ConvexCone.positive 𝕜 M : Set M)

end Rockafellar

open scoped Rockafellar

/- 
Source/core/bridge triage:
- `source-facing`: Definition 2.5.11 names the nonnegative cone of an ordered ambient space.
- `core/canonical`: the source-facing owner is the set-level orthant notation `orthant[𝕜](M)`;
  the bundled cone `ConvexCone.positive 𝕜 M` is retained as the upstream bridge owner.
- Primitive data vs derived API: the ordered-module structure and set-level orthant are primitive;
  bridges to `ConvexCone.positive` are derived API.
- Domain-style sampling: `orthant[𝕜](M)`, `ConvexCone.positive`, and `ConvexCone.mem_positive`.
- Layer target: `core/canonical`; concrete coordinate models belong in downstream bridge files.
-/

/- Definition 2.5.11: after equipping the ambient space with the relevant order, the
non-negative orthant cone is the canonical positive cone. -/
#check ConvexCone.positive

section SourceFacing

variable {𝕜 M : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  [Module 𝕜 M] [PosSMulMono 𝕜 M]

/-- Canonical short owner theorem: the orthant is the upper set `Set.Ici 0`. -/
@[simp] theorem orthant_eq_Ici :
    orthant[𝕜](M) = Set.Ici (0 : M) :=
  rfl

/-- Canonical short membership theorem for `orthant[𝕜](M)`. -/
@[simp] theorem mem_orthant_iff {x : M} :
    x ∈ orthant[𝕜](M) ↔ 0 ≤ x :=
  Iff.rfl

end SourceFacing
