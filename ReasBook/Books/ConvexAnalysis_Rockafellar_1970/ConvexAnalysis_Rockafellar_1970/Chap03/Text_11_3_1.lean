import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_0_3

-- Declarations for this item will be appended below by the statement pipeline.

namespace Set

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Text 11.3.1 defines what it means for a closed half-space to support a set.
- `core/canonical`: the owner abstractions already present in the project are the predicate
  `IsClosedHalfSpace` on subsets of `X` and the topological boundary operator `frontier`.
- `bridge/view`: the textbook phrase "supporting half-space" is the conjunction of those owner
  notions for a pair `(s, C)`; it does not introduce new primitive structure beyond the
  underlying half-space candidate `s`.
- Primitive data vs derived API: the primitive inputs are the candidate half-space `s` and the
  supported set `C`; the supporting condition itself is a derived `Prop` on the owner `s`,
  with primitive contact data encoded intrinsically as the set-level condition
  `(C ∩ frontier s).Nonempty`, while the pointwise witness form
  `∃ x ∈ C, x ∈ frontier s` is bridge API.
- Domain-style sampling used here: the project declaration `IsClosedHalfSpace`, the Chapter 11
  owner-predicate style in `AffineSubspace.IsSupportingHyperplane`, the refinement pattern in
  `AffineSubspace.IsNontrivialSupportingHyperplane`, and the standard boundary operator
  `frontier`. The notion depends only on these coordinate-free owners, so the declaration should
  live on the pairing-based half-space layer and specialize to concrete coordinate models only
  through downstream bridge instances.
- Layer target: `source-facing`, as a thin predicate on the owner set `s` with ambient supported
  set `C` and atomic companion lemmas, not as a typeclass wrapper.
-/

/-- Text 11.3.1, stated coordinate-free: a set `s` is a supporting half-space to `C` when `s` is
a closed half-space, contains `C`, and has a point of `C` on its boundary. -/
def IsSupportingHalfSpace {𝕜 : Type*} [LE 𝕜] [CommSemiring 𝕜]
    {X Y : Type*} [TopologicalSpace X] [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜] (s C : Set X) : Prop :=
  (closedHalfSpace[Y,𝕜] s) ∧ C ⊆ s ∧ (C ∩ frontier s).Nonempty

/-- Canonical notation for supporting half-spaces with pairing side `Y` over `𝕜`. -/
scoped[Rockafellar] notation:50 s " supports[" Y "," 𝕜 "] " C =>
  Set.IsSupportingHalfSpace (Y := Y) (𝕜 := 𝕜) s C

section

variable {X Y 𝕜 : Type*}
variable [LE 𝕜] [CommSemiring 𝕜]
variable [TopologicalSpace X]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]
open scoped Rockafellar

variable {C s : Set X}

local notation:50 s " supports " C =>
  s supports[Y,𝕜] C

/-- A supporting half-space is a closed half-space. -/
theorem IsSupportingHalfSpace.isClosedHalfSpace (hs : s supports C) :
    IsClosedHalfSpace Y 𝕜 s :=
  hs.1

/-- The supported set lies in every supporting half-space to it. -/
theorem IsSupportingHalfSpace.subset (hs : s supports C) :
    C ⊆ s :=
  hs.2.1

/-- A supporting half-space has a point of the supported set on its boundary. -/
theorem IsSupportingHalfSpace.exists_mem_frontier (hs : s supports C) :
    ∃ x ∈ C, x ∈ frontier s := by
  rcases hs.2.2 with ⟨x, hxC, hxs⟩
  exact ⟨x, hxC, hxs⟩

/-- A supporting half-space meets the supported set on its boundary. -/
theorem IsSupportingHalfSpace.inter_frontier_nonempty
    (hs : s supports C) : (C ∩ frontier s).Nonempty :=
  hs.2.2

end

end Set
