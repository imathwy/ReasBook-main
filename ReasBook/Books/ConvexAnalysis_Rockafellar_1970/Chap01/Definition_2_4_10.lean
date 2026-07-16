import ConvexAnalysis_Rockafellar_1970.Chap01.AffineDimension

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-
Source/core/bridge triage:
- `source-facing`: Definition 2.4.10 names the affine dimension of a set as the
  affine dimension of its affine hull.
- `core/canonical`: the owner abstractions are the affine hull `affineSpan` of a set together
  with the chapter owner notion `AffineSubspace.affineDim` from `AffineDimension`.
- `bridge/view`: the set-level declaration `Set.affineDim` below is the thin composite sending a
  set to the affine dimension of its affine hull. This bridge is intrinsically affine and
  finite-dimensional on the affine-span direction, so it is owned on an arbitrary affine space
  with the needed local finite-dimensional hypothesis.
- Domain-style sampling: the relevant owner declarations are the project owner
  `AffineSubspace.affineDim` from `AffineDimension`, mathlib's `affineSpan`, and the downstream
  bridge pattern from Definition 4.5, where function dimension is read directly as
  `Set.affineDim (dom(f))` rather than through a parallel packaged notion.
- Primitive data vs derived API: the affine hull is primitive; the dimension of a set is derived
  from it and should not be packaged into a separate wrapper structure.
- Layer target: `bridge/view`, preserving the source-facing set-level notion while reusing the
  affine-subspace owner abstraction directly.
-/

namespace Set

variable {𝕜 : Type*} {V : Type*} {P : Type*}
  [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
variable (𝕜)

/-- Definition 2.4.10 as the set-level owner on the intrinsic affine-subspace layer: the affine
dimension of a set whose affine span is finite-dimensional is the affine dimension of its
affine hull. -/
def affineDim (C : Set P) [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction] : ℤ :=
  (affineSpan 𝕜 C).affineDim

end Set

/-- Rockafellar-style set-dimension notation over a scalar division ring. -/
scoped[Rockafellar] notation "dim[" 𝕜 "](" C ")" => Set.affineDim 𝕜 C

namespace Set

variable {𝕜 : Type*} {V : Type*} {P : Type*}
  [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

open scoped Rockafellar

@[simp] theorem dim_eq_affineSpan_affineDim (C : Set P)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction] :
    dim[𝕜](C) = (affineSpan 𝕜 C).affineDim := rfl

end Set
