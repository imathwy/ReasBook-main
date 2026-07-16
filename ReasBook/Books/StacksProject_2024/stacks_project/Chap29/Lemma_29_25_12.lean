import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_24_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

section

variable {X Y : Scheme.{u}}

namespace Scheme.Hom

-- Semantic recall: `lean_leansearch` surfaced the exact mathlib theorem
-- `AlgebraicGeometry.Flat.isQuotientMap_of_surjective`, whose assumptions match this Stacks item
-- after adding quasi-compactness. The source-facing API below keeps the open and closed subset
-- criteria atomic and records the summary conclusion through the local owner
-- `AlgebraicGeometry.Submersive`.

/-- Lemma 29.25.12 (1): if `f : X ⟶ Y` is quasi-compact, surjective, and flat, then a subset
`T ⊆ Y` is open if and only if its inverse image in `X` is open. -/
@[stacks 02JY]
theorem isOpen_iff_preimage_isOpen_of_flat_of_quasiCompact_of_surjective
    (f : X ⟶ Y) [Flat f] [QuasiCompact f] [Surjective f] (T : Set Y) :
    IsOpen T ↔ IsOpen (f.base ⁻¹' T) := sorry

/-- Lemma 29.25.12 (2): if `f : X ⟶ Y` is quasi-compact, surjective, and flat, then a subset
`T ⊆ Y` is closed if and only if its inverse image in `X` is closed. -/
@[stacks 02JY]
theorem isClosed_iff_preimage_isClosed_of_flat_of_quasiCompact_of_surjective
    (f : X ⟶ Y) [Flat f] [QuasiCompact f] [Surjective f] (T : Set Y) :
    IsClosed T ↔ IsClosed (f.base ⁻¹' T) := sorry

/-- Lemma 29.25.12 (3): a quasi-compact, surjective, flat morphism of schemes is submersive. -/
@[stacks 02JY]
theorem submersive_of_flat_of_quasiCompact_of_surjective
    (f : X ⟶ Y) [Flat f] [QuasiCompact f] [Surjective f] :
    Submersive f := sorry

end Scheme.Hom

end
