import Mathlib.AlgebraicGeometry.Morphisms.Proper

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/- Semantic recall: `lean_leansearch` pointed to the canonical scheme-morphism properties
`AlgebraicGeometry.IsProper`, `AlgebraicGeometry.IsDominant`, and
`AlgebraicGeometry.IsFinite`; local Chapter 29 precedent keeps integrality of the source and
target schemes ambient for morphism notions over integral schemes, so the source-facing owner here
is the proper/dominant class together with the finite-on-a-nonempty-open clause. -/

/-- Definition 29.51.12: an alteration of an integral scheme `X` is a proper dominant morphism
`f : Y ⟶ X` with `Y` integral such that `f ∣_ U` is finite for some nonempty open `U ⊆ X`. -/
@[stacks 02NW]
class IsAlteration (f : Y ⟶ X) : Prop extends IsProper f, IsDominant f where
  /-- An alteration is finite over some nonempty open of the target. -/
  exists_nonempty_open_isFinite :
    ∃ U : X.Opens, Nonempty U ∧ IsFinite (f ∣_ U)

/-- Unfold `IsAlteration f` into properness, dominance, and the existence of a nonempty open on
which `f` is finite. -/
@[stacks 02NW]
theorem isAlteration_iff (f : Y ⟶ X) :
    IsAlteration f ↔
      IsProper f ∧
        IsDominant f ∧
        ∃ U : X.Opens, Nonempty U ∧ IsFinite (f ∣_ U) := by
  constructor
  · intro h
    exact ⟨h.toIsProper, h.toIsDominant, h.exists_nonempty_open_isFinite⟩
  · rintro ⟨hfProper, hfDominant, hFinite⟩
    exact
      { toIsProper := hfProper
        toIsDominant := hfDominant
        exists_nonempty_open_isFinite := hFinite }

end

end AlgebraicGeometry
