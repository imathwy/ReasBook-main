import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` recalled `Scheme.PartialMap`, `Scheme.RationalMap.IsOver`,
-- and `IsProper`. Local Chapter 29 precedent uses a concrete `PartialMap` when the source keeps
-- the chosen dense open domain `U` visible.

/-- Predicate saying that `p : X' ⟶ X` is the proper modification and
`f' : X' ⟶ Y` is the extension of a partial map over `S`. -/
structure IsProperModificationExtension
    (S : Scheme.{u}) {X Y X' : Scheme.{u}} [X.Over S] [Y.Over S]
    (f : X.PartialMap Y) (p : X' ⟶ X) (f' : X' ⟶ Y) : Prop where
  /-- The projection to `X` is proper. -/
  isProper : IsProper p
  /-- The projection is an isomorphism over the original domain. -/
  isIsoRestrict : IsIso (p ∣_ f.domain)
  /-- The extension map is over `S`. -/
  mapOver : f' ≫ (Y ↘ S) = p ≫ (X ↘ S)
  /-- The extension agrees with the original partial map on the pulled-back domain. -/
  restrict_eq : (p ⁻¹ᵁ f.domain).ι ≫ f' = (p ∣_ f.domain) ≫ f.hom

/-- Lemma 31.36.2: let `S` be a scheme, let `X` and `Y` be schemes over `S`, with `X`
Noetherian and `Y` proper over `S`. Given an `S`-rational map from a dense open subscheme of
`X` to `Y`, there is a proper morphism `p : X' ⟶ X` and an `S`-morphism `f' : X' ⟶ Y` such that
`p` is an isomorphism over the domain of the rational map and `f'` restricts there to the given
map. -/
@[stacks 0C4V]
theorem exists_proper_modification_extending_partialMap
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [IsNoetherian X] [IsProper (Y ↘ S)]
    (f : X.PartialMap Y) (hf : f.IsOver S) :
    ∃ (X' : Scheme.{u}) (p : X' ⟶ X) (f' : X' ⟶ Y),
      IsProperModificationExtension S f p f' := sorry

end AlgebraicGeometry
