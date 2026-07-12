import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-theoretic-image owner
-- `Scheme.Hom.image`, its closed immersion `Scheme.Hom.imageι`, and the restriction notation
-- `f ∣_ V`. Local Chapter 29 files state retrocompact opens as `IsRetrocompact (V : Set Y)`.
-- The Stacks tag evidence is consistent: item tag `0CNG` matches the source URL `/tag/0CNG`.

/-- Lemma 29.6.8: let `f : X ⟶ Y` be a separated morphism of schemes, let `V ⊆ Y` be a
retrocompact open, and let `s : V ⟶ X` be a section of `f` over `V`. If `Y'` is the
scheme-theoretic image of `s`, then the induced morphism `Y' ⟶ Y` is an isomorphism over `V`. -/
@[stacks 0CNG]
theorem schemeTheoreticImage_section_restrict_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] (V : Y.Opens)
    (hVretro : IsRetrocompact (V : Set Y)) (s : (V : Scheme.{u}) ⟶ X)
    (hs : s ≫ f = V.ι) :
    IsIso ((Scheme.Hom.imageι s ≫ f) ∣_ V) := sorry

end AlgebraicGeometry
