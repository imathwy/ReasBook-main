import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the scheme-morphism owner `IsFinite` and the
-- closed-map theorem `Scheme.Hom.isClosedMap`; local Chapter 29 precedent states finite morphisms
-- as `[IsFinite f]` and point-set images as `f.base '' T`. The source tag evidence is consistent:
-- item tag `03HX` agrees with the Stacks URL ending in `/tag/03HX`.

/-- Lemma 29.48.7 (1): if `f : Y \to X` is a finite morphism of schemes and `T` is a
closed nowhere dense subset of `Y`, then the set-theoretic image `f(T)` is closed in `X`. -/
@[stacks 03HX]
theorem isClosed_image_of_isFinite_of_isClosed_isNowhereDense
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] (T : Set Y)
    (hT_closed : IsClosed T) (hT_nowhere : IsNowhereDense T) :
    IsClosed (f.base '' T) := sorry

/-- Lemma 29.48.7 (2): if `f : Y \to X` is a finite morphism of schemes and `T` is a
closed nowhere dense subset of `Y`, then the set-theoretic image `f(T)` is nowhere dense in `X`. -/
@[stacks 03HX]
theorem isNowhereDense_image_of_isFinite_of_isClosed_isNowhereDense
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] (T : Set Y)
    (hT_closed : IsClosed T) (hT_nowhere : IsNowhereDense T) :
    IsNowhereDense (f.base '' T) := sorry

end AlgebraicGeometry
