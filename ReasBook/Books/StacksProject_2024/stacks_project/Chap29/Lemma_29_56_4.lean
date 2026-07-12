import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the scheme-morphism owner `LocallyQuasiFinite`
-- and the topological owner `IsNowhereDense`. Local Chapter 29 precedent states point-set images
-- as `f.base '' T`, and the finite analogue uses the same closed nowhere-dense hypotheses. The
-- source tag evidence is consistent: item tag `03J2` agrees with the Stacks URL ending in
-- `/tag/03J2`.

/-- Lemma 29.56.4: if `f : Y \to X` is a quasi-finite morphism of schemes and `T` is a
closed nowhere dense subset of `Y`, then the set-theoretic image `f(T)` is nowhere dense in `X`. -/
@[stacks 03J2]
theorem isNowhereDense_image_of_locallyQuasiFinite_of_isClosed_isNowhereDense
    {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f] (T : Set Y)
    (hT_closed : IsClosed T) (hT_nowhere : IsNowhereDense T) :
    IsNowhereDense (f.base '' T) := sorry

end AlgebraicGeometry
