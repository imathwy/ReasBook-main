import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/- Semantic recall: `lean_leansearch` recalled the canonical owners
`Scheme.Hom.QuasiFiniteAt` for quasi-finiteness at a point and `LocallyQuasiFinite` for the
induced morphism on an open subscheme. Local Chapter 29 precedent writes the open inclusion as
`U.ι` and the induced morphism to `S` as `U.ι ≫ f`. The Stacks tag evidence is consistent:
item tag `01TI` and source URL `https://stacks.math.columbia.edu/tag/01TI`. -/

/-- Lemma 29.56.2 (1): for a morphism of schemes `f : X ⟶ S`, the locus of points of `X` where
`f` is quasi-finite is open. -/
@[stacks 01TI]
theorem isOpen_quasiFiniteAt_locus :
    IsOpen {x : X | f.QuasiFiniteAt x} := sorry

/-- Lemma 29.56.2 (2): if `U ⊆ X` is the open locus where `f` is quasi-finite, then the induced
morphism `U ⟶ S` is locally quasi-finite. -/
@[stacks 01TI]
theorem locallyQuasiFinite_of_open_eq_quasiFiniteAt_locus
    (U : X.Opens) (hU : (U : Set X) = {x : X | f.QuasiFiniteAt x}) :
    LocallyQuasiFinite (U.ι ≫ f) := sorry

end Scheme.Hom
end AlgebraicGeometry
