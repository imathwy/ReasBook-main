import Mathlib

open AlgebraicGeometry CategoryTheory Limits

universe u

-- Semantic recall: `lean_leansearch` surfaced scheme pullback infrastructure in
-- `Mathlib.AlgebraicGeometry.Pullbacks`; the locally-ringed-space pullback is not available here by
-- instance, so the source-faithful surface is an existence theorem for the pullback in
-- `LocallyRingedSpace` together with a separate theorem that any such pullback object is a scheme.

namespace AlgebraicGeometry

/-- Remark 26.16.2 (1): for morphisms of schemes `f : X ⟶ S` and `g : Y ⟶ S`, the fibre product
of the underlying morphisms of locally ringed spaces exists in the category of locally ringed
spaces. -/
@[stacks 01JN]
theorem hasPullback_toLocallyRingedSpace_of_schemeMorphisms
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    HasPullback (Scheme.forgetToLocallyRingedSpace.map f)
      (Scheme.forgetToLocallyRingedSpace.map g) := sorry

/-- Remark 26.16.2 (2): any pullback of the underlying locally ringed-space morphisms of scheme
morphisms `f : X ⟶ S` and `g : Y ⟶ S` is isomorphic to the locally ringed space underlying a
scheme. -/
@[stacks 01JN]
theorem exists_scheme_of_isLimit_pullbackCone_toLocallyRingedSpace
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {P : LocallyRingedSpace.{u}}
    (p1 : P ⟶ X.toLocallyRingedSpace)
    (p2 : P ⟶ Y.toLocallyRingedSpace)
    (comm : p1 ≫ Scheme.forgetToLocallyRingedSpace.map f =
      p2 ≫ Scheme.forgetToLocallyRingedSpace.map g)
    (hP : IsLimit (PullbackCone.mk p1 p2 comm)) :
    ∃ Z : Scheme.{u}, Nonempty (Z.toLocallyRingedSpace ≅ P) := sorry

end AlgebraicGeometry
