import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

/- Source/core/bridge triage:
- `source-facing`: a morphism of locally ringed spaces whose underlying ringed-space morphism is
  an isomorphism is itself an isomorphism.
- `core/canonical`: `LocallyRingedSpace.isoOfSheafedSpaceIso`.
- `bridge/view`: the morphism-level companion theorem below, with hypothesis `[IsIso f.toShHom]`,
  is the source-facing specialization of the owner-level canonical iso lift. -/

/- Lemma 26.2.2: an isomorphism of the underlying ringed spaces of locally ringed spaces is
canonically an isomorphism of locally ringed spaces. The canonical owner-level lift is
`LocallyRingedSpace.isoOfSheafedSpaceIso`, and the source-facing morphism statement below is its
morphism-level specialization. -/
#check LocallyRingedSpace.isoOfSheafedSpaceIso

/- Companion specialization: the source-facing morphism statement below reuses the canonical iso
lift on underlying sheafed-space isomorphisms, then views its hom as the original morphism. -/

/-- Lemma 26.2.2: a morphism of locally ringed spaces whose underlying ringed-space morphism is an
isomorphism is itself an isomorphism. -/
@[stacks 01HC, instance]
theorem isIso_of_isIso_toShHom {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [IsIso f.toShHom] :
    IsIso f := by
  let _ : IsIso (forgetToSheafedSpace.map f) := by
    simpa using (inferInstance : IsIso f.toShHom)
  exact Functor.ReflectsIsomorphisms.reflects forgetToSheafedSpace f

end AlgebraicGeometry.LocallyRingedSpace
