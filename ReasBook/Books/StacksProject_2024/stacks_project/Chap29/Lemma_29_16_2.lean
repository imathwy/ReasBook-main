import Mathlib.AlgebraicGeometry.ResidueField
import StacksProject_2024.Chap29.Definition_29_15_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall / analogue check:
- local Chapter 29 precedent in `Definition_29_15_1` records scheme morphisms “of finite type” as
  `Scheme.Hom.FiniteType`;
- `Chap10/Lemma_10_54_4` already records the Artinian-local residue criterion on the ring side, so
  this file should remain only the scheme-language bridge;
- for `X = Spec(A)` with `A` local and Artinian, the source composition `Spec(κ) ⟶ Spec(A) ⟶ S`
  is canonically the residue-field point of the closed point of `Spec(A)`, with the raw
  `Spec.map (A → κ(A))` form kept as a bridge.
-/

/-- For a local ring `A`, the canonical residue-field point of the closed point of `Spec(A)` is
the scheme morphism induced by the residue map `A → κ(A)`. -/
private theorem fromSpecResidueField_closedPoint
    (A : Type u) [CommRing A] [IsLocalRing A] :
    (Spec (CommRingCat.of A)).fromSpecResidueField (IsLocalRing.closedPoint A) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) :=
  rfl

/-- Lemma 29.16.2: if `A` is an Artinian local ring with residue field `κ`, then a morphism
`f : Spec(A) ⟶ S` is of finite type if and only if the composition
`Spec(κ) ⟶ Spec(A) ⟶ S` is of finite type. -/
@[stacks 02HV]
theorem finiteType_iff_finiteType_comp_residueField
    {S : Scheme.{u}} {A : Type u} [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (f : Spec (CommRingCat.of A) ⟶ S) :
    FiniteType f ↔
      FiniteType
        ((Spec (CommRingCat.of A)).fromSpecResidueField (IsLocalRing.closedPoint A) ≫ f) := by
  sorry

/-- Companion bridge: for the closed point of `Spec(A)`, Lemma 29.16.2 can be rewritten using the
explicit morphism induced by the residue map `A → κ(A)`. -/
theorem finiteType_iff_finiteType_comp_specMap_residue
    {S : Scheme.{u}} {A : Type u} [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (f : Spec (CommRingCat.of A) ⟶ S) :
    FiniteType f ↔
      FiniteType (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ f) := by
  simpa [fromSpecResidueField_closedPoint A] using
    finiteType_iff_finiteType_comp_residueField f

end Scheme.Hom
end AlgebraicGeometry
