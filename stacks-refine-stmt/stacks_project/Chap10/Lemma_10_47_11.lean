import Mathlib
import stacks_project.Chap10.Definition_10_47_4
import stacks_project.Chap10.Lemma_10_47_10

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CommRingCat
open CategoryTheory MorphismProperty
open scoped RatFunc

namespace Algebra

open IntermediateField

noncomputable section

universe u

section

variable {M L K : Type u}
variable [Field M] [Field L] [Field K]
variable [Algebra M L] [Algebra L K] [Algebra M K] [IsScalarTower M L K]

attribute [local instance] Polynomial.algebra

private theorem adjoinSimple_restrictScalars_le (x : K) :
    M⟮x⟯ ≤ (L⟮x⟯).restrictScalars M := by
  rw [adjoin_simple_le_iff]
  exact mem_adjoin_simple_self L x

noncomputable instance adjoinSimpleAlgebra (x : K) : Algebra M⟮x⟯ L⟮x⟯ :=
  (IntermediateField.inclusion (adjoinSimple_restrictScalars_le x)).toAlgebra

variable [GeometricallyIrreducible (Spec.map (ofHom (algebraMap M L)))]

-- Proof sketch: use `RatFunc.algEquivOfTranscendental` to identify `M(x)` and `L(x)` with the
-- one-variable rational function fields over `M` and `L`, transport geometric irreducibility
-- across those algebra equivalences, and then apply Lemma 10.47.10 to `L / M`.
/-- Lemma 10.47.11 (Tag `0G32`): let `K/L/M` be a tower of fields with `L / M` geometrically
irreducible. If `x ∈ K` is transcendental over `L`, then `L(x) / M(x)` is geometrically
irreducible. -/
@[stacks 0G32]
theorem Lemma_10_47_11 (x : K)
    (hx : Transcendental L x) :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap M⟮x⟯ L⟮x⟯))) := by
  letI : IsScalarTower M M⟮x⟯ L⟮x⟯ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let xMap : M⟮x⟯ →ₐ[M] L⟮x⟯ := IsScalarTower.toAlgHom M M⟮x⟯ L⟮x⟯
  let hxM : Transcendental M x := Transcendental.of_tower_top M hx
  let eM : M⟮X⟯ ≃ₐ[M] M⟮x⟯ := RatFunc.algEquivOfTranscendental x hxM
  let eL : L⟮X⟯ ≃ₐ[M] L⟮x⟯ := (RatFunc.algEquivOfTranscendental x hx).restrictScalars M
  let eMhom : M⟮X⟯ →ₐ[M] M⟮x⟯ := eM.toAlgHom
  let eLinv : L⟮x⟯ →ₐ[M] L⟮X⟯ := eL.symm.toAlgHom
  let XMap : M⟮X⟯ →ₐ[M] L⟮X⟯ := IsScalarTower.toAlgHom M M⟮X⟯ L⟮X⟯
  let eMComm : of M⟮X⟯ ≅ of M⟮x⟯ := eM.toRingEquiv.toCommRingCatIso
  let eLComm : of L⟮X⟯ ≅ of L⟮x⟯ := eL.toRingEquiv.toCommRingCatIso
  let iM : Spec (of M⟮x⟯) ≅ Spec (of M⟮X⟯) :=
    Scheme.Spec.mapIso eMComm.op
  let iL : Spec (of L⟮x⟯) ≅ Spec (of L⟮X⟯) :=
    Scheme.Spec.mapIso eLComm.op
  have hX : GeometricallyIrreducible (Spec.map (ofHom (algebraMap M⟮X⟯ L⟮X⟯))) :=
    Lemma_10_47_10.mp
      (inferInstance : GeometricallyIrreducible (Spec.map (ofHom (algebraMap M L))))
  have hcomp_alg :
      (eLinv.comp (xMap.comp eMhom) : M⟮X⟯ →ₐ[M] L⟮X⟯) = XMap := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial M))
    apply Polynomial.algHom_ext
    change eL.symm (xMap (eM RatFunc.X)) = XMap RatFunc.X
    have heM : eM RatFunc.X = AdjoinSimple.gen M x := by
      ext
      simp [eM]
    have heL : eL.symm (AdjoinSimple.gen L x) = RatFunc.X := by
      simp [eL]
    rw [heM]
    change eL.symm (AdjoinSimple.gen L x) = XMap RatFunc.X
    rw [heL]
    symm
    rw [← RatFunc.algebraMap_X]
    change (IsFractionRing.lift (FaithfulSMul.algebraMap_injective (Polynomial M) L⟮X⟯))
        RatFunc.X = RatFunc.X
    rw [← RatFunc.algebraMap_X]
    have hpolyX : (algebraMap (Polynomial M) L⟮X⟯) Polynomial.X = RatFunc.X := by
      change
        (algebraMap (Polynomial L) L⟮X⟯)
            ((Polynomial.mapRingHom (algebraMap M L)) Polynomial.X) = RatFunc.X
      rw [show (Polynomial.mapRingHom (algebraMap M L)) Polynomial.X = Polynomial.X by simp]
      rw [RatFunc.algebraMap_X]
    simpa [hpolyX] using IsFractionRing.lift_algebraMap
      (FaithfulSMul.algebraMap_injective (Polynomial M) L⟮X⟯) Polynomial.X
  have hcomp_cat :
      (ofHom eMhom.toRingHom ≫ ofHom xMap.toRingHom ≫
          ofHom eLinv.toRingHom : of M⟮X⟯ ⟶ of L⟮X⟯) =
        ofHom (algebraMap M⟮X⟯ L⟮X⟯) := by
    ext g
    simpa [CommRingCat.hom_comp, CommRingCat.hom_ofHom, AlgEquiv.toRingEquiv_toRingHom, xMap,
      XMap] using
      congrArg (fun f : M⟮X⟯ →ₐ[M] L⟮X⟯ ↦ f g) hcomp_alg
  have hcomp_spec :
      Spec.map (ofHom eLinv.toRingHom) ≫
        Spec.map (ofHom xMap.toRingHom) ≫
        Spec.map (ofHom eMhom.toRingHom) =
      Spec.map (ofHom (algebraMap M⟮X⟯ L⟮X⟯)) := by
    simpa [← Spec.map_comp, Category.assoc] using
      congrArg
        (fun f : of M⟮X⟯ ⟶ of L⟮X⟯ ↦ Spec.map f)
        hcomp_cat
  have htransport :
      GeometricallyIrreducible
        (Spec.map (ofHom eLinv.toRingHom) ≫
          Spec.map (ofHom xMap.toRingHom) ≫
          Spec.map (ofHom eMhom.toRingHom)) := by
    rw [hcomp_spec]
    exact hX
  have hmid :
      GeometricallyIrreducible
        (Spec.map (ofHom xMap.toRingHom) ≫ Spec.map (ofHom eMhom.toRingHom)) := by
    refine (MorphismProperty.cancel_left_of_respectsIso
      (@GeometricallyIrreducible : MorphismProperty Scheme) iL.symm.hom _).mp ?_
    simpa [iL, eL, CommRingCat.hom_ofHom, RingEquiv.toCommRingCatIso_inv,
      AlgEquiv.toRingEquiv_toRingHom, Category.assoc] using htransport
  have hGI : GeometricallyIrreducible (Spec.map (ofHom xMap.toRingHom)) := by
    refine (MorphismProperty.cancel_right_of_respectsIso
      (@GeometricallyIrreducible : MorphismProperty Scheme) _ iM.hom).mp ?_
    simpa [iM, eM, CommRingCat.hom_ofHom, RingEquiv.toCommRingCatIso_hom,
      AlgEquiv.toRingEquiv_toRingHom, Category.assoc] using hmid
  simpa [xMap] using hGI

end

end

end Algebra
