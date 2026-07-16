import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.EisensteinAdjoinRootLocal
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.EisensteinAdjoinRootComplete

/-!
# Complete DVR package for Eisenstein `AdjoinRoot`

This file assembles the local, DVR, completeness, and residue-field pieces for adjoining a root
of a positive-degree Eisenstein polynomial over a complete DVR.
-/

noncomputable section

universe u

namespace Representation

open Polynomial

section EisensteinAdjoinRootPackage

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
variable {f : R[X]}

omit [IsAdicComplete (IsLocalRing.maximalIdeal R) R] in
/-- A positive-degree Eisenstein `AdjoinRoot` over a DVR is not a field. -/
theorem adjoinRoot_not_isField_of_eisenstein
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal R)) (hdeg : 0 < f.natDegree) :
    ¬ IsField (AdjoinRoot f) := by
  intro hfield
  have hlead_unit : IsUnit f.leadingCoeff :=
    IsLocalRing.notMem_maximalIdeal.mp hf.leading
  haveI : Algebra.IsIntegral R (AdjoinRoot f) :=
    adjoinRoot_algebra_isIntegral_of_isUnit_leadingCoeff hlead_unit
  letI : Field (AdjoinRoot f) := hfield.toField
  have hfdeg : f.degree ≠ 0 := (Polynomial.natDegree_pos_iff_degree_pos.mp hdeg).ne'
  have hinj : Function.Injective (algebraMap R (AdjoinRoot f)) :=
    AdjoinRoot.of.injective_of_degree_ne_zero hfdeg
  have hcomap_max :
      ((⊥ : Ideal (AdjoinRoot f)).comap (algebraMap R (AdjoinRoot f))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (⊥ : Ideal (AdjoinRoot f))
  have hcomap_bot :
      (⊥ : Ideal (AdjoinRoot f)).comap (algebraMap R (AdjoinRoot f)) = (⊥ : Ideal R) := by
    rw [Ideal.ext_iff]
    intro x
    change algebraMap R (AdjoinRoot f) x = 0 ↔ x = 0
    simpa using (hinj.eq_iff (a := x) (b := 0))
  have hmax_bot : IsLocalRing.maximalIdeal R = (⊥ : Ideal R) := by
    exact (IsLocalRing.eq_maximalIdeal hcomap_max).symm.trans hcomap_bot
  exact IsDiscreteValuationRing.not_a_field R hmax_bot

omit [IsAdicComplete (IsLocalRing.maximalIdeal R) R] in
/-- The adjoined root of a positive-degree Eisenstein polynomial over a DVR is nonzero. -/
theorem adjoinRoot_root_ne_zero_of_eisenstein
    [IsLocalRing (AdjoinRoot f)]
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal R)) (hdeg : 0 < f.natDegree) :
    AdjoinRoot.root f ≠ 0 := by
  intro hroot_zero
  have hmax :
      IsLocalRing.maximalIdeal (AdjoinRoot f) =
        Ideal.span ({AdjoinRoot.root f} : Set (AdjoinRoot f)) :=
    adjoinRoot_maximalIdeal_eq_span_root_of_eisenstein hf hdeg
  have hbot :
      IsLocalRing.maximalIdeal (AdjoinRoot f) = ⊥ := by
    rw [hmax, hroot_zero, Ideal.span_singleton_zero]
  exact (adjoinRoot_not_isField_of_eisenstein hf hdeg)
    (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot)

/-- Complete-DVR and residue-field package for a positive-degree monic Eisenstein
`AdjoinRoot`. -/
theorem adjoinRoot_complete_dvr_residue_of_eisenstein
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal R)) (hmonic : f.Monic)
    (hdeg : 0 < f.natDegree) [IsDomain (AdjoinRoot f)] :
    ∃ inst : IsDiscreteValuationRing (AdjoinRoot f),
      IsAdicComplete
          (@IsLocalRing.maximalIdeal (AdjoinRoot f) _ inst.toIsLocalRing)
          (AdjoinRoot f) ∧
        Nonempty
          (@IsLocalRing.ResidueField (AdjoinRoot f) _ inst.toIsLocalRing ≃+*
            IsLocalRing.ResidueField R) := by
  letI : IsLocalRing (AdjoinRoot f) :=
    adjoinRoot_isLocalRing_of_eisenstein hf hdeg
  have hroot :
      IsLocalRing.maximalIdeal (AdjoinRoot f) =
        Ideal.span ({AdjoinRoot.root f} : Set (AdjoinRoot f)) :=
    adjoinRoot_maximalIdeal_eq_span_root_of_eisenstein hf hdeg
  have hroot_ne_zero : AdjoinRoot.root f ≠ 0 :=
    adjoinRoot_root_ne_zero_of_eisenstein hf hdeg
  let instDVR : IsDiscreteValuationRing (AdjoinRoot f) :=
    adjoinRoot_isDiscreteValuationRing_of_maximalIdeal_eq_span_root
      (R := R) (f := f) hroot hroot_ne_zero
  refine ⟨instDVR, ?_, ?_⟩
  · letI : IsDiscreteValuationRing (AdjoinRoot f) := instDVR
    exact adjoinRoot_isAdicComplete_maximalIdeal_of_eisenstein hf hmonic hdeg
  · letI : IsDiscreteValuationRing (AdjoinRoot f) := instDVR
    exact
      ⟨adjoinRoot_residueField_equiv_base_of_maximalIdeal_eq_span_root
        (f := f)
        (adjoinRoot_maximalIdeal_eq_span_root_of_eisenstein hf hdeg) hf hdeg⟩

end EisensteinAdjoinRootPackage

end Representation
