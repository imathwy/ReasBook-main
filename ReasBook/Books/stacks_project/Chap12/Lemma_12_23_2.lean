import Mathlib
import stacks_project.Chap12.Definition_12_23_4
import stacks_project.Chap12.Lemma_12_19_12

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

open FilteredObject FilteredObject.Hom

namespace HomologicalComplex.Filtered

variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

/-- The page-`E₀` complex attached to the filtered differential object `K`. -/
noncomputable def pageZero :
    HomologicalComplex C (ComplexShape.up' (0 : ℤ)) :=
  { X := fun p ↦ (gradedPiece K p).X PUnit.unit
    d := fun p q ↦
      if h : p = q then by
        subst h
        exact (gradedPiece K p).d PUnit.unit PUnit.unit
      else 0
    shape := fun p q hpq ↦ by
      by_cases h : p = q
      · exfalso
        exact hpq (by simp [ComplexShape.up', h])
      · simp [h]
    d_comp_d' := fun p q r hpq hqr ↦ by
      have hpq' : p = q := by
        simpa [ComplexShape.up'] using hpq
      have hqr' : q = r := by
        simpa [ComplexShape.up'] using hqr
      subst hpq'
      subst hqr'
      simpa [gradedPiece] using
        (gradedPiece K p).d_comp_d PUnit.unit PUnit.unit PUnit.unit }

private noncomputable def pageZeroScIso (p : ℤ) :
    (pageZero K).sc' p p p ≅
      (gradedPiece K p).sc' PUnit.unit PUnit.unit PUnit.unit :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [pageZero, gradedPiece])
    (by simp [pageZero, gradedPiece])

/-- The page-`E₀` complex computes, in degree `p`, the homology of the graded differential object
`gr^p(K)`. -/
noncomputable def pageZeroHomologyIso (p : ℤ) :
    (pageZero K).homology p ≅
      (gradedPiece K p).homology PUnit.unit := by
  let hprevPage : (ComplexShape.up' (0 : ℤ)).prev p = p :=
    ComplexShape.prev_eq' (ComplexShape.up' (0 : ℤ)) (by simp [ComplexShape.up'])
  let hnextPage : (ComplexShape.up' (0 : ℤ)).next p = p :=
    ComplexShape.next_eq' (ComplexShape.up' (0 : ℤ)) (by simp [ComplexShape.up'])
  exact
    (pageZero K).homologyIsoSc' p p p hprevPage hnextPage ≪≫
      ShortComplex.homologyMapIso (pageZeroScIso K p) ≪≫
        ((gradedPiece K p).homologyIsoSc' PUnit.unit PUnit.unit PUnit.unit
          rfl rfl).symm

variable {E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0}

/-- The core owner class asserting that `E` is a spectral sequence associated to the filtered
differential object `K`, encoded by the literal page-zero identification with the associated
graded differential object. -/
class IsAssociatedToFilteredDifferentialObject
    (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0) : Prop where
  pageZero_eq : E.page 0 = pageZero K

/-- Source-facing companion: the owner page-zero equality yields the canonical isomorphism from
the zeroth page of `E` to the graded page-zero complex of `K`. -/
noncomputable def pageZeroIso
    (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    [hE : IsAssociatedToFilteredDifferentialObject K E] :
    E.page 0 ≅ pageZero K :=
  eqToIso hE.pageZero_eq

/-- The page-`E₁` identification induced by a page-`E₀` comparison with the associated graded
complex. -/
noncomputable def pageOneIso
    (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    [hE : IsAssociatedToFilteredDifferentialObject K E] (p : ℤ) :
    (E.page 1).X p ≅
      (gradedPiece K p).homology PUnit.unit :=
  (E.iso 0 1 p).symm ≪≫
    HomologicalComplex.homologyMapIso (pageZeroIso K E) p ≪≫
      pageZeroHomologyIso K p

/-- Lemma 12.23.2: a filtered differential object admits an associated spectral sequence together
with the canonical page-`E₀` comparison isomorphism to the associated graded differential object
`pageZero K`. The page-`E₁` identification with the homology of the graded pieces is then derived
from the owner class `IsAssociatedToFilteredDifferentialObject K E`, the owner transition
`E.iso 0 1`, and `pageOneIso`, rather than stored as separate primitive data. -/
theorem exists_associatedSpectralSequence :
    ∃ E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0,
      IsAssociatedToFilteredDifferentialObject K E := by
  sorry

end HomologicalComplex.Filtered

end CategoryTheory
