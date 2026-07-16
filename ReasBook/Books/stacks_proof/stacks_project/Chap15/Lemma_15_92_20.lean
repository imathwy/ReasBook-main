import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_59_13
import stacks_proof.stacks_project.Chap15.Definition_15_92_4
import stacks_proof.stacks_project.Chap15.Lemma_15_92_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/- Domain-style sampling for Lemma 15.92.20:
- primary domain: vanishing criteria for derived-complete objects of `D(A)` with respect to a
  finitely generated ideal, expressed through the canonical derived tensor product with the quotient
  object `(A ⧸ I)[0]`;
- sampled owner-side declarations:
  `DerivedCategory.IsDerivedCompleteWithRespectTo`,
  `CategoryTheory.derivedTensorProduct`,
  `DerivedTensorProduct` notation `K ⊗[A]^L L`,
  `derivedTensorProduct_isZero_of_modIdealPow_of_modIdeal_isZero`,
  `derivedLimitOfKoszulPowerTensorFunctorAdjunction`;
- best owner abstraction: the source-facing owner remains the predicate
  `K.IsDerivedCompleteWithRespectTo I`; the quotient tensor object `K ⊗[A]^L (A ⧸ I)[0]` is
  derived API and should use the chapter's canonical tensor notation rather than raw functor
  application;
- primitive data: the ideal `I`, finite generation `hI`, the derived object `K`, derived
  completeness of `K` with respect to `I`, and vanishing of the quotient tensor;
- derived API: the powered-Koszul tower comparison and its adjunction consequences, which belong in
  the proof route rather than in this theorem's public surface.

Source/core/bridge triage:
- `source-facing`: the vanishing criterion below for a derived-complete object annihilated modulo
  `I`;
- `core/canonical`: `K.IsDerivedCompleteWithRespectTo I` and the derived tensor owner
  `K ⊗[A]^L L`;
- `bridge/view`: finite-generator presentations of `I` and the powered-Koszul comparison machinery
  from Lemmas `15.89.8` and `15.92.18`. -/

-- Proof sketch: choose generators of the finitely generated ideal `I`, apply Lemma `15.89.8` to
-- deduce that tensoring `K` with each powered Koszul stage is zero from the vanishing modulo `I`,
-- and then use the derived-complete comparison from Lemma `15.92.18` to identify `K` with the
-- derived limit of that zero inverse system.
/-- Helper for Lemma 15.92.20: a finitely generated ideal can be reindexed by a finite family
`f : Fin r → A` without changing its span. -/
lemma exists_fin_generators_of_fg
    (I : Ideal A) (hI : I.FG) :
    ∃ r : ℕ, ∃ f : Fin r → A, Ideal.span (Set.range f) = I := by
  classical
  obtain ⟨s, hs⟩ := hI
  let r : ℕ := s.card
  let f : Fin r → A := fun i ↦ (s.equivFin.symm i : A)
  refine ⟨r, f, ?_⟩
  -- Proof comment: reindex the chosen finite generating set by `Fin r` and compare the two ranges.
  rw [← hs]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (s.equivFin.symm i).2
  · intro hx
    exact ⟨s.equivFin ⟨x, hx⟩, by simp [f]⟩

/-- Helper for Lemma 15.92.20: derived completeness is preserved by every integer shift. -/
lemma isDerivedCompleteWithRespectTo_shift_int
    (I : Ideal A) {K : DMod} (m : ℤ)
    (hK : K.IsDerivedCompleteWithRespectTo I) :
    K⟦m⟧.IsDerivedCompleteWithRespectTo I := by
  intro f hf E
  -- Proof comment: shift a morphism into `K⟦m⟧` back by `-m`, where the original derived
  -- completeness hypothesis on `K` applies directly.
  let F :
      DerivedCategory (ModuleCat (Localization.Away f)) ⥤ DMod :=
    (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
  let hsub : Subsingleton (F.obj (E⟦(-m : ℤ)⟧) ⟶ K) := hK f hf (E⟦(-m : ℤ)⟧)
  have hm : m + (-m) = (0 : ℤ) := by
    omega
  let eK : ((K⟦m⟧)⟦(-m : ℤ)⟧) ≅ K :=
    (shiftFunctorCompIsoId DMod m (-m : ℤ) hm).app K
  refine ⟨fun u v ↦ ?_⟩
  let u' : F.obj (E⟦(-m : ℤ)⟧) ⟶ K :=
    ((F.commShiftIso (-m : ℤ)).hom.app E) ≫ u⟦(-m : ℤ)⟧' ≫ eK.hom
  let v' : F.obj (E⟦(-m : ℤ)⟧) ⟶ K :=
    ((F.commShiftIso (-m : ℤ)).hom.app E) ≫ v⟦(-m : ℤ)⟧' ≫ eK.hom
  have hu'v' : u' = v' := hsub.elim _ _
  have huv :
      ((F.commShiftIso (-m : ℤ)).hom.app E) ≫ u⟦(-m : ℤ)⟧' ≫ eK.hom =
        ((F.commShiftIso (-m : ℤ)).hom.app E) ≫ v⟦(-m : ℤ)⟧' ≫ eK.hom := by
    simpa [u', v'] using hu'v'
  have hshift :
      u⟦(-m : ℤ)⟧' = v⟦(-m : ℤ)⟧' := by
    apply (cancel_epi ((F.commShiftIso (-m : ℤ)).hom.app E)).1
    apply (cancel_mono eK.hom).1
    simpa [Category.assoc] using huv
  exact (shiftFunctor DMod (-m : ℤ)).map_injective hshift

/-- Helper for Lemma 15.92.20: shifting the left tensor factor preserves the vanishing of the
quotient tensor product. -/
lemma derivedTensorProduct_modIdeal_shift_isZero
    (I : Ideal A) (K : DMod)
    (hKI : IsZero (K ⊗[A]^L (single₀).obj (ModuleCat.of A (A ⧸ I)))) (n : ℤ) :
    IsZero ((K⟦n⟧) ⊗[A]^L (single₀).obj (ModuleCat.of A (A ⧸ I))) := by
  -- Proof comment: tensoring with the quotient object commutes with shifts in the left variable,
  -- so the shifted tensor product is just a shift of an already zero object.
  have hShiftedZero :
      IsZero (((K ⊗[A]^L (single₀).obj (ModuleCat.of A (A ⧸ I)))⟦n⟧)) := by
    exact Functor.map_isZero (shiftFunctor DMod n) hKI
  exact
    hShiftedZero.of_iso
      (((derivedTensorProduct_commShift
        ((single₀).obj (ModuleCat.of A (A ⧸ I)))).commShiftIso n).app K)

/-- Helper for Lemma 15.92.20: if the shift `K⟦i - 1⟧` has no positive cohomology, then the
degree-`i` cohomology object of `K` is zero. -/
lemma homology_isZero_of_shifted_isLE_zero
    (K : DMod) (i : ℤ)
    (hK : (K⟦i - 1⟧).IsLE 0) :
    IsZero ((H i).obj K) := by
  -- Proof comment: degree `1` of the shifted object lies above the `D^{≤ 0}` bound, and the
  -- standard homology shift isomorphism transports that vanishing back to degree `i`.
  letI : (K⟦i - 1⟧).IsLE 0 := hK
  have hshifted :
      IsZero ((H 1).obj (K⟦i - 1⟧)) := by
    exact DerivedCategory.isZero_of_isLE (K⟦i - 1⟧) 0 1 (by omega)
  have hindex : (i - 1) + 1 = i := by
    omega
  let e :
      (H 1).obj (K⟦i - 1⟧) ≅ (H i).obj K :=
    ((H 0).shiftIso (i - 1) 1 i hindex).app K
  exact e.isZero_iff.1 hshifted

/-- Helper for Lemma 15.92.20: an object of `D(A)` is zero as soon as all of its cohomology
objects are zero. -/
lemma isZero_of_homologyFunctor_obj_isZero
    (K : DMod) (hK : ∀ i : ℤ, IsZero ((H i).obj K)) :
    IsZero K := by
  -- Proof comment: vanishing in every degree places `K` simultaneously in `D^{≤ 0}` and
  -- `D^{≥ 1}`, and the empty overlap of the standard t-structure is zero.
  have hLE : K.IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact hK i
  have hGE : K.IsGE 1 := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact hK i
  letI : K.IsLE 0 := hLE
  letI : K.IsGE 1 := hGE
  exact t.isZero K 0 1 (by omega)

/-- Lemma 15.92.20: let `I` be a finitely generated ideal of a commutative ring `A`, and let
`K ∈ D(A)` be derived complete with respect to `I`. If
`K \otimes_A^{\mathbf L} (A ⧸ I)[0]` is the zero object, then `K` is the zero object. -/
@[stacks 0G1U]
theorem isZero_of_isDerivedCompleteWithRespectTo_of_derivedTensorProduct_modIdeal_isZero
    (I : Ideal A) (hI : I.FG) (K : DMod)
    (hK : K.IsDerivedCompleteWithRespectTo I)
    (hKI : IsZero (K ⊗[A]^L (single₀).obj (ModuleCat.of A (A ⧸ I)))) :
    IsZero K := by
  classical
  obtain ⟨r, f, hspan⟩ := exists_fin_generators_of_fg (A := A) I hI
  have hKspan :
      K.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f)) := by
    -- Proof comment: rewrite the ideal through the chosen finite generating family.
    simpa [hspan] using hK
  have hKIspan :
      IsZero (K ⊗[A]^L (single₀).obj
        (ModuleCat.of A (A ⧸ Ideal.span (Set.range f)))) := by
    -- Proof comment: the quotient tensor hypothesis is the same after replacing `I` by its
    -- reindexed span presentation.
    cases hspan
    simpa using hKI
  refine isZero_of_homologyFunctor_obj_isZero (A := A) K ?_
  intro i
  -- Proof comment: apply Lemma `15.92.19` to the shift `K⟦i - 1⟧`, then transport the resulting
  -- `D^{≤ 0}` bound back to the actual degree-`i` cohomology of `K`.
  have hKshift :
      (K⟦i - 1⟧).IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f)) :=
    isDerivedCompleteWithRespectTo_shift_int (A := A) (Ideal.span (Set.range f)) (i - 1) hKspan
  have hKIshift :
      IsZero ((K⟦i - 1⟧) ⊗[A]^L
        (single₀).obj (ModuleCat.of A (A ⧸ Ideal.span (Set.range f)))) :=
    derivedTensorProduct_modIdeal_shift_isZero
      (A := A) (Ideal.span (Set.range f)) K hKIspan (i - 1)
  have hTensorLE :
      (((K⟦i - 1⟧) ⊗[A]^L
        (single₀).obj (ModuleCat.of A (A ⧸ Ideal.span (Set.range f))))).IsLE 0 := by
    -- Proof comment: a zero object has vanishing cohomology in every degree.
    rw [DerivedCategory.isLE_iff]
    intro j hj
    exact Functor.map_isZero (H j) hKIshift
  have hTfae :
      List.TFAE [
        (K⟦i - 1⟧).IsLE 0,
        (((K⟦i - 1⟧) ⊗[A]^L
          (single₀).obj (ModuleCat.of A (A ⧸ Ideal.span (Set.range f))))).IsLE 0,
        (((K⟦i - 1⟧) ⊗[A]^L
          (derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op 0))).IsLE 0
      ] :=
    derivedComplete_isLE_zero_tfae_of_span_range (A := A) f (K⟦i - 1⟧) hKshift
  have hShiftLE : (K⟦i - 1⟧).IsLE 0 := (hTfae.out 1 0).mp hTensorLE
  exact homology_isZero_of_shifted_isLE_zero (A := A) K i hShiftLE

end

end CategoryTheory
