import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Serre.Chap16.Corollary_16_16_1_6
import LinearRepresentations_Serre_1977.Serre.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Serre.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Serre.Chap18.Remark_18_18_1_3
import LinearRepresentations_Serre_1977.Serre.Chap18.Corollary_18_18_2_5

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section LocalExercise1829Fallback

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Exercise 18-18.3-2: local source input for the Exercise `18-18.2-9`
coefficient-ring Brauer basis over Serre's complete DVR coefficient ring, bundled with its
evaluation rule so the genuine missing input is recorded only once. -/
theorem exists_exercise_18_18_2_9_irreducible_modular_characters_basis
    (lift : PrimeToPRoot p k → A)
    (hlift : Function.Injective lift)
    (hred : ∀ ζ : PrimeToPRoot p k, IsLocalRing.residue A (lift ζ) = (ζ : k))
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    ∃ b : Module.Basis ι A (PRegularConjClass G p → A),
      ∀ i,
        b i = FDRep.modularCharacterOnPRegularConjClass (p := p) (E i) lift := by
  classical
  letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
  letI : Module.Finite k (PRegularConjClass G p → k) :=
    Module.Finite.of_basis (Pi.basisFun k (PRegularConjClass G p))
  letI : Finite ι :=
    (linearIndependent_brauer_value E (fun i ↦ hE_complete.isSimple i) hE_pairwise).finite
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  have hcard : Fintype.card ι = Fintype.card (PRegularConjClass G p) := by
    simpa [Nat.card_eq_fintype_card] using
      (card_eq_card_pRegularConjugacyClasses_of_complete_simple_family
        (p := p) (E := E) hE_pairwise hE_complete)
  let e : ι ≃ PRegularConjClass G p := Fintype.equivOfCardEq hcard
  let bA : Module.Basis ι A (PRegularConjClass G p → A) :=
    (Pi.basisFun A (PRegularConjClass G p)).reindex e.symm
  let bK : Module.Basis ι k (PRegularConjClass G p → k) :=
    (Pi.basisFun k (PRegularConjClass G p)).reindex e.symm
  let vA : ι → (PRegularConjClass G p → A) := fun i ↦
    FDRep.modularCharacterOnPRegularConjClass (p := p) (E i) lift
  let vK : ι → (PRegularConjClass G p → k) := fun i ↦
    FDRep.modularCharacterOnPRegularConjClass (p := p) (E i) (⇑(valueLift p k))
  have hresidue_modularCharacter :
      ∀ i : ι, (fun c ↦ IsLocalRing.residue A (vA i c)) = vK i := by
    intro i
    funext c
    let s := PRegularConjClass.representative (G := G) (p := p) c
    have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
      apply Subtype.ext
      simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
    rw [← hs]
    change IsLocalRing.residue A
        (FDRep.modularCharacterOnPRegularConjClass (p := p) (E i) lift
          (PRegularConjClass.ofSubtype (G := G) p s)) =
      FDRep.modularCharacterOnPRegularConjClass (p := p) (E i) (⇑(valueLift p k))
        (PRegularConjClass.ofSubtype (G := G) p s)
    rw [FDRep.modularCharacterOnPRegularConjClass_ofSubtype,
      FDRep.modularCharacterOnPRegularConjClass_ofSubtype]
    rw [ringHom_modularCharacter]
    apply modularCharacter_congr_of_eqOn_torsion
    intro x hx
    exact hred x
  have hentry :
      (IsLocalRing.residue A).mapMatrix (bA.toMatrix vA) = bK.toMatrix vK := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply,
      Module.Basis.toMatrix_apply]
    exact congrFun (hresidue_modularCharacter j) (e i)
  have hdet_map : IsLocalRing.residue A (bA.det vA) = bK.det vK := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
    simpa [hentry]
  have hbasisK : LinearIndependent k vK ∧ Submodule.span k (Set.range vK) = ⊤ := by
    have hli : LinearIndependent k vK := by
      simpa [vK] using
        (linearIndependent_brauer_value E (fun i ↦ hE_complete.isSimple i) hE_pairwise)
    have hspan : Submodule.span k (Set.range vK) = ⊤ := by
      simpa [vK] using
        (span_brauer_value_eq_top E hE_pairwise hE_complete)
    exact ⟨hli, hspan⟩
  have hunitK : IsUnit (bK.det vK) :=
    (Module.Basis.is_basis_iff_det bK).mp hbasisK
  have hunitA : IsUnit (bA.det vA) := by
    refine (IsLocalRing.residue_ne_zero_iff_isUnit (bA.det vA)).mp ?_
    rw [hdet_map]
    exact IsUnit.ne_zero hunitK
  have hbasisA : LinearIndependent A vA ∧ Submodule.span A (Set.range vA) = ⊤ :=
    (Module.Basis.is_basis_iff_det bA).mpr hunitA
  refine ⟨Module.Basis.mk hbasisA.1 hbasisA.2.ge, ?_⟩
  intro i
  simp [vA]

/-- Helper for Exercise 18-18.3-2: local export of the Exercise `18-18.2-9`
coefficient-ring Brauer basis API in Serre's complete DVR coefficient setting. -/
def exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
    (lift : PrimeToPRoot p k → A)
    (hlift : Function.Injective lift)
    (hred : ∀ ζ : PrimeToPRoot p k, IsLocalRing.residue A (lift ζ) = (ζ : k))
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Module.Basis ι A (PRegularConjClass G p → A) :=
  Classical.choose
    (exists_exercise_18_18_2_9_irreducible_modular_characters_basis
      (p := p) (A := A) (G := G)
      lift hlift hred E hE_pairwise hE_complete)

/-- Helper for Exercise 18-18.3-2: evaluation rule for the local Exercise `18-18.2-9` Brauer
basis owner. -/
@[simp] theorem exercise_18_18_2_9_irreducible_modular_characters_basis_apply_dvr
    (lift : PrimeToPRoot p k → A)
    (hlift : Function.Injective lift)
    (hred : ∀ ζ : PrimeToPRoot p k, IsLocalRing.residue A (lift ζ) = (ζ : k))
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (i : ι) :
    exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
        (p := p) (A := A) lift hlift hred E hE_pairwise hE_complete i =
      FDRep.modularCharacterOnPRegularConjClass (p := p) (E i) lift := by
  exact
    (Classical.choose_spec
      (exists_exercise_18_18_2_9_irreducible_modular_characters_basis
        (p := p) (A := A) (G := G)
        lift hlift hred E hE_pairwise hE_complete)) i

/-- Helper for Exercise 18-18.3-2: the basis coordinates of the `i`-th Brauer character in the
local Exercise `18-18.2-9` basis are the standard basis vector at `i`. -/
@[simp] theorem exercise_18_18_2_9_irreducible_modular_characters_basis_repr_modularCharacter_dvr
    (lift : PrimeToPRoot p k → A)
    (hlift : Function.Injective lift)
    (hred : ∀ ζ : PrimeToPRoot p k, IsLocalRing.residue A (lift ζ) = (ζ : k))
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (i : ι) :
    (exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
        (p := p) (A := A) lift hlift hred E hE_pairwise hE_complete).repr
      (FDRep.modularCharacterOnPRegularConjClass (p := p) (E i) lift) =
        Finsupp.single i 1 := by
  -- Rewrite the `i`-th Brauer character as the `i`-th basis vector, then apply `repr_self`.
  rw [← exercise_18_18_2_9_irreducible_modular_characters_basis_apply_dvr
    (p := p) (A := A) (lift := lift) (hlift := hlift) (hred := hred) (E := E)
    (hE_pairwise := hE_pairwise) (hE_complete := hE_complete) (i := i)]
  exact
    (exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
      (p := p) (A := A) lift hlift hred E hE_pairwise hE_complete).repr_self i

end LocalExercise1829Fallback

section LocalExercise1829FieldAPI

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p] [Fact p.Prime]
variable {K : Type u} [Field K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

/-- Helper for Exercise 18-18.3-2: field-valued Exercise `18.4` basis, routed through the
proved field owner from Theorem `18-18.2-1` instead of the local integral source input. -/
def exercise_18_18_2_9_field_irreducible_modular_characters_basis
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Module.Basis ι K (PRegularConjClass G p → K) :=
  irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
    (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete

/-- Helper for Exercise 18-18.3-2: evaluation rule for the field-valued Exercise `18.4` basis. -/
@[simp] theorem exercise_18_18_2_9_field_irreducible_modular_characters_basis_apply
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (i : ι) :
    exercise_18_18_2_9_field_irreducible_modular_characters_basis
        (p := p) lift hlift E hE_pairwise hE_complete i =
      FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
        (PrimeToPRoot.toFieldLift lift) := by
  -- Use the already-proved field-valued Exercise `18.4` basis computation.
  exact
    irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_apply
      (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete i

/-- Helper for Exercise 18-18.3-2: the field-valued Exercise `18.4` basis coordinates of the
`i`-th Brauer character are the standard basis vector at `i`. -/
@[simp] theorem exercise_18_18_2_9_field_irreducible_modular_characters_basis_repr_modularCharacter
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (i : ι) :
    (exercise_18_18_2_9_field_irreducible_modular_characters_basis
        (p := p) lift hlift E hE_pairwise hE_complete).repr
      (FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
        (PrimeToPRoot.toFieldLift lift)) =
        Finsupp.single i 1 := by
  -- Rewrite the Brauer character as the field-valued basis vector, then apply `repr_self`.
  rw [← exercise_18_18_2_9_field_irreducible_modular_characters_basis_apply
    (p := p) (lift := lift) (hlift := hlift) (E := E)
    (hE_pairwise := hE_pairwise) (hE_complete := hE_complete) (i := i)]
  exact
    (exercise_18_18_2_9_field_irreducible_modular_characters_basis
      (p := p) lift hlift E hE_pairwise hE_complete).repr_self i

end LocalExercise1829FieldAPI

end Representation
