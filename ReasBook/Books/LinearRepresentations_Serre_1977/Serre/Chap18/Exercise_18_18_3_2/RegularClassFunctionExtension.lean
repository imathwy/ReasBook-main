import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveEnvelopeHom
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PrimeToPRootLift
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_4_1

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section RegularClassFunctionExtension

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [NumberField K] [IsCyclotomicExtension {Monoid.exponent G} ℚ K]

local notation "k" => IsLocalRing.ResidueField A

local instance regularClassFunctionExtensionFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance regularClassFunctionExtensionDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

private noncomputable def canonicalFieldLift :
    PrimeToPRoot p k →* Kˣ :=
  (Units.map (algebraMap A K).toMonoidHom).comp
    (primeToPRoot_unitsLift (p := p) (A := A))

private theorem canonicalFieldLift_injective :
    Function.Injective (canonicalFieldLift (p := p) (A := A) (K := K)) := by
  intro ζ ξ hζξ
  apply primeToPRoot_unitsLift_injective (p := p) (A := A)
  apply IsFractionRing.injective A K
  exact congrArg (fun z : Kˣ => (z : K)) hζξ

private theorem canonicalFieldLift_residue_witness :
    ∀ ζ : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a =
          ((canonicalFieldLift (p := p) (A := A) (K := K) ζ : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((ζ : kˣ) : k) := by
  intro ζ
  refine ⟨primeToPRoot_canonicalLift (p := p) (A := A) ζ, ?_, ?_⟩
  · simp [canonicalFieldLift, primeToPRoot_canonicalLift]
  · exact residue_primeToPRoot_canonicalLift (p := p) (A := A) ζ

include A in
private theorem regular_root_exists
    (s : G) (hs : IsPRegular p s) :
    ∃ ω : K, IsPrimitiveRoot ω (orderOf s) :=
  exists_fractionField_primitiveRoot_of_isPRegular
    (p := p) (A := A) (K := K) (G := G) s hs

private abbrev finiteRepGrothendieckCharacterScalarExtension
    (y : R₀[K](G)) : A ⊗R[K](G) :=
  ⟨finiteRepGrothendieckCharacter K G y,
    mem_characterRingOverFieldAlgebraScalarExtension_of_mem_characterRingOverField
      (finiteRepGrothendieckCharacter K G y).property⟩

private theorem regularRestriction_finiteRepGrothendieckCharacterScalarExtension_eq_virtual
    (y : R₀[K](G)) :
    regularRestriction (p := p) (A := A) (K := K) (G := G)
        (finiteRepGrothendieckCharacterScalarExtension (A := A) (K := K) (G := G) y) =
      virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (canonicalFieldLift (p := p) (A := A) (K := K)))
        ((decompositionHom A K G) y) := by
  ext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
  rw [← hs, virtualModularCharacterOnPRegularConjClass_ofSubtype]
  exact
    regularRestriction_finiteRepGrothendieckCharacter_eq_virtualModularCharacterOnPRegular
      (p := p) (A := A) (K := K) (G := G)
      (canonicalFieldLift (p := p) (A := A) (K := K))
      (canonicalFieldLift_residue_witness (p := p) (A := A) (K := K))
      (regular_root_exists (p := p) (A := A) (K := K) (G := G)) y s

private noncomputable def canonicalDVRBrauerBasisLocal
    {ι : Type x}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Module.Basis ι A (PRegularConjClass G p → A) :=
  exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
    (p := p) (A := A) (G := G)
    (primeToPRoot_canonicalLift (p := p) (A := A))
    (primeToPRoot_unitsLift_injective (p := p) (A := A))
    (residue_primeToPRoot_canonicalLift (p := p) (A := A))
    π hπ_pairwise hπ_complete

private theorem canonicalDVRBrauerBasisLocal_algebraMap_apply_eq_virtualModularCharacter
    {ι : Type x}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (i : ι) :
    (fun c : PRegularConjClass G p =>
        algebraMap A K
          (canonicalDVRBrauerBasisLocal
            (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete i c)) =
      virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (canonicalFieldLift (p := p) (A := A) (K := K)))
        ([π i]₀ : R₀[k](G)) := by
  classical
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  let bA :=
    canonicalDVRBrauerBasisLocal
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  funext c
  have hbA :
      bA i c =
        FDRep.modularCharacterOnPRegularConjClass (p := p) (π i) liftA c := by
    exact congrFun
      (exercise_18_18_2_9_irreducible_modular_characters_basis_apply_dvr
        (p := p) (A := A) (G := G)
        liftA
        (primeToPRoot_unitsLift_injective (p := p) (A := A))
        (residue_primeToPRoot_canonicalLift (p := p) (A := A))
        π hπ_pairwise hπ_complete i) c
  calc
    algebraMap A K (bA i c)
        =
          FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := K) (π i)
            (PrimeToPRoot.toFieldLift
              (canonicalFieldLift (p := p) (A := A) (K := K))) c := by
          rw [hbA]
          simpa [liftA, canonicalFieldLift, primeToPRoot_canonicalLift] using
            congrFun
              (modularCharacterOnPRegularConjClass_comp_lift_local
                (p := p) (G := G)
                (σ := (algebraMap A K))
                (lift := (Units.coeHom A).comp
                  (primeToPRoot_unitsLift (p := p) (A := A)))
                (E := π i)) c
    _ =
        virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (canonicalFieldLift (p := p) (A := A) (K := K)))
          ([π i]₀ : R₀[k](G)) c := by
          symm
          exact congrFun
            (virtualModularCharacterOnPRegularConjClass_class
              (p := p)
              (lift := PrimeToPRoot.toFieldLift
                (canonicalFieldLift (p := p) (A := A) (K := K)))
              (E := π i)) c

private theorem exists_regularRestriction_eq_canonicalDVRBrauerBasisLocal_row_algebraMap
    {ι : Type x}
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (i : ι) :
    ∃ Φ : A ⊗R[K](G),
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
        fun c : PRegularConjClass G p =>
          algebraMap A K
            (canonicalDVRBrauerBasisLocal
              (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete i c) := by
  let lift := canonicalFieldLift (p := p) (A := A) (K := K)
  rcases exists_decompositionHom_section_of_pRegularComponent_virtualModularCharacter
      (p := p) (O := A) (K := K) (G := G) lift
      (canonicalFieldLift_residue_witness (p := p) (A := A) (K := K))
      (regular_root_exists (p := p) (A := A) (K := K) (G := G))
      (canonicalFieldLift_injective (p := p) (A := A) (K := K)) with
    ⟨sec, hleft, _hchar⟩
  refine ⟨finiteRepGrothendieckCharacterScalarExtension (A := A) (K := K) (G := G)
      (sec ([π i]₀ : R₀[k](G))), ?_⟩
  calc
    regularRestriction (p := p) (A := A) (K := K) (G := G)
        (finiteRepGrothendieckCharacterScalarExtension (A := A) (K := K) (G := G)
          (sec ([π i]₀ : R₀[k](G))))
        =
      virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift lift)
        ((decompositionHom A K G) (sec ([π i]₀ : R₀[k](G)))) := by
        simpa [lift] using
          regularRestriction_finiteRepGrothendieckCharacterScalarExtension_eq_virtual
            (p := p) (A := A) (K := K) (G := G)
            (sec ([π i]₀ : R₀[k](G)))
    _ =
      virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift lift)
        ([π i]₀ : R₀[k](G)) := by
        rw [hleft ([π i]₀ : R₀[k](G))]
    _ =
        fun c : PRegularConjClass G p =>
          algebraMap A K
            (canonicalDVRBrauerBasisLocal
              (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete i c) := by
        simpa [lift] using
          (canonicalDVRBrauerBasisLocal_algebraMap_apply_eq_virtualModularCharacter
            (p := p) (A := A) (K := K) (G := G)
            π hπ_pairwise hπ_complete i).symm

/-- Every `A`-valued function on the `p`-regular conjugacy classes is the regular restriction of
a full class-function representative in `A ⊗R[K](G)`, after applying `algebraMap A K` to its
values. -/
theorem exists_regularRestriction_eq_algebraMap
    (f : PRegularConjClass G p → A) :
    ∃ Φ : A ⊗R[K](G),
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
        fun c : PRegularConjClass G p => algebraMap A K (f c) := by
  classical
  rcases exists_complete_simple_family_with_projective_envelopes
      (p := p) (A := A) (G := G) with
    ⟨ι, hι, π, hπ_pairwise, hπ_complete, _P, _hP⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := Classical.decEq ι
  let bA :=
    canonicalDVRBrauerBasisLocal
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  have hrow :
      ∀ i : ι, ∃ Φ : A ⊗R[K](G),
        regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
          fun c : PRegularConjClass G p => algebraMap A K (bA i c) := by
    intro i
    simpa [bA] using
      exists_regularRestriction_eq_canonicalDVRBrauerBasisLocal_row_algebraMap
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete i
  choose Φ hΦ using hrow
  refine ⟨∑ i : ι, (bA.repr f i) • Φ i, ?_⟩
  ext c
  calc
    regularRestriction (p := p) (A := A) (K := K) (G := G)
        (∑ i : ι, (bA.repr f i) • Φ i) c
        =
      (∑ i : ι, (bA.repr f i) •
        regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G) (Φ i)) c := by
        change
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G)
            (∑ i : ι, (bA.repr f i) • Φ i)) c =
          (∑ i : ι, (bA.repr f i) •
            regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G) (Φ i)) c
        exact congrFun (by simp) c
    _ =
      (∑ i : ι, (bA.repr f i) •
        (fun c : PRegularConjClass G p => algebraMap A K (bA i c))) c := by
        refine congrArg (fun g : PRegularConjClass G p → K => g c) ?_
        refine Finset.sum_congr rfl ?_
        intro i _hi
        exact congrArg ((bA.repr f i) • ·) (hΦ i)
    _ =
      algebraMap A K (∑ i : ι, (bA.repr f i) • bA i c) := by
        simp [Algebra.smul_def, map_sum]
    _ = algebraMap A K (f c) := by
        have hsum := congrFun (bA.sum_repr f) c
        simpa [Pi.smul_apply] using congrArg (algebraMap A K) hsum

end RegularClassFunctionExtension

end Representation
