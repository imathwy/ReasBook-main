import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeSourceFaithful

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section BrauerBasisReadbackSourceFaithful

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerBasisReadbackSourceFaithfulFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisReadbackSourceFaithfulDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The canonical `A`-valued Exercise `18.4` Brauer basis attached to a complete simple family,
using the source-faithful Hensel lift of prime-to-`p` roots. -/
noncomputable def canonicalDVRBrauerBasis
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Module.Basis ι A (PRegularConjClass G p → A) :=
  exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
    (p := p) (A := A)
    (primeToPRoot_canonicalLift (p := p) (A := A))
    (primeToPRoot_unitsLift_injective (p := p) (A := A))
    (residue_primeToPRoot_canonicalLift (p := p) (A := A))
    π hπ_pairwise hπ_complete

omit [IsFractionRing A K] [Fintype ι] [DecidableEq ι] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Transporting a canonical `A`-valued Brauer-basis row to the fraction field gives exactly the
canonical virtual modular character row. -/
theorem canonicalDVRBrauerBasis_algebraMap_apply_eq_virtualModularCharacter
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (i : ι) :
    (fun c : PRegularConjClass G p =>
        algebraMap A K
          (canonicalDVRBrauerBasis
            (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete i c)) =
      virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        ([π i]₀ : R₀[k](G)) := by
  classical
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  funext c
  have hbA :
      bA i c =
        FDRep.modularCharacterOnPRegularConjClass (p := p) (π i) liftA c := by
    exact congrFun
      (exercise_18_18_2_9_irreducible_modular_characters_basis_apply_dvr
        (p := p) (A := A)
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
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) c := by
          rw [hbA]
          simpa [liftA, projectiveCartanASpanFieldLift, primeToPRoot_canonicalLift] using
            congrFun
              (modularCharacterOnPRegularConjClass_comp_lift_local
                (σ := (algebraMap A K))
                (lift := (Units.coeHom A).comp
                  (primeToPRoot_unitsLift (p := p) (A := A)))
                (E := π i)) c
    _ =
        virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          ([π i]₀ : R₀[k](G)) c := by
          symm
          exact congrFun
            (virtualModularCharacterOnPRegularConjClass_class
              (p := p)
              (lift := PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
              (E := π i)) c

/-- The smaller `A`-basis readback input equivalent to the fixed-coordinate regular-value row
congruence: each canonical `A`-valued Brauer row agrees with its fixed integer coordinate row
modulo the centralizer `p`-part at every regular class. -/
def brauerBasisFixedCoordinateReadbackDivisibility
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) : Prop :=
  ∀ i : ι, ∀ c : PRegularConjClass G p,
    ∃ a : A,
      canonicalDVRBrauerBasis
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete i c -
        ((regularClassCoordinateAddEquiv
          (p := p) (G := G) ([π i]₀ : R₀[k](G))) c : A) =
          (ConjClasses.centralizerPPart p c.1 : A) * a

omit [IsFractionRing A K] [Fintype ι] [DecidableEq ι] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- If the centralizer `p`-part at one regular class is trivial, the fixed-coordinate
Brauer-basis readback congruence at that class is automatic.  This isolates the nontrivial
readback work to coordinates with positive `p`-part. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_pointwise_of_centralizerPPart_eq_one
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (i : ι)
    (c : PRegularConjClass G p)
    (hc : ConjClasses.centralizerPPart p c.1 = 1) :
    ∃ a : A,
      canonicalDVRBrauerBasis
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete i c -
        ((regularClassCoordinateAddEquiv
          (p := p) (G := G) ([π i]₀ : R₀[k](G))) c : A) =
          (ConjClasses.centralizerPPart p c.1 : A) * a := by
  let a : A :=
    canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete i c -
      ((regularClassCoordinateAddEquiv
        (p := p) (G := G) ([π i]₀ : R₀[k](G))) c : A)
  refine ⟨a, ?_⟩
  have hz : (ConjClasses.centralizerPPart p c.1 : A) = 1 := by
    simp [hc]
  simp [a, hz]

omit [IsFractionRing A K] [Fintype ι] [DecidableEq ι] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Degenerate A-side readback case: if every regular centralizer has trivial `p`-part, then the
fixed-coordinate Brauer-basis readback divisibility follows directly, without using any readback
equivalence theorem. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_of_forall_centralizerPPart_eq_one
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hcentral :
      ∀ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 = 1) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  intro i c
  exact
    brauerBasisFixedCoordinateReadbackDivisibility_pointwise_of_centralizerPPart_eq_one
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete i c (hcentral c)

omit [IsFractionRing A K] [Fintype ι] [DecidableEq ι] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The fixed-coordinate readback congruence is reduced to the regular classes whose
centralizer `p`-part is nontrivial.  The `centralizerPPart = 1` coordinates are supplied by
`brauerBasisFixedCoordinateReadbackDivisibility_pointwise_of_centralizerPPart_eq_one`. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_of_nontrivial_centralizerPPart
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hread :
      ∀ i : ι, ∀ c : PRegularConjClass G p,
        ConjClasses.centralizerPPart p c.1 ≠ 1 →
          ∃ a : A,
            canonicalDVRBrauerBasis
                (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete i c -
              ((regularClassCoordinateAddEquiv
                (p := p) (G := G) ([π i]₀ : R₀[k](G))) c : A) =
                (ConjClasses.centralizerPPart p c.1 : A) * a) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  intro i c
  by_cases hc : ConjClasses.centralizerPPart p c.1 = 1
  · exact
      brauerBasisFixedCoordinateReadbackDivisibility_pointwise_of_centralizerPPart_eq_one
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete i c hc
  · exact hread i c hc

omit [IsFractionRing A K] [Fintype ι] [DecidableEq ι] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Equivalent nontrivial-coordinate form of the fixed-coordinate readback congruence. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_iff_nontrivial_centralizerPPart
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete ↔
      ∀ i : ι, ∀ c : PRegularConjClass G p,
        ConjClasses.centralizerPPart p c.1 ≠ 1 →
          ∃ a : A,
            canonicalDVRBrauerBasis
                (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete i c -
              ((regularClassCoordinateAddEquiv
                (p := p) (G := G) ([π i]₀ : R₀[k](G))) c : A) =
                (ConjClasses.centralizerPPart p c.1 : A) * a := by
  constructor
  · intro hread i c _hc
    exact hread i c
  · exact
      brauerBasisFixedCoordinateReadbackDivisibility_of_nontrivial_centralizerPPart
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete

omit [Fintype ι] [DecidableEq ι] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The fixed-coordinate row congruence needed by the source-faithful lattice endpoint is exactly
the `A`-valued canonical Brauer-basis readback divisibility statement above. -/
theorem fixedCoordinateRowCongruence_iff_brauerBasisFixedCoordinateReadbackDivisibility
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    (∀ i : ι,
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          ([π i]₀ : R₀[k](G)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π i]₀ : R₀[k](G))) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ↔
      brauerBasisFixedCoordinateReadbackDivisibility
        π hπ_pairwise hπ_complete := by
  classical
  constructor
  · intro hrow i c
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    let coord : PRegularConjClass G p → ℤ :=
      regularClassCoordinateAddEquiv
        (p := p) (G := G) ([π i]₀ : R₀[k](G))
    let χ : PRegularConjClass G p → K :=
      virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        ([π i]₀ : R₀[k](G))
    rcases (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G)
        (χ - regularIntegerFunctionCast (p := p) (K := K) (G := G) coord)).1
        (by simpa [χ, coord] using hrow i) c with
      ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply IsFractionRing.injective A K
    have hbasis := congrFun
      (canonicalDVRBrauerBasis_algebraMap_apply_eq_virtualModularCharacter
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete i) c
    calc
      algebraMap A K (bA i c - (coord c : A))
          = (χ - regularIntegerFunctionCast (p := p) (K := K) (G := G) coord) c := by
            simp [bA, χ, coord, regularIntegerFunctionCast, hbasis]
      _ = algebraMap A K ((ConjClasses.centralizerPPart p c.1 : A) * a) := ha
  · intro hread i
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    let coord : PRegularConjClass G p → ℤ :=
      regularClassCoordinateAddEquiv
        (p := p) (G := G) ([π i]₀ : R₀[k](G))
    let χ : PRegularConjClass G p → K :=
      virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        ([π i]₀ : R₀[k](G))
    refine (mem_regularValueDivisibilitySubmodule_iff
      (p := p) (A := A) (K := K) (G := G)
      (χ - regularIntegerFunctionCast (p := p) (K := K) (G := G) coord)).2 ?_
    intro c
    rcases hread i c with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hbasis := congrFun
      (canonicalDVRBrauerBasis_algebraMap_apply_eq_virtualModularCharacter
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete i) c
    calc
      (χ - regularIntegerFunctionCast (p := p) (K := K) (G := G) coord) c
          = algebraMap A K (bA i c - (coord c : A)) := by
            simp [bA, χ, coord, regularIntegerFunctionCast, hbasis]
      _ = algebraMap A K ((ConjClasses.centralizerPPart p c.1 : A) * a) := by
            rw [ha]

set_option linter.style.longLine false in
set_option linter.unusedFintypeInType false in
omit [DecidableEq ι] in
/-- Source-faithful endpoint with the fixed-coordinate row congruence replaced by the smaller
canonical `A`-basis readback divisibility input. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_of_serreBasis_divisibilityRepresentatives_brauerBasisReadback
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (g : ι → PRegularConjClass G p → ℤ)
    (hrow :
      ∀ i : ι,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π i]₀ : R₀[k](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) (g i) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hread :
      brauerBasisFixedCoordinateReadbackDivisibility
        π hπ_pairwise hπ_complete) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (A := A) (K := K) (G := G) :=
  projectiveCharacterLatticeIntegerRepresentativeCongruence_of_serreBasis_divisibilityRepresentatives_coordinateRows
    (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete g hrow
    ((fixedCoordinateRowCongruence_iff_brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete).2 hread)

end BrauerBasisReadbackSourceFaithful

end Representation
