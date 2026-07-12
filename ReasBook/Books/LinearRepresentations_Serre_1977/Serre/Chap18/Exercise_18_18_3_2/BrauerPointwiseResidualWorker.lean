import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerReadbackFinalIntegration
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerPointMassBasisResidualProof
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueCongruenceProjectiveCharacter

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerPointwiseResidualWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerPointwiseResidualWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerPointwiseResidualWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Pointwise source-row divisibility for the coordinate-normalized simple rows.

This is the Serre `18.5(a)` divisibility statement specialized to one normalized Brauer row and
then restricted to the nontrivial centralizer-`p`-part columns requested by the residual API. -/
def regularValueCongruenceSourceFaithfulPointwiseSourceDivisibilityProof : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep k G)
    (_hπ_simple : ∀ c, Simple (π c))
    (_hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p),
    ConjClasses.centralizerPPart p d.1 ≠ 1 →
      ∃ a : A,
        FDRep.modularCharacterOnPRegularConjClass
              (p := p) (G := G) (A := K) (π c)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d =
          algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)

omit [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Pointwise nontrivial-column descent from Serre `18.5(a)` source-row divisibility to the
pure `A`-valued residual used by `regularValueCongruenceSourceFaithfulPointwiseResidualProof`.

The proof only subtracts the projective-envelope row already identified by Exercise `18.4` and
orthogonality, then descends through fraction-field injectivity. -/
theorem coordinateNormalizedBrauerBasis_pointwiseResidual_of_sourceDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p)
    (_hd : ConjClasses.centralizerPPart p d.1 ≠ 1)
    (hsource :
      ∃ a : A,
        FDRep.modularCharacterOnPRegularConjClass
              (p := p) (G := G) (A := K) (π c)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d =
          algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    ∃ a : A,
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        (ConjClasses.centralizerPPart p d.1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d)) c) =
          (ConjClasses.centralizerPPart p d.1 : A) * a := by
  classical
  rcases hsource with ⟨a, ha⟩
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G)
        (inversePRegularConjClass (p := p) d)) c)
  refine ⟨a - coeff, ?_⟩
  apply IsFractionRing.injective A K
  have hbasis :=
    congrFun
      (canonicalDVRBrauerBasis_algebraMap_apply_eq_virtualModularCharacter
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete c) d
  calc
    algebraMap A K
        (bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
          (ConjClasses.centralizerPPart p d.1 : A) * coeff)
        =
      (FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := K) (π c)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
        algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * coeff) := by
          simp [bA, coeff, regularIntegerFunctionCast, hbasis, map_sub, map_mul]
    _ =
        algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * (a - coeff)) := by
          rw [ha]
          rw [← map_sub, mul_sub]

omit [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The pointwise source-row divisibility input closes the exact nontrivial-column residual
proof expected by `BrauerReadbackFinalIntegration`. -/
theorem regularValueCongruenceSourceFaithfulPointwiseResidualProof_of_pointwiseSourceDivisibility
    (hsource :
      regularValueCongruenceSourceFaithfulPointwiseSourceDivisibilityProof
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulPointwiseResidualProof
      (p := p) (A := A) (G := G) := by
  intro π hπ_simple hπ_coord c d hd
  exact
    coordinateNormalizedBrauerBasis_pointwiseResidual_of_sourceDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord c d hd
      (hsource π hπ_simple hπ_coord c d hd)

/-- Projective-character lattice congruence supplies the pointwise source-row divisibility by
Serre `18.5(a)`, without using Cartan range/cokernel/product endpoints. -/
theorem pointwiseSourceDivisibility_of_projectiveCharacter_lattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulPointwiseSourceDivisibilityProof
      (p := p) (A := A) (K := K) (G := G) := by
  intro π _hπ_simple hπ_coord c d _hd
  let row : PRegularConjClass G p → K :=
    virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        ([π c]₀ : R₀[k](G)) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (regularClassCoordinateAddEquiv
          (p := p) (G := G) ([π c]₀ : R₀[k](G)))
  have hrowD : row ∈ regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G) := by
    have hrowMap := hlattice ([π c]₀ : R₀[k](G))
    simpa [row, projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hrowMap
  rcases (mem_regularValueDivisibilitySubmodule_iff
      (p := p) (A := A) (K := K) (G := G) row).1 hrowD d with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa [row, hπ_coord c, regularIntegerFunctionCast,
    virtualModularCharacterOnPRegularConjClass_class] using ha

/-- Direct pointwise residual closure from the source-side projective-character lattice
congruence.  This is the non-valuation route: projective-character divisibility gives the
source row, and Exercise `18.4`/orthogonality subtracts the visible projective-envelope row. -/
theorem pointwiseResidualProof_of_projectiveCharacter_lattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulPointwiseResidualProof
      (p := p) (A := A) (G := G) :=
  regularValueCongruenceSourceFaithfulPointwiseResidualProof_of_pointwiseSourceDivisibility
    (p := p) (A := A) (K := K) (G := G)
    (pointwiseSourceDivisibility_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G) hlattice)

end BrauerPointwiseResidualWorker

section FullMixedBrauerPointwiseResidualWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerPointwiseResidualWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerPointwiseResidualWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed wrapper for the pointwise projective-character lattice route. -/
theorem fullMixedModelBrauerBasisPointwiseResidualBlocker_of_projectiveCharacter_lattice_pointwise
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisPointwiseResidualBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    pointwiseResidualProof_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)

end FullMixedBrauerPointwiseResidualWorker

end Representation
