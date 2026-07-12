import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerPointMassResidualProducer

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerPointMassBasisResidualProof

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

local instance brauerPointMassBasisResidualProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerPointMassBasisResidualProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- A fixed point-mass coordinate divisibility proof gives the pure `A`-basis residual
congruence.  This is the formal subtraction step: the projective-envelope row already contributes
the explicit centralizer-`p`-part multiple isolated by the Exercise `18.4`/orthogonality
calculation, so subtracting it preserves the same divisibility lattice. -/
theorem brauerPointMassBasisResidualDivisibility_of_coordinateDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G)
            ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hcoord :
      brauerPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    brauerPointMassBasisResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d
  rcases hcoord c d with ⟨a, ha⟩
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
  have hcoordK :
      FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d =
          algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := ha
  calc
    algebraMap A K
        (bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
          (ConjClasses.centralizerPPart p d.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G)
                (inversePRegularConjClass (p := p) d)) c))
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
          rw [hcoordK]
          rw [← map_sub, mul_sub]

omit [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Existential version of
`brauerPointMassBasisResidualDivisibility_of_coordinateDivisibility`. -/
theorem existsPointMassBasisResidualDivisibility_of_coordinateDivisibility
    (hcoord :
      regularValueCongruenceSourceFaithfulExistsPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
      (p := p) (A := A) (G := G) := by
  rcases hcoord with ⟨π, hπ_simple, hπ_coord, hcoord⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerPointMassBasisResidualDivisibility_of_coordinateDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord hcoord

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Conversely, the pure `A`-basis residual congruence gives the original point-mass coordinate
divisibility by adding back the projective-envelope row coefficient isolated by Exercise `18.4`
and orthogonality. -/
theorem brauerPointMassCoordinateDivisibility_of_basisResidualDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G)
            ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hbasis :
      brauerPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    brauerPointMassCoordinateDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  intro c d
  rcases hbasis c d with ⟨a, ha⟩
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
  let z : A := (ConjClasses.centralizerPPart p d.1 : A)
  refine ⟨a + coeff, ?_⟩
  have hbasisK :=
    congrFun
      (canonicalDVRBrauerBasis_algebraMap_apply_eq_virtualModularCharacter
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete c) d
  have ha_add : bA c d -
        ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
      z * (a + coeff) := by
    calc
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
        =
          (bA c d -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
            z * coeff) +
            z * coeff := by
              ring
      _ = z * a + z * coeff := by
            rw [ha]
      _ = z * (a + coeff) := by
            rw [mul_add]
  calc
    FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d
        =
          algebraMap A K
            (bA c d -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) := by
            simp [bA, regularIntegerFunctionCast, hbasisK, map_sub]
    _ =
        algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * (a + coeff)) := by
          simpa [z] using congrArg (fun x : A => algebraMap A K x) ha_add

omit [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Local equivalence between the pure basis-residual congruence and the established
coordinatewise point-mass divisibility statement. -/
theorem brauerPointMassBasisResidualDivisibility_iff_coordinateDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G)
            ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    brauerPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      brauerPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  constructor
  · exact
      brauerPointMassCoordinateDivisibility_of_basisResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord
  · exact
      brauerPointMassBasisResidualDivisibility_of_coordinateDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Existential version of
`brauerPointMassCoordinateDivisibility_of_basisResidualDivisibility`. -/
theorem existsPointMassCoordinateDivisibility_of_basisResidualDivisibility
    (hbasis :
      regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassCoordinateDivisibility
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hbasis with ⟨π, hπ_simple, hπ_coord, hbasis⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerPointMassCoordinateDivisibility_of_basisResidualDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord hbasis

omit [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Existential equivalence between the basis residual and coordinate divisibility forms. -/
theorem existsPointMassBasisResidualDivisibility_iff_coordinateDivisibility :
    regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · exact
      existsPointMassCoordinateDivisibility_of_basisResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)
  · exact
      existsPointMassBasisResidualDivisibility_of_coordinateDivisibility
        (p := p) (A := A) (K := K) (G := G)

end BrauerPointMassBasisResidualProof

section FullMixedModelBrauerPointMassBasisResidualProof

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelBrauerPointMassBasisResidualProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelBrauerPointMassBasisResidualProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model adapter from the point-mass coordinate blocker to the pure basis-residual
blocker. -/
theorem fullMixedModelPointMassBasisResidualDivisibilityBlocker_of_coordinateDivisibilityBlocker
    (hcoord :
      fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassBasisResidualDivisibilityBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    existsPointMassBasisResidualDivisibility_of_coordinateDivisibility
      (p := p) (A := A) (K := K) (G := G)
      (hcoord (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/- Full mixed-model adapter from the pure basis-residual blocker back to the point-mass
coordinate blocker. -/
theorem fullMixedModelPointMassCoordinateBlocker_of_basisResidualBlocker
    (hbasis :
      fullMixedModelPointMassBasisResidualDivisibilityBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassCoordinateDivisibilityBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    existsPointMassCoordinateDivisibility_of_basisResidualDivisibility
      (p := p) (A := A) (K := K) (G := G)
      (hbasis (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The pure basis-residual blocker is equivalent to the established point-mass coordinate
blocker formulation. -/
theorem fullMixedModelPointMassBasisResidualDivisibilityBlocker_iff_coordinateDivisibilityBlocker :
    fullMixedModelPointMassBasisResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelPointMassCoordinateBlocker_of_basisResidualBlocker
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelPointMassBasisResidualDivisibilityBlocker_of_coordinateDivisibilityBlocker
        (p := p) (k := k) (G := G)

end FullMixedModelBrauerPointMassBasisResidualProof

end Representation
