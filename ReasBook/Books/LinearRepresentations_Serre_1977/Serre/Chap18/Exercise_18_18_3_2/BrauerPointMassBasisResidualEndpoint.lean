import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerPointMassResidualProducer
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueCongruenceSourceFaithfulProof

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerPointMassBasisResidualEndpoint

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerPointMassBasisResidualEndpointFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerPointMassBasisResidualEndpointDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The fixed-coordinate Brauer-basis readback congruence gives the basis-residual form by
subtracting the projective-envelope row coefficient isolated by Serre `18.5(a)`. -/
theorem brauerPointMassBasisResidualDivisibility_of_fixedCoordinateReadback
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G)
            ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hread :
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G)
        π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) π hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) π hπ_simple hπ_coord)) :
    brauerPointMassBasisResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) π hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) π hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  let z : A := ConjClasses.centralizerPPart p d.1
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G)
        (inversePRegularConjClass (p := p) d)) c)
  rcases hread c d with ⟨a, ha⟩
  refine ⟨a - coeff, ?_⟩
  have hcoord_d :
      ((regularClassCoordinateAddEquiv
          (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
        ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) := by
    rw [hπ_coord c]
  -- The residual is just the fixed-coordinate readback congruence with one visible
  -- `z`-multiple subtracted.
  calc
    bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        z * coeff =
      bA c d -
          ((regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) -
        z * coeff := by
          rw [hcoord_d]
    _ = z * a - z * coeff := by
          rw [ha]
    _ = z * (a - coeff) := by
          rw [mul_sub]

/-- The basis-residual form is no weaker than the fixed-coordinate Brauer-basis readback
congruence, since the residual only subtracts an explicit centralizer-`p`-part multiple. -/
theorem fixedCoordinateReadback_of_brauerPointMassBasisResidualDivisibility
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
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) π hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) π hπ_simple hπ_coord) := by
  intro c d
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) π hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) π hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  let z : A := ConjClasses.centralizerPPart p d.1
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G)
        (inversePRegularConjClass (p := p) d)) c)
  rcases hbasis c d with ⟨a, ha⟩
  refine ⟨a + coeff, ?_⟩
  have hcoord_d :
      ((regularClassCoordinateAddEquiv
          (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
        ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) := by
    rw [hπ_coord c]
  -- Add back the explicit projective-envelope row multiple; this recovers the fixed-coordinate
  -- readback congruence.
  calc
    bA c d -
        ((regularClassCoordinateAddEquiv
          (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
      (bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        z * coeff) + z * coeff := by
          rw [hcoord_d]
          ring
    _ = z * a + z * coeff := by
          rw [ha]
    _ = z * (a + coeff) := by
          rw [mul_add]

/-- Local equivalence between the basis-residual endpoint and the fixed-coordinate Brauer-basis
readback input. -/
theorem brauerPointMassBasisResidualDivisibility_iff_fixedCoordinateReadback
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
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G)
        π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) π hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) π hπ_simple hπ_coord) := by
  constructor
  · exact
      fixedCoordinateReadback_of_brauerPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord
  · exact
      brauerPointMassBasisResidualDivisibility_of_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- The existing Brauer-basis readback input produces the requested existential basis-residual
endpoint. -/
theorem existsPointMassBasisResidualDivisibility_of_brauerBasisReadbackInput
    (hread :
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
      (p := p) (A := A) (G := G) := by
  rcases hread with ⟨π, hπ_simple, hπ_coord, hread⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerPointMassBasisResidualDivisibility_of_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hread

/-- Conversely, the existential basis-residual endpoint recovers exactly the existing
Brauer-basis readback input. -/
theorem brauerBasisReadbackInput_of_existsPointMassBasisResidualDivisibility
    (hbasis :
      regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  rcases hbasis with ⟨π, hπ_simple, hπ_coord, hbasis⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    fixedCoordinateReadback_of_brauerPointMassBasisResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hbasis

/-- Existential form: the basis-residual endpoint and the fixed-coordinate Brauer-basis
readback input are equivalent. -/
theorem existsPointMassBasisResidualDivisibility_iff_brauerBasisReadbackInput :
    regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G) := by
  constructor
  · exact
      brauerBasisReadbackInput_of_existsPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G)
  · exact
      existsPointMassBasisResidualDivisibility_of_brauerBasisReadbackInput
        (p := p) (A := A) (G := G)

end BrauerPointMassBasisResidualEndpoint

section FullMixedModelBrauerPointMassBasisResidualEndpoint

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelBrauerPointMassBasisResidualEndpointFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelBrauerPointMassBasisResidualEndpointDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model adapter from the Brauer-basis readback input to the basis-residual blocker. -/
theorem fullMixedModelPointMassBasisResidualDivisibilityBlocker_of_brauerBasisReadbackInput
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassBasisResidualDivisibilityBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    existsPointMassBasisResidualDivisibility_of_brauerBasisReadbackInput
      (p := p) (A := A) (G := G)
      (hread (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model adapter from the basis-residual blocker back to the Brauer-basis readback
input. -/
theorem fullMixedModelBrauerBasisReadbackInput_of_basisResidualDivisibilityBlocker
    (hbasis :
      fullMixedModelPointMassBasisResidualDivisibilityBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    brauerBasisReadbackInput_of_existsPointMassBasisResidualDivisibility
      (p := p) (A := A) (G := G)
      (hbasis (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model equivalence between the requested basis-residual blocker and the exact
Brauer-basis readback input. -/
theorem fullMixedModelPointMassBasisResidualBlocker_iff_brauerBasisReadbackInput :
    fullMixedModelPointMassBasisResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelBrauerBasisReadbackInput_of_basisResidualDivisibilityBlocker
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelPointMassBasisResidualDivisibilityBlocker_of_brauerBasisReadbackInput
        (p := p) (k := k) (G := G)

/-!
The remaining non-circular endpoint is exactly:

```
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_proof
    {p : ℕ} {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    {G : Type u} [Group G] [Finite G]
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
    [CharP (IsLocalRing.ResidueField A) p] :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G)
```

By the equivalences above, this is equivalent to the requested
`regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility_proof` and to the
full mixed-model basis-residual blocker.  Proving it is the source-faithful Exercise `18.4`
readback congruence for the coordinate-normalized DVR Brauer basis; it is not supplied by the
formal Cartan range/product endpoints and is not derived here from the coordinate blocker.
-/

end FullMixedModelBrauerPointMassBasisResidualEndpoint

end Representation
