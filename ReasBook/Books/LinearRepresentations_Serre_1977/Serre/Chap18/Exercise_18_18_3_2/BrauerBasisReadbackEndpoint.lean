import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackProducer
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassCoordinateProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassBasisResidualEndpoint

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerBasisReadbackEndpoint

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance brauerBasisReadbackEndpointFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisReadbackEndpointDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- A single coordinate-normalized family satisfying the canonical DVR Brauer-basis readback
divisibility is exactly enough to close the local readback endpoint. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_fixedFamilyReadback
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hread :
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G)
        π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) π hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) π hπ_simple hπ_coord)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  exact ⟨π, hπ_simple, hπ_coord, hread⟩

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The basis-residual endpoint is equivalent to the requested Brauer-basis readback input.
This records the pure `A`-valued subtraction step without using any Cartan product endpoint. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_basisResidual :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G) := by
  exact
    (existsPointMassBasisResidualDivisibility_iff_brauerBasisReadbackInput
      (p := p) (A := A) (G := G)).symm

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Any proof of the pure basis-residual form immediately closes the requested readback input. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_basisResidual
    (hbasis :
      regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) :=
  (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_basisResidual
    (p := p) (A := A) (G := G)).2 hbasis

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- A field-valued point-mass regular-value witness gives the requested integral Brauer-basis
readback input via Serre `18.5(a)` and the existing fixed-coordinate readback equivalence. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_regularValueWitness
    (hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  exact
    (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_existsPointMassCoordinateDivisibility
      (p := p) (A := A) (K := K) (G := G)).2
      (existsPointMassCoordinateDivisibility_of_regularValueWitness
        (p := p) (A := A) (K := K) (G := G) hwitness)

/-- A projective-restriction witness for the point-mass row differences closes the requested
Brauer-basis readback input.  This is the endpoint-facing form of the Serre `18.5(a)` route:
construct projective characters for the row differences, then read back the canonical DVR Brauer
basis coordinates. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_projectiveRestrictionWitness
    (hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_regularValueWitness
      (p := p) (A := A) (K := K) (G := G)
      (existsPointMassRegularValueWitness_of_projectiveRestrictionWitness
        (p := p) (A := A) (K := K) (G := G) hwitness)

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- A universal coordinate-normalized Exercise `18.4` readback lemma would close the requested
local endpoint after choosing the standard coordinate-normalized family.  This theorem isolates
the exact non-Cartan input still missing from the current API. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_universalReadback
    (hread :
      ∀ (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
        (hπ_simple : ∀ c, Simple (π c))
        (hπ_coord :
          ∀ c,
            regularClassCoordinateAddEquiv
                (p := p) (G := G)
                ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
        brauerBasisFixedCoordinateReadbackDivisibility
          (p := p) (A := A) (G := G)
          π
          (pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) π hπ_coord)
          (complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) π hπ_simple hπ_coord)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  rcases exists_coordinate_normalized_complete_family_with_projective_envelopes
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_fixedFamilyReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
      (hread π hπ_simple hπ_coord)

/-!
The unproved local endpoint requested in this file is still the non-circular Exercise `18.4`
readback congruence for one coordinate-normalized family:

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

The lemmas above show that it would be enough to supply either the fixed-family readback
divisibility directly, or a projective-restriction witness for the point-mass row differences.
No final Cartan range/product endpoint is used here.
-/

end BrauerBasisReadbackEndpoint

end Representation
