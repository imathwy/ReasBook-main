import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackEndpoint

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerPointMassRegularValueSourceProof

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

local instance brauerPointMassRegularValueSourceProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerPointMassRegularValueSourceProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Fixed-coordinate DVR Brauer-basis readback gives the source row-divisibility witness
`χ_c - δ_c ∈ regularValueDivisibilitySubmodule` for each coordinate-normalized simple row.

This is the direct Serre `18.5(a)` value-side form: Exercise `18.4` supplies the canonical
Brauer basis readback, and the fixed-coordinate row congruence equivalence translates it into
the centralizer-`p`-part divisibility lattice. -/
theorem brauerPointMassRegularValueDivisibilityWitness_of_fixedCoordinateReadback
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
    brauerPointMassRegularValueDivisibilityWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  classical
  intro c
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) π hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) π hπ_simple hπ_coord
  have hrows :
      ∀ c : PRegularConjClass G p,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π c]₀ : R₀[k](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[k](G))) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [hπ_pairwise, hπ_complete] using
      ((fixedCoordinateRowCongruence_iff_brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete).2 hread)
  simpa [brauerPointMassRegularValueDivisibilityWitness, hπ_coord c] using hrows c

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Existential readback input produces the point-mass regular-value witness directly, without
passing through the final source congruence endpoint. -/
theorem existsPointMassRegularValueWitness_of_brauerBasisReadbackInput
    (hread :
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hread with ⟨π, hπ_simple, hπ_coord, hread⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerPointMassRegularValueDivisibilityWitness_of_fixedCoordinateReadback
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord hread

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The regular-value point-mass witness and the canonical DVR Brauer-basis readback input are
the same A-side source obligation. -/
theorem existsPointMassRegularValueWitness_iff_brauerBasisReadbackInput :
    regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G) := by
  constructor
  · exact
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_regularValueWitness
        (p := p) (A := A) (K := K) (G := G)
  · exact
      existsPointMassRegularValueWitness_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G)

end BrauerPointMassRegularValueSourceProof

section FullMixedModelBrauerPointMassRegularValueSourceProof

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelBrauerPointMassRegularValueSourceProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelBrauerPointMassRegularValueSourceProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model readback input gives the regular-value point-mass witness blocker by the
direct value-side Serre `18.5(a)` row divisibility route. -/
theorem fullMixedModelPointMassRegularValueWitnessBlocker_of_brauerBasisReadbackInput
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassRegularValueWitnessBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    existsPointMassRegularValueWitness_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G)
      (hread (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model form: the point-mass regular-value witness blocker is equivalent to the
canonical Brauer-basis readback input. -/
theorem fullMixedModelPointMassRegularValueWitnessBlocker_iff_readbackInput :
    fullMixedModelPointMassRegularValueWitnessBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  constructor
  · intro hwitness A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (existsPointMassRegularValueWitness_iff_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G)).1
        (hwitness (A := A) (K := K) e0)
  · exact
      fullMixedModelPointMassRegularValueWitnessBlocker_of_brauerBasisReadbackInput
        (p := p) (k := k) (G := G)

end FullMixedModelBrauerPointMassRegularValueSourceProof

end Representation
