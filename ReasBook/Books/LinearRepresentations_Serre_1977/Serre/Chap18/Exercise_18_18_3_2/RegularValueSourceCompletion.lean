import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveEnvelopeResidualCompletion

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalRegularValueSourceCompletion

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "kA" => IsLocalRing.ResidueField A

local instance regularValueSourceCompletionFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance regularValueSourceCompletionDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Minimal source-side row input for the non-circular `18.5(a)` route.

For one coordinate-normalized complete simple family, each fixed point-mass row difference is
already in the projective-character restriction lattice.  This is weaker than the full
`projectiveCharacterLatticeIntegerRepresentativeCongruence`, which asks for the same congruence
for every virtual modular character. -/
def regularValueSourceCompletionPointMassProjectiveRowInput : Prop :=
  ∃ π : PRegularConjClass G p → FDRep kA G,
    ∃ _hπ_simple : ∀ c, Simple (π c),
      ∃ _hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        ∀ c : PRegularConjClass G p,
          virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
              ([π c]₀ : R₀[kA](G)) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
              Submodule.map
                (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
                (projectiveCharacterSubmodule (A := A) (K := K) (G := G))

omit [IsFractionRing A K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The full projective-character representative congruence supplies the smaller point-mass row
input by specializing to a coordinate-normalized complete family. -/
theorem regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveCharacter_lattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (A := A) (K := K) (G := G) := by
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  intro c
  simpa [hπ_coord c] using hlattice ([π c]₀ : R₀[kA](G))

/-- The point-mass projective-row input closes the requested local DVR Brauer-basis readback.

This uses only the source-side `18.5(a)` equality
`projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule` and the existing
fixed-coordinate readback equivalence; it does not use the final Cartan range, cokernel, or
product endpoints. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointMassProjectiveRows
    (hrows :
      regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  rcases hrows with ⟨π, hπ_simple, hπ_coord, hrows⟩
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  refine
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_fixedFamilyReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord ?_
  refine
    (fixedCoordinateRowCongruence_iff_brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete).1 ?_
  intro c
  have hmap := hrows c
  have hdiv :
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          ([π c]₀ : R₀[kA](G)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hmap
  simpa [hπ_coord c] using hdiv

/-- Non-circular local bridge from the full projective-character lattice input to the requested
Brauer-basis readback input, factored through the smaller point-mass row input above. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_projectiveCharacter_lattice_rows
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) :=
  regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointMassProjectiveRows
    (p := p) (A := A) (K := K) (G := G)
    (regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G) hlattice)

/-- The same source row input gives the local regular-value source-faithful congruence through
the readback adapter. -/
theorem regularValueCongruenceSourceFaithfulStatement_of_pointMassProjectiveRows
    (hrows :
      regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G) :=
  regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointMassProjectiveRows
      (p := p) (A := A) (K := K) (G := G) hrows)

end LocalRegularValueSourceCompletion

section FullMixedRegularValueSourceCompletion

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedRegularValueSourceCompletionFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedRegularValueSourceCompletionDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-characteristic version of the point-mass projective-row input. -/
def fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The full projective-character lattice input specializes to the full mixed point-mass row
input. -/
theorem
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveCharacter_lattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueSourceCompletionPointMassProjectiveRowInput_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model readback from the smaller point-mass projective-row input. -/
theorem fullMixedModelBrauerBasisReadbackInput_of_pointMassProjectiveRows
    (hrows :
      fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointMassProjectiveRows
      (p := p) (A := A) (K := K) (G := G)
      (hrows (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model regular-value source-faithful statement from the smaller point-mass
projective-row input. -/
theorem fullMixedModelRegularValueCongruenceSourceFaithfulStatement_of_pointMassProjectiveRows
    (hrows :
      fullMixedModelRegularValueSourceCompletionPointMassProjectiveRowInput
      (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueCongruenceSourceFaithfulStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulStatement_of_pointMassProjectiveRows
      (p := p) (A := A) (K := K) (G := G)
      (hrows (A := A) (K := K) e0)

end FullMixedRegularValueSourceCompletion

end Representation
