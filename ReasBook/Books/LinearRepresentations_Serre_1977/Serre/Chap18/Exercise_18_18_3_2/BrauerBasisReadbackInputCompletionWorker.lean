import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointwiseReadbackDirectProofWorker

/-!
Fixed-coordinate readback input completion worker.

This file keeps the route at the canonical DVR Brauer-basis row level.  It packages the
remaining fixed-coordinate input as the direct Brauer-character congruence on the nontrivial
centralizer-`p`-part columns, then proves that this package is equivalent to the existing local
and full mixed readback inputs.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalBrauerBasisReadbackInputCompletionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerBasisReadbackInputCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisReadbackInputCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Nontrivial-column form of the direct Brauer-character fixed-coordinate row congruence. -/
def fixedCoordinateBrauerCharacterNontrivialReadbackCongruence
    (π : PRegularConjClass G p → FDRep k G) : Prop :=
  ∀ c d : PRegularConjClass G p,
    ConjClasses.centralizerPPart p d.1 ≠ 1 →
      ∃ a : A,
        FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := A) (π c)
            (primeToPRoot_canonicalLift (p := p) (A := A)) d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
            (ConjClasses.centralizerPPart p d.1 : A) * a

/-- The direct Brauer-character row congruence is reduced to the nontrivial centralizer
`p`-part columns. -/
theorem brauerCharacterPointwiseReadbackCongruence_iff_fixedCoordinateNontrivial
    (π : PRegularConjClass G p → FDRep k G) :
    brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π ↔
      fixedCoordinateBrauerCharacterNontrivialReadbackCongruence
        (p := p) (A := A) (G := G) π := by
  constructor
  · intro h c d _hd
    exact h c d
  · intro h c d
    by_cases hd : ConjClasses.centralizerPPart p d.1 = 1
    · let a : A :=
        FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := A) (π c)
            (primeToPRoot_canonicalLift (p := p) (A := A)) d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
      refine ⟨a, ?_⟩
      have hz : (ConjClasses.centralizerPPart p d.1 : A) = 1 := by
        simp [hd]
      simp [a, hz]
    · exact h c d hd

/-- Fixed-family form of the direct nontrivial-column Brauer-character input. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_of_nontrivialBrauerCharacterReadbackCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hchar :
      fixedCoordinateBrauerCharacterNontrivialReadbackCongruence
        (p := p) (A := A) (G := G) π) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord) := by
  have hchar_all :
      brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π :=
    (brauerCharacterPointwiseReadbackCongruence_iff_fixedCoordinateNontrivial
      (p := p) (A := A) (G := G) π).2 hchar
  have hsource :
      coordinateNormalizedBrauerBasisPointwiseReadbackSource
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
    (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hchar_all
  exact
    (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hsource

/-- Fixed-family readback, opened to direct nontrivial Brauer-character rows. -/
theorem nontrivialBrauerCharacterReadbackCongruence_of_brauerBasisFixedCoordinateReadbackDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hread :
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G)
        π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord)) :
    fixedCoordinateBrauerCharacterNontrivialReadbackCongruence
      (p := p) (A := A) (G := G) π := by
  have hsource :
      coordinateNormalizedBrauerBasisPointwiseReadbackSource
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
    (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hread
  have hchar_all :
      brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π :=
    (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hsource
  exact
    (brauerCharacterPointwiseReadbackCongruence_iff_fixedCoordinateNontrivial
      (p := p) (A := A) (G := G) π).1 hchar_all

/-- The fixed-coordinate readback congruence is exactly the nontrivial-column direct
Brauer-character congruence for the same coordinate-normalized family. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_iff_nontrivialBrauerCharacterReadbackCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G)
        π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord) ↔
      fixedCoordinateBrauerCharacterNontrivialReadbackCongruence
        (p := p) (A := A) (G := G) π := by
  constructor
  · exact
      nontrivialBrauerCharacterReadbackCongruence_of_brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord
  · exact
      brauerBasisFixedCoordinateReadbackDivisibility_of_nontrivialBrauerCharacterReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- Local existential package of the remaining direct nontrivial Brauer-character input. -/
def regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput :
    Prop :=
  ∃ π : PRegularConjClass G p → FDRep k G,
    ∃ _hπ_simple : ∀ c, Simple (π c),
      ∃ _hπ_coord :
        (∀ c : PRegularConjClass G p,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
        fixedCoordinateBrauerCharacterNontrivialReadbackCongruence
          (p := p) (A := A) (G := G) π

/-- The direct nontrivial Brauer-character input closes the local fixed-coordinate readback
input. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_brauerCharacterNontrivialReadbackInput
    (hchar :
      regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  rcases hchar with ⟨π, hπ_simple, hπ_coord, hchar⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerBasisFixedCoordinateReadbackDivisibility_of_nontrivialBrauerCharacterReadbackCongruence
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hchar

/-- The local fixed-coordinate readback input is the same existential package, after opening
the canonical DVR Brauer-basis rows. -/
theorem regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_brauerBasisReadbackInput
    (hread :
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput
      (p := p) (A := A) (G := G) := by
  rcases hread with ⟨π, hπ_simple, hπ_coord, hread⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    nontrivialBrauerCharacterReadbackCongruence_of_brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hread

/-- Exact local boundary for the fixed-coordinate route. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_brauerCharacterNontrivialReadbackInput :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput
        (p := p) (A := A) (G := G) := by
  constructor
  · exact
      regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_brauerBasisReadbackInput
        (p := p) (A := A) (G := G)
  · exact
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_brauerCharacterNontrivialReadbackInput
        (p := p) (A := A) (G := G)

end LocalBrauerBasisReadbackInputCompletionWorker

section FullMixedBrauerBasisReadbackInputCompletionWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerBasisReadbackInputCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerBasisReadbackInputCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-characteristic form of the remaining direct nontrivial Brauer-character input. -/
def fullMixedModelBrauerCharacterNontrivialReadbackInput : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput
        (p := p) (A := A) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed direct nontrivial Brauer-character input closes the requested readback input. -/
theorem fullMixedModelBrauerBasisReadbackInput_of_brauerCharacterNontrivialReadbackInput
    (hchar :
      fullMixedModelBrauerCharacterNontrivialReadbackInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_brauerCharacterNontrivialReadbackInput
      (p := p) (A := A) (G := G)
      (hchar (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The requested full mixed readback input gives the same direct nontrivial Brauer-character
package in every mixed model. -/
theorem fullMixedModelBrauerCharacterNontrivialReadbackInput_of_brauerBasisReadbackInput
    (hread :
      fullMixedModelBrauerBasisReadbackInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerCharacterNontrivialReadbackInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulBrauerCharacterNontrivialReadbackInput_of_brauerBasisReadbackInput
      (p := p) (A := A) (G := G)
      (hread (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed boundary: the fixed-coordinate readback input is equivalent to the direct
nontrivial Brauer-character row congruence package. -/
theorem fullMixedModelBrauerBasisReadbackInput_iff_brauerCharacterNontrivialReadbackInput :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerCharacterNontrivialReadbackInput
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelBrauerCharacterNontrivialReadbackInput_of_brauerBasisReadbackInput
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelBrauerBasisReadbackInput_of_brauerCharacterNontrivialReadbackInput
        (p := p) (k := k) (G := G)

end FullMixedBrauerBasisReadbackInputCompletionWorker

end Representation
