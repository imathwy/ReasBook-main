import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisPairingResidualSourceWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerExercise18_4OrthogonalityAPI
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerOrthogonalityCongruenceWorker

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation ZeroObject

universe u

namespace Representation

section LocalBrauerOrthogonalitySourceGap

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

local instance brauerOrthogonalitySourceGapFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerOrthogonalitySourceGapDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Serre `18.5(a)` in lattice form supplies the explicit pairing-sum congruence.

The proof uses the direct row-divisibility bridge and then converts the resulting `A`-side
pairing residual back into the concrete orthogonality sums. -/
theorem orthogonalityPairingSumResidualCongruence_of_projectiveCharacter_lattice
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[kA[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumResidualCongruence
      (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P := by
  classical
  have hresidual :=
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_projectiveCharacter_lattice_rows
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord hlattice
  exact
    orthogonalityPairingSumResidualCongruence_of_coordinateNormalizedPairingResidual
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hresidual

/-- Existential source-side orthogonality input obtained from the `18.5(a)` lattice
congruence. -/
theorem regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_of_projectiveCharacter_lattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput
      (p := p) (A := A) (K := K) (G := G) := by
  classical
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, P, hP_envelope⟩
  refine ⟨π, hπ_simple, hπ_coord, P, hP_envelope, ?_⟩
  exact
    orthogonalityPairingSumResidualCongruence_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hlattice

end LocalBrauerOrthogonalitySourceGap

section FullMixedBrauerOrthogonalitySourceGap

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerOrthogonalitySourceGapFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerOrthogonalitySourceGapDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic source-gap bridge: the source `18.5(a)` lattice congruence is
sufficient for the explicit orthogonality input used by the existential pairing-residual route. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput_of_projectiveCharacter_lattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPairingResidualOrthogonalityInput_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)

end FullMixedBrauerOrthogonalitySourceGap

end Representation
