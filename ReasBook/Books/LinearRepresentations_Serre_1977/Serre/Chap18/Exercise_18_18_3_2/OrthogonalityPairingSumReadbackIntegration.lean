import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerReadbackFinalIntegration
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.OrthogonalityResidualMicroWorker

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section OrthogonalityPairingSumReadbackIntegrationLocal

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

local instance orthogonalityPairingSumReadbackIntegrationFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance orthogonalityPairingSumReadbackIntegrationDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Local source-side input isolated by the explicit Serre pairing-sum route.

This is the Franklin micro-frontier packaged as a readback-facing assumption: for one
coordinate-normalized complete simple family and its projective envelopes, the concrete
orthogonality pairing sums satisfy the centralizer-`p`-part residual congruence. -/
def regularValueCongruenceSourceFaithfulOrthogonalityPairingSumCongruenceInput : Prop :=
  ∃ π : PRegularConjClass G p → FDRep k G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        ∃ P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G,
          ∃ _hP_envelope :
            ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope,
            let hπ_pairwise :=
              pairwiseNonisomorphic_of_regularClassCoordinate_single
                (p := p) (G := G) (π := π) hπ_coord
            let hπ_complete :=
              complete_irreducible_family_of_regularClassCoordinate_single
                (p := p) (G := G) (π := π) hπ_simple hπ_coord
            orthogonalityPairingSumResidualCongruence
              (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P

/-- The explicit pairing-sum residual congruence closes the local Brauer-basis readback input.

This bridge is only the already-certified micro route:
`orthogonalityPairingSumResidualCongruence` gives the coordinate-normalized pairing residual,
which gives the fixed-coordinate Brauer-basis readback congruence. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_orthogonalityPairingSumCongruence
    (horth :
      regularValueCongruenceSourceFaithfulOrthogonalityPairingSumCongruenceInput
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  classical
  rcases horth with ⟨π, hπ_simple, hπ_coord, P, hP_envelope, hcongr⟩
  have hresidual :
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
    have hpoint :=
      coordinateNormalizedBasisResidualDivisibility_of_orthogonalityPairingSumResidualCongruence
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope hcongr
    simpa [coordinateNormalizedBrauerBasisPairingResidualDivisibility, canonicalDVRBrauerBasis]
      using hpoint
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_fixedFamilyReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
      (brauerBasisFixedCoordinateReadbackDivisibility_of_pairingResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord hresidual)

end OrthogonalityPairingSumReadbackIntegrationLocal

section OrthogonalityPairingSumReadbackIntegrationFullMixed

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedOrthogonalityPairingSumReadbackIntegrationFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedOrthogonalityPairingSumReadbackIntegrationDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-characteristic form of the explicit orthogonality pairing-sum congruence input. -/
def fullMixedModelOrthogonalityPairingSumCongruenceInput : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulOrthogonalityPairingSumCongruenceInput
        (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed pairing-sum congruences close the full mixed Brauer-basis readback input. -/
theorem fullMixedModelBrauerBasisReadbackInput_of_orthogonalityPairingSumCongruence
    (horth :
      fullMixedModelOrthogonalityPairingSumCongruenceInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_orthogonalityPairingSumCongruence
      (p := p) (A := A) (K := K) (G := G)
      (horth (A := A) (K := K) e0)

end OrthogonalityPairingSumReadbackIntegrationFullMixed

end Representation
