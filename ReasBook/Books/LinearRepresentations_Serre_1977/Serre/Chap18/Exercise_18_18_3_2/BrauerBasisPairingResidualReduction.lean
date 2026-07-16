import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisPointwiseResidualBlocker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisPairingResidualEndpoint

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalBrauerBasisPairingResidualReduction

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerBasisPairingResidualReductionFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisPairingResidualReductionDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Pointwise nontrivial-coordinate residuals are exactly the local proof obligation for
`coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof`; the
`centralizerPPart = 1` columns are supplied by the existing pointwise trivial lemma. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof_of_pointwiseResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hresidual :
      ∀ c d : PRegularConjClass G p,
        ConjClasses.centralizerPPart p d.1 ≠ 1 →
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
                (ConjClasses.centralizerPPart p d.1 : A) * a) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_nontrivial_centralizerPPart
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord hresidual

/-- Universal pointwise residuals close the universal pairing-residual proof. -/
theorem regularValueCongruenceSourceFaithfulPairingResidualProof_of_pointwiseResidualProof
    (hresidual :
      regularValueCongruenceSourceFaithfulPointwiseResidualProof
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulPairingResidualProof
      (p := p) (A := A) (G := G) := by
  intro π hπ_simple hπ_coord
  exact
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof_of_pointwiseResidual
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
      (hresidual π hπ_simple hπ_coord)

end LocalBrauerBasisPairingResidualReduction

section ProjectiveEnvelopeBrauerBasisPairingResidualReduction

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

local instance projectiveEnvelopeBrauerBasisPairingResidualReductionFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveEnvelopeBrauerBasisPairingResidualReductionDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Same-family projective-envelope residuals descend through the Exercise `18.4` orthogonality
API to the pure `A`-valued pairing residual. -/
theorem
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof_of_projectiveEnvelopeResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hresidual :
      brauerPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  refine
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof_of_pointwiseResidual
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord ?_
  intro c d _hd
  exact
    coordinateNormalizedBrauerBasis_pointwiseResidual_of_projectiveEnvelopeResidual
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hresidual c d

include K

/-- A single fixed-coordinate Brauer-basis readback input gives the universal pairing-residual
proof for every coordinate-normalized family.

The transfer step keeps the fixed `regularClassCoordinateAddEquiv` coordinates: two families
normalized to the same point masses have the same Grothendieck classes indexwise, and projective
envelope residuals are transported through that class equality before descending back to the
pure `A`-basis residual. -/
theorem regularValueCongruenceSourceFaithfulPairingResidualProof_of_brauerBasisReadbackInput
    (hread :
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulPairingResidualProof
      (p := p) (A := A) (G := G) := by
  classical
  rcases hread with ⟨π₀, hπ₀_simple, hπ₀_coord, hread₀⟩
  intro π hπ_simple hπ_coord
  have hP₀_exists :
      ∀ c : PRegularConjClass G p,
        ∃ P : FiniteProjectiveGroupAlgebraModule k G,
          ∃ f : P.V →ₗ[k[G]] asModule (π₀ c).ρ, f.IsProjectiveEnvelope := by
    intro c
    letI : Simple (π₀ c) := hπ₀_simple c
    exact exists_finite_projectiveEnvelope_of_simple_field (G := G) (τ := π₀ c)
  choose P₀ hP₀_envelope using hP₀_exists
  have hP_exists :
      ∀ c : PRegularConjClass G p,
        ∃ P : FiniteProjectiveGroupAlgebraModule k G,
          ∃ f : P.V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope := by
    intro c
    letI : Simple (π c) := hπ_simple c
    exact exists_finite_projectiveEnvelope_of_simple_field (G := G) (τ := π c)
  choose P hP_envelope using hP_exists
  have hpair₀ :
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π₀ hπ₀_simple hπ₀_coord :=
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π₀ hπ₀_simple hπ₀_coord hread₀
  have hbasis₀ :
      brauerPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G) π₀ hπ₀_simple hπ₀_coord :=
    hpair₀
  have hprojective₀ :
      brauerPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π₀ hπ₀_simple hπ₀_coord P₀ :=
    brauerPointMassProjectiveEnvelopeResidualDivisibility_of_basisResidualDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π₀ hπ₀_simple hπ₀_coord P₀ hP₀_envelope hbasis₀
  have hprojective :
      brauerPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P :=
    brauerPointMassProjectiveEnvelopeResidualDivisibility_of_coordinateNormalized_family
      (p := p) (A := A) (K := K) (G := G)
      π₀ π hπ₀_simple hπ_simple hπ₀_coord hπ_coord
      P₀ P hP₀_envelope hP_envelope hprojective₀
  exact
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof_of_projectiveEnvelopeResidual
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hprojective

/-- The existential projective-envelope residual form of Serre `18.5(a)` gives the universal
pairing residual. -/
theorem regularValueCongruenceSourceFaithfulPairingResidualProof_of_projectiveEnvelopeResidual
    (hresidual :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulPairingResidualProof
      (p := p) (A := A) (G := G) :=
  regularValueCongruenceSourceFaithfulPairingResidualProof_of_pointwiseResidualProof
    (p := p) (A := A) (G := G)
    (regularValueCongruenceSourceFaithfulPointwiseResidualProof_of_projectiveEnvelopeResidual
      (p := p) (A := A) (K := K) (G := G) hresidual)

end ProjectiveEnvelopeBrauerBasisPairingResidualReduction

section FullMixedBrauerBasisPairingResidualReduction

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerBasisPairingResidualReductionFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerBasisPairingResidualReductionDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model projective-envelope residuals imply the pairing-residual blocker. -/
theorem fullMixedModelBrauerBasisPairingResidualBlocker_of_projectiveEnvelopeResidual
    (hresidual :
      fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisPairingResidualBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulPairingResidualProof_of_projectiveEnvelopeResidual
      (p := p) (A := A) (K := K) (G := G)
      (hresidual (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The universal pairing-residual blocker is exactly the full mixed fixed-coordinate readback
input.

The reverse direction upgrades the existential readback family in each mixed model to the
universal pairing residual by transferring along equality of fixed
`regularClassCoordinateAddEquiv` coordinates; no natural Brauer-table coordinate is substituted.
-/
theorem fullMixedModelBrauerBasisPairingResidualBlocker_iff_readbackInput :
    fullMixedModelBrauerBasisPairingResidualBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelBrauerBasisReadbackInput_of_pairingResidualBlocker
        (p := p) (k := k) (G := G)
  · intro hread A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      regularValueCongruenceSourceFaithfulPairingResidualProof_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G)
        (hread (A := A) (K := K) e0)

end FullMixedBrauerBasisPairingResidualReduction

end Representation
