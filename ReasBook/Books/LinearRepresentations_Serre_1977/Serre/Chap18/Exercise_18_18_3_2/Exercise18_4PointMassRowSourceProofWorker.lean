import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.Exercise18_4PointMassRowCongruenceProofWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackACompletion
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ExplicitResidualPairingSumWorker

/-!
Source-side reductions for the Exercise `18.4` point-mass row congruence.

This worker does not close the row congruence unconditionally.  It isolates two equivalent
source-side frontiers:

* the pure `A`-side nontrivial-column residual after the visible projective row is split off;
* the literal Serre pairing-sum residual using Exercise `18.4` and
  `<Phi_E, phi_E'> = delta_EE'`.

No Cartan cokernel/product/Smith/determinant endpoint is used here.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section Exercise18_4PointMassRowSourceProofWorkerASide

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "kA" => IsLocalRing.ResidueField A

local instance exercise18_4PointMassRowSourceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance exercise18_4PointMassRowSourceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Universal pure `A`-side residual left by the Exercise `18.4` / orthogonality route.

For each coordinate-normalized Brauer family, this asks for divisibility of
`bA c d - delta_cd - z(d) * coeff(c,d)`, where the coefficient term is the already visible
projective-envelope row supplied by Exercise `18.4` and orthogonality. -/
def exercise18_4PointMassRowPairingResidualSourceLemma : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- Pointwise nontrivial-column form of the previous residual.  The columns with
`centralizerPPart = 1` are automatic in the existing A-side API, so this is the smallest
current pure pointwise source obligation. -/
def exercise18_4PointMassRowNontrivialPointwiseResidualSourceLemma : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p),
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
            (ConjClasses.centralizerPPart p d.1 : A) * a

/-- The requested Exercise `18.4` source theorem is exactly the universal pure `A`-side
pairing residual. -/
theorem exercise18_4PointMassRowCongruenceSourceTheorem_iff_pairingResidualSourceLemma :
    exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (G := G) ↔
      exercise18_4PointMassRowPairingResidualSourceLemma
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hsource π hπ_simple hπ_coord
    have hread :
        brauerBasisFixedCoordinateReadbackDivisibility
          (p := p) (A := A) (G := G)
          π
          (pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord)
          (complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord) :=
      (exercise18_4PointMassRowCongruenceAPI_iff_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
        (hsource π hπ_simple hπ_coord)
    exact
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hread
  · intro hresidual π hπ_simple hπ_coord
    have hread :
        brauerBasisFixedCoordinateReadbackDivisibility
          (p := p) (A := A) (G := G)
          π
          (pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord)
          (complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord) :=
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
        (hresidual π hπ_simple hπ_coord)
    exact
      (exercise18_4PointMassRowCongruenceAPI_iff_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hread

/-- The universal residual is equivalent to its nontrivial-column pointwise form. -/
theorem exercise18_4PointMassRowPairingResidualSourceLemma_iff_nontrivialPointwiseResidual :
    exercise18_4PointMassRowPairingResidualSourceLemma
        (p := p) (A := A) (G := G) ↔
      exercise18_4PointMassRowNontrivialPointwiseResidualSourceLemma
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hresidual π hπ_simple hπ_coord
    exact
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_nontrivial_centralizerPPart
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
        (hresidual π hπ_simple hπ_coord)
  · intro hpoint π hπ_simple hπ_coord
    exact
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_nontrivial_centralizerPPart
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2
        (hpoint π hπ_simple hπ_coord)

/-- Pointwise nontrivial-column residuals are equivalent to the requested source theorem. -/
theorem exercise18_4PointMassRowCongruenceSourceTheorem_iff_nontrivialPointwiseResidual :
    exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (G := G) ↔
      exercise18_4PointMassRowNontrivialPointwiseResidualSourceLemma
        (p := p) (A := A) (G := G) :=
  (exercise18_4PointMassRowCongruenceSourceTheorem_iff_pairingResidualSourceLemma
    (p := p) (A := A) (G := G)).trans
    (exercise18_4PointMassRowPairingResidualSourceLemma_iff_nontrivialPointwiseResidual
      (p := p) (A := A) (G := G))

end Exercise18_4PointMassRowSourceProofWorkerASide

section Exercise18_4PointMassRowSourceProofWorkerPairingSumSide

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

local instance exercise18_4PointMassRowSourceProofWorkerPairingSumFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance exercise18_4PointMassRowSourceProofWorkerPairingSumDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Universal literal Serre pairing-sum residual for every coordinate-normalized Exercise `18.4`
family, after choosing projective envelopes. -/
def exercise18_4PointMassRowPairingSumResidualSourceLemma : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
    ∃ P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G,
      (∀ c, ∃ f : (P c).V →ₗ[kA[G]] asModule (π c).ρ, f.IsProjectiveEnvelope) ∧
        let hπ_pairwise :=
          pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord
        let hπ_complete :=
          complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord
        orthogonalityPairingSumResidualCongruence
          (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P

/-- The literal pairing-sum residual is equivalent to the pure `A`-side residual. -/
theorem exercise18_4PointMassRowPairingSumResidualSourceLemma_iff_pairingResidualSourceLemma :
    exercise18_4PointMassRowPairingSumResidualSourceLemma
        (p := p) (A := A) (K := K) (G := G) ↔
      exercise18_4PointMassRowPairingResidualSourceLemma
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hsum π hπ_simple hπ_coord
    rcases hsum π hπ_simple hπ_coord with ⟨P, hP_envelope, hsum'⟩
    exact
      (orthogonalityPairingSumResidualCongruence_iff_coordinateNormalizedPairingResidual
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope).1 hsum'
  · intro hresidual π hπ_simple hπ_coord
    have hP_exists :
        ∀ c : PRegularConjClass G p,
          ∃ P : FiniteProjectiveGroupAlgebraModule kA G,
            ∃ f : P.V →ₗ[kA[G]] asModule (π c).ρ, f.IsProjectiveEnvelope := by
      intro c
      letI : Simple (π c) := hπ_simple c
      exact exists_finite_projectiveEnvelope_of_simple_field (G := G) (τ := π c)
    choose P hP_envelope using hP_exists
    refine ⟨P, hP_envelope, ?_⟩
    exact
      (orthogonalityPairingSumResidualCongruence_iff_coordinateNormalizedPairingResidual
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope).2
        (hresidual π hπ_simple hπ_coord)

/-- The requested Exercise `18.4` source theorem is equivalent to the literal universal
pairing-sum source lemma. -/
theorem exercise18_4PointMassRowCongruenceSourceTheorem_iff_pairingSumResidualSourceLemma :
    exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (G := G) ↔
      exercise18_4PointMassRowPairingSumResidualSourceLemma
        (p := p) (A := A) (K := K) (G := G) :=
  (exercise18_4PointMassRowCongruenceSourceTheorem_iff_pairingResidualSourceLemma
    (p := p) (A := A) (G := G)).trans
    (exercise18_4PointMassRowPairingSumResidualSourceLemma_iff_pairingResidualSourceLemma
      (p := p) (A := A) (K := K) (G := G)).symm

end Exercise18_4PointMassRowSourceProofWorkerPairingSumSide

end Representation
