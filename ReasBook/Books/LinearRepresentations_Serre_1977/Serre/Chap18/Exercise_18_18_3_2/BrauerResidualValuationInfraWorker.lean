import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerHighOrderResidualWorker

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerResidualValuationInfraWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerResidualValuationInfraWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerResidualValuationInfraWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Source-facing valuation input for the expanded pairing residual, restricted to columns whose
centralizer `p`-part is nontrivial.  The `centralizerPPart = 1` columns are automatic for the
existing DVR `addVal` residual input. -/
def coordinateNormalizedBrauerBasisNontrivialPointwiseAddValInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
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
      IsDiscreteValuationRing.addVal A (ConjClasses.centralizerPPart p d.1 : A) ≤
        IsDiscreteValuationRing.addVal A
          (bA c d -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
            (ConjClasses.centralizerPPart p d.1 : A) *
              (bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G)
                  (inversePRegularConjClass (p := p) d)) c))

/-- Nontrivial expanded valuation bounds fill the full named `addVal` residual input; the
trivial centralizer columns use `1 ∣ residual`. -/
theorem coordinateNormalizedBrauerBasisPairingResidualAddValInput_of_nontrivialPointwiseAddValInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hval :
      coordinateNormalizedBrauerBasisNontrivialPointwiseAddValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisPairingResidualAddValInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d
  by_cases hd : ConjClasses.centralizerPPart p d.1 = 1
  · have hdiv :
        (ConjClasses.centralizerPPart p d.1 : A) ∣
          coordinateNormalizedBrauerBasis_pairingResidual
            (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d := by
      simp [hd]
    exact
      (IsDiscreteValuationRing.addVal_le_iff_dvd
        (R := A)
        (a := (ConjClasses.centralizerPPart p d.1 : A))
        (b := coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d)).2 hdiv
  · simpa [coordinateNormalizedBrauerBasis_pairingResidual] using hval c d hd

/-- Existing named `addVal` residual input is equivalent to the source-facing nontrivial
expanded valuation input. -/
theorem coordinateNormalizedBrauerBasisPairingResidualAddValInput_iff_nontrivialPointwiseAddValInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPairingResidualAddValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerBasisNontrivialPointwiseAddValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  constructor
  · intro hval c d _hd
    simpa [coordinateNormalizedBrauerBasis_pairingResidual] using hval c d
  · exact
      coordinateNormalizedBrauerBasisPairingResidualAddValInput_of_nontrivialPointwiseAddValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- Source-facing prime-power divisibility input for the expanded pairing residual, restricted
to nontrivial centralizer columns. -/
def coordinateNormalizedBrauerBasisNontrivialPointwisePrimePowInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  ∀ c d : PRegularConjClass G p,
    ∀ n : ℕ,
      ConjClasses.centralizerPPart p d.1 ≠ 1 →
        ConjClasses.centralizerPPart p d.1 = p ^ n →
          let hπ_pairwise :=
            pairwiseNonisomorphic_of_regularClassCoordinate_single
              (p := p) (G := G) (π := π) hπ_coord
          let hπ_complete :=
            complete_irreducible_family_of_regularClassCoordinate_single
              (p := p) (G := G) (π := π) hπ_simple hπ_coord
          let bA :=
            canonicalDVRBrauerBasis
              (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
          (p : A) ^ n ∣
            bA c d -
                ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
              (ConjClasses.centralizerPPart p d.1 : A) *
                (bA.repr
                  (primeToP_regular_indicator
                    (p := p) (A := A) (G := G)
                    (inversePRegularConjClass (p := p) d)) c)

/-- Nontrivial expanded prime-power divisibility fills the full named prime-power residual
input; the `centralizerPPart = 1` columns again reduce to `1 ∣ residual`. -/
theorem coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_of_nontrivialPointwisePrimePowInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hpow :
      coordinateNormalizedBrauerBasisNontrivialPointwisePrimePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisPairingResidualPrimePowInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d n hdpow
  by_cases hd : ConjClasses.centralizerPPart p d.1 = 1
  · have hdiv :
        (ConjClasses.centralizerPPart p d.1 : A) ∣
          coordinateNormalizedBrauerBasis_pairingResidual
            (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d := by
      simp [hd]
    simpa [centralizerPPart_natCast_eq_pow_of_eq_primePow
      (A := A) (p := p) d.1 hdpow] using hdiv
  · simpa [coordinateNormalizedBrauerBasis_pairingResidual] using hpow c d n hd hdpow

/-- Existing named prime-power residual input is equivalent to the source-facing nontrivial
expanded prime-power input. -/
theorem coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_iff_nontrivialPointwisePrimePowInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPairingResidualPrimePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerBasisNontrivialPointwisePrimePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  constructor
  · intro hpow c d n _hd hdpow
    simpa [coordinateNormalizedBrauerBasis_pairingResidual] using hpow c d n hdpow
  · exact
      coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_of_nontrivialPointwisePrimePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- Nontrivial expanded valuation input closes the residual divisibility proposition. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_nontrivialPointwiseAddValInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hval :
      coordinateNormalizedBrauerBasisNontrivialPointwiseAddValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_addValInput
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord
    (coordinateNormalizedBrauerBasisPairingResidualAddValInput_of_nontrivialPointwiseAddValInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hval)

/-- Nontrivial expanded prime-power input closes the residual divisibility proposition. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_nontrivialPointwisePrimePowInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hpow :
      coordinateNormalizedBrauerBasisNontrivialPointwisePrimePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_primePowInput
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord
    (coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_of_nontrivialPointwisePrimePowInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hpow)

/-- Nontrivial expanded valuation input gives the named nontrivial pointwise residual. -/
theorem coordinateNormalizedBrauerBasisNontrivialPointwiseResidual_of_nontrivialPointwiseAddValInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hval :
      coordinateNormalizedBrauerBasisNontrivialPointwiseAddValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisNontrivialPointwiseResidual
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_nontrivialPointwiseResidual
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
    (coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_nontrivialPointwiseAddValInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hval)

/-- Nontrivial expanded prime-power input gives the named nontrivial pointwise residual. -/
theorem coordinateNormalizedBrauerBasisNontrivialPointwiseResidual_of_nontrivialPointwisePrimePowInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hpow :
      coordinateNormalizedBrauerBasisNontrivialPointwisePrimePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisNontrivialPointwiseResidual
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_nontrivialPointwiseResidual
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
    (coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_nontrivialPointwisePrimePowInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hpow)

end BrauerResidualValuationInfraWorker

end Representation
