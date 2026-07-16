import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerHigherResidueValuationWorker

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerHighOrderResidualWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerHighOrderResidualWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerHighOrderResidualWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Pointwise high-order DVR bridge for the pairing residual.

If the centralizer `p`-part at `d` is `p ^ n`, then the valuation inequality against the
centralizer `p`-part is exactly divisibility by `(p : A) ^ n`; this is the higher-order step
which is not supplied by a single residue-zero/uniformizer argument. -/
theorem coordinateNormalizedBrauerBasis_pairingResidual_primePow_dvd_of_addVal_le
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p) {n : ℕ}
    (hdpow : ConjClasses.centralizerPPart p d.1 = p ^ n)
    (hval :
      IsDiscreteValuationRing.addVal A (ConjClasses.centralizerPPart p d.1 : A) ≤
        IsDiscreteValuationRing.addVal A
          (coordinateNormalizedBrauerBasis_pairingResidual
            (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d)) :
    (p : A) ^ n ∣
      coordinateNormalizedBrauerBasis_pairingResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d := by
  have hcentral :
      (ConjClasses.centralizerPPart p d.1 : A) = (p : A) ^ n :=
    centralizerPPart_natCast_eq_pow_of_eq_primePow
      (A := A) (p := p) d.1 hdpow
  have hdiv :
      (ConjClasses.centralizerPPart p d.1 : A) ∣
        coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d :=
    (IsDiscreteValuationRing.addVal_le_iff_dvd
      (R := A)
      (a := (ConjClasses.centralizerPPart p d.1 : A))
      (b := coordinateNormalizedBrauerBasis_pairingResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d)).1 hval
  simpa [hcentral] using hdiv

/-- Exact valuation input for the pairing residual gives the high-order prime-power residual
input, retaining the full exponent `n` from `centralizerPPart p d.1 = p ^ n`. -/
theorem coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_of_addValInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hval :
      coordinateNormalizedBrauerBasisPairingResidualAddValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisPairingResidualPrimePowInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d n hdpow
  exact
    coordinateNormalizedBrauerBasis_pairingResidual_primePow_dvd_of_addVal_le
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d hdpow (hval c d)

/-- Conversely, the high-order prime-power input is exactly the valuation inequality form:
choose the prime-power expression for each centralizer `p`-part and apply the DVR divisibility
criterion. -/
theorem coordinateNormalizedBrauerBasisPairingResidualAddValInput_of_primePowInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hpow :
      coordinateNormalizedBrauerBasisPairingResidualPrimePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisPairingResidualAddValInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d
  rcases ConjClasses.centralizerPPart_eq_prime_pow (p := p) d.1 with ⟨n, hdpow⟩
  have hcentral :
      (ConjClasses.centralizerPPart p d.1 : A) = (p : A) ^ n :=
    centralizerPPart_natCast_eq_pow_of_eq_primePow
      (A := A) (p := p) d.1 hdpow
  have hdiv :
      (ConjClasses.centralizerPPart p d.1 : A) ∣
        coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d := by
    simpa [hcentral] using hpow c d n hdpow
  exact
    (IsDiscreteValuationRing.addVal_le_iff_dvd
      (R := A)
      (a := (ConjClasses.centralizerPPart p d.1 : A))
      (b := coordinateNormalizedBrauerBasis_pairingResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d)).2 hdiv

/-- The high-order prime-power residual input is equivalent to the exact DVR valuation input. -/
theorem coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_iff_addValInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPairingResidualPrimePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerBasisPairingResidualAddValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  constructor
  · exact
      coordinateNormalizedBrauerBasisPairingResidualAddValInput_of_primePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord
  · exact
      coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_of_addValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- Direct centralizer-`p`-part divisibility already contains the high-order prime-power
statement, because each centralizer `p`-part is literally `p ^ n`. -/
theorem coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_of_divisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hdiv :
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisPairingResidualPrimePowInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d n hdpow
  rcases hdiv c d with ⟨a, ha⟩
  have hcentral :
      (ConjClasses.centralizerPPart p d.1 : A) = (p : A) ^ n :=
    centralizerPPart_natCast_eq_pow_of_eq_primePow
      (A := A) (p := p) d.1 hdpow
  refine ⟨a, ?_⟩
  simpa [coordinateNormalizedBrauerBasis_pairingResidual, hcentral] using ha

/-- Centralizer-divisibility and the prime-power input are equivalent for coordinate-normalized
Brauer-basis pairing residuals.  The forward direction is the high-order readback missing from
the one-step residue route; the reverse direction was already available upstream. -/
theorem coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_iff_divisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPairingResidualPrimePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  constructor
  · exact
      coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_primePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord
  · exact
      coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_of_divisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord

end BrauerHighOrderResidualWorker

end Representation
