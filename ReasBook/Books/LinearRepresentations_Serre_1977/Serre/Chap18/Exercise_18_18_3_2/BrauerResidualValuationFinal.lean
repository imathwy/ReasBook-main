import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackACompletion

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerResidualValuationFinal

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerResidualValuationFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerResidualValuationFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsLocalRing A] [HenselianLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAlgClosed k] [CharP k p] in
private theorem centralizerPPart_natCast_dvd_of_addVal_le_for_residual
    (c : ConjClasses G) {x : A}
    (hval :
      IsDiscreteValuationRing.addVal A (ConjClasses.centralizerPPart p c : A) ≤
        IsDiscreteValuationRing.addVal A x) :
    (ConjClasses.centralizerPPart p c : A) ∣ x :=
  (IsDiscreteValuationRing.addVal_le_iff_dvd
    (R := A) (a := (ConjClasses.centralizerPPart p c : A)) (b := x)).1 hval

omit [IsLocalRing A] [HenselianLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAlgClosed k] [CharP k p] in
private theorem centralizerPPart_natCast_dvd_of_primePow_dvd_for_residual
    (c : ConjClasses G) {n : ℕ} {x : A}
    (hc : ConjClasses.centralizerPPart p c = p ^ n)
    (hx : (p : A) ^ n ∣ x) :
    (ConjClasses.centralizerPPart p c : A) ∣ x := by
  simpa [hc, Nat.cast_pow] using hx

/-- The fixed-coordinate visible readback residual for a coordinate-normalized Brauer family. -/
def coordinateNormalizedBrauerBasis_visibleReadbackResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p) : A :=
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  bA c d - ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)

/-- The pairing-route residual after subtracting the visible projective-envelope multiple. -/
def coordinateNormalizedBrauerBasis_pairingResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p) : A :=
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  bA c d -
      ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
    (ConjClasses.centralizerPPart p d.1 : A) *
      (bA.repr
        (primeToP_regular_indicator
          (p := p) (A := A) (G := G)
          (inversePRegularConjClass (p := p) d)) c)

/-- Exact missing valuation input for closing all visible fixed-coordinate readback residuals. -/
def coordinateNormalizedBrauerBasisVisibleReadbackAddValInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  ∀ c d : PRegularConjClass G p,
    IsDiscreteValuationRing.addVal A (ConjClasses.centralizerPPart p d.1 : A) ≤
      IsDiscreteValuationRing.addVal A
        (coordinateNormalizedBrauerBasis_visibleReadbackResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d)

/-- Exact missing valuation input for closing all pairing residuals. -/
def coordinateNormalizedBrauerBasisPairingResidualAddValInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  ∀ c d : PRegularConjClass G p,
    IsDiscreteValuationRing.addVal A (ConjClasses.centralizerPPart p d.1 : A) ≤
      IsDiscreteValuationRing.addVal A
        (coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d)

/-- Conditional bridge: a DVR valuation inequality on the visible readback residual gives the
centralizer-`p`-part multiplier required by the fixed-coordinate readback API. -/
theorem coordinateNormalizedBrauerBasis_visibleReadback_dvd_of_addVal_le
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p)
    (hval :
      IsDiscreteValuationRing.addVal A (ConjClasses.centralizerPPart p d.1 : A) ≤
        IsDiscreteValuationRing.addVal A
          (coordinateNormalizedBrauerBasis_visibleReadbackResidual
            (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d)) :
    ∃ a : A,
      coordinateNormalizedBrauerBasis_visibleReadbackResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d =
        (ConjClasses.centralizerPPart p d.1 : A) * a :=
  centralizerPPart_natCast_dvd_of_addVal_le_for_residual
    (A := A) (p := p) d.1 hval

/-- Prime-power version of the visible readback bridge. -/
theorem coordinateNormalizedBrauerBasis_visibleReadback_dvd_of_primePow_dvd
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p) {n : ℕ}
    (hdpow : ConjClasses.centralizerPPart p d.1 = p ^ n)
    (hpow :
      (p : A) ^ n ∣
        coordinateNormalizedBrauerBasis_visibleReadbackResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d) :
    ∃ a : A,
      coordinateNormalizedBrauerBasis_visibleReadbackResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d =
        (ConjClasses.centralizerPPart p d.1 : A) * a :=
  centralizerPPart_natCast_dvd_of_primePow_dvd_for_residual
    (A := A) (p := p) d.1 hdpow hpow

/-- Conditional bridge for the pairing-route residual. -/
theorem coordinateNormalizedBrauerBasis_pairingResidual_dvd_of_addVal_le
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p)
    (hval :
      IsDiscreteValuationRing.addVal A (ConjClasses.centralizerPPart p d.1 : A) ≤
        IsDiscreteValuationRing.addVal A
          (coordinateNormalizedBrauerBasis_pairingResidual
            (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d)) :
    ∃ a : A,
      coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d =
        (ConjClasses.centralizerPPart p d.1 : A) * a :=
  centralizerPPart_natCast_dvd_of_addVal_le_for_residual
    (A := A) (p := p) d.1 hval

/-- Prime-power version of the pairing residual bridge. -/
theorem coordinateNormalizedBrauerBasis_pairingResidual_dvd_of_primePow_dvd
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p) {n : ℕ}
    (hdpow : ConjClasses.centralizerPPart p d.1 = p ^ n)
    (hpow :
      (p : A) ^ n ∣
        coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d) :
    ∃ a : A,
      coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d =
        (ConjClasses.centralizerPPart p d.1 : A) * a :=
  centralizerPPart_natCast_dvd_of_primePow_dvd_for_residual
    (A := A) (p := p) d.1 hdpow hpow

/-- All visible readback valuation inequalities close the fixed-coordinate readback input. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_of_visibleReadbackAddValInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hval :
      coordinateNormalizedBrauerBasisVisibleReadbackAddValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord) := by
  intro c d
  rcases coordinateNormalizedBrauerBasis_visibleReadback_dvd_of_addVal_le
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d (hval c d) with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa [coordinateNormalizedBrauerBasis_visibleReadbackResidual, hπ_coord c] using ha

/-- All pairing-residual valuation inequalities close the pairing residual input. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_addValInput
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
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d
  rcases coordinateNormalizedBrauerBasis_pairingResidual_dvd_of_addVal_le
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d (hval c d) with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa [coordinateNormalizedBrauerBasis_pairingResidual] using ha

/-- Pairing-residual divisibility gives the exact visible-readback DVR valuation input.

The visible residual differs from the pairing residual by the explicit
centralizer-`p`-part multiple isolated by the projective-envelope column, so the same
centralizer divisor controls both expressions. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackAddValInput_of_pairingResidualDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hresidual :
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisVisibleReadbackAddValInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  let z : A := ConjClasses.centralizerPPart p d.1
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G)
        (inversePRegularConjClass (p := p) d)) c)
  rcases hresidual c d with ⟨a, ha⟩
  have hpair :
      coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d =
        z * a := by
    simpa [coordinateNormalizedBrauerBasis_pairingResidual, hπ_pairwise, hπ_complete,
      bA, z, coeff] using ha
  have hdiv :
      (ConjClasses.centralizerPPart p d.1 : A) ∣
        coordinateNormalizedBrauerBasis_visibleReadbackResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d := by
    refine ⟨a + coeff, ?_⟩
    change
      coordinateNormalizedBrauerBasis_visibleReadbackResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d =
        z * (a + coeff)
    calc
      coordinateNormalizedBrauerBasis_visibleReadbackResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d =
          coordinateNormalizedBrauerBasis_pairingResidual
              (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d +
            z * coeff := by
            simp [coordinateNormalizedBrauerBasis_visibleReadbackResidual,
              coordinateNormalizedBrauerBasis_pairingResidual, bA, z, coeff]
      _ = z * a + z * coeff := by
            rw [hpair]
      _ = z * (a + coeff) := by
            rw [mul_add]
  exact
    (IsDiscreteValuationRing.addVal_le_iff_dvd
      (R := A)
      (a := (ConjClasses.centralizerPPart p d.1 : A))
      (b := coordinateNormalizedBrauerBasis_visibleReadbackResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d)).2 hdiv

/-- The exact pairing-residual DVR valuation input implies the exact visible-readback input. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackAddValInput_of_pairingResidualAddValInput
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
    coordinateNormalizedBrauerBasisVisibleReadbackAddValInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  coordinateNormalizedBrauerBasisVisibleReadbackAddValInput_of_pairingResidualDivisibility
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord
    (coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_addValInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hval)

/-- The visible-readback and pairing-residual DVR valuation inputs are equivalent: their
residuals differ by an explicit centralizer-`p`-part multiple. -/
theorem coordinateNormalizedBrauerBasisPairingResidualAddValInput_of_visibleReadbackAddValInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hval :
      coordinateNormalizedBrauerBasisVisibleReadbackAddValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisPairingResidualAddValInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  let z : A := ConjClasses.centralizerPPart p d.1
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G)
        (inversePRegularConjClass (p := p) d)) c)
  rcases
      (IsDiscreteValuationRing.addVal_le_iff_dvd
        (R := A)
        (a := (ConjClasses.centralizerPPart p d.1 : A))
        (b := coordinateNormalizedBrauerBasis_visibleReadbackResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d)).1 (hval c d) with
    ⟨a, ha⟩
  have hdiv :
      (ConjClasses.centralizerPPart p d.1 : A) ∣
        coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d := by
    refine ⟨a - coeff, ?_⟩
    change
      coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d =
        z * (a - coeff)
    calc
      coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d =
          coordinateNormalizedBrauerBasis_visibleReadbackResidual
              (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d -
            z * coeff := by
            simp [coordinateNormalizedBrauerBasis_visibleReadbackResidual,
              coordinateNormalizedBrauerBasis_pairingResidual, bA, z, coeff]
      _ = z * a - z * coeff := by
            rw [ha]
      _ = z * (a - coeff) := by
            rw [mul_sub]
  exact
    (IsDiscreteValuationRing.addVal_le_iff_dvd
      (R := A)
      (a := (ConjClasses.centralizerPPart p d.1 : A))
      (b := coordinateNormalizedBrauerBasis_pairingResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d)).2 hdiv

/-- The exact visible-readback and pairing-residual valuation inputs are the same local
high-order DVR datum. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackAddValInput_iff_pairingResidualAddValInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisVisibleReadbackAddValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerBasisPairingResidualAddValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  constructor
  · exact
      coordinateNormalizedBrauerBasisPairingResidualAddValInput_of_visibleReadbackAddValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord
  · exact
      coordinateNormalizedBrauerBasisVisibleReadbackAddValInput_of_pairingResidualAddValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord

end BrauerResidualValuationFinal

end Representation
