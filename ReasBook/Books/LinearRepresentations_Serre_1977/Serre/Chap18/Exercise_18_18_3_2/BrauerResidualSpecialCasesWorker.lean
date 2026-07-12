import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerHigherResidueValuationWorker

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerResidualSpecialCasesWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerResidualSpecialCasesWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerResidualSpecialCasesWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- If `(p : A)` itself is an irreducible uniformizer, residue-zero of the pairing residual
gives one visible `p` factor. -/
theorem coordinateNormalizedBrauerBasis_pairingResidual_p_dvd_of_residueZero_of_irreducible_natCast
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hpA : Irreducible (p : A))
    (hres :
      coordinateNormalizedBrauerBasisPairingResidualResidueZeroInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)
    (c d : PRegularConjClass G p) :
    (p : A) ∣
      coordinateNormalizedBrauerBasis_pairingResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d :=
  coordinateNormalizedBrauerBasis_pairingResidual_uniformizer_dvd_of_residueZero
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord
    (ϖ := (p : A)) hpA hres c d

/-- Associated-uniformizer variant of the one-step residue bridge. -/
theorem coordinateNormalizedBrauerBasis_pairingResidual_p_dvd_of_residueZero_of_associated_uniformizer
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    {ϖ : A} (hϖ : Irreducible ϖ)
    (hpϖ : Associated (p : A) ϖ)
    (hres :
      coordinateNormalizedBrauerBasisPairingResidualResidueZeroInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)
    (c d : PRegularConjClass G p) :
    (p : A) ∣
      coordinateNormalizedBrauerBasis_pairingResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d := by
  have hϖ_dvd :
      ϖ ∣
        coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d :=
    coordinateNormalizedBrauerBasis_pairingResidual_uniformizer_dvd_of_residueZero
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hϖ hres c d
  exact (hpϖ.dvd_iff_dvd_left).2 hϖ_dvd

/-- Pointwise `centralizerPPart = p` residual from residue-zero when `(p : A)` is a
uniformizer. -/
theorem coordinateNormalizedBrauerBasis_pairingResidual_centralizerPPart_dvd_of_residueZero_of_eq_p
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hpA : Irreducible (p : A))
    (hres :
      coordinateNormalizedBrauerBasisPairingResidualResidueZeroInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)
    (c d : PRegularConjClass G p)
    (hd : ConjClasses.centralizerPPart p d.1 = p) :
    ∃ a : A,
      coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d =
        (ConjClasses.centralizerPPart p d.1 : A) * a := by
  have hp_dvd :
      (p : A) ∣
        coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d :=
    coordinateNormalizedBrauerBasis_pairingResidual_p_dvd_of_residueZero_of_irreducible_natCast
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hpA hres c d
  have hp_pow :
      (p : A) ^ 1 ∣
        coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d := by
    simpa [pow_one] using hp_dvd
  have hd_pow : ConjClasses.centralizerPPart p d.1 = p ^ 1 := by
    simpa [pow_one] using hd
  exact
    coordinateNormalizedBrauerBasis_pairingResidual_dvd_of_primePow_dvd
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d hd_pow hp_pow

/-- Associated-uniformizer variant of the pointwise `centralizerPPart = p` residual. -/
theorem coordinateNormalizedBrauerBasis_pairingResidual_centralizerPPart_dvd_of_residueZero_of_eq_p_associated
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    {ϖ : A} (hϖ : Irreducible ϖ)
    (hpϖ : Associated (p : A) ϖ)
    (hres :
      coordinateNormalizedBrauerBasisPairingResidualResidueZeroInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)
    (c d : PRegularConjClass G p)
    (hd : ConjClasses.centralizerPPart p d.1 = p) :
    ∃ a : A,
      coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d =
        (ConjClasses.centralizerPPart p d.1 : A) * a := by
  have hp_dvd :
      (p : A) ∣
        coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d :=
    coordinateNormalizedBrauerBasis_pairingResidual_p_dvd_of_residueZero_of_associated_uniformizer
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hϖ hpϖ hres c d
  have hp_pow :
      (p : A) ^ 1 ∣
        coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d := by
    simpa [pow_one] using hp_dvd
  have hd_pow : ConjClasses.centralizerPPart p d.1 = p ^ 1 := by
    simpa [pow_one] using hd
  exact
    coordinateNormalizedBrauerBasis_pairingResidual_dvd_of_primePow_dvd
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d hd_pow hp_pow

/-- Expanded pointwise residual statement for the `centralizerPPart = p` special case. -/
theorem coordinateNormalizedBrauerBasisPairingResidual_pointwise_of_residueZero_of_centralizerPPart_eq_p
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hpA : Irreducible (p : A))
    (hres :
      coordinateNormalizedBrauerBasisPairingResidualResidueZeroInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)
    (c d : PRegularConjClass G p)
    (hd : ConjClasses.centralizerPPart p d.1 = p) :
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
          (ConjClasses.centralizerPPart p d.1 : A) * a := by
  have hdiv :=
    coordinateNormalizedBrauerBasis_pairingResidual_centralizerPPart_dvd_of_residueZero_of_eq_p
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hpA hres c d hd
  simpa [coordinateNormalizedBrauerBasis_pairingResidual] using hdiv

/-- Expanded associated-uniformizer pointwise residual statement for `centralizerPPart = p`. -/
theorem coordinateNormalizedBrauerBasisPairingResidual_pointwise_of_residueZero_of_centralizerPPart_eq_p_associated
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    {ϖ : A} (hϖ : Irreducible ϖ)
    (hpϖ : Associated (p : A) ϖ)
    (hres :
      coordinateNormalizedBrauerBasisPairingResidualResidueZeroInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)
    (c d : PRegularConjClass G p)
    (hd : ConjClasses.centralizerPPart p d.1 = p) :
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
          (ConjClasses.centralizerPPart p d.1 : A) * a := by
  have hdiv :=
    coordinateNormalizedBrauerBasis_pairingResidual_centralizerPPart_dvd_of_residueZero_of_eq_p_associated
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hϖ hpϖ hres c d hd
  simpa [coordinateNormalizedBrauerBasis_pairingResidual] using hdiv

/-- Low-order provider: if every nontrivial regular centralizer `p`-part is exactly `p`, then
residue-zero plus `(p : A)` a uniformizer closes the full pairing residual. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_residueZero_of_nontrivial_centralizerPPart_eq_p
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hpA : Irreducible (p : A))
    (hres :
      coordinateNormalizedBrauerBasisPairingResidualResidueZeroInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)
    (hcentral :
      ∀ d : PRegularConjClass G p,
        ConjClasses.centralizerPPart p d.1 ≠ 1 →
          ConjClasses.centralizerPPart p d.1 = p) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  refine
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_nontrivial_centralizerPPart
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord ?_
  intro c d hd_ne
  exact
    coordinateNormalizedBrauerBasisPairingResidual_pointwise_of_residueZero_of_centralizerPPart_eq_p
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hpA hres c d
      (hcentral d hd_ne)

/-- Associated-uniformizer version of the low-order provider. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_residueZero_of_nontrivial_centralizerPPart_eq_p_associated
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    {ϖ : A} (hϖ : Irreducible ϖ)
    (hpϖ : Associated (p : A) ϖ)
    (hres :
      coordinateNormalizedBrauerBasisPairingResidualResidueZeroInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)
    (hcentral :
      ∀ d : PRegularConjClass G p,
        ConjClasses.centralizerPPart p d.1 ≠ 1 →
          ConjClasses.centralizerPPart p d.1 = p) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  refine
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_nontrivial_centralizerPPart
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord ?_
  intro c d hd_ne
  exact
    coordinateNormalizedBrauerBasisPairingResidual_pointwise_of_residueZero_of_centralizerPPart_eq_p_associated
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hϖ hpϖ hres c d
      (hcentral d hd_ne)

/-- Simpler low-order corollary stated as `centralizerPPart ∈ {1, p}`. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_residueZero_of_centralizerPPart_eq_one_or_p
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hpA : Irreducible (p : A))
    (hres :
      coordinateNormalizedBrauerBasisPairingResidualResidueZeroInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)
    (hcentral :
      ∀ d : PRegularConjClass G p,
        ConjClasses.centralizerPPart p d.1 = 1 ∨
          ConjClasses.centralizerPPart p d.1 = p) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_residueZero_of_nontrivial_centralizerPPart_eq_p
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord hpA hres
    (fun d hd_ne ↦ Or.resolve_left (hcentral d) hd_ne)

/-- Uniformizer-associated version of the `{1, p}` low-order corollary. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_residueZero_of_centralizerPPart_eq_one_or_p_associated
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    {ϖ : A} (hϖ : Irreducible ϖ)
    (hpϖ : Associated (p : A) ϖ)
    (hres :
      coordinateNormalizedBrauerBasisPairingResidualResidueZeroInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)
    (hcentral :
      ∀ d : PRegularConjClass G p,
        ConjClasses.centralizerPPart p d.1 = 1 ∨
          ConjClasses.centralizerPPart p d.1 = p) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_residueZero_of_nontrivial_centralizerPPart_eq_p_associated
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord hϖ hpϖ hres
    (fun d hd_ne ↦ Or.resolve_left (hcentral d) hd_ne)

end BrauerResidualSpecialCasesWorker

end Representation
