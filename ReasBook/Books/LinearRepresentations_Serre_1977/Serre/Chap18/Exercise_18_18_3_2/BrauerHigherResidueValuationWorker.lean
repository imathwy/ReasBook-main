import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackEndpoint
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerResidualValuationFinal
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CentralizerPPartDivisibilityInfraFinal

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerHigherResidueValuationWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerHigherResidueValuationWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerHigherResidueValuationWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- High-order input in the prime-power form of Serre's centralizer `p`-part divisibility.

For each column `d`, once `centralizerPPart p d.1 = p ^ n`, the pairing residual is assumed
to be divisible by `(p : A) ^ n`.  This is equivalent to the centralizer-`p`-part divisibility
needed by the readback route, but keeps the missing exponent visible. -/
def coordinateNormalizedBrauerBasisPairingResidualPrimePowInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  ∀ c d : PRegularConjClass G p,
    ∀ n : ℕ,
      ConjClasses.centralizerPPart p d.1 = p ^ n →
        (p : A) ^ n ∣
          coordinateNormalizedBrauerBasis_pairingResidual
            (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d

/-- Prime-power residual divisibility closes the coordinate-normalized pairing residual. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_primePowInput
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
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d
  rcases ConjClasses.centralizerPPart_eq_prime_pow (p := p) d.1 with ⟨n, hn⟩
  exact
    coordinateNormalizedBrauerBasis_pairingResidual_dvd_of_primePow_dvd
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d hn
      (hpow c d n hn)

/-- The high-order prime-power residual input gives the exact visible-readback valuation input. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackAddValInput_of_primePowInput
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
    coordinateNormalizedBrauerBasisVisibleReadbackAddValInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  coordinateNormalizedBrauerBasisVisibleReadbackAddValInput_of_pairingResidualDivisibility
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord
    (coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_primePowInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hpow)

/-- The same prime-power input closes the named nontrivial pointwise residual. -/
theorem coordinateNormalizedBrauerBasisNontrivialPointwiseResidual_of_primePowInput
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
    coordinateNormalizedBrauerBasisNontrivialPointwiseResidual
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_nontrivialPointwiseResidual
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
    (coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_primePowInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hpow)

/-- A fixed coordinate-normalized family with the prime-power residual input gives the local
readback endpoint. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_primePowResidualInput
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
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  refine
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_fixedFamilyReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord ?_
  exact
    (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_primePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord hpow)

/-- Residue-zero input for the same pairing residual.  This is intentionally weaker than the
prime-power input above: in a DVR it gives one uniformizer factor, not the full `p`-power
centralizer factor. -/
def coordinateNormalizedBrauerBasisPairingResidualResidueZeroInput
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  ∀ c d : PRegularConjClass G p,
    IsLocalRing.residue A
      (coordinateNormalizedBrauerBasis_pairingResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d) = 0

/-- A residue-zero pairing residual is divisible by any chosen irreducible uniformizer. -/
theorem coordinateNormalizedBrauerBasis_pairingResidual_uniformizer_dvd_of_residueZero
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    {ϖ : A} (hϖ : Irreducible ϖ)
    (hres :
      coordinateNormalizedBrauerBasisPairingResidualResidueZeroInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)
    (c d : PRegularConjClass G p) :
    ϖ ∣
      coordinateNormalizedBrauerBasis_pairingResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d :=
  (residue_eq_zero_iff_irreducible_dvd (A := A) hϖ).1 (hres c d)

/-- Residue-zero closes the pairing residual only after an extra divisibility bridge from each
centralizer `p`-part to the chosen uniformizer.  This records the precise gap left by a
one-step residue computation. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_residueZero_uniformizerBridge
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    {ϖ : A} (hϖ : Irreducible ϖ)
    (hres :
      coordinateNormalizedBrauerBasisPairingResidualResidueZeroInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)
    (hcentral :
      ∀ d : PRegularConjClass G p,
        (ConjClasses.centralizerPPart p d.1 : A) ∣ ϖ) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d
  have hϖ_dvd :
      ϖ ∣
        coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d :=
    coordinateNormalizedBrauerBasis_pairingResidual_uniformizer_dvd_of_residueZero
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord hϖ hres c d
  have hdiv :
      (ConjClasses.centralizerPPart p d.1 : A) ∣
        coordinateNormalizedBrauerBasis_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d :=
    (hcentral d).trans hϖ_dvd
  simpa [coordinateNormalizedBrauerBasis_pairingResidual] using hdiv

end BrauerHigherResidueValuationWorker

section FullMixedBrauerHigherResidueValuationWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerHigherResidueValuationWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerHigherResidueValuationWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model version of the high-order prime-power residual input. -/
def fullMixedModelBrauerBasisPairingResidualPrimePowBlocker : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      ∀ (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
        (hπ_simple : ∀ c, Simple (π c))
        (hπ_coord :
          ∀ c,
            regularClassCoordinateAddEquiv
                (p := p) (G := G) ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
        coordinateNormalizedBrauerBasisPairingResidualPrimePowInput
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model high-order residual input closes the existing full readback input. -/
theorem fullMixedModelBrauerBasisReadbackInput_of_pairingResidualPrimePowBlocker
    (hpow :
      fullMixedModelBrauerBasisPairingResidualPrimePowBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  refine
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_universalReadback
      (p := p) (A := A) (G := G) ?_
  intro π hπ_simple hπ_coord
  exact
    (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_primePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord
        (hpow (A := A) (K := K) e0 π hπ_simple hπ_coord))

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model high-order residual input supplies the exact visible-readback valuation
input for every coordinate-normalized family, without passing through Cartan range/cokernel or
product endpoints. -/
theorem fullMixedModelCoordinateNormalizedBrauerBasisVisibleReadbackAddValInput_of_pairingResidualPrimePowBlocker
    (hpow :
      fullMixedModelBrauerBasisPairingResidualPrimePowBlocker
        (p := p) (k := k) (G := G)) :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
      [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
      {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
      [HasEnoughRootsOfUnity K (Monoid.exponent G)]
      [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
      IsLocalRing.ResidueField A ≃+* k →
        ∀ (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
          (hπ_simple : ∀ c, Simple (π c))
          (hπ_coord :
            ∀ c,
              regularClassCoordinateAddEquiv
                  (p := p) (G := G)
                  ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
          coordinateNormalizedBrauerBasisVisibleReadbackAddValInput
            (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0 π hπ_simple hπ_coord
  exact
    coordinateNormalizedBrauerBasisVisibleReadbackAddValInput_of_primePowInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
      (hpow (A := A) (K := K) e0 π hπ_simple hπ_coord)

end FullMixedBrauerHigherResidueValuationWorker

end Representation
