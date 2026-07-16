import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveEnvelopeResidualCompletion
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerHighOrderResidualWorker

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerResidualSourceValuationWorker

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

local instance brauerResidualSourceValuationWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerResidualSourceValuationWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Source-side provider for the coordinate-normalized A-valued pairing residual.

This is the Serre `18.5(a)` route in local form: the projective-character lattice congruence
puts the point-mass row minus the chosen projective-envelope row in the regular-value
divisibility lattice; Exercise `18.4` and the projective-envelope orthogonality relation descend
that fraction-field residual to the pure `A`-valued Brauer-basis residual. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_projectiveCharacter_lattice
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
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  classical
  have hprojectiveResidual :
      brauerPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P :=
    brauerPointMassProjectiveEnvelopeResidualDivisibility_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hlattice
  intro c d
  exact
    fixedFamilyPointwiseResidual_of_projectiveEnvelopeResidualFormula
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hprojectiveResidual c d

/-- Source-side provider for the actual high-order prime-power pairing residual input.

This is only a repackaging of the projective-character lattice/orthogonality route above:
the source theorem gives divisibility by the full cast centralizer `p`-part, and the DVR
centralizer API identifies that factor with `(p : A) ^ n` when
`centralizerPPart p d.1 = p ^ n`. -/
theorem coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_of_projectiveCharacter_lattice
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
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    coordinateNormalizedBrauerBasisPairingResidualPrimePowInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_of_divisibility
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord
    (coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hlattice)

/-- The same source-side provider in the exact DVR valuation form used by the high-order
residual API. -/
theorem coordinateNormalizedBrauerBasisPairingResidualAddValInput_of_projectiveCharacter_lattice
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
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    coordinateNormalizedBrauerBasisPairingResidualAddValInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  exact
    coordinateNormalizedBrauerBasisPairingResidualAddValInput_of_primePowInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
      (coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_of_projectiveCharacter_lattice
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope hlattice)

/-- Universal fixed-family residual provider from the local projective-character lattice
congruence.  The projective envelopes are chosen independently for each simple in the supplied
coordinate-normalized family, so this stays upstream of the Cartan range/cokernel/product
endpoints. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_forall_of_projectiveCharacter_lattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    ∀ (π : PRegularConjClass G p → FDRep k G)
      (hπ_simple : ∀ c, Simple (π c))
      (hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  classical
  intro π hπ_simple hπ_coord
  have hP_exists :
      ∀ c : PRegularConjClass G p,
        ∃ P : FiniteProjectiveGroupAlgebraModule k G,
          ∃ f : P.V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope := by
    intro c
    letI : Simple (π c) := hπ_simple c
    exact exists_finite_projectiveEnvelope_of_simple_field (G := G) (τ := π c)
  choose P hP_envelope using hP_exists
  exact
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hlattice

/-- Universal high-order prime-power residual provider from the local projective-character
lattice congruence. -/
theorem coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_forall_of_projectiveCharacter_lattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    ∀ (π : PRegularConjClass G p → FDRep k G)
      (hπ_simple : ∀ c, Simple (π c))
      (hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
      coordinateNormalizedBrauerBasisPairingResidualPrimePowInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro π hπ_simple hπ_coord
  exact
    coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_of_divisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_forall_of_projectiveCharacter_lattice
        (p := p) (A := A) (K := K) (G := G) hlattice
        π hπ_simple hπ_coord)

/-- Universal AddVal provider from the same source-side lattice congruence. -/
theorem coordinateNormalizedBrauerBasisPairingResidualAddValInput_forall_of_projectiveCharacter_lattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    ∀ (π : PRegularConjClass G p → FDRep k G)
      (hπ_simple : ∀ c, Simple (π c))
      (hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
      coordinateNormalizedBrauerBasisPairingResidualAddValInput
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro π hπ_simple hπ_coord
  exact
    coordinateNormalizedBrauerBasisPairingResidualAddValInput_of_primePowInput
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
      (coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_forall_of_projectiveCharacter_lattice
        (p := p) (A := A) (K := K) (G := G) hlattice
        π hπ_simple hπ_coord)

end BrauerResidualSourceValuationWorker

section FullMixedBrauerResidualSourceValuationWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerResidualSourceValuationWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerResidualSourceValuationWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model residual provider from the source-side projective-character lattice route,
kept in the explicit `∀ π` form rather than routed through downstream Cartan endpoints. -/
theorem fullMixedModelCoordinateNormalizedBrauerBasisPairingResidualDivisibility_of_projectiveCharacter_lattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
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
          coordinateNormalizedBrauerBasisPairingResidualDivisibility
            (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_forall_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model version of the actual high-order prime-power residual provider from the
source-side projective-character lattice route. -/
theorem fullMixedModelBrauerBasisPairingResidualPrimePowBlocker_of_projectiveCharacter_lattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisPairingResidualPrimePowBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    coordinateNormalizedBrauerBasisPairingResidualPrimePowInput_forall_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model AddVal provider from the same source-side projective-character lattice
route. -/
theorem fullMixedModelCoordinateNormalizedBrauerBasisPairingResidualAddValInput_of_projectiveCharacter_lattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
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
          coordinateNormalizedBrauerBasisPairingResidualAddValInput
            (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    coordinateNormalizedBrauerBasisPairingResidualAddValInput_forall_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)

end FullMixedBrauerResidualSourceValuationWorker

end Representation
