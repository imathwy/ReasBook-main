import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackSourceFaithful
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerPointMassCoordinateProducer

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerPointMassResidualProducer

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

local instance brauerPointMassResidualProducerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerPointMassResidualProducerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The pure `A`-valued residual form of the point-mass row problem, after replacing the
chosen projective-envelope regular-restriction row by Serre's Exercise 18.4 readback formula.
This is the same remaining congruence as the projective-envelope residual blocker, but with the
projective envelope and fraction-field row removed. -/
def brauerPointMassBasisResidualDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (_hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G)
            ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) _hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  ∀ c d : PRegularConjClass G p,
    ∃ a : A,
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        (ConjClasses.centralizerPPart p d.1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d)) c) =
          (ConjClasses.centralizerPPart p d.1 : A) * a

/-- Pointwise comparison between the projective-envelope residual row and the pure `A`-basis
residual.  The only input is Exercise 18.4 readback plus the projective-envelope orthogonality
formula already proved upstream. -/
theorem brauerPointMassProjectiveEnvelopeResidual_field_eq_basisResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G)
            ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (c d : PRegularConjClass G p) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    (FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
      algebraMap A K
        (bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
          (ConjClasses.centralizerPPart p d.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G)
                (inversePRegularConjClass (p := p) d)) c)) := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  have hchar :
      FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d =
        algebraMap A K (bA c d) := by
    have hbasis :=
      congrFun
        (canonicalDVRBrauerBasis_algebraMap_apply_eq_virtualModularCharacter
          (p := p) (A := A) (K := K) (G := G)
          π hπ_pairwise hπ_complete c) d
    have hclass :=
      congrFun
        (virtualModularCharacterOnPRegularConjClass_class
          (p := p)
          (lift := PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          (E := π c)) d
    exact hclass.symm.trans hbasis.symm
  have hproj :
      regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
        algebraMap A K
          ((ConjClasses.centralizerPPart p d.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G)
                (inversePRegularConjClass (p := p) d)) c)) := by
    simpa [bA, canonicalDVRBrauerBasis] using
      (coordinate_normalized_projective_envelope_regularRestriction_value
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c d)
  calc
    (FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d
        =
          algebraMap A K (bA c d) -
            algebraMap A K
              (((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) -
          algebraMap A K
            ((ConjClasses.centralizerPPart p d.1 : A) *
              (bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G)
                  (inversePRegularConjClass (p := p) d)) c)) := by
            rw [hchar, hproj]
            simp [regularIntegerFunctionCast]
    _ =
      algebraMap A K
        (bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
          (ConjClasses.centralizerPPart p d.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G)
                (inversePRegularConjClass (p := p) d)) c)) := by
            simp [map_sub, map_mul]

/-- The pure basis residual congruence implies the projective-envelope residual blocker for any
chosen coordinate-normalized projective envelopes. -/
theorem brauerPointMassProjectiveEnvelopeResidualDivisibility_of_basisResidualDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G)
            ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (hbasis :
      brauerPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    brauerPointMassProjectiveEnvelopeResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P := by
  intro c d
  rcases hbasis c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  rw [brauerPointMassProjectiveEnvelopeResidual_field_eq_basisResidual
    (p := p) (A := A) (K := K) (G := G)
    π hπ_simple hπ_coord P hP_envelope c d, ha]

/-- Conversely, any projective-envelope residual proof yields the pure `A`-basis residual
congruence. -/
theorem brauerPointMassBasisResidualDivisibility_of_projectiveEnvelopeResidualDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G)
            ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (hresidual :
      brauerPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    brauerPointMassBasisResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d
  rcases hresidual c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply IsFractionRing.injective A K
  calc
    algebraMap A K
        ((let hπ_pairwise :=
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
                  (inversePRegularConjClass (p := p) d)) c))) =
      (FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := K) (π c)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
          regularRestriction (p := p) (A := A) (K := K) (G := G)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d := by
          rw [brauerPointMassProjectiveEnvelopeResidual_field_eq_basisResidual
            (p := p) (A := A) (K := K) (G := G)
            π hπ_simple hπ_coord P hP_envelope c d]
    _ = algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := ha

/-- The projective-envelope residual and the pure `A`-basis residual are the same local input.
-/
theorem brauerPointMassProjectiveEnvelopeResidualDivisibility_iff_basisResidualDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G)
            ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope) :
    brauerPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P ↔
      brauerPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  constructor
  · exact
      brauerPointMassBasisResidualDivisibility_of_projectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope
  · exact
      brauerPointMassProjectiveEnvelopeResidualDivisibility_of_basisResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope

/-- Existential pure basis-residual version of the Brauer point-mass residual blocker. -/
def regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility :
    Prop :=
  ∃ π : PRegularConjClass G p → FDRep k G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G)
              ([π c]₀ : R₀[k](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        brauerPointMassBasisResidualDivisibility
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- The pure basis-residual existence statement produces the projective-envelope residual
existence statement by choosing projective envelopes for the same simple family. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_basisResidualDivisibility
    (hbasis :
      regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hbasis with ⟨π, hπ_simple, hπ_coord, hbasis⟩
  have hP_exists :
      ∀ c : PRegularConjClass G p,
        ∃ P : FiniteProjectiveGroupAlgebraModule k G,
          ∃ f : P.V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope := by
    intro c
    letI : Simple (π c) := hπ_simple c
    exact exists_finite_projectiveEnvelope_of_simple_field (G := G) (τ := π c)
  choose P hP_envelope using hP_exists
  refine ⟨π, hπ_simple, hπ_coord, P, hP_envelope, ?_⟩
  exact
    brauerPointMassProjectiveEnvelopeResidualDivisibility_of_basisResidualDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hbasis

/-- The existential projective-envelope residual statement is equivalent to the pure
`A`-basis residual statement. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_basisResidualDivisibility :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G) := by
  constructor
  · rintro ⟨π, hπ_simple, hπ_coord, P, hP_envelope, hresidual⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    exact
      brauerPointMassBasisResidualDivisibility_of_projectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope hresidual
  · exact
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_basisResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)

end BrauerPointMassResidualProducer

section FullMixedModelBrauerPointMassResidualProducer

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelBrauerPointMassResidualProducerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelBrauerPointMassResidualProducerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-model form of the pure `A`-valued basis-residual blocker. -/
def fullMixedModelPointMassBasisResidualDivisibilityBlocker : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed projective-envelope residual blocker is equivalent to the pure basis-residual
blocker. -/
theorem fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_iff_basisResidualDivisibilityBlocker :
    fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassBasisResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hblock A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_basisResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)).1
        (hblock (A := A) (K := K) e0)
  · intro hblock A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_basisResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)).2
        (hblock (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- A direct producer from the smaller pure basis-residual blocker to the A3 target. -/
theorem fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_of_basisResidualDivisibilityBlocker
    (hbasis : fullMixedModelPointMassBasisResidualDivisibilityBlocker
      (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_basisResidualDivisibility
      (p := p) (A := A) (K := K) (G := G)
      (hbasis (A := A) (K := K) e0)

end FullMixedModelBrauerPointMassResidualProducer

end Representation
