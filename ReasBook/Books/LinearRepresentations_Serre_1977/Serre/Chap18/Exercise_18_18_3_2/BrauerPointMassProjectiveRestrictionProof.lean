import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassProjectiveRestrictionEquiv
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassCoordinateProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassBasisResidualEndpoint
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisPairingResidualProof

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerPointMassProjectiveRestrictionProof

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

local instance brauerPointMassProjectiveRestrictionProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerPointMassProjectiveRestrictionProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- A projective-envelope residual proof directly gives the regular-value point-mass row
divisibility witness.

This is the value-side source route: the residual row is in the divisibility lattice by
hypothesis, while the visible projective-envelope row is in the same lattice by Exercise `18.4`
plus projective-envelope orthogonality. -/
theorem brauerPointMassRegularValueWitness_of_projectiveEnvelopeResidualDivisibility
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
    brauerPointMassRegularValueDivisibilityWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  classical
  intro c
  let row : PRegularConjClass G p → K :=
    virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        ([π c]₀ : R₀[k](G)) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)
  let ΦP : A ⊗R[K](G) :=
    projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀
  let residual : PRegularConjClass G p → K :=
    row - regularRestriction (p := p) (A := A) (K := K) (G := G) ΦP
  have hresidualD :
      residual ∈ regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    refine
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G) residual).2 ?_
    intro d
    rcases hresidual c d with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simpa [residual, row, ΦP, virtualModularCharacterOnPRegularConjClass_class] using ha
  have hΦPD :
      regularRestriction (p := p) (A := A) (K := K) (G := G) ΦP ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    refine
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G)
        (regularRestriction (p := p) (A := A) (K := K) (G := G) ΦP)).2 ?_
    intro d
    rcases
        coordinate_normalized_projective_envelope_regularRestriction_coordinateDivisibility
          (p := p) (A := A) (K := K) (G := G)
          π hπ_simple hπ_coord P hP_envelope c d with
      ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simpa [ΦP] using ha
  have hsum :
      residual + regularRestriction (p := p) (A := A) (K := K) (G := G) ΦP ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)).add_mem
      hresidualD hΦPD
  have hrow :
      row =
        residual + regularRestriction (p := p) (A := A) (K := K) (G := G) ΦP := by
    ext d
    simp [residual, row]
  change row ∈ regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  rw [hrow]
  exact hsum

/-- A projective-envelope residual proof directly constructs the point-mass
projective-restriction witness.

This is the source-route bridge: the residual row is sent into the projective-character
restriction lattice by Serre `18.5(a)`, and the visible projective-envelope row is then added
back.  It does not pass through the point-mass coordinate-divisibility equivalence. -/
theorem brauerPointMassProjectiveRestrictionWitness_of_projectiveEnvelopeResidualDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hresidual :
      brauerPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    brauerPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  classical
  intro c
  let row : PRegularConjClass G p → K :=
    virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        ([π c]₀ : R₀[k](G)) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)
  let ΦP : A ⊗R[K](G) :=
    projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀
  let residual : PRegularConjClass G p → K :=
    row - regularRestriction (p := p) (A := A) (K := K) (G := G) ΦP
  have hresidualD :
      residual ∈ regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    refine
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G) residual).2 ?_
    intro d
    rcases hresidual c d with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simpa [residual, row, ΦP, virtualModularCharacterOnPRegularConjClass_class] using ha
  have hresidualMap :
      residual ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
    simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hresidualD
  rcases Submodule.mem_map.1 hresidualMap with ⟨Ψ, hΨ, hΨres⟩
  refine ⟨Ψ + ΦP, ?_, ?_⟩
  · exact
      (projectiveCharacterSubmodule (A := A) (K := K) (G := G)).add_mem hΨ
        (projectiveCharacterScalarExtension_mem_projectiveCharacterSubmodule
          (A := A) (K := K) (G := G) [P c]ₚ₀)
  · calc
      regularRestriction (p := p) (A := A) (K := K) (G := G) (Ψ + ΦP)
          =
            regularRestriction (p := p) (A := A) (K := K) (G := G) Ψ +
              regularRestriction (p := p) (A := A) (K := K) (G := G) ΦP := by
              simpa [regularRestrictionLinearMap] using
                (regularRestrictionLinearMap
                  (p := p) (A := A) (K := K) (G := G)).map_add Ψ ΦP
      _ = residual + regularRestriction (p := p) (A := A) (K := K) (G := G) ΦP := by
            rw [show
              regularRestriction (p := p) (A := A) (K := K) (G := G) Ψ = residual by
                simpa [regularRestrictionLinearMap] using hΨres]
      _ = row := by
            ext d
            simp [residual, row]

/-- A pure `A`-valued basis residual proof directly constructs the fixed-family point-mass
projective-restriction witness, after choosing projective envelopes for the normalized simple
family. -/
theorem brauerPointMassProjectiveRestrictionWitness_of_basisResidualDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hbasis :
      brauerPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    brauerPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  classical
  have hP_exists :
      ∀ c : PRegularConjClass G p,
        ∃ P : FiniteProjectiveGroupAlgebraModule k G,
          ∃ f : P.V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope := by
    intro c
    letI : Simple (π c) := hπ_simple c
    exact exists_finite_projectiveEnvelope_of_simple_field (G := G) (τ := π c)
  choose P hP_envelope using hP_exists
  exact
    brauerPointMassProjectiveRestrictionWitness_of_projectiveEnvelopeResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P
      (brauerPointMassProjectiveEnvelopeResidualDivisibility_of_basisResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope hbasis)

/-- Existential projective-envelope residual input directly produces the point-mass
projective-restriction witness. -/
theorem
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_projectiveEnvelopeResidualDivisibility
    (hresidual :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hresidual with ⟨π, hπ_simple, hπ_coord, P, _hP_envelope, hresidual⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerPointMassProjectiveRestrictionWitness_of_projectiveEnvelopeResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P hresidual

/-- Existential projective-envelope residual input directly produces the regular-value
point-mass witness. -/
theorem
    regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness_of_projectiveEnvelopeResidualDivisibility
    (hresidual :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hresidual with ⟨π, hπ_simple, hπ_coord, P, hP_envelope, hresidual⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerPointMassRegularValueWitness_of_projectiveEnvelopeResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P hP_envelope hresidual

/-- The pure Exercise `18.4` basis-residual input directly produces the point-mass
projective-restriction witness. -/
theorem
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_basisResidualDivisibility
    (hbasis :
      regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) := by
  exact
    let ⟨π, hπ_simple, hπ_coord, hbasis⟩ := hbasis
    ⟨π, hπ_simple, hπ_coord,
      brauerPointMassProjectiveRestrictionWitness_of_basisResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hbasis⟩

/-- Existential pointwise residual input for the projective-restriction route, with the
trivial centralizer-`p`-part columns removed.

This is the smallest A-side residual form needed here: the omitted `centralizerPPart = 1`
columns are supplied by the pointwise residual lemma from Exercise `18.4`; the remaining
nontrivial columns are exactly the fixed-coordinate residual left after subtracting the visible
projective-envelope row. -/
def regularValueCongruenceSourceFaithfulExistsPointMassNontrivialResidualDivisibility : Prop :=
  ∃ π : PRegularConjClass G p → FDRep k G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G)
              ([π c]₀ : R₀[k](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
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
                  (ConjClasses.centralizerPPart p d.1 : A) * a

/-- The nontrivial-column residual input fills the full pure A-side basis residual. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility_of_nontrivialResidualDivisibility
    (hresidual :
      regularValueCongruenceSourceFaithfulExistsPointMassNontrivialResidualDivisibility
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
      (p := p) (A := A) (G := G) := by
  rcases hresidual with ⟨π, hπ_simple, hπ_coord, hresidual⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerPointMassBasisResidualDivisibility_of_coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_nontrivial_centralizerPPart
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord hresidual)

/-- Nontrivial A-side residuals produce the projective-restriction witness by the same forward
Serre `18.5(a)` route as the full basis residual. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_nontrivialResidualDivisibility
    (hresidual :
      regularValueCongruenceSourceFaithfulExistsPointMassNontrivialResidualDivisibility
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) :=
  regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_basisResidualDivisibility
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility_of_nontrivialResidualDivisibility
      (p := p) (A := A) (G := G) hresidual)

/-- The pure Exercise `18.4` basis-residual input directly produces the regular-value
point-mass witness. -/
theorem
    regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness_of_basisResidualDivisibility
    (hbasis :
      regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness
      (p := p) (A := A) (K := K) (G := G) :=
  regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness_of_projectiveEnvelopeResidualDivisibility
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_of_basisResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) hbasis)

/-- The canonical DVR Brauer-basis readback input produces the point-mass
projective-restriction witness through the non-coordinate residual route. -/
theorem
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_brauerBasisReadbackInput
    (hread : regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) := by
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_basisResidualDivisibility
      (p := p) (A := A) (K := K) (G := G)
      (existsPointMassBasisResidualDivisibility_of_brauerBasisReadbackInput
        (p := p) (A := A) (G := G) hread)

end BrauerPointMassProjectiveRestrictionProof

section FullMixedModelBrauerPointMassProjectiveRestrictionProof

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelBrauerPointMassProjectiveRestrictionProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelBrauerPointMassProjectiveRestrictionProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model residual input directly produces the full mixed-model point-mass
projective-restriction witness blocker. -/
theorem
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_of_projectiveEnvelopeResidualDivisibilityBlocker
    (hresidual :
      fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_projectiveEnvelopeResidualDivisibility
      (p := p) (A := A) (K := K) (G := G)
      (hresidual (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model basis-residual input directly produces the full mixed-model point-mass
projective-restriction witness blocker. -/
theorem
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_of_basisResidualDivisibilityBlocker
    (hbasis :
      fullMixedModelPointMassBasisResidualDivisibilityBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_basisResidualDivisibility
      (p := p) (A := A) (K := K) (G := G)
      (hbasis (A := A) (K := K) e0)

/-- Full mixed-characteristic nontrivial-column residual blocker for the
projective-restriction route. -/
def fullMixedModelPointMassNontrivialResidualDivisibilityBlocker : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulExistsPointMassNontrivialResidualDivisibility
        (p := p) (A := A) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model nontrivial A-side residuals close the projective-restriction witness
blocker. -/
theorem fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_of_nontrivialResidualDivisibilityBlocker
    (hresidual :
      fullMixedModelPointMassNontrivialResidualDivisibilityBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_nontrivialResidualDivisibility
      (p := p) (A := A) (K := K) (G := G)
      (hresidual (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model Brauer-basis readback input directly produces the full mixed-model
point-mass projective-restriction witness blocker. -/
theorem
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker_of_brauerBasisReadbackInput
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassProjectiveRestrictionWitnessBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G)
      (hread (A := A) (K := K) e0)

end FullMixedModelBrauerPointMassProjectiveRestrictionProof

end Representation
