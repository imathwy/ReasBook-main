import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackEndpoint
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackFixedFamilyCompletion
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueCongruenceProjectiveCharacter

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveEnvelopeResidualCompletion

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

local instance projectiveEnvelopeResidualCompletionFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveEnvelopeResidualCompletionDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The projective-character lattice representative congruence gives the same-family
projective-envelope residual formula.

This is the fraction-field residual route: the point-mass row is in the projective-character
restriction lattice by hypothesis, the chosen projective-envelope row is visibly in the same
lattice, and their difference is therefore in Serre's regular-value divisibility lattice.
No Cartan range, cokernel, or product endpoint is used. -/
theorem brauerPointMassProjectiveEnvelopeResidualDivisibility_of_projectiveCharacter_lattice
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G)
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    brauerPointMassProjectiveEnvelopeResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P := by
  classical
  intro c d
  let row : PRegularConjClass G p → K :=
    virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        ([π c]₀ : R₀[kA](G)) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)
  let ΦP : A ⊗R[K](G) :=
    projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀
  let residual : PRegularConjClass G p → K :=
    row - regularRestriction (p := p) (A := A) (K := K) (G := G) ΦP
  have hrowMap :
      row ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
    simpa [row, hπ_coord c] using hlattice ([π c]₀ : R₀[kA](G))
  have hΦPMap :
      regularRestriction (p := p) (A := A) (K := K) (G := G) ΦP ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
    refine Submodule.mem_map.2 ?_
    refine ⟨ΦP, ?_, ?_⟩
    · exact
        projectiveCharacterScalarExtension_mem_projectiveCharacterSubmodule
          (A := A) (K := K) (G := G) [P c]ₚ₀
    · rfl
  have hresidualMap :
      residual ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
    simpa [residual] using
      (Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G))).sub_mem
        hrowMap hΦPMap
  have hresidualD :
      residual ∈ regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hresidualMap
  rcases
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G) residual).1 hresidualD d with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa [residual, row, ΦP, virtualModularCharacterOnPRegularConjClass_class] using ha

/-- The regular-value congruence version of the same residual formula, obtained by rewriting it
as the projective-character lattice representative congruence. -/
theorem brauerPointMassProjectiveEnvelopeResidualDivisibility_of_regularValueCongruence
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G)
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    brauerPointMassProjectiveEnvelopeResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P := by
  exact
    brauerPointMassProjectiveEnvelopeResidualDivisibility_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P
      ((projectiveCharacter_latticeIntegerRepresentatives_iff_regularValueCongruence
        (p := p) (A := A) (K := K) (G := G)).2 hregular)

/-- Same-family projective-envelope residual divisibility is already in the exact shape needed
by the fixed-family readback completion API. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_of_projectiveEnvelopeResidualDivisibility
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[kA[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hresidual :
      brauerPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord) := by
  exact
    brauerBasisFixedCoordinateReadbackDivisibility_of_projectiveEnvelopeResidualFormula
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope
      (fun c d => hresidual c d)

/-- Local readback closure from the projective-character lattice residual route.  The only
substantive input is the lattice representative congruence, not any final Cartan endpoint. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_projectiveCharacter_lattice_via_projectiveEnvelopeResidual
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, P, hP_envelope⟩
  have hresidual :
      brauerPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P :=
    brauerPointMassProjectiveEnvelopeResidualDivisibility_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hlattice
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_fixedFamilyReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
      (brauerBasisFixedCoordinateReadbackDivisibility_of_projectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope hresidual)

/-- Local readback closure from an independent regular-value congruence, routed through the
projective-envelope residual formula above. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_regularValueCongruence_via_projectiveEnvelopeResidual
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_projectiveCharacter_lattice_via_projectiveEnvelopeResidual
      (p := p) (A := A) (K := K) (G := G)
      ((projectiveCharacter_latticeIntegerRepresentatives_iff_regularValueCongruence
        (p := p) (A := A) (K := K) (G := G)).2 hregular)

end ProjectiveEnvelopeResidualCompletion

section FullMixedProjectiveEnvelopeResidualCompletion

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedProjectiveEnvelopeResidualCompletionFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedProjectiveEnvelopeResidualCompletionDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model readback closure from the projective-character lattice route, through the
same projective-envelope residual formula. -/
theorem fullMixedModelBrauerBasisReadbackInput_of_projectiveCharacter_lattice_via_projectiveEnvelopeResidual
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_projectiveCharacter_lattice_via_projectiveEnvelopeResidual
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)

end FullMixedProjectiveEnvelopeResidualCompletion

end Representation
