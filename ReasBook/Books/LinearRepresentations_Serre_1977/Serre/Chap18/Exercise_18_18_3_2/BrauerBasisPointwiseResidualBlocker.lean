import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisResidualDirectProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerExercise18_4OrthogonalityAPI
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerReadbackFinalIntegration
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassCoordinateProducer

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerBasisPointwiseResidualBlocker

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

local instance brauerBasisPointwiseResidualBlockerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisPointwiseResidualBlockerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Same-family descent from the fraction-field projective-envelope residual to the pure
`A`-valued Exercise `18.4` Brauer-basis residual.

The only non-formal step is
`canonicalDVRBrauerBasis_residual_eq_of_projectiveEnvelope_residual_eq_algebraMap`, which
combines the Exercise `18.4` Brauer-basis expansion with projective-envelope orthogonality and
then uses fraction-field injectivity. -/
theorem coordinateNormalizedBrauerBasis_pointwiseResidual_of_projectiveEnvelopeResidual
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
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P)
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
    ∃ a : A,
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        (ConjClasses.centralizerPPart p d.1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d)) c) =
          (ConjClasses.centralizerPPart p d.1 : A) * a := by
  rcases hresidual c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  exact
    canonicalDVRBrauerBasis_residual_eq_of_projectiveEnvelope_residual_eq_algebraMap
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope c d a ha

omit [IsFractionRing A K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Projective-envelope residuals transfer between any two coordinate-normalized simple
families indexed by `PRegularConjClass G p`.

The modular rows agree because the coordinate-normalized Grothendieck classes agree indexwise;
the projective-envelope rows agree because projective envelopes of the same simple class have
the same projective Grothendieck class. -/
theorem brauerPointMassProjectiveEnvelopeResidualDivisibility_of_coordinateNormalized_family
    (π₀ π : PRegularConjClass G p → FDRep k G)
    (hπ₀_simple : ∀ c, Simple (π₀ c))
    (hπ_simple : ∀ c, Simple (π c))
    (hπ₀_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π₀ c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P₀ P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP₀_envelope :
      ∀ c, ∃ f : (P₀ c).V →ₗ[k[G]] asModule (π₀ c).ρ, f.IsProjectiveEnvelope)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hresidual₀ :
      brauerPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π₀ hπ₀_simple hπ₀_coord P₀) :
    brauerPointMassProjectiveEnvelopeResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P := by
  intro c d
  rcases hresidual₀ c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hπ_class :
      ∀ c : PRegularConjClass G p, ([π₀ c]₀ : R₀[k](G)) = [π c]₀ :=
    finiteRepClass_eq_of_coordinate_normalized_families
      (p := p) π₀ π hπ₀_coord hπ_coord
  have hP_class :
      ∀ c : PRegularConjClass G p, ([P₀ c]ₚ₀ : P₀[k](G)) = [P c]ₚ₀ :=
    finiteProjectiveClass_eq_of_projectiveEnvelope_simple_class_eq
      π₀ π hπ₀_simple hπ_simple P₀ P hP₀_envelope hP_envelope hπ_class
  have hmod :
      FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π₀ c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d =
        FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d := by
    have hclass₀ :=
      congrFun
        (virtualModularCharacterOnPRegularConjClass_class
          (p := p)
          (lift := PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          (E := π₀ c)) d
    have hclass :=
      congrFun
        (virtualModularCharacterOnPRegularConjClass_class
          (p := p)
          (lift := PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          (E := π c)) d
    rw [← hclass₀, hπ_class c, hclass]
  have hproj :
      regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P₀ c]ₚ₀) d =
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d := by
    rw [hP_class c]
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
      (FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π₀ c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P₀ c]ₚ₀) d := by
          rw [hmod, hproj]
    _ = algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := ha

/-- An existential projective-envelope residual blocker for one coordinate-normalized family
gives the universal pointwise Brauer-basis residual proof used by the Faraday integration file.

This step is non-circular: it transfers the projective-envelope residual to an arbitrary
coordinate-normalized family, then descends it through the Exercise `18.4` orthogonality API. -/
theorem regularValueCongruenceSourceFaithfulPointwiseResidualProof_of_projectiveEnvelopeResidual
    (hresidual :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulPointwiseResidualProof
      (p := p) (A := A) (G := G) := by
  rcases hresidual with ⟨π₀, hπ₀_simple, hπ₀_coord, P₀, hP₀_envelope, hresidual₀⟩
  intro π hπ_simple hπ_coord c d _hd
  have hP_exists :
      ∀ c : PRegularConjClass G p,
        ∃ P : FiniteProjectiveGroupAlgebraModule k G,
          ∃ f : P.V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope := by
    intro c
    letI : Simple (π c) := hπ_simple c
    exact exists_finite_projectiveEnvelope_of_simple_field (G := G) (τ := π c)
  choose P hP_envelope using hP_exists
  have hresidual :
      brauerPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P :=
    brauerPointMassProjectiveEnvelopeResidualDivisibility_of_coordinateNormalized_family
      (p := p) (A := A) (K := K) (G := G)
      π₀ π hπ₀_simple hπ_simple hπ₀_coord hπ_coord
      P₀ P hP₀_envelope hP_envelope hresidual₀
  exact
    coordinateNormalizedBrauerBasis_pointwiseResidual_of_projectiveEnvelopeResidual
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hresidual c d

end BrauerBasisPointwiseResidualBlocker

section FullMixedModelBrauerBasisPointwiseResidualBlocker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelBrauerBasisPointwiseResidualBlockerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelBrauerBasisPointwiseResidualBlockerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model projective-envelope residuals give the Faraday pointwise Brauer-basis
residual blocker. -/
theorem fullMixedModelBrauerBasisPointwiseResidualBlocker_of_projectiveEnvelopeResidual
    (hresidual :
      fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisPointwiseResidualBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulPointwiseResidualProof_of_projectiveEnvelopeResidual
      (p := p) (A := A) (K := K) (G := G)
      (hresidual (A := A) (K := K) e0)

end FullMixedModelBrauerBasisPointwiseResidualBlocker

end Representation
