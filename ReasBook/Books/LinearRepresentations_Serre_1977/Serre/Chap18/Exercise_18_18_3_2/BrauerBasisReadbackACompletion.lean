import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackResidualProof
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerExercise18_4OrthogonalityAPI

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerBasisReadbackACompletion

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerBasisReadbackACompletionFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisReadbackACompletionDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Named form of the remaining A-side pointwise residual, restricted to the genuinely
nontrivial centralizer-`p`-part columns.  The columns with centralizer `p`-part equal to `1`
are already discharged by
`coordinateNormalizedBrauerBasisPairingResidual_pointwise_of_centralizerPPart_eq_one`. -/
def coordinateNormalizedBrauerBasisNontrivialPointwiseResidual
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
      ∃ a : A,
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
          (ConjClasses.centralizerPPart p d.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G)
                (inversePRegularConjClass (p := p) d)) c) =
            (ConjClasses.centralizerPPart p d.1 : A) * a

/-- The named nontrivial pointwise residual is exactly the nontrivial-coordinate form of the
pairing residual already isolated by the A-side API. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_nontrivialPointwiseResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerBasisNontrivialPointwiseResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  simpa [coordinateNormalizedBrauerBasisNontrivialPointwiseResidual] using
    (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_nontrivial_centralizerPPart
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord)

/-- The fixed-coordinate readback blocker is equivalent to the named nontrivial A-side
pointwise residual.  This is only the previously proved A-linear arithmetic bridge; it does not
use any Cartan range, cokernel, product endpoint, or final readback theorem. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_iff_nontrivialPointwiseResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G)
        π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord) ↔
      coordinateNormalizedBrauerBasisNontrivialPointwiseResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  constructor
  · intro hread
    exact
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_nontrivialPointwiseResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
        ((coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_fixedCoordinateReadback
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hread)
  · intro hpoint
    exact
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
        ((coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_nontrivialPointwiseResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hpoint)

/-- Forward direction used by worker tasks: proving only the nontrivial pointwise residual closes
the fixed-coordinate readback input; the trivial centralizer columns are filled internally by the
existing pointwise `centralizerPPart = 1` lemma. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_of_nontrivialPointwiseResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hpoint :
      coordinateNormalizedBrauerBasisNontrivialPointwiseResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord) :=
  (brauerBasisFixedCoordinateReadbackDivisibility_iff_nontrivialPointwiseResidual
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hpoint

section ProjectiveEnvelopeNontrivialResidual

variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

/-- Fraction-field form of the same nontrivial residual, before descending through Exercise
`18.4` and fraction-field injectivity.  This is the source-faithful target compatible with
Serre's orthogonality computation, but still restricted to the nontrivial centralizer columns. -/
def coordinateNormalizedProjectiveEnvelopeNontrivialResidual
    (π : PRegularConjClass G p → FDRep k G)
    (_hπ_simple : ∀ c, Simple (π c))
    (_hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G) : Prop :=
  ∀ c d : PRegularConjClass G p,
    ConjClasses.centralizerPPart p d.1 ≠ 1 →
      ∃ a : A,
        (FDRep.modularCharacterOnPRegularConjClass
              (p := p) (G := G) (A := K) (π c)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
          regularRestriction (p := p) (A := A) (K := K) (G := G)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
            algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)

/-- Nontrivial-column descent from the fraction-field projective-envelope residual to the pure
A-side pointwise residual.  The only mathematical input is the Exercise `18.4` orthogonality
formula already packaged in
`canonicalDVRBrauerBasis_residual_eq_of_projectiveEnvelope_residual_eq_algebraMap`. -/
theorem nontrivialPointwiseResidual_of_projectiveEnvelopeResidual
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
      coordinateNormalizedProjectiveEnvelopeNontrivialResidual
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    coordinateNormalizedBrauerBasisNontrivialPointwiseResidual
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d hd
  rcases hresidual c d hd with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  exact
    canonicalDVRBrauerBasis_residual_eq_of_projectiveEnvelope_residual_eq_algebraMap
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope c d a ha

/-- A nontrivial-column projective-envelope residual formula closes the fixed-family
fixed-coordinate readback congruence, without using any final Cartan range/cokernel/product
endpoint. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_of_projectiveEnvelopeNontrivialResidual
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
      coordinateNormalizedProjectiveEnvelopeNontrivialResidual
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord) :=
  brauerBasisFixedCoordinateReadbackDivisibility_of_nontrivialPointwiseResidual
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord
    (nontrivialPointwiseResidual_of_projectiveEnvelopeResidual
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hresidual)

end ProjectiveEnvelopeNontrivialResidual

end BrauerBasisReadbackACompletion

end Representation
