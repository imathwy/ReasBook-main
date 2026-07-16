import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackFromPairing
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerExercise18_4OrthogonalityAPI

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerBasisReadbackFixedFamilyCompletion

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerBasisReadbackFixedFamilyCompletionFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisReadbackFixedFamilyCompletionDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Fixed-family completion of the A-side residual gap.

For one coordinate-normalized complete simple family, it is enough to prove the pointwise
pairing residual only in the nontrivial centralizer-`p`-part columns.  The trivial columns are
filled by `coordinateNormalizedBrauerBasisPairingResidual_pointwise_of_centralizerPPart_eq_one`,
and then the existing A-linear readback bridge adds back the explicit projective-envelope row. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_of_fixedFamilyPointwiseResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hresidual :
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
                (ConjClasses.centralizerPPart p d.1 : A) * a) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord) := by
  exact
    brauerBasisFixedCoordinateReadbackDivisibility_of_pairingResidual
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_nontrivial_centralizerPPart
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord hresidual)

section ProjectiveEnvelopeFormula

variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

/-- Same-family descent from the projective-envelope residual formula to the pure A-side
pointwise residual.  This uses only Exercise `18.4` orthogonality and fraction-field
injectivity; it does not use any final Cartan range, cokernel, or product endpoint. -/
theorem fixedFamilyPointwiseResidual_of_projectiveEnvelopeResidualFormula
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
      ∀ c d : PRegularConjClass G p,
        ∃ a : A,
          (FDRep.modularCharacterOnPRegularConjClass
                (p := p) (G := G) (A := K) (π c)
                (PrimeToPRoot.toFieldLift
                  (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
              regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
            regularRestriction (p := p) (A := A) (K := K) (G := G)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
              algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a))
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

/-- A same-family projective-envelope residual formula closes the fixed-family readback
divisibility after the Exercise `18.4` A-side descent above. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_of_projectiveEnvelopeResidualFormula
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
      ∀ c d : PRegularConjClass G p,
        ∃ a : A,
          (FDRep.modularCharacterOnPRegularConjClass
                (p := p) (G := G) (A := K) (π c)
                (PrimeToPRoot.toFieldLift
                  (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
              regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
            regularRestriction (p := p) (A := A) (K := K) (G := G)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
              algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord) := by
  exact
    brauerBasisFixedCoordinateReadbackDivisibility_of_fixedFamilyPointwiseResidual
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
      (fun c d _hd =>
        fixedFamilyPointwiseResidual_of_projectiveEnvelopeResidualFormula
          (p := p) (A := A) (K := K) (G := G)
          π hπ_simple hπ_coord P hP_envelope hresidual c d)

end ProjectiveEnvelopeFormula

/-!
The remaining non-circular A-side formula, after this file, is the pointwise residual supplied
to `brauerBasisFixedCoordinateReadbackDivisibility_of_fixedFamilyPointwiseResidual`:
for one coordinate-normalized complete family `π`, and only when
`ConjClasses.centralizerPPart p d.1 ≠ 1`, prove

```
∃ a : A,
  bA c d - ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
    - (ConjClasses.centralizerPPart p d.1 : A)
        * (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d)) c)
    =
  (ConjClasses.centralizerPPart p d.1 : A) * a
```

where `bA` is the canonical DVR Brauer basis attached to `π`.  Equivalently, it is enough to
prove the displayed projective-envelope residual formula in the fraction field for the same
family and chosen projective envelopes; Exercise `18.4` orthogonality then descends it to this
pure A-side residual.
-/

end BrauerBasisReadbackFixedFamilyCompletion

end Representation
