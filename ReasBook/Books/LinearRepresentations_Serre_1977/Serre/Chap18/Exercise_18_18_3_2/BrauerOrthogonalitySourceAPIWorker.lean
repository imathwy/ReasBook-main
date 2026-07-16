import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerExercise18_4OrthogonalityAPI
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisResidualDirectProof

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerOrthogonalitySourceAPIWorkerASide

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerOrthogonalitySourceAPIWorkerASideFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerOrthogonalitySourceAPIWorkerASideDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Source-side Exercise `18.4` expansion of the inverse prime-to-`p` point mass, with the
target centralizer `p`-part already multiplied in. -/
theorem canonicalDVRBrauerBasis_inversePrimeToPIndicator_centralizerPPart_sum_apply
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
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
    ∑ i : PRegularConjClass G p,
        bA i c *
          ((ConjClasses.centralizerPPart p d.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) i)) =
      (ConjClasses.centralizerPPart p d.1 : A) *
        (primeToP_regular_indicator
          (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c := by
  classical
  let invd := inversePRegularConjClass (p := p) d
  simpa [invd, inversePRegularConjClass_val, ConjClasses.centralizerPPart_inv] using
    (coordinateNormalizedBrauerBasis_primeToPIndicator_centralizerPPart_sum
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord c invd)

/-- In inverse coordinates, the previous source expansion is exactly the full centralizer
point mass.  This is the raw `18.4` matrix identity before any Cartan range or cokernel input. -/
theorem canonicalDVRBrauerBasis_inversePointMass_centralizerPPart_sum_eq
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
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
    ∑ i : PRegularConjClass G p,
        bA i (inversePRegularConjClass (p := p) c) *
          ((ConjClasses.centralizerPPart p d.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) i)) =
      if c = d then (ConjClasses.centralizerCard d.1 : A) else 0 := by
  classical
  simpa using
    (coordinateNormalizedBrauerBasis_inverse_pointMass_matrix_identity
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d)

end BrauerOrthogonalitySourceAPIWorkerASide

section BrauerOrthogonalitySourceAPIWorkerFieldSide

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

local instance brauerOrthogonalitySourceAPIWorkerFieldSideFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerOrthogonalitySourceAPIWorkerFieldSideDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Coefficient readback form of Serre's orthogonality computation: after embedding in the
fraction field, the Exercise `18.4` coefficient of the inverse prime-to-`p` indicator is the
projective-envelope regular value divided by the centralizer `p`-part. -/
theorem canonicalDVRBrauerBasis_inversePrimeToPIndicator_repr_algebraMap_eq_inv_mul_projectiveEnvelope
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
    algebraMap A K
        ((bA.repr
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d))) c) =
      (algebraMap A K (ConjClasses.centralizerPPart p d.1 : A))⁻¹ *
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d := by
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
  let z : A := ConjClasses.centralizerPPart p d.1
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d))) c
  change
    algebraMap A K coeff =
      (algebraMap A K z)⁻¹ *
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d
  have hvalue :
      regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
        algebraMap A K (z * coeff) := by
    simpa [bA, z, coeff] using
      (canonicalDVRBrauerBasis_projectiveEnvelope_regularRestriction_value
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c d)
  have hz : algebraMap A K z ≠ 0 := by
    simpa [z] using
      algebraMap_centralizerPPart_ne_zero
        (p := p) (A := A) (K := K) (G := G) d
  symm
  calc
    (algebraMap A K z)⁻¹ *
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d
        =
          (algebraMap A K z)⁻¹ * algebraMap A K (z * coeff) := by
            rw [hvalue]
    _ = (algebraMap A K z)⁻¹ * (algebraMap A K z * algebraMap A K coeff) := by
          rw [map_mul]
    _ = algebraMap A K coeff := by
          rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]

/-- If the pure `A`-side residual has a centralizer-`p`-part factor, then the corresponding
projective-envelope field residual is the fraction-field image of that same factorization. -/
theorem canonicalDVRBrauerBasis_projectiveEnvelope_residual_eq_algebraMap_of_residual_eq
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
    (c d : PRegularConjClass G p) (a : A)
    (hA :
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
              (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c) =
          (ConjClasses.centralizerPPart p d.1 : A) * a) :
    (FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
      regularRestriction (p := p) (A := A) (K := K) (G := G)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
        algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := by
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
  let z : A := ConjClasses.centralizerPPart p d.1
  let residualA : A :=
    bA c d -
        ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
      z *
        (bA.repr
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c)
  let residualK : K :=
    (FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
      regularRestriction (p := p) (A := A) (K := K) (G := G)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d
  change residualK = algebraMap A K (z * a)
  have hresidual :
      residualK = algebraMap A K residualA := by
    simpa [residualK, residualA, bA, z] using
      (canonicalDVRBrauerBasis_projectiveEnvelope_residual_algebraMap_eq
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c d)
  have hA' : residualA = z * a := by
    simpa [residualA, bA, z] using hA
  rw [hresidual, hA']

/-- Bidirectional residual bridge: the projective-envelope residual is a fraction-field image of
a centralizer-`p`-part multiple exactly when the corresponding canonical `A`-basis residual is
that multiple. -/
theorem canonicalDVRBrauerBasis_projectiveEnvelope_residual_eq_algebraMap_iff
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
    (c d : PRegularConjClass G p) (a : A) :
    ((FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
      regularRestriction (p := p) (A := A) (K := K) (G := G)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
        algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)) ↔
      (let hπ_pairwise :=
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
              (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c) =
          (ConjClasses.centralizerPPart p d.1 : A) * a) := by
  constructor
  · intro hK
    exact
      canonicalDVRBrauerBasis_residual_eq_of_projectiveEnvelope_residual_eq_algebraMap
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c d a hK
  · intro hA
    exact
      canonicalDVRBrauerBasis_projectiveEnvelope_residual_eq_algebraMap_of_residual_eq
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c d a hA

end BrauerOrthogonalitySourceAPIWorkerFieldSide

end Representation
