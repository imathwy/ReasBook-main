import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackSourceFaithful
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveEnvelopePairing

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerExercise18_4OrthogonalityAPI

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

local instance brauerExercise18_4OrthogonalityAPIFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerExercise18_4OrthogonalityAPIDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Exercise `18.4` plus projective-envelope orthogonality, in the canonical DVR Brauer-basis
API: the value of a coordinate-normalized projective-envelope regular row is the centralizer
`p`-part times the dual-basis coefficient of the inverse prime-to-`p` indicator. -/
theorem canonicalDVRBrauerBasis_projectiveEnvelope_regularRestriction_value
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
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
    let bA := canonicalDVRBrauerBasis (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    regularRestriction (p := p) (A := A) (K := K) (G := G)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
      algebraMap A K
        ((ConjClasses.centralizerPPart p d.1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c)) := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  have hsrc :=
    projectiveEnvelope_regularRestriction_value_eq_centralizerPPart_mul_repr_inv
      (p := p) (A := A) (K := K) (G := G) (hω := hω)
      (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
      (P := P) (hP_envelope := hP_envelope) c (inversePRegularConjClass (p := p) d)
  change
    regularRestriction (p := p) (A := A) (K := K) (G := G)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀)
        (inversePRegularConjClass (p := p) (inversePRegularConjClass (p := p) d)) =
      algebraMap A K
        ((ConjClasses.centralizerPPart p (inversePRegularConjClass (p := p) d).1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c)) at hsrc
  rw [inversePRegularConjClass_involutive] at hsrc
  rw [inversePRegularConjClass_val, ConjClasses.centralizerPPart_inv] at hsrc
  exact hsrc

/-- Pointwise residual readback formula for the A-side basis residual.  The field residual
obtained by subtracting the fixed coordinate row and the projective-envelope row is exactly the
fraction-field image of the corresponding Exercise `18.4` basis residual. -/
theorem canonicalDVRBrauerBasis_projectiveEnvelope_residual_algebraMap_eq
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
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
    let bA := canonicalDVRBrauerBasis (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
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
                  (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c)) := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  have hchar :
      FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d =
        algebraMap A K (bA c d) := by
    have hbasis :=
      congrFun
        (canonicalDVRBrauerBasis_algebraMap_apply_eq_virtualModularCharacter
          (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete c) d
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
                (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c)) :=
    canonicalDVRBrauerBasis_projectiveEnvelope_regularRestriction_value
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P hP_envelope c d
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
            algebraMap A K (((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) -
            algebraMap A K
              ((ConjClasses.centralizerPPart p d.1 : A) *
                (bA.repr
                  (primeToP_regular_indicator
                    (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c)) := by
          rw [hchar, hproj]
          simp [regularIntegerFunctionCast]
    _ =
        algebraMap A K
          (bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
            (ConjClasses.centralizerPPart p d.1 : A) *
              (bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c)) := by
          simp [map_sub, map_mul]

/-- Descent form of the residual formula: any pointwise fraction-field divisibility witness for
the projective-envelope residual gives the same A-side residual witness. -/
theorem canonicalDVRBrauerBasis_residual_eq_of_projectiveEnvelope_residual_eq_algebraMap
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (c d : PRegularConjClass G p) (a : A)
    (hres :
      (FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := K) (π c)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
          algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA := canonicalDVRBrauerBasis (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    bA c d -
        ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        (ConjClasses.centralizerPPart p d.1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c) =
      (ConjClasses.centralizerPPart p d.1 : A) * a := by
  classical
  apply IsFractionRing.injective A K
  rw [← hres]
  symm
  exact
    canonicalDVRBrauerBasis_projectiveEnvelope_residual_algebraMap_eq
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P hP_envelope c d

end BrauerExercise18_4OrthogonalityAPI

end Representation
