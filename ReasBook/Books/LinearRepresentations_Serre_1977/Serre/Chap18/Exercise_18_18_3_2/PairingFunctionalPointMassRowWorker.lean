import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerCoordinateReadback
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ExplicitResidualPairingSumWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveEnvelopePairing
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointMassRowsSourceClosureWorker

/-!
Pairing-functional route for the point-mass row source.

The projective-envelope pairing formula identifies the `d`-th Brauer-basis coordinate
functional with pairing against the `d`-th projective envelope.  For a coordinate-normalized
Brauer basis row `bA c`, this functional evaluates to `delta c d`.

What is not supplied by the pairing formula alone is the remaining congruence between ordinary
evaluation at `d` and this functional, modulo `centralizerPPart(d)`.  This file isolates that
as the minimal pairing-functional source input and proves that it closes the existing
point-mass row target.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section PairingFunctionalPointMassRowWorker

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

local instance pairingFunctionalPointMassRowWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pairingFunctionalPointMassRowWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The missing pairing-functional readout: evaluation of the `c`-th canonical Brauer row at
`d`, minus the `d`-th projective-envelope coordinate functional applied to that row, is a
`centralizerPPart(d)`-multiple in the fraction field.

This is deliberately stated before replacing the functional by `delta`; the replacement is
proved below from `fixed_basis_repr_eq_projective_envelope_regular_pairing_of_function`. -/
def projectiveEnvelopePairingFunctionalPointMassReadout
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G) : Prop :=
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  ∀ c d : PRegularConjClass G p,
    ∃ a : A,
      algebraMap A K (bA c d) -
          projectiveEnvelopeRegularPairingSum
            (p := p) (A := A) (K := K) (G := G) (P d) (bA c) =
        algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)

/-- Functional form of projective-envelope orthogonality: applying the `d`-th
projective-envelope pairing functional to the `c`-th canonical DVR Brauer basis row gives
`delta c d`.

The proof uses `fixed_basis_repr_eq_projective_envelope_regular_pairing_of_function` to identify
the pairing with the `d`-th coefficient functional, then reads that coefficient on the `c`-th
basis vector. -/
theorem projectiveEnvelopePairingFunctional_canonicalDVRBrauerBasis_eq_delta
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
    projectiveEnvelopeRegularPairingSum
        (p := p) (A := A) (K := K) (G := G) (P d) (bA c) =
      algebraMap A K (((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) := by
  classical
  let liftK := projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)
  have hliftK : Function.Injective liftK :=
    projectiveCartanASpanFieldLift_injective (p := p) (A := A) (K := K)
  have hredK : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((liftK x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k) := by
    intro x
    refine ⟨((primeToPRoot_unitsLift (p := p) (A := A) x : Aˣ) : A), ?_, ?_⟩
    · simp [liftK, projectiveCartanASpanFieldLift]
    · exact residue_primeToPRoot_unitLift (p := p) (A := A) x
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  let bK :=
    exercise_18_18_2_9_field_irreducible_modular_characters_basis
      (p := p) (K := K) liftK hliftK π hπ_pairwise hπ_complete
  let φ : PRegularConjClass G p → K := fun t => algebraMap A K (bA c t)
  have hφ_eq_basis : φ = bK c := by
    funext t
    have hbA :=
      congrFun
        (canonicalDVRBrauerBasis_algebraMap_apply_eq_virtualModularCharacter
          (p := p) (A := A) (K := K) (G := G)
          π hπ_pairwise hπ_complete c) t
    have hclass :=
      congrFun
        (virtualModularCharacterOnPRegularConjClass_class
          (p := p)
          (lift := PrimeToPRoot.toFieldLift liftK)
          (E := π c)) t
    have hbK :
        bK c t =
          FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := K) (π c)
            (PrimeToPRoot.toFieldLift liftK) t := by
      exact congrFun
        (exercise_18_18_2_9_field_irreducible_modular_characters_basis_apply
          (p := p) (K := K) liftK hliftK
          π hπ_pairwise hπ_complete c) t
    calc
      φ t = algebraMap A K (bA c t) := rfl
      _ =
          virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift liftK) ([π c]₀ : R₀[k](G)) t := hbA
      _ =
          FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := K) (π c)
            (PrimeToPRoot.toFieldLift liftK) t := hclass
      _ = bK c t := hbK.symm
  have hrepr :
      bK.repr φ d =
        algebraMap A K (((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) := by
    have hrepr_self :
        bK.repr (bK c) d = if c = d then (1 : K) else 0 := by
      rw [bK.repr_self c]
      by_cases hcd : c = d <;> simp [hcd]
    calc
      bK.repr φ d = bK.repr (bK c) d := by rw [hφ_eq_basis]
      _ = if c = d then (1 : K) else 0 := hrepr_self
      _ = algebraMap A K (((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) := by
        by_cases hcd : c = d
        · subst d
          simp
        · have hdc : d ≠ c := fun h => hcd h.symm
          simp [hcd, hdc]
  have hfunctional :=
    fixed_basis_repr_eq_projective_envelope_regular_pairing_of_function
      (p := p) (G := G) (A := A) (K := K)
      liftK hliftK hredK π hπ_simple hπ_coord P hP_envelope φ d
  calc
    projectiveEnvelopeRegularPairingSum
        (p := p) (A := A) (K := K) (G := G) (P d) (bA c)
        =
          bK.repr φ d := by
            simpa [projectiveEnvelopeRegularPairingSum, liftK, hπ_pairwise, hπ_complete,
              bA, bK, φ] using hfunctional.symm
    _ = algebraMap A K
          (((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) := hrepr

/-- The pairing-functional readout, together with the functional formula above, gives the pure
point-mass source congruence `bA c d = delta c d mod centralizerPPart(d)`. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_of_pairingFunctionalReadout
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
    (hreadout :
      projectiveEnvelopePairingFunctionalPointMassReadout
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
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
  change
    ∀ c d : PRegularConjClass G p,
      ∃ a : A,
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
          (ConjClasses.centralizerPPart p d.1 : A) * a
  intro c d
  rcases hreadout c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply IsFractionRing.injective A K
  have hdelta :=
    projectiveEnvelopePairingFunctional_canonicalDVRBrauerBasis_eq_delta
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope c d
  calc
    algebraMap A K
        (bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A))
        =
          algebraMap A K (bA c d) -
            projectiveEnvelopeRegularPairingSum
              (p := p) (A := A) (K := K) (G := G) (P d) (bA c) := by
            simp [map_sub, hdelta, bA]
    _ = algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := by
          simpa [projectiveEnvelopePairingFunctionalPointMassReadout, hπ_pairwise,
            hπ_complete, bA] using ha

/-- The pure point-mass source congruence implies the A-side pairing residual used by the
existing point-mass row closure worker. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_pointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hsource :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
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
  change
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
  intro c d
  rcases hsource c d with ⟨a, ha⟩
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G)
        (inversePRegularConjClass (p := p) d))) c
  refine ⟨a - coeff, ?_⟩
  have ha' :
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
        (ConjClasses.centralizerPPart p d.1 : A) * a := by
    simpa [orthogonalityPairingSumPointMassSourceCongruence, hπ_pairwise, hπ_complete,
      bA, canonicalDVRBrauerBasis] using ha
  calc
    bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        (ConjClasses.centralizerPPart p d.1 : A) * coeff
        =
          (ConjClasses.centralizerPPart p d.1 : A) * a -
            (ConjClasses.centralizerPPart p d.1 : A) * coeff := by
            rw [ha']
    _ = (ConjClasses.centralizerPPart p d.1 : A) * (a - coeff) := by
          rw [mul_sub]

/-- Fixed-family closure: the pairing-functional readout is sufficient for the direct
point-mass row divisibility target used by `PointMassRowsSourceClosureWorker`. -/
theorem coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_pairingFunctionalReadout
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
    (hreadout :
      projectiveEnvelopePairingFunctionalPointMassReadout
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
      (p := p) (A := A) (K := K) (G := G) π := by
  have hsource :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
    orthogonalityPairingSumPointMassSourceCongruence_of_pairingFunctionalReadout
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hreadout
  exact
    coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_pairingResidualDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_pointMassSourceCongruence
        (p := p) (A := A) (G := G)
        π hπ_simple hπ_coord hsource)

end PairingFunctionalPointMassRowWorker

end Representation
