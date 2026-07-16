import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackFromPairing
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerExercise18_4OrthogonalityAPI
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ExplicitResidualPairingSumWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointMassBrauerBasisEntryCongruenceWorker

/-!
Direct point-mass orthogonality source worker.

This file keeps the Serre `18.4` route at the visible pairing-sum level.  The two
orthogonality readbacks

* `<Phi_c, b_d> = delta_cd`, and
* `<Phi_c, 1_{d^{-1}}> = b.repr(1_{d^{-1}})_c`

are substituted directly into the explicit residual congruence.  The only remaining term is the
point-mass row congruence

```
  b c d - delta_cd = centralizerPPart(d) * a.
```

No Cartan range, cokernel, product, determinant, or final endpoint is used here.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section PointMassOrthogonalitySourceWorker

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

local instance pointMassOrthogonalitySourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointMassOrthogonalitySourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Pointwise direct simplification of the Exercise `18.4` pairing residual.

After substituting the two available Serre orthogonality sums, the explicit pairing residual
has the single remaining visible point-mass term
`bA c d - delta_cd`, divisible by the target centralizer `p`-part. -/
theorem pointMass_visibleCongruence_of_orthogonalityPairingSum_pointwise
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (horth :
      orthogonalityPairingSumResidualCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P)
    (c d : PRegularConjClass G p) :
    let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
    let hliftA := primeToPRoot_unitsLift_injective (p := p) (A := A)
    let bA :=
      exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
        (p := p) (A := A) liftA hliftA
        (residue_primeToPRoot_canonicalLift (p := p) (A := A))
        π hπ_pairwise hπ_complete
    ∃ a : A,
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
        (ConjClasses.centralizerPPart p d.1 : A) * a := by
  classical
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  let hliftA : Function.Injective liftA :=
    primeToPRoot_unitsLift_injective (p := p) (A := A)
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
      (p := p) (A := A) liftA hliftA
      (residue_primeToPRoot_canonicalLift (p := p) (A := A))
      π hπ_pairwise hπ_complete
  change
    ∃ a : A,
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
        (ConjClasses.centralizerPPart p d.1 : A) * a
  rcases horth c d with ⟨a, ha⟩
  let z : A := ConjClasses.centralizerPPart p d.1
  let deltaA : A := ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d))) c
  have hdelta :
      projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
          (P c) (bA d) =
        algebraMap A K deltaA := by
    simpa [liftA, hliftA, bA, deltaA] using
      projectiveEnvelopeRegularPairingSum_brauerBasis_eq_single
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope c d
  have hcoeff :
      projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
          (P c)
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) =
        algebraMap A K coeff := by
    simpa [liftA, hliftA, bA, coeff] using
      projectiveEnvelopeRegularPairingSum_primeToPIndicator_eq_repr
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope c d
  have ha' :
      algebraMap A K (bA c d) -
          projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
            (P c) (bA d) -
        algebraMap A K z *
          projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
            (P c)
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) =
        algebraMap A K (z * a) := by
    simpa [orthogonalityPairingSumResidualCongruence, liftA, hliftA, bA, z] using ha
  refine ⟨a + coeff, ?_⟩
  apply IsFractionRing.injective A K
  calc
    algebraMap A K (bA c d - deltaA)
        = algebraMap A K (bA c d) - algebraMap A K deltaA := by
            simp [map_sub]
    _ =
        algebraMap A K (bA c d) -
          projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
            (P c) (bA d) := by
            rw [hdelta]
    _ =
        (algebraMap A K (bA c d) -
            projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
              (P c) (bA d) -
          algebraMap A K z *
            projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
              (P c)
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d))) +
          algebraMap A K z *
            projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
              (P c)
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) := by
            ring
    _ = algebraMap A K (z * a) + algebraMap A K z * algebraMap A K coeff := by
            rw [ha', hcoeff]
    _ = algebraMap A K (z * (a + coeff)) := by
            simp [map_mul, map_add, mul_add]

/-- Fixed-family visible point-mass row congruence obtained directly from the explicit
orthogonality pairing-sum input. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_of_orthogonalityPairingSum_direct
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
    (horth :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumResidualCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P) :
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  intro c d
  simpa [coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra,
    canonicalDVRBrauerBasis, hπ_pairwise, hπ_complete] using
    pointMass_visibleCongruence_of_orthogonalityPairingSum_pointwise
      (p := p) (A := A) (K := K) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope horth c d

/-- Direct fixed-coordinate readback consequence of the visible point-mass congruence above.
This wrapper only replaces the normalized coordinate row by `Pi.single c 1`; it does not use any
Cartan endpoint. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_of_orthogonalityPairingSum_direct
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
    (horth :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumResidualCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord) := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  have hvisible :=
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_of_orthogonalityPairingSum_direct
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope horth
  intro c d
  rcases hvisible c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hcoord_d :
      ((regularClassCoordinateAddEquiv
          (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
        ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) := by
    rw [hπ_coord c]
  simpa [brauerBasisFixedCoordinateReadbackDivisibility,
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra,
    hπ_pairwise, hπ_complete, hcoord_d] using ha

/-- Remaining source lemma in literal pointwise form if one wants to prove the point-mass row
congruence without first assuming the explicit pairing-sum residual. -/
def coordinateNormalizedPointMassVisibleDivisibilitySource
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- The remaining source lemma is sufficient for the fixed-coordinate readback input. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_of_visibleDivisibilitySource
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hsource :
      coordinateNormalizedPointMassVisibleDivisibilitySource
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord) := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  intro c d
  rcases hsource c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hcoord_d :
      ((regularClassCoordinateAddEquiv
          (p := p) (G := G) ([π c]₀ : R₀[k](G))) d : A) =
        ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) := by
    rw [hπ_coord c]
  simpa [coordinateNormalizedPointMassVisibleDivisibilitySource,
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra,
    brauerBasisFixedCoordinateReadbackDivisibility, hπ_pairwise, hπ_complete,
    hcoord_d] using ha

end PointMassOrthogonalitySourceWorker

end Representation
