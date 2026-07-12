import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointMassOrthogonalitySourceWorker

/-!
Direct worker for the Brauer-basis fixed-coordinate readback divisibility.

This file keeps the reduction at the Exercise `18.4` orthogonality pairing-sum
level.  It does not use the Cartan cokernel/product/Smith/determinant route or
any final endpoint.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerBasisReadbackDivisibilityDirectWorker2

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

local instance brauerBasisReadbackDivisibilityDirectWorker2FintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisReadbackDivisibilityDirectWorker2DecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Pointwise direct reduction from the Exercise `18.4` orthogonality pairing-sum residual to
the canonical DVR Brauer-basis row with the visible `Pi.single` coordinate row. -/
theorem canonicalDVRBrauerBasis_fixedRowSingleDivisibility_directWorker2_of_orthogonalityPairingSum
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (horth :
      orthogonalityPairingSumResidualCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P)
    (i c : PRegularConjClass G p) :
    ∃ a : A,
      canonicalDVRBrauerBasis
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete i c -
        ((Pi.single i (1 : ℤ) : PRegularConjClass G p → ℤ) c : A) =
          (ConjClasses.centralizerPPart p c.1 : A) * a := by
  classical
  simpa [canonicalDVRBrauerBasis] using
    pointMass_visibleCongruence_of_orthogonalityPairingSum_pointwise
      (p := p) (A := A) (K := K) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope horth i c

/-- Pointwise fixed-coordinate readback divisibility from the Exercise `18.4`
orthogonality pairing-sum residual, after identifying the source-faithful coordinate row with
the visible `Pi.single` row. -/
theorem canonicalDVRBrauerBasis_fixedRowDivisibility_directWorker2_of_orthogonalityPairingSum
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ_coord :
      ∀ i,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π i]₀ : R₀[k](G)) =
          (Pi.single i (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (horth :
      orthogonalityPairingSumResidualCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P)
    (i c : PRegularConjClass G p) :
    ∃ a : A,
      canonicalDVRBrauerBasis
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete i c -
        ((regularClassCoordinateAddEquiv
          (p := p) (G := G) ([π i]₀ : R₀[k](G))) c : A) =
          (ConjClasses.centralizerPPart p c.1 : A) * a := by
  classical
  rcases
    canonicalDVRBrauerBasis_fixedRowSingleDivisibility_directWorker2_of_orthogonalityPairingSum
      (p := p) (A := A) (K := K) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope horth i c with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hcoord_c :
      ((regularClassCoordinateAddEquiv
          (p := p) (G := G) ([π i]₀ : R₀[k](G))) c : A) =
        ((Pi.single i (1 : ℤ) : PRegularConjClass G p → ℤ) c : A) := by
    rw [hπ_coord i]
  simpa [hcoord_c] using ha

/-- Fixed-coordinate Brauer-basis readback divisibility reduced directly to the Exercise `18.4`
orthogonality pairing-sum residual and the source-faithful coordinate-row identification. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_directWorker2_of_orthogonalityPairingSum
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ_coord :
      ∀ i,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π i]₀ : R₀[k](G)) =
          (Pi.single i (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (horth :
      orthogonalityPairingSumResidualCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P) :
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  intro i c
  exact
    canonicalDVRBrauerBasis_fixedRowDivisibility_directWorker2_of_orthogonalityPairingSum
      (p := p) (A := A) (K := K) (G := G)
      π hπ_pairwise hπ_complete hπ_coord P hP_envelope horth i c

end BrauerBasisReadbackDivisibilityDirectWorker2

end Representation
