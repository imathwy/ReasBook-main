import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ResidualClassSumAValuedCompletionWorker

/-!
Source-side audit for the residual class-sum `A`-valued blocker.

This worker stays on the Exercise `18.4` / projective-envelope orthogonality route.  It proves
the missing reverse direction for the projective-dual class-sum residual: after the class-sum
denominator computation and the projective-envelope dual readback, the projective-dual
`A`-valuedness is exactly the already isolated A-side pairing residual divisibility.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ResidualAValuedSourceProofWorker

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

local instance residualAValuedSourceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance residualAValuedSourceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The A-side pairing residual gives the projective-dual class-sum residual.

After the class-sum denominator formula, the first term is
`z(d)^{-1} * (bA c d - delta_cd)`.  The projective-envelope dual readback identifies the
subtracted term with the Exercise `18.4` coefficient of the inverse prime-to-`p` indicator.
Thus the required class-sum `A`-valuedness is exactly the expanded pairing residual divided by
`z(d)`. -/
theorem
    coordinateNormalizedBrauerBasisResidualClassSumMinusProjectiveDualAValued_of_pairingResidualDivisibility
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
    (hres :
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisResidualClassSumMinusProjectiveDualAValued
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P := by
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
      let f :=
        primeToP_regular_indicator
          (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)
      ∃ a : A,
        regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
            (fun e =>
              bA c e -
                ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) e : A))
            f -
          projectiveEnvelopeRegularPairingSum
            (p := p) (A := A) (K := K) (G := G) (P c) f =
          algebraMap A K a
  intro c d
  let f :=
    primeToP_regular_indicator
      (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)
  let diff : PRegularConjClass G p → A := fun e =>
    bA c e - ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) e : A)
  let z : A := ConjClasses.centralizerPPart p d.1
  let coeff : A := (bA.repr f) c
  rcases hres c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hz : algebraMap A K z ≠ 0 :=
    algebraMap_centralizerPPart_ne_zero (p := p) (A := A) (K := K) (G := G) d
  have hpair :
      regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G) diff f =
        (algebraMap A K z)⁻¹ * algebraMap A K (diff d) := by
    simpa [diff, f, z, inversePRegularConjClass_involutive,
      inversePRegularConjClass_val, ConjClasses.centralizerPPart_inv] using
      (regularClassFunctionPairingSum_primeToPIndicator_eq_inverse_value
        (p := p) (A := A) (K := K) (G := G)
        diff (inversePRegularConjClass (p := p) d))
  have hproj :
      projectiveEnvelopeRegularPairingSum
          (p := p) (A := A) (K := K) (G := G) (P c) f =
        algebraMap A K coeff := by
    simpa [hπ_pairwise, hπ_complete, bA, f, coeff, canonicalDVRBrauerBasis] using
      projectiveEnvelopeRegularPairingSum_primeToPIndicator_eq_repr
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope c d
  have hdiff :
      diff d - z * coeff = z * a := by
    simpa [coordinateNormalizedBrauerBasisPairingResidualDivisibility, hπ_pairwise,
      hπ_complete, bA, diff, z, coeff, f] using ha
  have hdiff' : diff d = z * (a + coeff) := by
    calc
      diff d = (diff d - z * coeff) + z * coeff := by ring
      _ = z * a + z * coeff := by rw [hdiff]
      _ = z * (a + coeff) := by rw [mul_add]
  calc
    regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
        (fun e =>
          bA c e - ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) e : A))
        f -
      projectiveEnvelopeRegularPairingSum
        (p := p) (A := A) (K := K) (G := G) (P c) f
        =
      regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
          diff f -
        algebraMap A K coeff := by
          simp [diff, hproj]
    _ = (algebraMap A K z)⁻¹ * algebraMap A K (diff d) -
        algebraMap A K coeff := by
          rw [hpair]
    _ = (algebraMap A K z)⁻¹ * algebraMap A K (z * (a + coeff)) -
        algebraMap A K coeff := by
          rw [hdiff']
    _ = algebraMap A K a := by
          rw [map_mul, map_add]
          field_simp [hz]
          ring

/-- Exact fixed-family identification of the projective-dual class-sum residual with the
previously isolated A-side pairing residual. -/
theorem
    coordinateNormalizedBrauerBasisResidualClassSumMinusProjectiveDualAValued_iff_pairingResidualDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope) :
    coordinateNormalizedBrauerBasisResidualClassSumMinusProjectiveDualAValued
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P ↔
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  constructor
  · exact
      coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_projectiveDualResidual
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope
  · exact
      coordinateNormalizedBrauerBasisResidualClassSumMinusProjectiveDualAValued_of_pairingResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope

end ResidualAValuedSourceProofWorker

end Representation
