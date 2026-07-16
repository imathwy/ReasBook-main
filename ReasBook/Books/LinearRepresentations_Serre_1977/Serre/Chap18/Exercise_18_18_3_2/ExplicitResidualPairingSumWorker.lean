import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.OrthogonalityResidualMicroWorker

/-!
Pairing-sum reduction for the last source-side orthogonality residual.

The two visible Exercise `18.4`/projective-envelope pairings already available in
`OrthogonalityResidualMicroWorker` show that the explicit residual congruence is equivalent to
the smaller point-mass row congruence

```
  algebraMap A K (bA c d) - <Phi_c, bA d> in z(d) A.
```

Thus the remaining non-circular source input is the row congruence `bA c d = delta_cd mod z(d)`;
the prime-to-`p` indicator term is visibly a `z(d)`-multiple after the Exercise `18.4` readback.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ExplicitResidualPairingSumWorker

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

local instance explicitResidualPairingSumWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance explicitResidualPairingSumWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Smaller pairing-sum source frontier for the final orthogonality residual.

This removes the prime-to-`p` indicator term from
`orthogonalityPairingSumResidualCongruence`; that term is automatically a
`centralizerPPart`-multiple by Exercise `18.4` readback. -/
def orthogonalityPairingSumPointMassResidualDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G) : Prop :=
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  let hliftA := primeToPRoot_unitsLift_injective (p := p) (A := A)
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
      (p := p) (A := A) liftA hliftA
      (residue_primeToPRoot_canonicalLift (p := p) (A := A))
      π hπ_pairwise hπ_complete
  ∀ c d : PRegularConjClass G p,
    ∃ a : A,
      algebraMap A K (bA c d) -
          projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
            (P c) (bA d) =
        algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)

/-- Pure source form left after the visible pairing sums are evaluated.

This is the missing source orthogonality/readback congruence: each canonical Brauer-basis row is
congruent to the corresponding point mass modulo the `p`-part of the target centralizer. -/
def orthogonalityPairingSumPointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) : Prop :=
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  let hliftA := primeToPRoot_unitsLift_injective (p := p) (A := A)
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
      (p := p) (A := A) liftA hliftA
      (residue_primeToPRoot_canonicalLift (p := p) (A := A))
      π hπ_pairwise hπ_complete
  ∀ c d : PRegularConjClass G p,
    ∃ a : A,
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
        (ConjClasses.centralizerPPart p d.1 : A) * a

/-- The pure source point-mass congruence gives the smaller pairing-sum residual after replacing
`<Phi_c, bA d>` by `delta_cd`. -/
theorem pointMassResidualDivisibility_of_pointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hsource :
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete) :
    orthogonalityPairingSumPointMassResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P := by
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
    ∀ c d : PRegularConjClass G p,
      ∃ a : A,
        algebraMap A K (bA c d) -
            projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
              (P c) (bA d) =
          algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)
  intro c d
  rcases hsource c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  let deltaA : A := ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
  let z : A := ConjClasses.centralizerPPart p d.1
  have hdelta :
      projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
          (P c) (bA d) =
        algebraMap A K deltaA := by
    simpa [liftA, hliftA, bA, deltaA] using
      projectiveEnvelopeRegularPairingSum_brauerBasis_eq_single
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope c d
  have ha' : bA c d - deltaA = z * a := by
    simpa [orthogonalityPairingSumPointMassSourceCongruence, liftA, hliftA, bA, deltaA, z]
      using ha
  calc
    algebraMap A K (bA c d) -
          projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
            (P c) (bA d)
        = algebraMap A K (bA c d) - algebraMap A K deltaA := by
            rw [hdelta]
    _ = algebraMap A K (bA c d - deltaA) := by
            simp [map_sub]
    _ = algebraMap A K (z * a) := by
            rw [ha']

/-- The smaller pairing-sum residual descends back to the pure source point-mass congruence by
fraction-field injectivity. -/
theorem pointMassSourceCongruence_of_pointMassResidualDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hpoint :
      orthogonalityPairingSumPointMassResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P) :
    orthogonalityPairingSumPointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
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
    ∀ c d : PRegularConjClass G p,
      ∃ a : A,
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
          (ConjClasses.centralizerPPart p d.1 : A) * a
  intro c d
  rcases hpoint c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply IsFractionRing.injective A K
  let deltaA : A := ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
  let z : A := ConjClasses.centralizerPPart p d.1
  have hdelta :
      projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
          (P c) (bA d) =
        algebraMap A K deltaA := by
    simpa [liftA, hliftA, bA, deltaA] using
      projectiveEnvelopeRegularPairingSum_brauerBasis_eq_single
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope c d
  have ha' :
      algebraMap A K (bA c d) -
          projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
            (P c) (bA d) =
        algebraMap A K (z * a) := by
    simpa [orthogonalityPairingSumPointMassResidualDivisibility, liftA, hliftA, bA, z]
      using ha
  calc
    algebraMap A K (bA c d - deltaA)
        = algebraMap A K (bA c d) - algebraMap A K deltaA := by
            simp [map_sub]
    _ =
        algebraMap A K (bA c d) -
          projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
            (P c) (bA d) := by
            rw [hdelta]
    _ = algebraMap A K (z * a) := ha'

/-- The point-mass pairing-sum residual is exactly the pure source point-mass congruence. -/
theorem orthogonalityPairingSumPointMassResidualDivisibility_iff_sourceCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope) :
    orthogonalityPairingSumPointMassResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P ↔
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  constructor
  · exact
      pointMassSourceCongruence_of_pointMassResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope
  · exact
      pointMassResidualDivisibility_of_pointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope

/-- The smaller point-mass pairing-sum congruence implies the explicit residual congruence:
the omitted prime-to-`p` indicator pairing is an `A`-valued coefficient, hence becomes a
`centralizerPPart`-multiple after clearing the visible factor. -/
theorem orthogonalityPairingSumResidualCongruence_of_pointMassResidualDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hpoint :
      orthogonalityPairingSumPointMassResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P) :
    orthogonalityPairingSumResidualCongruence
      (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P := by
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
    ∀ c d : PRegularConjClass G p,
      ∃ a : A,
        algebraMap A K (bA c d) -
            projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
              (P c) (bA d) -
          algebraMap A K (ConjClasses.centralizerPPart p d.1 : A) *
            projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
              (P c)
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) =
          algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)
  intro c d
  rcases hpoint c d with ⟨a, ha⟩
  let z : A := ConjClasses.centralizerPPart p d.1
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d))) c
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
  refine ⟨a - coeff, ?_⟩
  have ha' :
      algebraMap A K (bA c d) -
          projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
            (P c) (bA d) =
        algebraMap A K (z * a) := by
    simpa [orthogonalityPairingSumPointMassResidualDivisibility, liftA, hliftA, bA, z]
      using ha
  calc
    algebraMap A K (bA c d) -
          projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
            (P c) (bA d) -
        algebraMap A K z *
          projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
            (P c)
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d))
        =
      algebraMap A K (z * a) - algebraMap A K z * algebraMap A K coeff := by
        rw [ha', hcoeff]
    _ = algebraMap A K (z * a) - algebraMap A K (z * coeff) := by
        simp [map_mul]
    _ = algebraMap A K (z * (a - coeff)) := by
        rw [← map_sub, ← mul_sub]

/-- Conversely, the explicit residual congruence gives the smaller point-mass pairing-sum
congruence, because the prime-to-`p` indicator term is again a visible
`centralizerPPart`-multiple. -/
theorem pointMassResidualDivisibility_of_orthogonalityPairingSumResidualCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hcongr :
      orthogonalityPairingSumResidualCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P) :
    orthogonalityPairingSumPointMassResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P := by
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
    ∀ c d : PRegularConjClass G p,
      ∃ a : A,
        algebraMap A K (bA c d) -
            projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
              (P c) (bA d) =
          algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)
  intro c d
  rcases hcongr c d with ⟨a, ha⟩
  let z : A := ConjClasses.centralizerPPart p d.1
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d))) c
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
  refine ⟨a + coeff, ?_⟩
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
  calc
    algebraMap A K (bA c d) -
          projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
            (P c) (bA d)
        =
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

/-- With projective envelopes fixed, the explicit pairing-sum residual is exactly the smaller
point-mass pairing-sum row congruence. -/
theorem orthogonalityPairingSumResidualCongruence_iff_pointMassResidualDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope) :
    orthogonalityPairingSumResidualCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P ↔
      orthogonalityPairingSumPointMassResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P := by
  constructor
  · exact
      pointMassResidualDivisibility_of_orthogonalityPairingSumResidualCongruence
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope
  · exact
      orthogonalityPairingSumResidualCongruence_of_pointMassResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope

/-- Final local reduction: the requested explicit pairing-sum residual is equivalent to the pure
source congruence `bA c d = delta_cd mod centralizerPPart(d)`. -/
theorem orthogonalityPairingSumResidualCongruence_iff_pointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope) :
    orthogonalityPairingSumResidualCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P ↔
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  exact
    (orthogonalityPairingSumResidualCongruence_iff_pointMassResidualDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope).trans
      (orthogonalityPairingSumPointMassResidualDivisibility_iff_sourceCongruence
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope)

end ExplicitResidualPairingSumWorker

end Representation
