import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerCoordinateReadback
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveEnvelopePairing

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section OrthogonalityResidualMicroWorker

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

local instance orthogonalityResidualMicroWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance orthogonalityResidualMicroWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Serre's projective-envelope pairing sum with an arbitrary `A`-valued regular class
function.  This is the literal finite-group sum appearing in the orthogonality relation
`<Φ_E, φ_E'>`. -/
noncomputable def projectiveEnvelopeRegularPairingSum
    (P : FiniteProjectiveGroupAlgebraModule k G)
    (φ : PRegularConjClass G p → A) : K :=
  (Fintype.card G : K)⁻¹ *
    ∑ s : G,
      (if hs : IsPRegular p (s⁻¹) then
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P]ₚ₀)
          (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
      else 0) *
        (if hs : IsPRegular p s then
          algebraMap A K (φ (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
        else 0)

/-- Unconditional micro-provider for the `δ` part of Serre orthogonality: pairing the projective
envelope row of `c` with the `d`-th Brauer basis vector gives the fixed point mass
`Pi.single c 1` evaluated at `d`. -/
theorem projectiveEnvelopeRegularPairingSum_brauerBasis_eq_single
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (c d : PRegularConjClass G p) :
    let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
    let hliftA := primeToPRoot_unitsLift_injective (p := p) (A := A)
    let bA :=
      exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
        (p := p) (A := A) liftA hliftA
        (residue_primeToPRoot_canonicalLift (p := p) (A := A))
        π hπ_pairwise hπ_complete
    projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
        (P c) (bA d) =
      algebraMap A K (((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) := by
  classical
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  let hliftA : Function.Injective liftA :=
    primeToPRoot_unitsLift_injective (p := p) (A := A)
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
      (p := p) (A := A) liftA hliftA
      (residue_primeToPRoot_canonicalLift (p := p) (A := A))
      π hπ_pairwise hπ_complete
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  have hdelta :=
    projectiveEnvelope_pairing_primeToP_indicator_eq_basis_repr
      (p := p) (A := A) (K := K) (G := G) (hω := hω)
      (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
      (P := P) (hP_envelope := hP_envelope) c d
  calc
    projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
        (P c) (bA d)
        = if c = d then (1 : K) else 0 := by
          simpa [projectiveEnvelopeRegularPairingSum, liftA, hliftA, bA] using hdelta
    _ = algebraMap A K
          (((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) := by
          by_cases hcd : c = d
          · subst d
            simp
          · have hdc : d ≠ c := fun h => hcd h.symm
            simp [hcd, hdc]

/-- Unconditional micro-provider for the point-mass coefficient: pairing the projective envelope
row of `c` with the prime-to-`p` indicator of the inverse class of `d` recovers the Exercise
`18.4` coefficient `bA.repr (...) c` after embedding into the fraction field. -/
theorem projectiveEnvelopeRegularPairingSum_primeToPIndicator_eq_repr
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (c d : PRegularConjClass G p) :
    let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
    let hliftA := primeToPRoot_unitsLift_injective (p := p) (A := A)
    let bA :=
      exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
        (p := p) (A := A) liftA hliftA
        (residue_primeToPRoot_canonicalLift (p := p) (A := A))
        π hπ_pairwise hπ_complete
    projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
        (P c)
        (primeToP_regular_indicator
          (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) =
      algebraMap A K
        ((bA.repr
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d))) c) := by
  classical
  let invd := inversePRegularConjClass (p := p) d
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  let hliftA : Function.Injective liftA :=
    primeToPRoot_unitsLift_injective (p := p) (A := A)
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
      (p := p) (A := A) liftA hliftA
      (residue_primeToPRoot_canonicalLift (p := p) (A := A))
      π hπ_pairwise hπ_complete
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator (p := p) (A := A) (G := G) invd)) c
  have hsum :=
    projectiveEnvelope_pairing_primeToP_indicator_eq_inverse_regularRestriction
      (p := p) (A := A) (K := K) (G := G) (i := P c) invd
  have hsum_d :
      projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
          (P c)
          (primeToP_regular_indicator (p := p) (A := A) (G := G) invd) =
        (algebraMap A K (ConjClasses.centralizerPPart p d.1 : A))⁻¹ *
          regularRestriction (p := p) (A := A) (K := K) (G := G)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d := by
    simpa [projectiveEnvelopeRegularPairingSum, invd, inversePRegularConjClass_involutive,
      inversePRegularConjClass_val, ConjClasses.centralizerPPart_inv] using hsum
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  have hvalue :=
    projectiveEnvelope_regularRestriction_value_eq_centralizerPPart_mul_repr_inv
      (p := p) (A := A) (K := K) (G := G)
      (hω := hω)
      (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
      (P := P) (hP_envelope := hP_envelope) c invd
  have hvalue_d :
      regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
        algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * coeff) := by
    change
      regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀)
          (inversePRegularConjClass (p := p) invd) =
        algebraMap A K
          ((ConjClasses.centralizerPPart p invd.1 : A) *
            ((bA.repr
              (primeToP_regular_indicator (p := p) (A := A) (G := G) invd)) c)) at hvalue
    rw [inversePRegularConjClass_involutive] at hvalue
    rw [inversePRegularConjClass_val, ConjClasses.centralizerPPart_inv] at hvalue
    simpa [coeff] using hvalue
  let z : A := ConjClasses.centralizerPPart p d.1
  have hz : algebraMap A K z ≠ 0 :=
    algebraMap_centralizerPPart_ne_zero (p := p) (A := A) (K := K) (G := G) d
  calc
    projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
        (P c)
        (primeToP_regular_indicator
          (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d))
        =
          (algebraMap A K z)⁻¹ *
            regularRestriction (p := p) (A := A) (K := K) (G := G)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d := by
          simpa [invd, z] using hsum_d
    _ = (algebraMap A K z)⁻¹ * algebraMap A K (z * coeff) := by
          rw [hvalue_d]
    _ = algebraMap A K coeff := by
          rw [map_mul]
          field_simp [hz]

/-- The explicit orthogonality-sum congruence which is sufficient for the A-side residual.
It replaces the `δ` term by the projective-envelope/Brauer-basis pairing sum and replaces the
`bA.repr` point-mass coefficient by the projective-envelope/indicator pairing sum. -/
def orthogonalityPairingSumResidualCongruence
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
            (P c) (bA d) -
        algebraMap A K (ConjClasses.centralizerPPart p d.1 : A) *
          projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
            (P c)
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) =
        algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)

/-- The explicit orthogonality-sum congruence implies the pure A-side residual divisibility.
This is the small remaining bridge: the only unproved input is now a congruence between concrete
Serre pairing sums, not the `bA.repr` residual itself. -/
theorem basisResidualDivisibility_of_orthogonalityPairingSumResidualCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hcongr :
      orthogonalityPairingSumResidualCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P) :
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
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
          (ConjClasses.centralizerPPart p d.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c) =
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
    ∀ c d : PRegularConjClass G p,
      ∃ a : A,
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
          (ConjClasses.centralizerPPart p d.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c) =
          (ConjClasses.centralizerPPart p d.1 : A) * a
  intro c d
  rcases hcongr c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply IsFractionRing.injective A K
  let z : A := ConjClasses.centralizerPPart p d.1
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d))) c
  have hdelta :=
    projectiveEnvelopeRegularPairingSum_brauerBasis_eq_single
      (p := p) (A := A) (K := K) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope c d
  have hcoeff :=
    projectiveEnvelopeRegularPairingSum_primeToPIndicator_eq_repr
      (p := p) (A := A) (K := K) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope c d
  calc
    algebraMap A K
        (bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
          z * coeff)
        =
          algebraMap A K (bA c d) -
              algebraMap A K
                (((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) -
            algebraMap A K z * algebraMap A K coeff := by
          simp [map_sub, map_mul]
    _ =
          algebraMap A K (bA c d) -
              projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
                (P c) (bA d) -
            algebraMap A K z *
              projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
                (P c)
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) := by
          rw [← hdelta, ← hcoeff]
    _ = algebraMap A K (z * a) := by
          simpa [orthogonalityPairingSumResidualCongruence, liftA, hliftA, bA, z] using ha

/-- Coordinate-normalized wrapper for the previous micro-bridge, matching the A-side residual
shape used by the point-mass worker files. -/
theorem coordinateNormalizedBasisResidualDivisibility_of_orthogonalityPairingSumResidualCongruence
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
    (hcongr :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumResidualCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
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
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
          (ConjClasses.centralizerPPart p d.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c) =
          (ConjClasses.centralizerPPart p d.1 : A) * a := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  exact
    basisResidualDivisibility_of_orthogonalityPairingSumResidualCongruence
      (p := p) (A := A) (K := K) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope hcongr

end OrthogonalityResidualMicroWorker

end Representation
