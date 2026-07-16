import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackSourceFaithful
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.OrthogonalityResidualMicroWorker

/-!
Direct Exercise `18.4` / orthogonality attempt for the point-mass row congruence.

The available source-faithful API gives the literal orthogonality readback

```
  <Phi_c, bA_d> = delta_cd
```

for the canonical `A`-valued Exercise `18.4` Brauer basis `bA`.  To get the desired point-mass
row congruence directly from that readback, the remaining missing line is the congruence between
the basis value `bA c d` and the same projective-envelope pairing, modulo the target centralizer
`p`-part.  This file records that exact local blocker and proves that, together with the already
formalized orthogonality relation, it is equivalent to the requested row congruence.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section Exercise18_4OrthogonalityPointMassDirectWorker

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

local instance exercise18_4OrthogonalityPointMassDirectWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance exercise18_4OrthogonalityPointMassDirectWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The exact direct-route blocker after Exercise `18.4` and before the final point-mass
congruence: the `A`-basis value `bA c d`, embedded in `K`, is congruent to the projective
orthogonality pairing `<Phi_c, bA_d>` modulo the target centralizer `p`-part. -/
def exercise18_4OrthogonalityPointMassDirectPairingResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G) : Prop :=
  let bA := canonicalDVRBrauerBasis (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  ∀ c d : PRegularConjClass G p,
    ∃ a : A,
      algebraMap A K (bA c d) -
          projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
            (P c) (bA d) =
        algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)

/-- The desired fixed-family point-mass row congruence for the canonical Exercise `18.4`
Brauer basis. -/
def exercise18_4OrthogonalityPointMassRowCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) : Prop :=
  let bA := canonicalDVRBrauerBasis (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  ∀ c d : PRegularConjClass G p,
    ∃ a : A,
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
        (ConjClasses.centralizerPPart p d.1 : A) * a

/-- Direct residual plus the already-formalized orthogonality relation
`<Phi_c, bA_d> = delta_cd` gives the point-mass row congruence. -/
theorem exercise18_4OrthogonalityPointMassRowCongruence_of_directPairingResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hdirect :
      exercise18_4OrthogonalityPointMassDirectPairingResidual
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P) :
    exercise18_4OrthogonalityPointMassRowCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  classical
  dsimp [exercise18_4OrthogonalityPointMassDirectPairingResidual] at hdirect
  dsimp [exercise18_4OrthogonalityPointMassRowCongruence]
  intro c d
  let bA := canonicalDVRBrauerBasis (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  let deltaA : A := ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
  let z : A := ConjClasses.centralizerPPart p d.1
  rcases hdirect c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply IsFractionRing.injective A K
  have hdelta :
      projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
          (P c) (bA d) =
        algebraMap A K deltaA := by
    simpa [bA, deltaA, canonicalDVRBrauerBasis] using
      projectiveEnvelopeRegularPairingSum_brauerBasis_eq_single
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope c d
  have ha' :
      algebraMap A K (bA c d) -
          projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
            (P c) (bA d) =
        algebraMap A K (z * a) := by
    simpa [bA, z] using ha
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

/-- Conversely, the point-mass row congruence immediately gives the direct pairing-residual
blocker, by substituting `<Phi_c, bA_d> = delta_cd`. -/
theorem exercise18_4OrthogonalityDirectPairingResidual_of_pointMassRowCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hrow :
      exercise18_4OrthogonalityPointMassRowCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete) :
    exercise18_4OrthogonalityPointMassDirectPairingResidual
      (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P := by
  classical
  dsimp [exercise18_4OrthogonalityPointMassRowCongruence] at hrow
  dsimp [exercise18_4OrthogonalityPointMassDirectPairingResidual]
  intro c d
  let bA := canonicalDVRBrauerBasis (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  let deltaA : A := ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
  let z : A := ConjClasses.centralizerPPart p d.1
  rcases hrow c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hdelta :
      projectiveEnvelopeRegularPairingSum (p := p) (A := A) (K := K) (G := G)
          (P c) (bA d) =
        algebraMap A K deltaA := by
    simpa [bA, deltaA, canonicalDVRBrauerBasis] using
      projectiveEnvelopeRegularPairingSum_brauerBasis_eq_single
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope c d
  have ha' : bA c d - deltaA = z * a := by
    simpa [bA, deltaA, z] using ha
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

/-- With projective envelopes fixed, the direct Exercise `18.4` / orthogonality blocker is
equivalent to the point-mass row congruence.  This is the precise Lean obstruction left by the
source route in this worker. -/
theorem exercise18_4OrthogonalityDirectPairingResidual_iff_pointMassRowCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope) :
    exercise18_4OrthogonalityPointMassDirectPairingResidual
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P ↔
      exercise18_4OrthogonalityPointMassRowCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  constructor
  · exact
      exercise18_4OrthogonalityPointMassRowCongruence_of_directPairingResidual
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope
  · exact
      exercise18_4OrthogonalityDirectPairingResidual_of_pointMassRowCongruence
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope

/-- Coordinate-normalized global form of the minimal direct-route upstream lemma.  It asks for
projective envelopes and the direct pairing residual for every coordinate-normalized Exercise
`18.4` Brauer family. -/
def exercise18_4OrthogonalityPointMassDirectSourceBlocker : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
    ∃ P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G,
      (∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope) ∧
        let hπ_pairwise :=
          pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord
        let hπ_complete :=
          complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord
        exercise18_4OrthogonalityPointMassDirectPairingResidual
          (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P

/-- The direct-route source blocker is sufficient for the coordinate-normalized point-mass row
congruence for every Exercise `18.4` Brauer family. -/
theorem exercise18_4OrthogonalityPointMassRowCongruence_of_directSourceBlocker
    (hblock :
      exercise18_4OrthogonalityPointMassDirectSourceBlocker
        (p := p) (A := A) (K := K) (G := G)) :
    ∀ (π : PRegularConjClass G p → FDRep k G)
      (hπ_simple : ∀ c, Simple (π c))
      (hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      exercise18_4OrthogonalityPointMassRowCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  intro π hπ_simple hπ_coord
  rcases hblock π hπ_simple hπ_coord with ⟨P, hP_envelope, hdirect⟩
  exact
    exercise18_4OrthogonalityPointMassRowCongruence_of_directPairingResidual
      (p := p) (A := A) (K := K) (G := G)
      π
      (pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord)
      (complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord)
      P hP_envelope hdirect

end Exercise18_4OrthogonalityPointMassDirectWorker

end Representation
