import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerResidualMatrixClosureFinal
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PairingResidualDirectWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerOrthogonalityCongruenceWorker

/-!
Source-side bridges for the coordinate-normalized visible Brauer readback statement.

The unconditional fixed-family theorem is still not available from the current local API without
an additional source row input.  The two bridges below keep that input explicit:

* the literal Exercise 18.4 / orthogonality pairing-sum congruence implies visible readback;
* the smaller point-mass regular-value row divisibility implies visible readback directly.

Neither bridge uses a Cartan range, cokernel, product, or determinant endpoint.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerVisibleReadbackSourceProofWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerVisibleReadbackSourceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerVisibleReadbackSourceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The explicit Exercise `18.4` / projective-envelope orthogonality pairing-sum congruence
closes the coordinate-normalized visible readback statement for the same fixed family. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_sourceProof_of_orthogonalityPairingSum
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
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  have hresidual :
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
    (orthogonalityPairingSumResidualCongruence_iff_coordinateNormalizedPairingResidual
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope).1 horth
  exact
    (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_visibleReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hresidual

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The point-mass regular-value row input is enough to prove visible readback directly.

This is the compressed remaining source lemma for the fixed family: for each `c`, the
`K`-valued row `φ_c - δ_c` lies in Serre's regular-value divisibility lattice.  The proof then
descends the coordinatewise divisibility through the canonical DVR Brauer basis. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_sourceProof_of_pointMassRows
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hrows :
      coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π) :
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  classical
  intro c d
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  let row : PRegularConjClass G p → K :=
    FDRep.modularCharacterOnPRegularConjClass
        (p := p) (G := G) (A := K) (π c)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)
  rcases
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G) row).1
        (by
          simpa [row, coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule]
            using hrows c)
        d with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply IsFractionRing.injective A K
  have hbasis :=
    congrFun
      (canonicalDVRBrauerBasis_algebraMap_apply_eq_virtualModularCharacter
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete c) d
  have hclass :=
    congrFun
      (virtualModularCharacterOnPRegularConjClass_class
        (p := p)
        (lift := PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        (E := π c)) d
  have hchar :
      algebraMap A K (bA c d) =
        FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d :=
    hbasis.trans hclass
  calc
    algebraMap A K
        (bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A))
        =
          algebraMap A K (bA c d) -
            algebraMap A K
              (((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) := by
          simp [map_sub]
    _ =
          FDRep.modularCharacterOnPRegularConjClass
              (p := p) (G := G) (A := K) (π c)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d := by
          rw [hchar]
          simp [regularIntegerFunctionCast]
    _ = row d := rfl
    _ = algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := ha

end BrauerVisibleReadbackSourceProofWorker

end Representation
