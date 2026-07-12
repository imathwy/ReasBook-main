import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.VisibleReadbackCaseSplitSourceWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PairingFunctionalPointMassRowWorker

/-!
Diagonal source-side worker for the visible point-mass readback.

This file keeps the source-side diagonal obligation isolated.  The closed part is the
`centralizerPPart = 1` branch and the diagonal orthogonality readout
`<Phi_E, phi_E> = 1`; the remaining input is the diagonal-only comparison between ordinary
evaluation and that projective-envelope pairing functional.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation ZeroObject

universe u

namespace Representation

section VisibleReadbackDiagonalSourceCompletionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "kA" => IsLocalRing.ResidueField A

local instance visibleReadbackDiagonalSourceCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance visibleReadbackDiagonalSourceCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The diagonal target is automatic at classes whose centralizer has trivial `p`-part. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackDiagonalSource_of_centralizerPPart_eq_one
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c : PRegularConjClass G p)
    (hc : ConjClasses.centralizerPPart p c.1 = 1) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    ∃ a : A, bA c c - (1 : A) = (ConjClasses.centralizerPPart p c.1 : A) * a := by
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
  refine ⟨bA c c - (1 : A), ?_⟩
  have hz : (ConjClasses.centralizerPPart p c.1 : A) = 1 := by
    simp [hc]
  change bA c c - (1 : A) =
    (ConjClasses.centralizerPPart p c.1 : A) * (bA c c - (1 : A))
  simp [hz]

/-- The full visible source lemma still gives the diagonal half by the case-split worker. -/
theorem exercise18_4PointMassRowVisibleReadbackDiagonalSourceLemma_of_visibleReadbackSourceLemma
    (hvisible :
      exercise18_4PointMassRowVisibleReadbackSourceLemma
        (p := p) (A := A) (G := G)) :
    exercise18_4PointMassRowVisibleReadbackDiagonalSourceLemma
      (p := p) (A := A) (G := G) :=
  ((exercise18_4PointMassRowVisibleReadbackSourceLemma_iff_diagonal_and_offDiagonal
    (p := p) (A := A) (G := G)).1 hvisible).1

section DiagonalPairingReadout

variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)]

/-- Diagonal orthogonality readout in residual form.

For a chosen family of projective envelopes, the field image of the visible diagonal residual
`bA c c - 1` is exactly ordinary evaluation of the row at `c` minus the projective-envelope
pairing functional. -/
theorem coordinateNormalizedBrauerBasisDiagonal_visibleResidual_algebraMap_eq
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[kA[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (c : PRegularConjClass G p) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    algebraMap A K (bA c c - (1 : A)) =
      algebraMap A K (bA c c) -
        projectiveEnvelopeRegularPairingSum
          (p := p) (A := A) (K := K) (G := G) (P c) (bA c) := by
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
  have hdelta :
      projectiveEnvelopeRegularPairingSum
          (p := p) (A := A) (K := K) (G := G) (P c) (bA c) =
        algebraMap A K (1 : A) := by
    simpa [hπ_pairwise, hπ_complete, bA] using
      projectiveEnvelopePairingFunctional_canonicalDVRBrauerBasis_eq_delta
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c c
  calc
    algebraMap A K (bA c c - (1 : A)) =
        algebraMap A K (bA c c) - algebraMap A K (1 : A) := by
          simp [map_sub]
    _ =
        algebraMap A K (bA c c) -
          projectiveEnvelopeRegularPairingSum
            (p := p) (A := A) (K := K) (G := G) (P c) (bA c) := by
          rw [hdelta]

/-- Diagonal-only source completion from the nontrivial diagonal pairing readout.

This is the remaining local proposition after the closed orthogonality readout above: for each
normalized Brauer family, choose projective envelopes so that ordinary diagonal evaluation and
the diagonal projective-envelope functional agree modulo the centralizer `p`-part at every
nontrivial centralizer column. -/
theorem exercise18_4PointMassRowVisibleReadbackDiagonalSourceLemma_of_diagonalPairingReadout
    (hreadout :
      ∀ (π : PRegularConjClass G p → FDRep kA G)
        (hπ_simple : ∀ c, Simple (π c))
        (hπ_coord :
          ∀ c,
            regularClassCoordinateAddEquiv
                (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
        ∃ P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G,
          (∀ c, ∃ f : (P c).V →ₗ[kA[G]] asModule (π c).ρ,
            f.IsProjectiveEnvelope) ∧
            let hπ_pairwise :=
              pairwiseNonisomorphic_of_regularClassCoordinate_single
                (p := p) (G := G) (π := π) hπ_coord
            let hπ_complete :=
              complete_irreducible_family_of_regularClassCoordinate_single
                (p := p) (G := G) (π := π) hπ_simple hπ_coord
            let bA :=
              canonicalDVRBrauerBasis
                (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
            ∀ c : PRegularConjClass G p,
              ConjClasses.centralizerPPart p c.1 ≠ 1 →
              ∃ a : A,
                algebraMap A K (bA c c) -
                    projectiveEnvelopeRegularPairingSum
                      (p := p) (A := A) (K := K) (G := G) (P c) (bA c) =
                  algebraMap A K ((ConjClasses.centralizerPPart p c.1 : A) * a)) :
    exercise18_4PointMassRowVisibleReadbackDiagonalSourceLemma
      (p := p) (A := A) (G := G) := by
  classical
  intro π hπ_simple hπ_coord c
  by_cases hc : ConjClasses.centralizerPPart p c.1 = 1
  · exact
      coordinateNormalizedBrauerBasisVisibleReadbackDiagonalSource_of_centralizerPPart_eq_one
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord c hc
  rcases hreadout π hπ_simple hπ_coord with ⟨P, hP_envelope, hreadoutπ⟩
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  rcases hreadoutπ c hc with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply IsFractionRing.injective A K
  calc
    algebraMap A K (bA c c - (1 : A)) =
        algebraMap A K (bA c c) -
          projectiveEnvelopeRegularPairingSum
            (p := p) (A := A) (K := K) (G := G) (P c) (bA c) := by
          simpa [hπ_pairwise, hπ_complete, bA] using
            coordinateNormalizedBrauerBasisDiagonal_visibleResidual_algebraMap_eq
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord P hP_envelope c
    _ = algebraMap A K ((ConjClasses.centralizerPPart p c.1 : A) * a) := by
          simpa [hπ_pairwise, hπ_complete, bA] using ha

end DiagonalPairingReadout

end VisibleReadbackDiagonalSourceCompletionWorker

end Representation
