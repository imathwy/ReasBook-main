import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.VisibleReadbackSourceLemmaCompletionWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerCharacterPointwiseSourceProofWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerNontrivialCentralizerRowCompletionWorker

/-!
Direct source-side attempt for the visible readback case split.

The attempted unconditional nontrivial-column proof reaches the direct Brauer-character
pointwise source API: the canonical DVR Brauer-basis row opens to the Brauer character row, so
that API would close the requested visible readback nontrivial source lemma by a local rewrite.

No Exercise `18.5(b)`, Cartan cokernel/product/Smith/determinant endpoint, or final range theorem
is used here.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section VisibleReadbackCaseSplitDirectWorker2

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "kA" => IsLocalRing.ResidueField A

local instance visibleReadbackCaseSplitDirectWorker2FintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance visibleReadbackCaseSplitDirectWorker2DecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The exact local row API that closes the nontrivial visible readback source lemma.

This is the point where the direct attempt stops: after opening `canonicalDVRBrauerBasis`,
the remaining goal is precisely the direct Brauer-character pointwise congruence
`coordinateNormalizedBrauerCharacterPointwiseSourceAPI`. -/
theorem exercise18_4PointMassRowVisibleReadbackNontrivialSourceLemma_of_brauerCharacterPointwiseSourceAPI
    (hapi :
      coordinateNormalizedBrauerCharacterPointwiseSourceAPI
        (p := p) (A := A) (G := G)) :
    exercise18_4PointMassRowVisibleReadbackNontrivialSourceLemma
      (p := p) (A := A) (G := G) := by
  classical
  intro π hπ_simple hπ_coord c d _hd
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  rcases hapi π hπ_simple hπ_coord c d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa [brauerCharacterPointwiseReadbackCongruence, canonicalDVRBrauerBasis,
    hπ_pairwise, hπ_complete, bA] using ha

/-- The nontrivial-column Brauer-character API directly closes the nontrivial visible readback
source lemma.  This is the same local rewrite as the full pointwise API, but it keeps the
already-formal `centralizerPPart = 1` columns out of the source boundary. -/
theorem exercise18_4PointMassRowVisibleReadbackNontrivialSourceLemma_of_nontrivialPointwiseReadbackCongruenceAPI
    (hapi :
      coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI
        (p := p) (A := A) (G := G)) :
    exercise18_4PointMassRowVisibleReadbackNontrivialSourceLemma
      (p := p) (A := A) (G := G) := by
  classical
  intro π hπ_simple hπ_coord c d hd
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  rcases hapi π hπ_simple hπ_coord c d hd with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa [coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence,
    canonicalDVRBrauerBasis, hπ_pairwise, hπ_complete, bA] using ha

/-- The nontrivial-column Brauer-character API closes the full visible source lemma, because the
unit-centralizer columns are filled by
`exercise18_4PointMassRowVisibleReadbackSourceLemma_iff_nontrivialSourceLemma`. -/
theorem exercise18_4PointMassRowVisibleReadbackSourceLemma_of_nontrivialPointwiseReadbackCongruenceAPI
    (hapi :
      coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI
        (p := p) (A := A) (G := G)) :
    exercise18_4PointMassRowVisibleReadbackSourceLemma
      (p := p) (A := A) (G := G) :=
  exercise18_4PointMassRowVisibleReadbackSourceLemma_of_nontrivialSourceLemma
    (p := p) (A := A) (G := G)
    (exercise18_4PointMassRowVisibleReadbackNontrivialSourceLemma_of_nontrivialPointwiseReadbackCongruenceAPI
      (p := p) (A := A) (G := G) hapi)

/-- The same nontrivial-column API closes the local Exercise `18.4` point-mass row source
theorem through the visible readback boundary. -/
theorem exercise18_4PointMassRowCongruenceSourceTheorem_of_nontrivialPointwiseReadbackCongruenceAPI
    (hapi :
      coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI
        (p := p) (A := A) (G := G)) :
    exercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (A := A) (G := G) :=
  exercise18_4PointMassRowCongruenceSourceTheorem_of_visibleReadbackNontrivialSourceLemma
    (p := p) (A := A) (G := G)
    (exercise18_4PointMassRowVisibleReadbackNontrivialSourceLemma_of_nontrivialPointwiseReadbackCongruenceAPI
      (p := p) (A := A) (G := G) hapi)

end VisibleReadbackCaseSplitDirectWorker2

end Representation
