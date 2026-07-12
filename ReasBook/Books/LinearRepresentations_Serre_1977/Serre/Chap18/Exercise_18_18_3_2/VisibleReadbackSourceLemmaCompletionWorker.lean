import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CanonicalDVRBrauerBasisPointwiseSourceCompletionWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointMassBrauerBasisEntryCongruenceWorker

/-!
Source-side completion boundary for the visible readback lemma.

This worker stays on the Exercise `18.4` canonical DVR Brauer-basis route.  It does not use
`18.5(b)`, Cartan cokernel/product/Smith/determinant endpoints, or any final range theorem.

The unconditional visible source lemma is not available from the current local API.  The sharp
remaining proposition is the same visible row congruence restricted to the columns with nontrivial
centralizer `p`-part; the trivial columns are formal because divisibility by `1` is automatic.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section VisibleReadbackSourceLemmaCompletionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance visibleReadbackSourceLemmaCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance visibleReadbackSourceLemmaCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The exact remaining source-side proposition: prove the visible point-mass row congruence only
in columns whose centralizer `p`-part is nontrivial.  Columns with centralizer `p`-part equal to
`1` are filled formally by divisibility by `1`. -/
def exercise18_4PointMassRowVisibleReadbackNontrivialSourceLemma : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p),
    ConjClasses.centralizerPPart p d.1 ≠ 1 →
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      let bA :=
        canonicalDVRBrauerBasis
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
      ∃ a : A,
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
          (ConjClasses.centralizerPPart p d.1 : A) * a

/-- The universal visible readback source lemma is equivalent to the nontrivial-column version.
This is the sharp local reduction left by the canonical DVR Brauer-basis route. -/
theorem exercise18_4PointMassRowVisibleReadbackSourceLemma_iff_nontrivialSourceLemma :
    exercise18_4PointMassRowVisibleReadbackSourceLemma
        (p := p) (A := A) (G := G) ↔
      exercise18_4PointMassRowVisibleReadbackNontrivialSourceLemma
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hvisible π hπ_simple hπ_coord c d _hd
    exact hvisible π hπ_simple hπ_coord c d
  · intro hnontrivial π hπ_simple hπ_coord
    classical
    intro c d
    by_cases hd : ConjClasses.centralizerPPart p d.1 = 1
    · let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      let bA :=
        canonicalDVRBrauerBasis
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
      refine
        ⟨bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A), ?_⟩
      have hz : (ConjClasses.centralizerPPart p d.1 : A) = 1 := by
        simp [hd]
      change
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
          (ConjClasses.centralizerPPart p d.1 : A) *
            (bA c d -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A))
      simp [hz]
    · exact hnontrivial π hπ_simple hπ_coord c d hd

/-- Forward adapter from the nontrivial-column visible readback lemma to the full visible
source lemma. -/
theorem exercise18_4PointMassRowVisibleReadbackSourceLemma_of_nontrivialSourceLemma
    (h :
      exercise18_4PointMassRowVisibleReadbackNontrivialSourceLemma
        (p := p) (A := A) (G := G)) :
    exercise18_4PointMassRowVisibleReadbackSourceLemma
      (p := p) (A := A) (G := G) :=
  (exercise18_4PointMassRowVisibleReadbackSourceLemma_iff_nontrivialSourceLemma
    (p := p) (A := A) (G := G)).2 h

/-- The visible source lemma is exactly the local Exercise `18.4` point-mass row congruence
source theorem.  This only unfolds the canonical DVR Brauer-basis row congruence into the
existing point-mass API. -/
theorem exercise18_4PointMassRowVisibleReadbackSourceLemma_iff_congruenceSourceTheorem :
    exercise18_4PointMassRowVisibleReadbackSourceLemma
        (p := p) (A := A) (G := G) ↔
      exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hvisible π hπ_simple hπ_coord
    have hpoint :
        let hπ_pairwise :=
          pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord
        let hπ_complete :=
          complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord
        orthogonalityPairingSumPointMassSourceCongruence
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
      orthogonalityPairingSumPointMassSourceCongruence_of_visibleReadbackBasisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord
        (hvisible π hπ_simple hπ_coord)
    simpa [exercise18_4PointMassRowCongruenceAPI] using hpoint
  · intro hsource π hπ_simple hπ_coord
    have hpoint :
        let hπ_pairwise :=
          pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord
        let hπ_complete :=
          complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord
        orthogonalityPairingSumPointMassSourceCongruence
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
      simpa [exercise18_4PointMassRowCongruenceAPI] using
        hsource π hπ_simple hπ_coord
    exact
      visibleReadbackBasisAlgebra_of_orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord hpoint

/-- The nontrivial-column visible readback proposition is sufficient to close the local
Exercise `18.4` row congruence source theorem. -/
theorem exercise18_4PointMassRowCongruenceSourceTheorem_of_visibleReadbackNontrivialSourceLemma
    (h :
      exercise18_4PointMassRowVisibleReadbackNontrivialSourceLemma
        (p := p) (A := A) (G := G)) :
    exercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (A := A) (G := G) :=
  (exercise18_4PointMassRowVisibleReadbackSourceLemma_iff_congruenceSourceTheorem
    (p := p) (A := A) (G := G)).1
    (exercise18_4PointMassRowVisibleReadbackSourceLemma_of_nontrivialSourceLemma
      (p := p) (A := A) (G := G) h)

end VisibleReadbackSourceLemmaCompletionWorker

end Representation
