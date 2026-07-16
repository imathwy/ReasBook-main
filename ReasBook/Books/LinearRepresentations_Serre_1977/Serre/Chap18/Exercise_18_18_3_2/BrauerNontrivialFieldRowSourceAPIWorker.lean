import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerNontrivialCentralizerRowCompletionWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CanonicalBrauerRowTransportWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.Exercise18_4PointMassRowCongruenceProofWorker

/-!
Source-side boundary for the nontrivial-field Brauer row API.

The target `coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI` is not a new
Cartan-side endpoint: after fraction-field transport it is exactly the same source row
congruence as the direct Brauer-character pointwise API, equivalently the Exercise `18.4`
point-mass row congruence plus the already-formalized orthogonality row transport.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerNontrivialFieldRowSourceAPIWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerNontrivialFieldRowSourceAPIWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerNontrivialFieldRowSourceAPIWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The all-column direct Brauer-character source API is equivalent to its nontrivial-column
form.  The omitted columns have `centralizerPPart = 1`, where divisibility is automatic. -/
theorem coordinateNormalizedBrauerCharacterPointwiseSourceAPI_iff_nontrivialReadbackAPI :
    coordinateNormalizedBrauerCharacterPointwiseSourceAPI
        (p := p) (A := A) (G := G) ↔
      coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hapi π hπ_simple hπ_coord
    exact
      (brauerCharacterPointwiseReadbackCongruence_iff_nontrivial
        (p := p) (A := A) (G := G) π).1
        (hapi π hπ_simple hπ_coord)
  · intro hapi π hπ_simple hπ_coord
    exact
      (brauerCharacterPointwiseReadbackCongruence_iff_nontrivial
        (p := p) (A := A) (G := G) π).2
        (hapi π hπ_simple hπ_coord)

omit [CharZero K] in
/-- Exact local boundary: the K-valued nontrivial-field row API is the same source statement as
the direct A-valued Brauer-character pointwise API. -/
theorem coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_iff_pointwiseSourceAPI :
    coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI
        (p := p) (A := A) (K := K) (G := G) ↔
      coordinateNormalizedBrauerCharacterPointwiseSourceAPI
        (p := p) (A := A) (G := G) :=
  (coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI_iff_fieldRowSourceAPI
    (p := p) (A := A) (K := K) (G := G)).symm.trans
    (coordinateNormalizedBrauerCharacterPointwiseSourceAPI_iff_nontrivialReadbackAPI
      (p := p) (A := A) (G := G)).symm

omit [CharZero K] in
/-- A proof of the direct Brauer-character pointwise source API closes the nontrivial-field
row API. -/
theorem coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_of_pointwiseSourceAPI
    (hapi :
      coordinateNormalizedBrauerCharacterPointwiseSourceAPI
        (p := p) (A := A) (G := G)) :
    coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI
      (p := p) (A := A) (K := K) (G := G) :=
  (coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_iff_pointwiseSourceAPI
    (p := p) (A := A) (K := K) (G := G)).2 hapi

omit [CharZero K] in
/-- Fixed-family boundary: the K-valued nontrivial-field row source for `π` is equivalent to
the Exercise `18.4` point-mass row congruence for the same coordinate-normalized family. -/
theorem coordinateNormalizedBrauerCharacterNontrivialFieldRowSource_iff_exercise18_4PointMassRowCongruenceAPI
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerCharacterNontrivialFieldRowSource
        (p := p) (A := A) (K := K) (G := G) π ↔
      exercise18_4PointMassRowCongruenceAPI
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  constructor
  · intro hfield
    have hnontrivial :
        coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence
          (p := p) (A := A) (G := G) π :=
      (coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence_iff_fieldRowSource
        (p := p) (A := A) (K := K) (G := G) π).2 hfield
    have hpoint :
        brauerCharacterPointwiseReadbackCongruence
          (p := p) (A := A) (G := G) π :=
      (brauerCharacterPointwiseReadbackCongruence_iff_nontrivial
        (p := p) (A := A) (G := G) π).2 hnontrivial
    have hsource :
        let hπ_pairwise :=
          pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord
        let hπ_complete :=
          complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord
        orthogonalityPairingSumPointMassSourceCongruence
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
      (orthogonalityPairingSumPointMassSourceCongruence_iff_brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hpoint
    simpa [exercise18_4PointMassRowCongruenceAPI] using hsource
  · intro hsource
    have horth :
        let hπ_pairwise :=
          pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord
        let hπ_complete :=
          complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord
        orthogonalityPairingSumPointMassSourceCongruence
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
      simpa [exercise18_4PointMassRowCongruenceAPI] using hsource
    have hpoint :
        brauerCharacterPointwiseReadbackCongruence
          (p := p) (A := A) (G := G) π :=
      (orthogonalityPairingSumPointMassSourceCongruence_iff_brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 horth
    have hnontrivial :
        coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence
          (p := p) (A := A) (G := G) π :=
      (brauerCharacterPointwiseReadbackCongruence_iff_nontrivial
        (p := p) (A := A) (G := G) π).1 hpoint
    exact
      (coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence_iff_fieldRowSource
        (p := p) (A := A) (K := K) (G := G) π).1 hnontrivial

/-- The direct pointwise source API is exactly the fully local Exercise `18.4` point-mass row
source theorem, after unfolding its orthogonality point-mass row formulation. -/
theorem coordinateNormalizedBrauerCharacterPointwiseSourceAPI_iff_exercise18_4PointMassRowCongruenceSourceTheorem :
    coordinateNormalizedBrauerCharacterPointwiseSourceAPI
        (p := p) (A := A) (G := G) ↔
      exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (G := G) := by
  simpa [exercise18_4PointMassRowCongruenceSourceTheorem,
    exercise18_4PointMassRowCongruenceAPI] using
    (coordinateNormalizedBrauerCharacterPointwiseSourceAPI_iff_all_orthogonalityPointMassSource
      (p := p) (A := A) (G := G))

omit [CharZero K] in
/-- Strongest source-side local form found here: the target nontrivial-field row API is
equivalent to the Exercise `18.4` point-mass row congruence theorem for all
coordinate-normalized Brauer families. -/
theorem coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_iff_exercise18_4PointMassRowCongruenceSourceTheorem :
    coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI
        (p := p) (A := A) (K := K) (G := G) ↔
      exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (G := G) :=
  (coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_iff_pointwiseSourceAPI
    (p := p) (A := A) (K := K) (G := G)).trans
    (coordinateNormalizedBrauerCharacterPointwiseSourceAPI_iff_exercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (A := A) (G := G))

omit [CharZero K] in
/-- In closure form: Exercise `18.4` plus the orthogonality row transport closes
`coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI`. -/
theorem coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_of_exercise18_4PointMassRowCongruenceSourceTheorem
    (hsource :
      exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (G := G)) :
    coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI
      (p := p) (A := A) (K := K) (G := G) :=
  (coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI_iff_exercise18_4PointMassRowCongruenceSourceTheorem
    (p := p) (A := A) (K := K) (G := G)).2 hsource

end BrauerNontrivialFieldRowSourceAPIWorker

end Representation
