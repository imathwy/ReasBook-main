import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.Serre18_5ASourceTextRouteWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassRowsReadbackSourceHelper
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.OrthogonalityPointMassSourceProofWorker

/-!
Worker for the Exercise `18.4` point-mass row congruence in the source route for
Serre `18.5(a)`.

The file keeps the route at the source level.  Exercise `18.4` supplies the Brauer-character
`A`-basis of regular class functions; the projective-envelope orthogonality relation
`<Phi_E, phi_E'> = delta_EE'` has already been formalized upstream as the bridge from
projective rows to fixed-coordinate Brauer-basis readback.  The theorem below records that the
requested `exercise18_4PointMassRowCongruenceAPI` is exactly that fixed-coordinate readback
congruence, and that the projective-character lattice source theorem is precisely the remaining
input needed to close it.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalExercise18_4PointMassRowCongruenceProofWorkerASide

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "kA" => IsLocalRing.ResidueField A

local instance exercise18_4PointMassRowCongruenceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance exercise18_4PointMassRowCongruenceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The source API isolated in `Serre18_5ASourceTextRouteWorker` is definitionally the same
entrywise congruence as fixed-coordinate Brauer-basis readback. -/
theorem exercise18_4PointMassRowCongruenceAPI_iff_fixedCoordinateReadback
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    exercise18_4PointMassRowCongruenceAPI
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G) π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord) := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  simpa [exercise18_4PointMassRowCongruenceAPI, hπ_pairwise, hπ_complete] using
    (orthogonalityPairingSumPointMassSourceCongruence_iff_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord)

/-- Convenient name for the fully local Exercise `18.4` row source theorem: every
coordinate-normalized Brauer family satisfies the point-mass row congruence. -/
def exercise18_4PointMassRowCongruenceSourceTheorem : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
      exercise18_4PointMassRowCongruenceAPI
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord

end LocalExercise18_4PointMassRowCongruenceProofWorkerASide

section LocalExercise18_4PointMassRowCongruenceProofWorkerFieldSide

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "kA" => IsLocalRing.ResidueField A

local instance exercise18_4PointMassRowCongruenceProofWorkerFieldFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance exercise18_4PointMassRowCongruenceProofWorkerFieldDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The projective-character lattice source theorem closes the requested fixed-family
Exercise `18.4` point-mass row congruence. -/
theorem exercise18_4PointMassRowCongruenceAPI_of_projectiveCharacter_lattice
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    exercise18_4PointMassRowCongruenceAPI
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  have hread :
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
    brauerBasisFixedCoordinateReadbackDivisibility_of_projectiveCharacter_lattice_rows
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hlattice
  exact
    (exercise18_4PointMassRowCongruenceAPI_iff_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hread

/-- Local theorem form: the projective-character lattice source theorem gives the Exercise
`18.4` row congruence for every coordinate-normalized family. -/
theorem exercise18_4PointMassRowCongruenceSourceTheorem_of_projectiveCharacter_lattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    exercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (A := A) (G := G) := by
  intro π hπ_simple hπ_coord
  exact
    exercise18_4PointMassRowCongruenceAPI_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hlattice

/-- The local Exercise `18.4` row theorem closes the source-text point-mass readback theorem
used in the Serre `18.5(a)` route. -/
theorem serre18_5aSourceTextPointMassReadbackTheorem_of_exercise18_4PointMassRowCongruenceSourceTheorem
    (hsource :
      exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (G := G)) :
    serre18_5aSourceTextPointMassReadbackTheorem
      (p := p) (A := A) (G := G) := by
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := kA) (G := G) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
  exact
    serre18_5aSourceTextPointMassReadbackTheorem_of_exercise18_4PointMassRowCongruenceAPI
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
      (hsource π hπ_simple hπ_coord)

/-- Source route packaged at the current boundary: the projective-character lattice source
  theorem gives the Serre `18.5(a)` point-mass theorem. -/
theorem serre18_5aSourceTextPointMassReadbackTheorem_of_projectiveCharacter_lattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    serre18_5aSourceTextPointMassReadbackTheorem
      (p := p) (A := A) (G := G) :=
  serre18_5aSourceTextPointMassReadbackTheorem_of_exercise18_4PointMassRowCongruenceSourceTheorem
    (p := p) (A := A) (G := G)
    (exercise18_4PointMassRowCongruenceSourceTheorem_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G) hlattice)

end LocalExercise18_4PointMassRowCongruenceProofWorkerFieldSide

section FullMixedExercise18_4PointMassRowCongruenceProofWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedExercise18_4PointMassRowCongruenceProofWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedExercise18_4PointMassRowCongruenceProofWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed source boundary: the current source-text theorem is equivalent to the
projective-character lattice source theorem. -/
theorem fullMixedModelSerre18_5ASourceTextTheorem_iff_projectiveCharacter_lattice :
    fullMixedModelSerre18_5ASourceTextTheorem (p := p) (k := k) (G := G) ↔
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G) :=
  (fullMixedModelSerre18_5ASourceTextTheorem_iff_regularValueSourceStatement
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelRegularValueSourceStatement_iff_projectiveCharacter_lattice_sourceProof
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed provider from the projective-character lattice source theorem to the source-text
point-mass theorem. -/
theorem fullMixedModelSerre18_5ASourceTextTheorem_of_projectiveCharacter_lattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    fullMixedModelSerre18_5ASourceTextTheorem (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hlocal :
      serre18_5aSourceTextPointMassReadbackTheorem
        (p := p) (A := A) (G := G) :=
    serre18_5aSourceTextPointMassReadbackTheorem_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)
  rcases
      (serre18_5aSourceTextPointMassReadbackTheorem_iff_pointwiseReadbackSource
        (p := p) (A := A) (G := G)).1 hlocal with
    ⟨π, hπ_simple, hπ_coord, hpoint⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hpoint

end FullMixedExercise18_4PointMassRowCongruenceProofWorker

end Representation
