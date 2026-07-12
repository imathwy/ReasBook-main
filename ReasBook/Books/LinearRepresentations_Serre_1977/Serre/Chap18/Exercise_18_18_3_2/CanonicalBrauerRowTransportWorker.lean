import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerCharacterPointwiseSourceProofWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisCoordinateDefinitionAuditWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointMassBrauerBasisEntryCongruenceWorker

/-!
Canonical Brauer row transport worker.

This file only transports the same pointwise row congruence between its current names:

* the direct Brauer-character row statement using
  `FDRep.modularCharacterOnPRegularConjClass ... primeToPRoot_canonicalLift`;
* the Exercise `18.4`/orthogonality point-mass row statement;
* the canonical DVR Brauer-basis fixed-coordinate/readback statements.

It does not prove the representation-theoretic divisibility itself and does not use Cartan
range, cokernel, product, determinant, or final endpoint theorems.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalCanonicalBrauerRowTransportWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance canonicalBrauerRowTransportWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance canonicalBrauerRowTransportWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Row-level canonical-lift transport: the canonical DVR Brauer-basis row is exactly the
Brauer character evaluated with `primeToPRoot_canonicalLift`. -/
theorem canonicalDVRBrauerBasis_row_eq_modularCharacterOnPRegularConjClass_canonicalLift
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (c : PRegularConjClass G p) :
    canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete c =
      FDRep.modularCharacterOnPRegularConjClass
        (p := p) (G := G) (A := A) (π c)
        (primeToPRoot_canonicalLift (p := p) (A := A)) :=
  canonicalDVRBrauerBasis_apply_eq_modularCharacterOnPRegularConjClass
    (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete c

/-- Fixed-coordinate readback is the same fixed-family statement as the coordinate-normalized
pointwise readback source. -/
theorem fixedCoordinateReadbackDivisibility_iff_coordinateNormalizedBrauerBasisPointwiseReadbackSource
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete ↔
      coordinateNormalizedBrauerBasisPointwiseReadbackSource
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  exact
    (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).symm

/-- The orthogonality point-mass row congruence is the same fixed-family statement as the
coordinate-normalized pointwise readback source. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_iff_coordinateNormalizedBrauerBasisPointwiseReadbackSource
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete ↔
      coordinateNormalizedBrauerBasisPointwiseReadbackSource
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  exact
    (orthogonalityPairingSumPointMassSourceCongruence_iff_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).trans
      (fixedCoordinateReadbackDivisibility_iff_coordinateNormalizedBrauerBasisPointwiseReadbackSource
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)

/-- The orthogonality point-mass row congruence is exactly the direct Brauer-character row
congruence after opening `canonicalDVRBrauerBasis` and the canonical lift. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_iff_brauerCharacterPointwiseReadbackCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete ↔
      brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π := by
  exact
    (orthogonalityPairingSumPointMassSourceCongruence_iff_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).trans
      (fixedCoordinateReadbackDivisibility_iff_brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)

/-- Reverse orientation of the fixed-family row transport equivalence. -/
theorem brauerCharacterPointwiseReadbackCongruence_iff_orthogonalityPairingSumPointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π ↔
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  exact
    (orthogonalityPairingSumPointMassSourceCongruence_iff_brauerCharacterPointwiseReadbackCongruence
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).symm

/-- Short adapter from the direct Brauer-character row theorem to the orthogonality
point-mass row theorem. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_of_brauerCharacterPointwiseReadbackCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hrow :
      brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
  (brauerCharacterPointwiseReadbackCongruence_iff_orthogonalityPairingSumPointMassSourceCongruence
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hrow

/-- Short adapter from the orthogonality point-mass row theorem to the direct
Brauer-character row theorem. -/
theorem brauerCharacterPointwiseReadbackCongruence_of_orthogonalityPairingSumPointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hsource :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete) :
    brauerCharacterPointwiseReadbackCongruence
      (p := p) (A := A) (G := G) π :=
  (brauerCharacterPointwiseReadbackCongruence_iff_orthogonalityPairingSumPointMassSourceCongruence
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hsource

/-- Short adapter from the orthogonality point-mass row theorem to fixed-coordinate readback. -/
theorem fixedCoordinateReadbackDivisibility_of_orthogonalityPairingSumPointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hsource :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
  (orthogonalityPairingSumPointMassSourceCongruence_iff_fixedCoordinateReadback
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hsource

/-- Short adapter from fixed-coordinate readback to the orthogonality point-mass row theorem. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_of_fixedCoordinateReadbackDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hfixed :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
  (orthogonalityPairingSumPointMassSourceCongruence_iff_fixedCoordinateReadback
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hfixed

/-- Short adapter from the orthogonality point-mass row theorem to the named pointwise source. -/
theorem coordinateNormalizedBrauerBasisPointwiseReadbackSource_of_orthogonalityPairingSumPointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hsource :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete) :
    coordinateNormalizedBrauerBasisPointwiseReadbackSource
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  (orthogonalityPairingSumPointMassSourceCongruence_iff_coordinateNormalizedBrauerBasisPointwiseReadbackSource
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hsource

/-- Short adapter from the named pointwise source to the orthogonality point-mass row theorem. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_of_coordinateNormalizedBrauerBasisPointwiseReadbackSource
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hpoint :
      coordinateNormalizedBrauerBasisPointwiseReadbackSource
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
  (orthogonalityPairingSumPointMassSourceCongruence_iff_coordinateNormalizedBrauerBasisPointwiseReadbackSource
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hpoint

/-- Short adapter from direct Brauer-character rows to fixed-coordinate readback. -/
theorem fixedCoordinateReadbackDivisibility_of_brauerCharacterPointwiseReadbackCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hrow :
      brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    brauerBasisFixedCoordinateReadbackDivisibility
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
  (fixedCoordinateReadbackDivisibility_iff_brauerCharacterPointwiseReadbackCongruence
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hrow

/-- Short adapter from fixed-coordinate readback to direct Brauer-character rows. -/
theorem brauerCharacterPointwiseReadbackCongruence_of_fixedCoordinateReadbackDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hfixed :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete) :
    brauerCharacterPointwiseReadbackCongruence
      (p := p) (A := A) (G := G) π :=
  (fixedCoordinateReadbackDivisibility_iff_brauerCharacterPointwiseReadbackCongruence
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hfixed

/-- Global/local API form: the direct Brauer-character API is equivalent to proving the
fixed-coordinate readback theorem for every coordinate-normalized family. -/
theorem coordinateNormalizedBrauerCharacterPointwiseSourceAPI_iff_all_fixedCoordinateReadback
    :
    coordinateNormalizedBrauerCharacterPointwiseSourceAPI
        (p := p) (A := A) (G := G) ↔
      ∀ (π : PRegularConjClass G p → FDRep k G)
        (hπ_simple : ∀ c, Simple (π c))
        (hπ_coord :
          ∀ c,
            regularClassCoordinateAddEquiv
                (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
        brauerBasisFixedCoordinateReadbackDivisibility
          (p := p) (A := A) (G := G)
          π
          (pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord)
          (complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord) := by
  constructor
  · intro hapi π hπ_simple hπ_coord
    exact
      (fixedCoordinateReadbackDivisibility_iff_brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2
        (hapi π hπ_simple hπ_coord)
  · intro hfixed π hπ_simple hπ_coord
    exact
      (fixedCoordinateReadbackDivisibility_iff_brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
        (hfixed π hπ_simple hπ_coord)

/-- Global/local API form: the direct Brauer-character API is equivalent to proving the named
coordinate-normalized pointwise readback source for every coordinate-normalized family. -/
theorem coordinateNormalizedBrauerCharacterPointwiseSourceAPI_iff_all_coordinateNormalizedBrauerBasisPointwiseReadbackSource
    :
    coordinateNormalizedBrauerCharacterPointwiseSourceAPI
        (p := p) (A := A) (G := G) ↔
      ∀ (π : PRegularConjClass G p → FDRep k G)
        (hπ_simple : ∀ c, Simple (π c))
        (hπ_coord :
          ∀ c,
            regularClassCoordinateAddEquiv
                (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
        coordinateNormalizedBrauerBasisPointwiseReadbackSource
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  coordinateNormalizedBrauerCharacterPointwiseSourceAPI_iff_all_pointwiseReadbackSource
    (p := p) (A := A) (G := G)

/-- Global/local API form: the direct Brauer-character API is equivalent to proving the
orthogonality point-mass source congruence for every coordinate-normalized family. -/
theorem coordinateNormalizedBrauerCharacterPointwiseSourceAPI_iff_all_orthogonalityPointMassSource
    :
    coordinateNormalizedBrauerCharacterPointwiseSourceAPI
        (p := p) (A := A) (G := G) ↔
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
        orthogonalityPairingSumPointMassSourceCongruence
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  constructor
  · intro hapi π hπ_simple hπ_coord
    exact
      (orthogonalityPairingSumPointMassSourceCongruence_iff_brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2
        (hapi π hπ_simple hπ_coord)
  · intro hsource π hπ_simple hπ_coord
    exact
      (orthogonalityPairingSumPointMassSourceCongruence_iff_brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
        (hsource π hπ_simple hπ_coord)

/-- The exact remaining local source API after all canonical-lift and row-transport issues have
been removed.  Any one of the equivalent theorems above proves this, and this proves all of
them. -/
def canonicalBrauerRowTransportRemainingAPI : Prop :=
  coordinateNormalizedBrauerCharacterPointwiseSourceAPI
    (p := p) (A := A) (G := G)

theorem canonicalBrauerRowTransportRemainingAPI_iff_all_fixedCoordinateReadback
    :
    canonicalBrauerRowTransportRemainingAPI
        (p := p) (A := A) (G := G) ↔
      ∀ (π : PRegularConjClass G p → FDRep k G)
        (hπ_simple : ∀ c, Simple (π c))
        (hπ_coord :
          ∀ c,
            regularClassCoordinateAddEquiv
                (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
        brauerBasisFixedCoordinateReadbackDivisibility
          (p := p) (A := A) (G := G)
          π
          (pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord)
          (complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord) := by
  simpa [canonicalBrauerRowTransportRemainingAPI] using
    (coordinateNormalizedBrauerCharacterPointwiseSourceAPI_iff_all_fixedCoordinateReadback
      (p := p) (A := A) (G := G))

theorem canonicalBrauerRowTransportRemainingAPI_iff_all_pointwiseReadbackSource
    :
    canonicalBrauerRowTransportRemainingAPI
        (p := p) (A := A) (G := G) ↔
      ∀ (π : PRegularConjClass G p → FDRep k G)
        (hπ_simple : ∀ c, Simple (π c))
        (hπ_coord :
          ∀ c,
            regularClassCoordinateAddEquiv
                (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
        coordinateNormalizedBrauerBasisPointwiseReadbackSource
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  simpa [canonicalBrauerRowTransportRemainingAPI] using
    (coordinateNormalizedBrauerCharacterPointwiseSourceAPI_iff_all_coordinateNormalizedBrauerBasisPointwiseReadbackSource
      (p := p) (A := A) (G := G))

theorem canonicalBrauerRowTransportRemainingAPI_iff_all_orthogonalityPointMassSource
    :
    canonicalBrauerRowTransportRemainingAPI
        (p := p) (A := A) (G := G) ↔
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
        orthogonalityPairingSumPointMassSourceCongruence
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  simpa [canonicalBrauerRowTransportRemainingAPI] using
    (coordinateNormalizedBrauerCharacterPointwiseSourceAPI_iff_all_orthogonalityPointMassSource
      (p := p) (A := A) (G := G))

end LocalCanonicalBrauerRowTransportWorker

end Representation
