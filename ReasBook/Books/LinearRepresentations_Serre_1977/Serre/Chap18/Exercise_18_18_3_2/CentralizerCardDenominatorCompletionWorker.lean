import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CentralizerUnitDenominatorWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.Exercise18_4PointMassRowCongruenceProofWorker

/-!
Centralizer-card denominator completion for the Serre `18.5(a)` source route.

The remaining source-side row congruence is

```
  bA c d - delta_cd ∈ centralizerPPart(d) A.
```

This file records the denominator form that is directly aligned with Serre's class-sum
orthogonality relation: if the stronger quotient by the full centralizer order,
`(bA c d - delta_cd) / |C_G(d)|`, is represented by an element of `A`, then the row
congruence follows because the prime-to-`p` part of `|C_G(d)|` is an `A`-unit.

No Cartan cokernel/product/Smith/determinant endpoint is used here.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CentralizerCardDenominatorCompletionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]

local notation "k" => IsLocalRing.ResidueField A

local instance centralizerCardDenominatorCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance centralizerCardDenominatorCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Fixed-family denominator condition for the point-mass row residual.

For every source row `c` and target regular class `d`, the residual
`bA c d - delta_cd`, divided in the fraction field by the full centralizer order
`|C_G(d)|`, is represented by an element of the DVR `A`.

This is the local input expected from the Serre `18.4` basis plus the orthogonality relation
`<Phi_E, phi_E'> = delta_EE'`. -/
def canonicalDVRBrauerBasisCentralizerCardDenominatorCondition
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  ∀ c d : PRegularConjClass G p,
    ∃ coeff : A,
      algebraMap A K coeff =
        algebraMap A K
            (bA c d -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) *
          (algebraMap A K (ConjClasses.centralizerCard d.1 : A))⁻¹

/-- The centralizer-card denominator condition implies the desired point-mass row congruence.

The only denominator cancellation used is that
`|C_G(d)| = centralizerPPart(d) * ordCompl[p] |C_G(d)|`, with the second factor an `A`-unit. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_of_centralizerCardDenominator
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hden :
      canonicalDVRBrauerBasisCentralizerCardDenominatorCondition
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
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
  change
    ∀ c d : PRegularConjClass G p,
      ∃ a : A,
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
          (ConjClasses.centralizerPPart p d.1 : A) * a
  intro c d
  let rowDiff : A :=
    bA c d - ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
  rcases hden c d with ⟨coeff, hcoeff⟩
  have hcoeff' :
      algebraMap A K coeff =
        algebraMap A K rowDiff *
          (algebraMap A K (ConjClasses.centralizerCard d.1 : A))⁻¹ := by
    simpa [canonicalDVRBrauerBasisCentralizerCardDenominatorCondition,
      hπ_pairwise, hπ_complete, bA, rowDiff] using hcoeff
  simpa [rowDiff] using
    exists_eq_centralizerPPart_mul_of_pairingCoefficient_eq_mul_centralizerCard_inv
      (p := p) (A := A) (K := K) (G := G)
      d (rowDiff := rowDiff) (coeff := coeff) hcoeff'

/-- Conversely, the row congruence gives the centralizer-card denominator condition.

This packages the same local obstruction as an equivalence: after the row residual is a
`centralizerPPart(d)`-multiple, dividing by `|C_G(d)|` only divides by the prime-to-`p`
unit factor. -/
theorem centralizerCardDenominator_of_orthogonalityPairingSumPointMassSourceCongruence
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
    canonicalDVRBrauerBasisCentralizerCardDenominatorCondition
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
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
  change
    ∀ c d : PRegularConjClass G p,
      ∃ coeff : A,
        algebraMap A K coeff =
          algebraMap A K
              (bA c d -
                ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) *
            (algebraMap A K (ConjClasses.centralizerCard d.1 : A))⁻¹
  intro c d
  let rowDiff : A :=
    bA c d - ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
  let zA : A := ConjClasses.centralizerPPart p d.1
  let uA : Aˣ := centralizerPrimeToPUnit (p := p) (A := A) (G := G) d
  rcases hsource c d with ⟨a, ha⟩
  have ha' : rowDiff = zA * a := by
    simpa [orthogonalityPairingSumPointMassSourceCongruence,
      hπ_pairwise, hπ_complete, bA, rowDiff, zA, canonicalDVRBrauerBasis] using ha
  refine ⟨(((uA⁻¹ : Aˣ) : A) * a), ?_⟩
  have hcard_ne :
      algebraMap A K (ConjClasses.centralizerCard d.1 : A) ≠ 0 :=
    algebraMap_centralizerCard_ne_zero (p := p) (A := A) (K := K) (G := G) d
  apply (mul_right_injective₀ hcard_ne)
  have hcard :
      (ConjClasses.centralizerCard d.1 : A) = zA * ((uA : Aˣ) : A) := by
    simpa [zA, uA] using
      centralizerCard_natCast_eq_centralizerPPart_mul_primeToPUnit
        (p := p) (A := A) (G := G) d
  have hu :
      algebraMap A K (((uA⁻¹ : Aˣ) : A)) *
          algebraMap A K (((uA : Aˣ) : A)) =
        1 := by
    simp
  have hcoeff_mul_card :
      algebraMap A K (((uA⁻¹ : Aˣ) : A) * a) *
        algebraMap A K (ConjClasses.centralizerCard d.1 : A)
        = algebraMap A K rowDiff := by
    calc
      algebraMap A K (((uA⁻¹ : Aˣ) : A) * a) *
          algebraMap A K (ConjClasses.centralizerCard d.1 : A)
          =
            (algebraMap A K (((uA⁻¹ : Aˣ) : A)) * algebraMap A K a) *
              (algebraMap A K zA * algebraMap A K (((uA : Aˣ) : A))) := by
              rw [hcard]
              simp [map_mul]
      _ = algebraMap A K zA * algebraMap A K a := by
            calc
              (algebraMap A K (((uA⁻¹ : Aˣ) : A)) * algebraMap A K a) *
                  (algebraMap A K zA * algebraMap A K (((uA : Aˣ) : A)))
                  =
                    (algebraMap A K zA * algebraMap A K a) *
                      (algebraMap A K (((uA⁻¹ : Aˣ) : A)) *
                        algebraMap A K (((uA : Aˣ) : A))) := by
                      ring
              _ = algebraMap A K zA * algebraMap A K a := by
                    rw [hu]
                    ring
      _ = algebraMap A K rowDiff := by
            rw [ha']
            simp [map_mul, zA]
  calc
    algebraMap A K (ConjClasses.centralizerCard d.1 : A) *
        algebraMap A K (((uA⁻¹ : Aˣ) : A) * a)
        = algebraMap A K (((uA⁻¹ : Aˣ) : A) * a) *
            algebraMap A K (ConjClasses.centralizerCard d.1 : A) := by
          ring
    _ = algebraMap A K rowDiff := hcoeff_mul_card
    _ =
        algebraMap A K (ConjClasses.centralizerCard d.1 : A) *
          (algebraMap A K rowDiff *
            (algebraMap A K (ConjClasses.centralizerCard d.1 : A))⁻¹) := by
          field_simp [hcard_ne]

/-- The fixed-family denominator condition is exactly the point-mass source congruence. -/
theorem centralizerCardDenominator_iff_orthogonalityPairingSumPointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    canonicalDVRBrauerBasisCentralizerCardDenominatorCondition
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ↔
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  constructor
  · exact
      orthogonalityPairingSumPointMassSourceCongruence_of_centralizerCardDenominator
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  · exact
      centralizerCardDenominator_of_orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

/-- Denominator condition adapter for the local `exercise18_4PointMassRowCongruenceAPI`. -/
theorem exercise18_4PointMassRowCongruenceAPI_of_centralizerCardDenominator
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hden :
      canonicalDVRBrauerBasisCentralizerCardDenominatorCondition
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    exercise18_4PointMassRowCongruenceAPI
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  have hsource :=
    orthogonalityPairingSumPointMassSourceCongruence_of_centralizerCardDenominator
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hden
  simpa [exercise18_4PointMassRowCongruenceAPI] using hsource

/-- Global source theorem form of the centralizer-card denominator blocker. -/
def exercise18_4PointMassRowCentralizerCardDenominatorSourceTheorem : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
      canonicalDVRBrauerBasisCentralizerCardDenominatorCondition
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

/-- The global centralizer-card denominator blocker closes the requested Exercise `18.4`
point-mass row source theorem. -/
theorem exercise18_4PointMassRowCongruenceSourceTheorem_of_centralizerCardDenominatorSourceTheorem
    (hden :
      exercise18_4PointMassRowCentralizerCardDenominatorSourceTheorem
        (p := p) (A := A) (K := K) (G := G)) :
    exercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (A := A) (G := G) := by
  intro π hπ_simple hπ_coord
  exact
    exercise18_4PointMassRowCongruenceAPI_of_centralizerCardDenominator
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord (hden π hπ_simple hπ_coord)

/-- Equivalence form: the denominator blocker is neither weaker nor stronger than the already
isolated point-mass source theorem; it is the same local obstruction with the prime-to-`p`
centralizer factor displayed as a unit denominator. -/
theorem exercise18_4PointMassRowCongruenceSourceTheorem_iff_centralizerCardDenominatorSourceTheorem :
    exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (G := G) ↔
      exercise18_4PointMassRowCentralizerCardDenominatorSourceTheorem
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
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
      centralizerCardDenominator_of_orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hpoint
  · exact
      exercise18_4PointMassRowCongruenceSourceTheorem_of_centralizerCardDenominatorSourceTheorem
        (p := p) (A := A) (K := K) (G := G)

end CentralizerCardDenominatorCompletionWorker

end Representation
