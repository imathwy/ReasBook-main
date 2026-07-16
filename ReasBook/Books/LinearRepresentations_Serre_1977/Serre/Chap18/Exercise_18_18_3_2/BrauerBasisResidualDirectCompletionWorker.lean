import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackResidualProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointwiseReadbackDirectProofWorker

/-!
Direct completion frontier for the fixed-family A-side pairing residual.

The Exercise `18.4` Brauer-basis expansion and the projective-envelope pairing
`<Phi_E, phi_E'> = delta_EE'` already identify the subtracted projective row in
`coordinateNormalizedBrauerBasisPairingResidualDivisibility`.  After that identification, the
remaining source-side assertion is exactly the pointwise Brauer-character row congruence

```
  phi_c(d) - delta_cd in centralizerPPart(d) A.
```

This file records that exact frontier in a fixed-family form, with the columns
`centralizerPPart = 1` discharged internally.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerBasisResidualDirectCompletionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerBasisResidualDirectCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisResidualDirectCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Nontrivial-column form of the direct Brauer-character row congruence left after the
Exercise `18.4` pairing row has been subtracted.  The omitted columns have
`centralizerPPart = 1`, where divisibility is automatic. -/
def coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence
    (π : PRegularConjClass G p → FDRep k G) : Prop :=
  ∀ c d : PRegularConjClass G p,
    ConjClasses.centralizerPPart p d.1 ≠ 1 →
      ∃ a : A,
        FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := A) (π c)
            (primeToPRoot_canonicalLift (p := p) (A := A)) d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
            (ConjClasses.centralizerPPart p d.1 : A) * a

/-- The direct Brauer-character row congruence is reduced to the nontrivial centralizer
`p`-part columns. -/
theorem brauerCharacterPointwiseReadbackCongruence_iff_nontrivial
    (π : PRegularConjClass G p → FDRep k G) :
    brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π ↔
      coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π := by
  constructor
  · intro h c d hd
    exact h c d
  · intro h c d
    by_cases hd : ConjClasses.centralizerPPart p d.1 = 1
    · let a : A :=
        FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := A) (π c)
            (primeToPRoot_canonicalLift (p := p) (A := A)) d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
      refine ⟨a, ?_⟩
      have hz : (ConjClasses.centralizerPPart p d.1 : A) = 1 := by
        simp [hd]
      simp [a, hz]
    · exact h c d hd

/-- Exact fixed-family frontier: the A-side pairing residual is equivalent to the direct
Brauer-character row-value congruence.  This composes only the local Exercise `18.4` pairing
readback with the canonical-basis opening lemma; it does not use the Cartan range/cokernel/product
endpoints or the projective-character lattice endpoint. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_brauerCharacterPointwiseReadbackCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π := by
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  have hpair :
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
        brauerBasisFixedCoordinateReadbackDivisibility
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
  have hpoint :
      coordinateNormalizedBrauerBasisPointwiseReadbackSource
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
        brauerBasisFixedCoordinateReadbackDivisibility
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
    coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
  have hchar :
      coordinateNormalizedBrauerBasisPointwiseReadbackSource
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
        brauerCharacterPointwiseReadbackCongruence
          (p := p) (A := A) (G := G) π :=
    coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
  exact hpair.trans (hpoint.symm.trans hchar)

/-- Nontrivial-column version of the exact fixed-family frontier. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_nontrivialBrauerCharacterPointwiseReadbackCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π :=
  (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_brauerCharacterPointwiseReadbackCongruence
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).trans
    (brauerCharacterPointwiseReadbackCongruence_iff_nontrivial
      (p := p) (A := A) (G := G) π)

/-- Conditional completion wrapper for the requested fixed-family residual.

Thus the precise remaining unconditional goal is
`coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence π`, i.e. the
nontrivial centralizer-column row congruence for the actual Brauer characters. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_proof_completion
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hpoint :
      coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_nontrivialBrauerCharacterPointwiseReadbackCongruence
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hpoint

end BrauerBasisResidualDirectCompletionWorker

end Representation
