import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisResidualDirectCompletionWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ExplicitResidualPairingSumWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CanonicalBrauerRowTransportWorker

/-!
Direct completion boundary for the point-mass source congruence.

This file keeps the source route from Serre Exercise `18.5(a)`: Exercise `18.4` supplies the
`A`-basis of regular class functions, and the already-formalized projective-envelope
orthogonality relation `<Phi_E, phi_E'> = delta_EE'` evaluates the visible pairing sums.  After
those two source-side computations, the remaining local input is exactly the nontrivial-column
Brauer-character row congruence.

No Cartan range, cokernel, Smith/product, determinant, or endpoint argument is used here.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section OrthogonalityPairingSumPointMassDirectCompletionWorker

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

local instance orthogonalityPairingSumPointMassDirectCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance orthogonalityPairingSumPointMassDirectCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Source-faithful pairing-sum form of the target for one coordinate-normalized family.

The equivalence is just the direct Serre pairing computation already isolated upstream:
`<Phi_c, phi_d> = delta_cd` converts the displayed pairing sum into the point-mass row
congruence, and fraction-field injectivity descends it back to `A`. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_iff_pairingSumResidual_direct
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete ↔
      orthogonalityPairingSumPointMassResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  exact
    (orthogonalityPairingSumPointMassResidualDivisibility_iff_sourceCongruence
      (p := p) (A := A) (K := K) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope).symm

/-- The exact remaining fixed-family blocker after the Exercise `18.4`/orthogonality pairing
sums have been evaluated.

Equivalently, to prove the point-mass source congruence it is enough and necessary to prove the
nontrivial centralizer-column congruence for the actual canonical Brauer-character rows. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_iff_nontrivialBrauerCharacterRows
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
      coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  exact
    (orthogonalityPairingSumPointMassSourceCongruence_iff_brauerCharacterPointwiseReadbackCongruence
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).trans
      (brauerCharacterPointwiseReadbackCongruence_iff_nontrivial
        (p := p) (A := A) (G := G) π)

/-- Conditional direct completion of the requested source theorem.

This is the strongest source-side completion available without adding an endpoint theorem:
nontrivial-column Brauer-character row divisibility closes
`orthogonalityPairingSumPointMassSourceCongruence` for the same coordinate-normalized family. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_of_nontrivialBrauerCharacterRows
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hrows :
      coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
  (orthogonalityPairingSumPointMassSourceCongruence_iff_nontrivialBrauerCharacterRows
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hrows

/-- If the direct Serre pairing-sum residual is supplied for projective envelopes of the same
coordinate-normalized family, then the point-mass source congruence follows immediately. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_of_pairingSumResidual_direct
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
    (hresidual :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      orthogonalityPairingSumPointMassResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete P) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
  (orthogonalityPairingSumPointMassSourceCongruence_iff_pairingSumResidual_direct
    (p := p) (A := A) (K := K) (G := G)
    π hπ_simple hπ_coord P hP_envelope).2 hresidual

end OrthogonalityPairingSumPointMassDirectCompletionWorker

end Representation
