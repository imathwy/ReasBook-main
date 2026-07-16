import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.Exercise18_4PointMassRowSourceProofWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ExplicitResidualBasisAlgebraWorker

/-!
Definition-level completion for the canonical DVR Brauer-basis pointwise source residual.

The residual in `exercise18_4PointMassRowNontrivialPointwiseResidualSourceLemma` differs from
the visible point-mass row congruence
`bA c d - delta_cd = centralizerPPart(d) * a` by the already displayed multiple
`centralizerPPart(d) * bA.repr (primeToP_regular_indicator d⁻¹) c`.

This file records that exact A-side arithmetic equivalence.  It does not use any Cartan range,
cokernel, product, Smith, determinant, or downstream endpoint.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CanonicalDVRBrauerBasisPointwiseSourceCompletionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "kA" => IsLocalRing.ResidueField A

local instance canonicalDVRBrauerBasisPointwiseSourceCompletionFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance canonicalDVRBrauerBasisPointwiseSourceCompletionDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Fixed-family A-side arithmetic: the nontrivial pointwise residual is exactly the visible
point-mass row congruence.  The forward direction adds back the displayed
`centralizerPPart * repr` term; the reverse direction subtracts it. -/
theorem coordinateNormalizedBrauerBasisNontrivialPointwiseResidual_iff_visibleReadbackBasisAlgebra
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisNontrivialPointwiseResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
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
  constructor
  · intro hpoint c d
    let z : A := ConjClasses.centralizerPPart p d.1
    let delta : A := ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
    by_cases hd : ConjClasses.centralizerPPart p d.1 = 1
    · refine ⟨bA c d - delta, ?_⟩
      have hz : z = 1 := by
        simp [z, hd]
      change bA c d - delta = z * (bA c d - delta)
      simp [hz]
    · let coeff : A :=
        (bA.repr
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G)
            (inversePRegularConjClass (p := p) d)) c)
      rcases hpoint c d hd with ⟨a, ha⟩
      refine ⟨a + coeff, ?_⟩
      have ha' : bA c d - delta - z * coeff = z * a := by
        simpa [coordinateNormalizedBrauerBasisNontrivialPointwiseResidual,
          hπ_pairwise, hπ_complete, bA, z, delta, coeff] using ha
      calc
        bA c d - delta =
            (bA c d - delta - z * coeff) + z * coeff := by
              ring
        _ = z * a + z * coeff := by
              rw [ha']
        _ = z * (a + coeff) := by
              rw [mul_add]
  · intro hvisible c d hd
    let z : A := ConjClasses.centralizerPPart p d.1
    let delta : A := ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
    let coeff : A :=
      (bA.repr
        (primeToP_regular_indicator
          (p := p) (A := A) (G := G)
          (inversePRegularConjClass (p := p) d)) c)
    rcases hvisible c d with ⟨a, ha⟩
    refine ⟨a - coeff, ?_⟩
    have ha' : bA c d - delta = z * a := by
      simpa [coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra,
        hπ_pairwise, hπ_complete, bA, z, delta] using ha
    calc
      bA c d - delta - z * coeff =
          z * a - z * coeff := by
            rw [ha']
      _ = z * (a - coeff) := by
            rw [mul_sub]

/-- Universal visible point-mass row congruence, stated without any projective-envelope or
downstream Cartan endpoint data. -/
def exercise18_4PointMassRowVisibleReadbackSourceLemma : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- The requested nontrivial residual source lemma is equivalent to the smaller visible
point-mass row congruence at the canonical DVR Brauer-basis definition layer. -/
theorem exercise18_4PointMassRowNontrivialPointwiseResidualSourceLemma_iff_visibleReadbackSourceLemma :
    exercise18_4PointMassRowNontrivialPointwiseResidualSourceLemma
        (p := p) (A := A) (G := G) ↔
      exercise18_4PointMassRowVisibleReadbackSourceLemma
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hpoint π hπ_simple hπ_coord
    exact
      (coordinateNormalizedBrauerBasisNontrivialPointwiseResidual_iff_visibleReadbackBasisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
        (hpoint π hπ_simple hπ_coord)
  · intro hvisible π hπ_simple hπ_coord
    exact
      (coordinateNormalizedBrauerBasisNontrivialPointwiseResidual_iff_visibleReadbackBasisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2
        (hvisible π hπ_simple hπ_coord)

/-- Forward adapter: proving the smaller visible point-mass row congruence closes
`exercise18_4PointMassRowNontrivialPointwiseResidualSourceLemma`. -/
theorem exercise18_4PointMassRowNontrivialPointwiseResidualSourceLemma_of_visibleReadbackSourceLemma
    (hvisible :
      exercise18_4PointMassRowVisibleReadbackSourceLemma
        (p := p) (A := A) (G := G)) :
    exercise18_4PointMassRowNontrivialPointwiseResidualSourceLemma
      (p := p) (A := A) (G := G) :=
  (exercise18_4PointMassRowNontrivialPointwiseResidualSourceLemma_iff_visibleReadbackSourceLemma
    (p := p) (A := A) (G := G)).2 hvisible

end CanonicalDVRBrauerBasisPointwiseSourceCompletionWorker

end Representation
