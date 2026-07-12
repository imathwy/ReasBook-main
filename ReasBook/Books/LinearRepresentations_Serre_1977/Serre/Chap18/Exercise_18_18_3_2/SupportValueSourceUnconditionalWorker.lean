import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.FinalSourceBlockerEquivalenceWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ResidualFullRepresentativeConstructionCompletionWorker

/-!
Unconditional support/value source audit for Serre `18.5(a)`.

This worker adds no new source hypothesis.  It records the part that is genuinely formal from
the existing definitions: once a point-mass residual row is known to lie in Serre's regular-value
divisibility lattice, the existing API constructs a full class-function representative with the
support and value divisibility properties visible.

It also records the exact full mixed blocker equivalence for the larger target.  Thus an
unconditional proof of the source support/value row API would require the same missing
pointwise readback theorem as the existing Exercise `18.4` source route.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalSupportValueSourceUnconditionalWorker

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

local instance supportValueSourceUnconditionalWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance supportValueSourceUnconditionalWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Support/value construction for a fixed coordinate-normalized point-mass residual row.

This is the strict local construction that the support/value source package needs: from the
honest regular-value divisibility witness for the row, it chooses a full projective
class-function representative, proves that it is zero on the `p`-singular locus, proves the
centralizer-`p`-part value divisibility on the regular locus, and identifies its regular
restriction with the residual row. -/
theorem coordinateNormalizedPointMassResidualSupportValueRepresentative_of_regularValueWitness
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hwitness :
      brauerPointMassRegularValueDivisibilityWitness
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
    (c : PRegularConjClass G p) :
    ∃ Φ : A ⊗R[K](G),
      Φ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) ∧
        (∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0) ∧
        (∀ g : G, IsPRegular p g →
          ∃ a : A, (Φ : G → K) g =
            algebraMap A K ((centralizerPPart p g : A) * a)) ∧
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
        coordinateNormalizedPointMassExplicitResidualRow
          (p := p) (A := A) (K := K) (G := G) π c := by
  exact
    coordinateNormalizedPointMassExplicitResidualRow_fullRepresentative_of_regularValueWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hwitness c

/-- Existential representative form of the support/value row package.

This theorem is the provable local construction behind
`regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows`: it needs only the
regular-value row divisibility witness, and it does not assert any point-mass Brauer character
values. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows_of_regularValueWitness_sourceUnconditional
    (hwitness :
      regularValueCongruenceSourceFaithfulExistsPointMassRegularValueWitness
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassSerreSupportValueRows
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hwitness with ⟨π, hπ_simple, hπ_coord, hwitness⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  intro c
  rcases
      coordinateNormalizedPointMassResidualSupportValueRepresentative_of_regularValueWitness
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord hwitness c with
    ⟨Φ, _hΦ, hzero, hvalue, hres⟩
  exact ⟨Φ, hzero, hvalue, hres⟩

end LocalSupportValueSourceUnconditionalWorker

section FullMixedSupportValueSourceUnconditionalWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedSupportValueSourceUnconditionalWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedSupportValueSourceUnconditionalWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Exact blocker equivalence for target option 1.

The full mixed literal Serre `18.5(a)` support/value row API is equivalent to the direct
Brauer-character pointwise readback congruence.  Therefore an unconditional proof of the target
requires an unconditional proof of this readback theorem. -/
theorem fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI_iff_brauerCharacterPointwiseReadback_sourceUnconditional :
    fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerCharacterPointwiseReadbackCongruence
        (p := p) (k := k) (G := G) :=
  (fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI_iff_orthogonalityPointMassSourceBlocker
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker_iff_brauerCharacterPointwiseReadbackCongruence
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- Exact blocker equivalence for target option 2.

The full mixed Exercise `18.4` point-mass row theorem is the same remaining source obligation as
the direct Brauer-character pointwise readback congruence. -/
theorem fullMixedModelExercise18_4PointMassRowCongruenceSourceTheorem_iff_brauerCharacterPointwiseReadback_sourceUnconditional :
    fullMixedModelExercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerCharacterPointwiseReadbackCongruence
        (p := p) (k := k) (G := G) :=
  (fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI_iff_exercise18_4PointMassRowCongruenceSourceTheorem
    (p := p) (k := k) (G := G)).symm.trans
    (fullMixedModelProjectiveCharacterLatticeSourceTextSupportValueAPI_iff_brauerCharacterPointwiseReadback_sourceUnconditional
      (p := p) (k := k) (G := G))

end FullMixedSupportValueSourceUnconditionalWorker

end Representation
