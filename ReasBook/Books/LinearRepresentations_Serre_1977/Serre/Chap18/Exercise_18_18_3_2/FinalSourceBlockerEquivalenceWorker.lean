import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueSourceStatementSourceWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.OrthogonalityInputSourceProofWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointwiseReadbackDirectProofWorker

/-!
Final source-side blocker equivalences for Exercise `18.5(a)`.

The remaining source obligation can be written in any of the following equivalent forms:
the explicit Serre `18.4` orthogonality input, the fixed-coordinate canonical DVR Brauer-basis
readback, or the direct Brauer-character row congruence.  This file records the equivalence
without using any Cartan cokernel, product, determinant, or final range endpoint.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalFinalSourceBlockerEquivalenceWorker

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

local instance finalSourceBlockerEquivalenceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance finalSourceBlockerEquivalenceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The orthogonality point-mass blocker and the canonical-basis pointwise readback blocker are
the same local source theorem.  The projective-envelope family in the orthogonality blocker is
auxiliary: the row congruence itself does not depend on it. -/
theorem regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker_iff_pointwiseReadbackSource :
    regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hblock
    rcases hblock with ⟨π, hπ_simple, hπ_coord, _P, _hP_envelope, hsource⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    have hread :
        brauerBasisFixedCoordinateReadbackDivisibility
          (p := p) (A := A) (G := G)
          π
          (pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord)
          (complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord) :=
      (orthogonalityPairingSumPointMassSourceCongruence_iff_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hsource
    exact
      (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hread
  · intro hpoint
    rcases hpoint with ⟨π, hπ_simple, hπ_coord, hsource⟩
    have hP_exists :
        ∀ c : PRegularConjClass G p,
          ∃ P : FiniteProjectiveGroupAlgebraModule kA G,
            ∃ f : P.V →ₗ[kA[G]] asModule (π c).ρ, f.IsProjectiveEnvelope := by
      intro c
      letI : Simple (π c) := hπ_simple c
      exact exists_finite_projectiveEnvelope_of_simple_field (G := G) (τ := π c)
    choose P hP_envelope using hP_exists
    refine ⟨π, hπ_simple, hπ_coord, P, hP_envelope, ?_⟩
    have hread :
        brauerBasisFixedCoordinateReadbackDivisibility
          (p := p) (A := A) (G := G)
          π
          (pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord)
          (complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord) :=
      (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hsource
    exact
      (orthogonalityPairingSumPointMassSourceCongruence_iff_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hread

end LocalFinalSourceBlockerEquivalenceWorker

section FullMixedFinalSourceBlockerEquivalenceWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedFinalSourceBlockerEquivalenceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedFinalSourceBlockerEquivalenceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed form: the orthogonality point-mass blocker is exactly the canonical-basis
pointwise readback source. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker_iff_pointwiseReadbackSource :
    fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisPointwiseReadbackSource
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hblock A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker_iff_pointwiseReadbackSource
        (p := p) (A := A) (G := G)).1
        (hblock (A := A) (K := K) e0)
  · intro hpoint A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker_iff_pointwiseReadbackSource
        (p := p) (A := A) (G := G)).2
        (hpoint (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed form with the blocker opened all the way to the direct Brauer-character row
congruence. -/
theorem fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker_iff_brauerCharacterPointwiseReadbackCongruence :
    fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerCharacterPointwiseReadbackCongruence
        (p := p) (k := k) (G := G) :=
  (fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker_iff_pointwiseReadbackSource
    (p := p) (k := k) (G := G)).trans
    (fullMixedModelBrauerBasisPointwiseReadbackSource_sourceProof_iff_brauerCharacterPointwiseReadbackCongruence
      (p := p) (k := k) (G := G))

omit [IsAlgClosed k] [CharP k p] in
/-- The regular-value source statement needed by the non-endpoint Cartan-range adapter is
equivalent to the direct Brauer-character row congruence. -/
theorem fullMixedModelRegularValueSourceStatement_iff_brauerCharacterPointwiseReadbackCongruence_sourceClosure :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerCharacterPointwiseReadbackCongruence
        (p := p) (k := k) (G := G) :=
  (fullMixedModelRegularValueSourceStatement_iff_orthogonalityInput_sourceProof
    (p := p) (k := k) (G := G)).trans
    ((fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityInput_sourceProof_iff_pointMassSourceBlocker
      (p := p) (k := k) (G := G)).trans
      (fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker_iff_brauerCharacterPointwiseReadbackCongruence
        (p := p) (k := k) (G := G)))

omit [IsAlgClosed k] [CharP k p] in
/-- The currently isolated point-mass source blocker closes the regular-value source statement.

This is only a source-boundary adapter: it does not prove the blocker itself.  It keeps the
downstream Cartan range and determinant statements from re-opening the same local mixed model
argument at every use site. -/
theorem fullMixedModelRegularValueSourceStatement_of_pointMassSourceBlocker
    (hsource :
      fullMixedModelBrauerBasisExistsPairingResidualOrthogonalityPointMassSourceBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hlocal :
      regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker
        (p := p) (A := A) (G := G) :=
    hsource (A := A) (K := K) e0
  rcases
      (regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker_iff_pointwiseReadbackSource
        (p := p) (A := A) (G := G)).1 hlocal with
    ⟨π, hπ_simple, hπ_coord, hpoint⟩
  have hread :
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G) := by
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    exact
      (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_fixedCoordinateReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hpoint
  exact
    regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G) hread

end FullMixedFinalSourceBlockerEquivalenceWorker

end Representation
