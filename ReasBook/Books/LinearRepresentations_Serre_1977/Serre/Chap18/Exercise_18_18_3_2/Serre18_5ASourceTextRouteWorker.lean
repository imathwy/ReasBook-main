import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.FinalSourceBlockerEquivalenceWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.Serre18_5ASupportValueCriterionWorker

/-!
Source-text route for Serre Exercise `18.5(a)`.

This file stays on the original source side: class functions supported on the `p`-regular
locus, value divisibility by the `p`-part of the centralizer, and the Exercise `18.4`
orthogonality point-mass row congruence.  It does not use Cartan cokernel/product/range
endpoints to recover source-side input.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalSerre18_5ASourceTextRouteWorker

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

local instance serre18_5ASourceTextRouteWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance serre18_5ASourceTextRouteWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Literal support/value form of Serre `18.5(a)`: a full class function is in the
projective-character lattice exactly when it vanishes off the `p`-regular locus and its
`p`-regular values are divisible by the centralizer `p`-part. -/
def serre18_5aSourceTextSupportValueCriterion : Prop :=
  ∀ Φ : A ⊗R[K](G),
    Φ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) ↔
      (∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0) ∧
        ∀ g : G, IsPRegular p g →
          ∃ a : A, (Φ : G → K) g =
            algebraMap A K ((centralizerPPart p g : A) * a)

/-- The source-text support/value criterion is already available from the non-endpoint
Exercise `18.5(a)` support/value API. -/
theorem serre18_5aSourceTextSupportValueCriterion_holds :
    serre18_5aSourceTextSupportValueCriterion (p := p) (A := A) (K := K) (G := G) := by
  intro Φ
  exact
    mem_projectiveCharacterSubmodule_iff_serre18_5a_rhs_of_enoughRoots
      (p := p) (A := A) (K := K) (G := G) Φ

/-- The Exercise `18.4` point-mass row congruence still missing at the local source frontier.

After the visible projective-envelope pairings are evaluated, this is the exact remaining row
congruence
`bA c d = delta_cd mod centralizerPPart(d)` for one coordinate-normalized Brauer family. -/
def exercise18_4PointMassRowCongruenceAPI
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  orthogonalityPairingSumPointMassSourceCongruence
    (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete

/-- Source-text theorem at the current blocker: Serre `18.5(a)` reduced through Exercise `18.4`
and the orthogonality relation `<Phi_E, phi_E'> = delta_EE'`. -/
def serre18_5aSourceTextPointMassReadbackTheorem : Prop :=
  regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker
    (p := p) (A := A) (G := G)

/-- The named source-text theorem is exactly the currently isolated pointwise readback source. -/
theorem serre18_5aSourceTextPointMassReadbackTheorem_iff_pointwiseReadbackSource :
    serre18_5aSourceTextPointMassReadbackTheorem
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulBrauerBasisPointwiseReadbackSource
        (p := p) (A := A) (G := G) :=
  regularValueCongruenceSourceFaithfulOrthogonalityPointMassSourceBlocker_iff_pointwiseReadbackSource
    (p := p) (A := A) (G := G)

/-- A proof of the missing local Exercise `18.4` point-mass row congruence for one normalized
family closes the source-text point-mass theorem. -/
theorem serre18_5aSourceTextPointMassReadbackTheorem_of_exercise18_4PointMassRowCongruenceAPI
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hapi :
      exercise18_4PointMassRowCongruenceAPI
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    serre18_5aSourceTextPointMassReadbackTheorem
      (p := p) (A := A) (G := G) := by
  have hP_exists :
      ∀ c : PRegularConjClass G p,
        ∃ P : FiniteProjectiveGroupAlgebraModule kA G,
          ∃ f : P.V →ₗ[kA[G]] asModule (π c).ρ, f.IsProjectiveEnvelope := by
    intro c
    letI : Simple (π c) := hπ_simple c
    exact exists_finite_projectiveEnvelope_of_simple_field (G := G) (τ := π c)
  choose P hP_envelope using hP_exists
  exact ⟨π, hπ_simple, hπ_coord, P, hP_envelope, hapi⟩

/-- Equivalently, the current source-text point-mass theorem is the existence of one
coordinate-normalized family satisfying the missing Exercise `18.4` point-mass row API. -/
theorem serre18_5aSourceTextPointMassReadbackTheorem_iff_exists_exercise18_4PointMassRowCongruenceAPI :
    serre18_5aSourceTextPointMassReadbackTheorem
        (p := p) (A := A) (G := G) ↔
      ∃ π : PRegularConjClass G p → FDRep kA G,
        ∃ hπ_simple : ∀ c, Simple (π c),
          ∃ hπ_coord :
            (∀ c : PRegularConjClass G p,
              regularClassCoordinateAddEquiv
                  (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
            exercise18_4PointMassRowCongruenceAPI
              (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  constructor
  · intro hsource
    rcases hsource with ⟨π, hπ_simple, hπ_coord, _P, _hP_envelope, hapi⟩
    exact ⟨π, hπ_simple, hπ_coord, hapi⟩
  · rintro ⟨π, hπ_simple, hπ_coord, hapi⟩
    exact
      serre18_5aSourceTextPointMassReadbackTheorem_of_exercise18_4PointMassRowCongruenceAPI
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord hapi

end LocalSerre18_5ASourceTextRouteWorker

section FullMixedSerre18_5ASourceTextRouteWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedSerre18_5ASourceTextRouteWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedSerre18_5ASourceTextRouteWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model package of the source-text theorem at the regular-value source boundary. -/
def fullMixedModelSerre18_5ASourceTextTheorem : Prop :=
  fullMixedModelBrauerCharacterPointwiseReadbackCongruence (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The source-text theorem is exactly the direct Brauer-character pointwise readback statement. -/
theorem fullMixedModelSerre18_5ASourceTextTheorem_iff_brauerCharacterPointwiseReadbackCongruence :
    fullMixedModelSerre18_5ASourceTextTheorem (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerCharacterPointwiseReadbackCongruence
        (p := p) (k := k) (G := G) :=
  Iff.rfl

omit [IsAlgClosed k] [CharP k p] in
/-- The same source-text theorem is equivalent to the regular-value source statement used by the
non-endpoint source route. -/
theorem fullMixedModelSerre18_5ASourceTextTheorem_iff_regularValueSourceStatement :
    fullMixedModelSerre18_5ASourceTextTheorem (p := p) (k := k) (G := G) ↔
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) :=
  (fullMixedModelRegularValueSourceStatement_iff_brauerCharacterPointwiseReadbackCongruence_sourceClosure
    (p := p) (k := k) (G := G)).symm

omit [IsAlgClosed k] [CharP k p] in
/-- Source boundary for Serre `18.5(a)`/`18.5(b)` at the regular-value source route. -/
theorem fullMixedModelSerre18_5ASourceTextTheorem_source
    (hsource :
      fullMixedModelSerre18_5ASourceTextTheorem
        (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement
      (p := p) (k := k) (G := G) :=
  by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    rcases hsource (A := A) (K := K) e0 with
      ⟨π, hπ_simple, hπ_coord, hpoint⟩
    have hsourcePoint :
        coordinateNormalizedBrauerBasisPointwiseReadbackSource
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
      (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hpoint
    have hread :
        regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
          (p := p) (A := A) (G := G) := by
      refine ⟨π, hπ_simple, hπ_coord, ?_⟩
      exact
        (coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_fixedCoordinateReadback
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hsourcePoint
    exact
      regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G) hread

omit [IsAlgClosed k] [CharP k p] in
/-- Entailment form for the current regular-value blocker. -/
theorem fullMixedModelRegularValueSourceStatement_of_serre18_5ASourceTextTheorem :
    fullMixedModelSerre18_5ASourceTextTheorem (p := p) (k := k) (G := G) →
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) :=
  (fullMixedModelSerre18_5ASourceTextTheorem_iff_regularValueSourceStatement
    (p := p) (k := k) (G := G)).mp

omit [IsAlgClosed k] [CharP k p] in
/-- Entailment form for the direct Brauer-character pointwise readback blocker. -/
theorem fullMixedModelBrauerCharacterPointwiseReadbackCongruence_of_serre18_5ASourceTextTheorem :
    fullMixedModelSerre18_5ASourceTextTheorem (p := p) (k := k) (G := G) →
      fullMixedModelBrauerCharacterPointwiseReadbackCongruence (p := p) (k := k) (G := G) :=
  (fullMixedModelSerre18_5ASourceTextTheorem_iff_brauerCharacterPointwiseReadbackCongruence
    (p := p) (k := k) (G := G)).mp

end FullMixedSerre18_5ASourceTextRouteWorker

end Representation
