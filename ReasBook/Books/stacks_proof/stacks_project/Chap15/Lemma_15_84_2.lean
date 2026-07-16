import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_6_1
import stacks_proof.stacks_project.Chap15.Definition_15_84_1
import stacks_proof.stacks_project.Chap15.Lemma_15_65_6
import stacks_proof.stacks_project.Chap15.Lemma_15_67_5
import stacks_proof.stacks_project.Chap15.Lemma_15_67_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling for Lemma 15.84.2:
- primary domain: triangulated object properties in derived categories of modules, together with
  restriction of scalars along `R → A`;
- sampled owner declarations:
  `DerivedCategory.IsPerfectOver`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsTriangulated`,
  `(P.inverseImage F).IsTriangulated`,
  `(P ⊓ P').IsTriangulated`;
- best owner abstraction: the source-facing owner is `DerivedCategory.IsPerfectOver R`, while the
  retract and distinguished-triangle closure statements belong canonically to `ObjectProperty`;
- primitive vs. derived:
  primitive data are the two defining owner predicates `K.IsPseudoCoherent` and finite tor
  dimension after applying the canonical derived restriction-of-scalars functor;
  derived API are retract stability and triangulated closure of their intersection;
- source/core/bridge triage:
  `source-facing`: `DerivedCategory.IsPerfectOver R`;
  `core/canonical`: `ObjectProperty.IsStableUnderRetracts` and
    `ObjectProperty.IsTriangulated`;
  `bridge/view`: inverse image along the canonical derived restriction-of-scalars functor.

Accordingly, this file exposes the closure result at the owner layer as an
`ObjectProperty.IsTriangulated` instance for `DerivedCategory.IsPerfectOver R`, deriving it from
the canonical object-property owners rather than maintaining a parallel closure API. -/

/-- Helper for Lemma 15.84.2: enlarging the tor-amplitude interval preserves tor-amplitude. -/
private theorem hasTorAmplitudeIn_mono {K : DModR} {a b a' b' : ℤ}
    (hK : HasTorAmplitudeIn K a b) (ha : a' ≤ a) (hb : b ≤ b') :
    HasTorAmplitudeIn K a' b' := by
  -- Proof comment: once the excluded interval grows, every degree excluded before is still
  -- excluded now.
  intro M i hi
  exact hK M i <| by
    intro hi'
    exact hi ⟨le_trans ha hi'.1, le_trans hi'.2 hb⟩

/-- Helper for Lemma 15.84.2: finite tor dimension is closed under the `obj₂` slot of a
distinguished triangle. -/
private theorem hasFiniteTorDimension_obj₂_of_distinguishedTriangle
    (T : Triangle DModR) (hT : T ∈ distTriang DModR)
    (h₁ : HasFiniteTorDimension T.obj₁) (h₃ : HasFiniteTorDimension T.obj₃) :
    HasFiniteTorDimension T.obj₂ := by
  -- Proof comment: choose tor-amplitude intervals for the outer terms, enlarge them to a common
  -- interval, and then apply the fixed-interval triangle lemma.
  rcases h₁ with ⟨a₁, b₁, h₁⟩
  rcases h₃ with ⟨a₃, b₃, h₃⟩
  refine ⟨min a₁ a₃, max b₁ b₃, ?_⟩
  exact hasTorAmplitudeIn_obj₂_of_distinguishedTriangle T hT
    (hasTorAmplitudeIn_mono h₁ (min_le_left _ _) (le_max_left _ _))
    (hasTorAmplitudeIn_mono h₃ (min_le_right _ _) (le_max_right _ _))

/-- Objects of `D(R)` with finite tor dimension are stable under retracts/direct summands. -/
instance hasFiniteTorDimension_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts (fun K : DModR ↦ HasFiniteTorDimension K) where
  of_retract h hK := by
    -- Proof comment: keep the same tor-amplitude interval and transport it across the retract.
    rcases hK with ⟨a, b, hK⟩
    exact ⟨a, b, prop_of_retract (fun K : DModR ↦ HasTorAmplitudeIn K a b) h hK⟩

/-- Helper for Lemma 15.84.2: the zero object has finite tor dimension. -/
private theorem hasFiniteTorDimension_zero : HasFiniteTorDimension (0 : DModR) := by
  refine ⟨0, 0, ?_⟩
  -- Proof comment: tensoring the zero object remains zero, so every homology object vanishes.
  intro M i hi
  letI : (derivedTensorProduct ((single₀).obj M)).IsTriangulated :=
    derivedTensorProduct_isTriangulated ((single₀).obj M)
  letI : (derivedTensorProduct ((single₀).obj M)).Additive := inferInstance
  letI : (derivedTensorProduct ((single₀).obj M)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  simpa using
    (H i).map_isZero <|
      (derivedTensorProduct ((single₀).obj M)).map_isZero (isZero_zero DModR)

private instance hasFiniteTorDimension_containsZero :
    ObjectProperty.ContainsZero (fun K : DModR ↦ HasFiniteTorDimension K) where
  exists_zero := by
    exact ⟨0, isZero_zero DModR, hasFiniteTorDimension_zero⟩

private instance hasFiniteTorDimension_isStableUnderShift :
    ObjectProperty.IsStableUnderShift (fun K : DModR ↦ HasFiniteTorDimension K) ℤ where
  isStableUnderShiftBy n := .mk <| by
    intro K hK
    exact (hasFiniteTorDimension_shift_iff K n).2 hK

private instance hasFiniteTorDimension_isTriangulatedClosed₂ :
    ObjectProperty.IsTriangulatedClosed₂ (fun K : DModR ↦ HasFiniteTorDimension K) :=
  .mk' fun T hT h₁ h₃ ↦ hasFiniteTorDimension_obj₂_of_distinguishedTriangle T hT h₁ h₃

/-- Objects of `D(R)` with finite tor dimension form a triangulated object property. -/
instance hasFiniteTorDimension_isTriangulated :
    ObjectProperty.IsTriangulated (fun K : DModR ↦ HasFiniteTorDimension K) where
  toContainsZero := hasFiniteTorDimension_containsZero
  toIsStableUnderShift := hasFiniteTorDimension_isStableUnderShift
  toIsTriangulatedClosed₂ := hasFiniteTorDimension_isTriangulatedClosed₂

/-- Helper for Lemma 15.84.2: pseudo-coherent derived objects are stable under retracts. -/
private theorem isPseudoCoherent_of_retract
    {S : Type u} [CommRing S] {X Y : DerivedCategory (ModuleCat S)}
    (h : Retract X Y) (hY : Y.IsPseudoCoherent) :
    X.IsPseudoCoherent := by
  -- Route correction: the intended source-faithful proof uses Lemma `15.65.8`, but this target
  -- file cannot currently import that earlier file because `lake lean` fails inside it first.
  -- TODO: rebuild the direct-summand argument from Lemma `15.65.8` locally, or restore that
  -- earlier file and then replace this placeholder by the imported retract-stability theorem.
  sorry

-- Proof sketch: `DerivedCategory.IsPerfectOver R` is definitionally the intersection of the
-- pseudo-coherent owner property on `D(A)` and the inverse image, along the canonical derived
-- restriction-of-scalars functor, of the finite-tor-dimension owner property on `D(R)`. The
-- retract stability statement is therefore the canonical `⊓`-instance.
/-- `R`-perfect objects of `D(A)` are stable under retracts/direct summands. -/
instance isPerfectOver_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts
      (fun K : DModA ↦ DerivedCategory.IsPerfectOver R K) := by
  refine ⟨?_⟩
  intro X Y h hY
  rcases hY with ⟨hYpc, hYtor⟩
  constructor
  · -- Proof comment: the pseudo-coherent half is the single remaining blocked ingredient.
    exact isPseudoCoherent_of_retract h hYpc
  · -- Proof comment: finite tor dimension transports along the induced retract after restricting
    -- scalars to `R`.
    exact prop_of_retract
      (fun K : DModR ↦ HasFiniteTorDimension K)
      (h.map ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory))
      hYtor

-- Proof sketch: the same definitional decomposition identifies `DerivedCategory.IsPerfectOver R`
-- with the intersection of a pseudo-coherent triangulated object property on `D(A)` and the
-- inverse image, along the canonical derived restriction-of-scalars functor, of the
-- finite-tor-dimension triangulated object property on `D(R)`. The instance is then the canonical
-- `⊓`-instance for triangulated object properties.
/-- Lemma 15.84.2: the `R`-perfect objects of `D(A)` form a saturated triangulated strictly full
subcategory; the flat finite-presentation hypotheses from the source are not needed for this
closure statement. -/
@[stacks 0DHT]
instance isPerfectOver_isTriangulated :
    ObjectProperty.IsTriangulated
      (fun K : DModA ↦ DerivedCategory.IsPerfectOver R K) := by
  let P₁ : ObjectProperty DModA := fun K ↦ K.IsPseudoCoherent
  let P₂ : ObjectProperty DModR := fun K ↦ HasFiniteTorDimension K
  let F : DModA ⥤ DModR := (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory
  letI : P₁.IsTriangulated := by
    -- Proof comment: reuse the canonical pseudo-coherent triangulated owner from Lemma `15.65.6`.
    simpa [P₁] using
      (inferInstance : ObjectProperty.IsTriangulated (fun K : DModA ↦ K.IsPseudoCoherent))
  letI : P₂.IsTriangulated := by
    -- Proof comment: the finite-tor-dimension owner was proved triangulated above.
    simpa [P₂] using
      (inferInstance :
        ObjectProperty.IsTriangulated (fun K : DModR ↦ HasFiniteTorDimension K))
  simpa [DerivedCategory.IsPerfectOver, P₁, P₂, F, ObjectProperty.inverseImage] using
    (inferInstance : ObjectProperty.IsTriangulated (P₁ ⊓ P₂.inverseImage F))

end

end CategoryTheory
