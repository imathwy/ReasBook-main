import Mathlib
import StacksProject_2024.Chap12.Definition_12_5_3
import StacksProject_2024.Chap13.Definition_13_15_3
import StacksProject_2024.Chap13.Lemma_13_15_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty
open ComplexShape
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "QisPlus" => boundedBelowHomotopyQuasiIso 𝒜
local notation "QisMinus" => boundedAboveHomotopyQuasiIso 𝒜
local notation "KplusToDplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow F
local notation "KminusToDminus" => mapBoundedAboveHomotopyCategoryToDerivedAbove F

/- Domain-style sampling for Proposition 13.16.8:
- primary domain: bounded-below / bounded-above derived-functor existence and computation from
  acyclic resolutions in an abelian category;
- sampled owner declarations:
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor`,
  `IsBoundedAboveLeftAcyclicForAdditiveFunctor`,
  `IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor`,
  `ObjectProperty.HasMonoEmbedding`,
  `ObjectProperty.HasEpiCover`;
- best owner abstraction: Proposition `13.16.8` is source-facing and bounded. Its acyclicity
  hypotheses should therefore be organized around the Chapter `13` owners
  `IsBoundedBelowRightAcyclicForAdditiveFunctor F`,
  `IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F`,
  `IsBoundedAboveLeftAcyclicForAdditiveFunctor F`, and
  `IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor F`, while the mono/epi reachability
  hypotheses are canonically owned by `ObjectProperty.HasMonoEmbedding` and
  `ObjectProperty.HasEpiCover`;
- primitive data: the additive functor `F` and the bounded mono/epi reachability owners for those
  bounded acyclicity predicates;
- derived API: pointwise and total bounded derived-functor existence, plus the computation
  theorems for termwise bounded-acyclic complexes.

Source/core/bridge triage:
- `source-facing`: the four bounded derived-functor existence statements and the two computation
  statements below;
- `core/canonical`: `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor`,
  `IsBoundedAboveLeftAcyclicForAdditiveFunctor`,
  `IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor`,
  `ObjectProperty.HasMonoEmbedding`, and `ObjectProperty.HasEpiCover`;
- `bridge/view`: the bounded/unbounded comparison lemmas from `13.15.2`, which remain stronger
  companion transport API rather than the main public surface here.
-/

section Right

local notation "BoundedBelowRightAcyclic" =>
  (fun A : 𝒜 ↦ IsBoundedBelowRightAcyclicForAdditiveFunctor F A)

-- Proof sketch: resolve any bounded-below complex termwise by a quasi-isomorphic bounded-below
-- complex of bounded-below right `F`-acyclic objects using the mono-embedding hypothesis
-- degreewise and the
-- bounded-below resolution lemma. Then quasi-isomorphisms between such termwise right-acyclic
-- complexes are sent to quasi-isomorphisms, so Lemma `13.14.15` yields pointwise existence of
-- the bounded-below right derived functor at every object of `K^+(\mathcal A)`.
/-- Proposition 13.16.8: if every object of `𝒜` admits a monomorphism into an object that is
acyclic for the bounded-below right derived functor of `F`, formalized by the canonical owner
`ObjectProperty.HasMonoEmbedding BoundedBelowRightAcyclic`, then the bounded-below right derived
functor of `K^+(\mathcal A) ⥤ D^+(\mathcal B)` is everywhere defined in the canonical pointwise
sense `KplusToDplus.HasPointwiseRightDerivedFunctor QisPlus`. -/
theorem boundedBelow_hasPointwiseRightDerivedFunctor_of_mono_into_boundedBelowRightAcyclic
    [HasMonoEmbedding BoundedBelowRightAcyclic] :
    Functor.HasPointwiseRightDerivedFunctor KplusToDplus QisPlus := sorry

/-- Corollary: under the hypotheses of Proposition 13.16.8, the bounded-below total right
derived functor exists. -/
theorem boundedBelow_hasRightDerivedFunctor_of_mono_into_boundedBelowRightAcyclic
    [HasMonoEmbedding BoundedBelowRightAcyclic] :
    Functor.HasRightDerivedFunctor KplusToDplus QisPlus := by
  let _ : Functor.HasPointwiseRightDerivedFunctor KplusToDplus QisPlus :=
    boundedBelow_hasPointwiseRightDerivedFunctor_of_mono_into_boundedBelowRightAcyclic F
  infer_instance

-- Proof sketch: this is the bounded Leray acyclicity criterion of Lemma `13.16.7`, expressed
-- directly with the owner `IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor`.
/-- Any bounded-below complex whose terms are acyclic for the bounded-below right derived functor
computes the bounded-below right derived functor. -/
theorem computesRightDerivedFunctorAt_of_termwise_boundedBelowRightAcyclic
    [Functor.HasRightDerivedFunctor KplusToDplus QisPlus]
    (A : K⁺(𝒜))
    (hA : IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F A) :
    Functor.ComputesRightDerivedAt KplusToDplus QisPlus A := sorry

end Right

section Left

local notation "BoundedAboveLeftAcyclic" =>
  IsBoundedAboveLeftAcyclicForAdditiveFunctor F

-- Proof sketch: dualize the bounded-below argument. Use the epi-cover hypothesis by
-- bounded-above left-acyclic objects to choose bounded-above resolutions, then apply the dual
-- form of
-- Lemma `13.14.15` to obtain pointwise existence of the bounded-above left derived functor at
-- every object.
/-- If every object of `𝒜` is a quotient of an object that is acyclic for the bounded-above left
derived functor of `F`, formalized by the canonical owner
`ObjectProperty.HasEpiCover BoundedAboveLeftAcyclic`, then the bounded-above left derived
functor of `K^-(\mathcal A) ⥤ D^-(\mathcal B)` is everywhere defined in the canonical pointwise
sense `KminusToDminus.HasPointwiseLeftDerivedFunctor QisMinus`. -/
theorem boundedAbove_hasPointwiseLeftDerivedFunctor_of_epi_from_boundedAboveLeftAcyclic
    [HasEpiCover BoundedAboveLeftAcyclic] :
    Functor.HasPointwiseLeftDerivedFunctor KminusToDminus QisMinus := sorry

/-- Corollary: under the dual hypotheses of Proposition 13.16.8, the bounded-above total left
derived functor exists. -/
theorem boundedAbove_hasLeftDerivedFunctor_of_epi_from_boundedAboveLeftAcyclic
    [HasEpiCover BoundedAboveLeftAcyclic] :
    Functor.HasLeftDerivedFunctor KminusToDminus QisMinus := by
  let _ : Functor.HasPointwiseLeftDerivedFunctor KminusToDminus QisMinus :=
    boundedAbove_hasPointwiseLeftDerivedFunctor_of_epi_from_boundedAboveLeftAcyclic F
  infer_instance

-- Proof sketch: this is the bounded-above dual of the bounded Leray acyclicity criterion,
-- expressed directly with the owner
-- `IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor`.
/-- Any bounded-above complex whose terms are acyclic for the bounded-above left derived functor
computes the bounded-above left derived functor. -/
theorem computesLeftDerivedFunctorAt_of_termwise_boundedAboveLeftAcyclic
    [Functor.HasLeftDerivedFunctor KminusToDminus QisMinus]
    (A : K⁻(𝒜))
    (hA : IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor F A) :
    Functor.ComputesLeftDerivedAt KminusToDminus QisMinus A := sorry

end Left

end

end CategoryTheory
