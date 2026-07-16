import Mathlib
import stacks_proof.stacks_project.Chap04.Lemma_4_35_17
import stacks_proof.stacks_project.Chap08.Lemma_8_2_3
import stacks_proof.stacks_project.Chap08.Definition_8_5_5
import stacks_proof.stacks_project.Chap08.Definition_8_11_1
import stacks_proof.stacks_project.Chap08.Lemma_8_5_4
import stacks_proof.stacks_project.Chap08.Lemma_8_10_1
import stacks_proof.stacks_project.Chap08.Lemma_8_10_5.Index
import stacks_proof.stacks_project.Chap08.Lemma_8_10_5
import stacks_proof.stacks_project.Chap08.Lemma_8_10_4.ProjectionFamilyCovering

open CategoryTheory
open BasedFunctor
open Functor
open Functor.Fiber
open Functor.IsStronglyCartesian
open FibredCategoryOver

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory

/-- Helper for Lemma 8.11.3: the topology on the total category of a fibred category inherited
from the base site. -/
abbrev inheritedTopology
    {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) (X : FibredCategoryOver C) :
    GrothendieckTopology X.S :=
  (stronglyCartesianLiftPrecoverage J.toPrecoverage X.p).toGrothendieck

namespace FibredCategoryMor

section

variable {C : Type u₁} [Category.{v₁} C]
variable {J : GrothendieckTopology C}
variable {X Y : FibredCategoryOver C} [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p]

/- Domain-style sampling for Lemma 8.11.3:
- primary domain: morphisms of fibred categories over a site, expressed through canonical
  pullback functors on fibers and comparison isomorphisms between `f^*F(x)` and `F(f^*x)`;
- inspected owner-level declarations:
  `BasedFunctor.fiberFunctor`,
  `PullbackChoice.pullbackFunctor`,
  `canonicalPullbackChoice`,
  `Functor.IsStronglyCartesian.domainIsoOfBaseIso`;
- best owner abstraction: the source-facing predicate
  `FibredCategoryMor.LocallyLiftsFiberMorphisms`, stated in the fiber categories using the
  canonical pullback functors and the comparison square they induce;
- primitive data: a morphism `b` in the target fiber over `U`, together with local lifts `a` in
  the pulled-back source fibers over a covering family;
- derived API: the canonical stack-morphism shorthand
  `StackInGroupoidsOver.Hom.LocallyLiftsFiberMorphisms` and the gerbe characterization theorem at
  the end of the file.

Source/core/bridge triage:
- `source-facing`: `FibredCategoryMor.LocallyLiftsFiberMorphisms`;
- `core/canonical`: `BasedFunctor.fiberFunctor`, `canonicalPullbackChoice`,
  `PullbackChoice.pullbackFunctor`, `FibredCategoryMor.pullbackComparison`, and
  `IsStronglyCartesian.domainIsoOfBaseIso`;
- `bridge/view`: `FibredCategoryMor.pullbackComparison`, reused here to express the source
  condition as a commuting square in the pulled-back target fiber. -/

/-- Any morphism between two objects in the image of a fiber is locally lifted after restricting
to a covering family. This is condition `(2)(b)` in Lemma `8.11.3`. -/
def LocallyLiftsFiberMorphisms
    (J : GrothendieckTopology C) (F : FibredCategoryMor X Y) : Prop :=
  let hcX := canonicalPullbackChoice X.p
  let hcY := canonicalPullbackChoice Y.p
  ∀ {U : C} (x x' : X.p.Fiber U)
      (b : (fiberFunctor F U).obj x ⟶ (fiberFunctor F U).obj x'),
      ∃ S : J.Cover U, ∀ I : S.Arrow,
        ∃ a : I.f ^*[hcX] x ⟶ I.f ^*[hcX] x',
          CommSq
            ((hcY.pullbackFunctor I.f).map b)
            (pullbackComparison F I.f x).hom
            (pullbackComparison F I.f x').hom
            ((fiberFunctor F I.Y).map a)

end

end FibredCategoryMor

namespace StackInGroupoidsOver.Hom

section

variable {C : Type u₁} [Category.{v₁} C]
variable {J : GrothendieckTopology C}
variable {X Y : StackInGroupoidsOver J}

/-- Owner-level shorthand for the local lifting condition on a `1`-morphism of stacks in
groupoids. -/
abbrev LocallyLiftsFiberMorphisms (F : X ⟶ Y) : Prop :=
  FibredCategoryMor.LocallyLiftsFiberMorphisms J (toFibredCategoryMor F)

end

end StackInGroupoidsOver.Hom

namespace StackInGroupoidsOver.Hom

section

variable {B : Type u₂} [Category.{v₂} B]
variable {K : GrothendieckTopology B}
variable {𝒮₁ 𝒮₂ : StackInGroupoidsOver.{u₂, v₂, max u₂ v₂, v₂} K}

/-- Helper for Lemma 8.11.3: an equivalence over the base transports a gerbe structure from the
source stack in groupoids to the target stack in groupoids. -/
theorem gerbeOfEquivalenceOverBase
    (F : 𝒮₁ ⟶ 𝒮₂)
    (hF : F.IsEquivalenceOverBase)
    (h₁ : IsGerbe K 𝒮₁.p) :
    IsGerbe K 𝒮₂.p := by
  refine
    { toIsStackInGroupoids := inferInstance
      locally_inhabited := ?_
      locally_isomorphic := ?_ }
  · intro U
    -- Push local sections forward along the fiber functor.
    obtain ⟨S, hS⟩ := h₁.locally_inhabited U
    refine ⟨S, fun I ↦ ?_⟩
    obtain ⟨x⟩ := hS I
    exact ⟨(F.fiberFunctor I.Y).obj x⟩
  · intro U x y
    -- Choose source preimages of the two target-fiber objects and transport the local
    -- source isomorphism through pullback comparison and the counit isomorphisms.
    let F' := F.toFibredCategoryMor
    let fiberU := F.fiberFunctor U
    letI : fiberU.IsEquivalence :=
      fiberFunctor_isEquivalence_of_isEquivalenceOverBase F.toBasedFunctor hF U
    let eU := fiberU.asEquivalence
    let x₁ : 𝒮₁.p.Fiber U := eU.inverse.obj x
    let y₁ : 𝒮₁.p.Fiber U := eU.inverse.obj y
    let εx : fiberU.obj x₁ ≅ x := eU.counitIso.app x
    let εy : fiberU.obj y₁ ≅ y := eU.counitIso.app y
    obtain ⟨S, hS⟩ := h₁.locally_isomorphic x₁ y₁
    refine ⟨S, fun I ↦ ?_⟩
    let fiberI := F.fiberFunctor I.Y
    letI : fiberI.IsEquivalence :=
      fiberFunctor_isEquivalence_of_isEquivalenceOverBase F.toBasedFunctor hF I.Y
    let hc₂ := canonicalPullbackChoice 𝒮₂.p
    obtain ⟨α⟩ := hS I
    exact
      ⟨(hc₂.pullbackFunctor I.f).mapIso εx.symm ≪≫
        FibredCategoryMor.pullbackComparison F' I.f x₁ ≪≫
        fiberI.mapIso α ≪≫
        (FibredCategoryMor.pullbackComparison F' I.f y₁).symm ≪≫
        (hc₂.pullbackFunctor I.f).mapIso εy⟩

/-- Helper for Lemma 8.11.3: being a gerbe is invariant under an equivalence over the base. -/
theorem gerbe_iff_of_equivalenceOverBase
    (F : 𝒮₁ ⟶ 𝒮₂)
    (hF : F.IsEquivalenceOverBase) :
    IsGerbe K 𝒮₁.p ↔ IsGerbe K 𝒮₂.p := by
  constructor
  · exact gerbeOfEquivalenceOverBase F hF
  · intro h₂
    -- Use a chosen inverse equivalence over the base for the reverse implication.
    let e : EquivalenceOverBase F.toBasedFunctor := Classical.choice hF.nonempty
    let G : 𝒮₂ ⟶ 𝒮₁ := ofBasedFunctor e.inverse
    have hG : G.IsEquivalenceOverBase := e.inverse_isEquivalenceOverBase
    simpa [G] using gerbeOfEquivalenceOverBase G hG h₂

end

end StackInGroupoidsOver.Hom

end CategoryTheory
