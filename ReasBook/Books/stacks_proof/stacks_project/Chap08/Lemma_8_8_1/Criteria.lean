import stacks_proof.stacks_project.Chap04.Lemma_4_35_9
import stacks_proof.stacks_project.Chap04.Definition_4_36_2
import stacks_proof.stacks_project.Chap08.Lemma_8_2_3
import stacks_proof.stacks_project.Chap08.Definition_8_4_1
import stacks_proof.stacks_project.Chap08.Definition_8_4_5
import stacks_proof.stacks_project.Chap08.Lemma_8_4_4
import stacks_proof.stacks_project.Chap07.Lemma_7_10_17

universe u v

namespace CategoryTheory

open Bicategory
open BasedFunctor
open FibredCategoryMor
open InducedCategory.Hom
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace FibredCategoryMor

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- A morphism from a fibred category to a stack is a stackification morphism if it sheafifies all
fiberwise morphism presheaves and is locally essentially surjective on objects of the fibers. This
packages the two conditions appearing in Stacks Project Lemma 8.8.1. -/
class IsStackification
    {X : FibredCategoryOver C} {Y : StackOver J}
    (G : X ⟶ Y) : Prop where
  /-- The induced map on each fiberwise morphism presheaf becomes an isomorphism after
  sheafification, in the canonical mathlib sense of `(J.over U).W`. This is the owner-level form
  of the local-bijectivity condition from the source. -/
  morphismPresheafMap_W :
    ∀ (U : C) (x y : X.p.Fiber U),
      (J.over U).W (fibredMorphismPresheafMap G x y)
  /-- Every object of the target fiber is locally in the essential image of the induced fiber
  functor, in the canonical sense of `FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects`.
  -/
  locallyEssentiallySurjectiveOnObjects :
    FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J G

end FibredCategoryMor

/-- Helper for Lemma 8.8.1: the forward half of the Hom-presheaf criterion from Lemma `8.4.7`
upgrades full faithfulness of a fibred-category morphism to isomorphisms on all canonical
Hom-presheaf comparison maps. -/
-- TODO: mirror the owner-level argument from `Lemma_8_4_7` locally. The current file cannot
-- import that theorem directly in this Lake state, so this bridge should be reproved by showing
-- each component of `fibredMorphismPresheafMap` is conjugation by pullback-comparison
-- isomorphisms around the fiberwise map of a fully faithful functor.
theorem fibredMorphismPresheafMap_isIso_of_fullyFaithful_local
    {X Y : FibredCategoryOver C}
    (F : X ⟶ Y)
    (hF : Nonempty F.toHom.FullyFaithful)
    {U : C} (x y : X.p.Fiber U) :
    IsIso (fibredMorphismPresheafMap F x y) := by
  -- Compare each component with the fiberwise map on morphisms, conjugated by pullback
  -- comparison isomorphisms.
  rw [NatTrans.isIso_iff_isIso_app]
  intro W
  rw [isIso_iff_bijective]
  let xW := W.unop.hom ^*[canonicalPullbackChoice X.p] x
  let yW := W.unop.hom ^*[canonicalPullbackChoice X.p] y
  let FxW := (F.toHom.fiberFunctor W.unop.left).obj xW
  let FyW := (F.toHom.fiberFunctor W.unop.left).obj yW
  let ex := FibredCategoryMor.pullbackComparison F W.unop.hom x
  let ey := FibredCategoryMor.pullbackComparison F W.unop.hom y
  have hFiberFF :
      Nonempty ((F.toHom.fiberFunctor W.unop.left).FullyFaithful) :=
    (FibredCategoryMor.fullyFaithful_iff_fiberwise (F := F)).1 hF W.unop.left
  have hFiberMapBijective :
      ∀ a b : X.p.Fiber W.unop.left,
        Function.Bijective
          ((F.toHom.fiberFunctor W.unop.left).map : (a ⟶ b) →
            ((F.toHom.fiberFunctor W.unop.left).obj a ⟶
              (F.toHom.fiberFunctor W.unop.left).obj b)) := by
    -- Full faithfulness on the fiber is exactly bijectivity on each hom-set map.
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective] at hFiberFF
    exact hFiberFF
  have hMap :
      Function.Bijective
        ((F.toHom.fiberFunctor W.unop.left).map : (xW ⟶ yW) → (FxW ⟶ FyW)) := by
    exact hFiberMapBijective xW yW
  let eCongr :
      (FxW ⟶ FyW) ≃
        ((canonicalFiberPseudofunctor Y.p).presheafHom
          ((F.toHom.fiberFunctor U).obj x)
          ((F.toHom.fiberFunctor U).obj y)).obj W :=
    Iso.homCongr ex.symm ey.symm
  have hApp :
      (fibredMorphismPresheafMap (F := F) x y).app W =
        fun δ : xW ⟶ yW ↦ eCongr ((F.toHom.fiberFunctor W.unop.left).map δ) := by
    funext δ
    rfl
  rw [hApp]
  constructor
  · intro δ₁ δ₂ hδ
    -- Injectivity follows because both the fiberwise map and the conjugation equivalence are
    -- injective.
    apply hMap.1
    apply eCongr.injective
    exact hδ
  · intro θ
    -- Surjectivity follows by first undoing the conjugation and then using surjectivity in the
    -- fiber.
    rcases eCongr.surjective θ with ⟨θ', rfl⟩
    rcases hMap.2 θ' with ⟨δ, rfl⟩
    exact ⟨δ, rfl⟩

/-- Helper for Lemma 8.8.1: precomposing a locally essentially surjective morphism with an
equivalence over the base on the source preserves the same local essential-image condition. -/
theorem locallyEssentiallySurjectiveOnObjects_comp_left_of_isEquivalenceOverBase
    {X₁ X₂ : FibredCategoryOver C} {Y : StackOver J}
    (E : X₁ ⟶ X₂)
    (hE : FibredCategoryMor.IsEquivalenceOverBase E)
    (G : X₂ ⟶ Y)
    (hG : FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J G) :
    FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J (E ≫ G) := by
  intro U y
  -- Keep the same covering from `G`, and lift each local source object back through the
  -- fiberwise equivalence induced by `E`.
  rcases hG U y with ⟨S, hS⟩
  refine ⟨S, ?_⟩
  intro I
  rcases hS I with ⟨x₂, ⟨eG⟩⟩
  have hEI :
      (FibredCategoryMor.fiberFunctor E I.Y).IsEquivalence :=
    BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
      (FibredCategoryMor.toBasedFunctor E) hE I.Y
  let _ : (FibredCategoryMor.fiberFunctor E I.Y).IsEquivalence := hEI
  let _ : (FibredCategoryMor.fiberFunctor E I.Y).EssSurj := by infer_instance
  obtain ⟨x₁, ⟨eE⟩⟩ := Functor.EssSurj.mem_essImage
    (F := FibredCategoryMor.fiberFunctor E I.Y) x₂
  refine ⟨x₁, ?_⟩
  -- After rewriting the composite fiber functor, the desired local image is the image of the
  -- chosen equivalence-preimage under `G`, followed by the original local identification.
  change Nonempty
    (((FibredCategoryMor.fiberFunctor G I.Y).obj
        ((FibredCategoryMor.fiberFunctor E I.Y).obj x₁)) ≅
      I.f ^*[canonicalPullbackChoice Y.p] y)
  exact ⟨(FibredCategoryMor.fiberFunctor G I.Y).mapIso eE ≪≫ eG⟩

end CategoryTheory
