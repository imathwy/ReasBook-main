import stacks_proof.stacks_project.Chap04.Lemma_4_35_9
import stacks_proof.stacks_project.Chap04.Lemma_4_36_4
import stacks_proof.stacks_project.Chap04.Definition_4_36_2
import stacks_proof.stacks_project.Chap08.Lemma_8_2_3
import stacks_proof.stacks_project.Chap08.Definition_8_4_1
import stacks_proof.stacks_project.Chap08.Definition_8_4_5
import stacks_proof.stacks_project.Chap08.Lemma_8_4_4
import stacks_proof.stacks_project.Chap07.Lemma_7_10_17
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.Index
import stacks_proof.stacks_project.Chap08.Lemma_8_4_8
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.
--
-- STATUS NOTE (stackification, Stacks Tag 02ZN). The two headline theorems
-- `exists_stackification` and `stackification_unique_up_to_unique_twoIso` are proved modulo the
-- remaining `sorry` in `PlusConstruction/Existence.lean` — exactly the step the Stacks source
-- marks "Details omitted", i.e. the actual construction of the stackification:
--   * `catPseudofunctorPlusPlusStackificationExists` /
--     `exists_stackification_of_split_fibred_category` — the source-faithful construction of the
--     stackification of a split (Cat-valued) model via the plus-plus descent-data construction
--     (quotient locally equal morphisms, sheafify Hom presheaves by locally defined morphisms,
--     then adjoin descent-data objects and prove stackness).
--   * `split_fibred_category_model_exists` — strictification (Categories Lemma 4.36.4,
--     `Chap04.Lemma_4_36_4.exists_split_fibred_category_over_base`); a universe gap blocks a direct
--     wiring (the split model lands in a larger object universe; the faithful fix changes the
--     public theorem's universe signature).
--   * the comparison-existence wrapper is closed below by the precomposition equivalence package
--     from Lemma 8.8.3. That package contains the same object-and-arrow descent construction as
--     its own remaining proof obligation, so this file no longer duplicates that wrapper.
-- Everything else is `sorry`-free and (for the foundational layer) verified axiom-clean: the
-- comparison/transport layer (`fibredMorphismPresheafMap_comp`, `_app_id_local`,
-- `stack_hom_presheafMap_isIso_of_W`, `comparison_iso_on_fiber`, the canonical `fiberHomPresheafIso`
-- transport + the two conjugation factor lemmas, `..._slice_pullback_cover_family_mem`,
-- `stackification_hom_image_cover`/`stackification_coverwise_hom_lift` = local surjectivity of the
-- stackification `W`-map via `Presheaf.imageSieve`/`localPreimage`,
-- `isStackification_comp_left_of_isEquivalenceOverBase`); the entire `W`-chain reduction
-- scaffolding; the comparison morphism's full faithfulness + equivalence-over-base
-- (`comparison_stackification_isEquivalenceOverBase`, complete now that `_W_of_common_local_models`
-- and the equivalence-over-base lemma — `←` of Lemma 8.4.8 / Tag 046N, after deduping 8.4.8's
-- `pullbackComparison` cluster against `Lemma_8_2_3.PullbackComparisonNaturality` — are closed);
-- and the coverwise uniqueness assembly for compatible comparison `2`-isomorphisms.

universe u v w uX vX

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

end FibredCategoryMor

section

attribute [local instance] Types.instFunLike Types.instConcreteCategory uliftCategory

/-- Helper for Chap08 Lemma 8 8 1: a split fibred category comes with a Cat-valued
co-Grothendieck model and an explicit based equivalence over the base. -/
private theorem splitCoGrothendieckModelBasedEquivalence
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    [Functor.IsSplitFibredCategory X.p] :
    ∃ (F : Cᵒᵖ ⥤ Cat.{vX, uX})
      (e : BasedCategory.ofFunctor X.p ⥤ᵇ
        BasedCategory.ofFunctor
          (Pseudofunctor.CoGrothendieck.forget (F.toPseudofunctor'))),
      BasedFunctor.IsEquivalenceOverBase e := by
  -- Unpack the split model and convert the strict inverse equations into unit/counit isomorphisms.
  rcases (inferInstance : Functor.IsSplitFibredCategory X.p).existsCoGrothendieckModel with
    ⟨F, e, eInv, hη, hε⟩
  refine ⟨F, e, ?_⟩
  exact
    BasedFunctor.IsEquivalenceOverBase.mkPrime eInv
      (eqToIso hη.symm)
      (eqToIso hε)

/-- Helper for Chap08 Lemma 8 8 1: a cartesian-preserving based equivalence induces an
equivalence-over-base morphism of fibred categories. -/
private theorem ofBasedFunctor_isEquivalenceOverBase
    {X Y : FibredCategoryOver.{u, v, uX, vX} C}
    (e : X.toBasedCategory ⥤ᵇ Y.toBasedCategory)
    (he : e.IsEquivalenceOverBase)
    (hcart : e.PreservesStronglyCartesian) :
    FibredCategoryMor.IsEquivalenceOverBase
      (FibredCategoryMor.ofBasedFunctor e hcart) := by
  -- The owner predicate is the same predicate on the underlying based functor.
  change BasedFunctor.IsEquivalenceOverBase
    (FibredCategoryMor.toBasedFunctor (FibredCategoryMor.ofBasedFunctor e hcart))
  simpa [FibredCategoryMor.toBasedFunctor, FibredCategoryMor.ofBasedFunctor] using he

/-- Helper for Lemma 8.8.1: every fibred category admits an equivalence over the base to a split
fibred category. -/
private theorem split_fibred_category_model_exists
    (X : FibredCategoryOver.{u, v, max u (max v uX), max v vX} C) :
    ∃ Xₛ : FibredCategoryOver.{u, v, max u (max v uX), max v vX} C,
      ∃ _ : FibredCategoryOver.ofFunctor X.p ≌ Xₛ,
        Functor.IsSplitFibredCategory Xₛ.p := by
  exact exists_split_fibred_category_over_base_owner_equivalence.{v, vX, u, uX} X.p

/-- Helper for Chap08 Lemma 8 8 1: precomposing a stackification with an equivalence over the
source preserves the stackification condition. -/
private theorem isStackification_comp_left_of_isEquivalenceOverBase_core
    {X₁ X₂ : FibredCategoryOver C} {Y : StackOver J}
    (E : X₁ ⟶ X₂)
    (hE : FibredCategoryMor.IsEquivalenceOverBase E)
    (G : X₂ ⟶ Y)
    (hG : FibredCategoryMor.IsStackification G) :
    FibredCategoryMor.IsStackification (E ≫ G) := by
  -- The Hom-presheaf map for the composite factors through the equivalence-induced isomorphism
  -- on the source side and then through the stackification map for `G`.
  refine ⟨?_, ?_⟩
  · intro U x y
    rw [fibredMorphismPresheafMap_comp E G x y]
    have hIso : IsIso (fibredMorphismPresheafMap E x y) :=
      fibredMorphismPresheafMap_isIso_of_isEquivalenceOverBase E hE x y
    let _ : IsIso (fibredMorphismPresheafMap E x y) := hIso
    exact
      (J.over U).W.comp_mem _ _
        ((J.over U).W.of_isIso (fibredMorphismPresheafMap E x y))
        (hG.morphismPresheafMap_W U
          ((FibredCategoryMor.fiberFunctor E U).obj x)
          ((FibredCategoryMor.fiberFunctor E U).obj y))
  · -- Local essential surjectivity is invariant under precomposition by an equivalence over base.
    exact
      locallyEssentiallySurjectiveOnObjects_comp_left_of_isEquivalenceOverBase
        E hE G hG.locallyEssentiallySurjectiveOnObjects

/-- Helper for Chap08 Lemma 8 8 1: a split fibred category is equivalent over the base to its
same-owner Cat-valued co-Grothendieck model. -/
private theorem splitCoGrothendieckModelFibredEquivalence
    {X : FibredCategoryOver.{u, v, max u (max v uX), max v vX} C}
    [Functor.IsSplitFibredCategory X.p] :
    ∃ (F : Cᵒᵖ ⥤ Cat.{max v vX, max u (max v uX)})
      (E : X ⟶
        FibredCategoryOver.ofFunctor
          (Pseudofunctor.CoGrothendieck.forget (F.toPseudofunctor'))),
      FibredCategoryMor.IsEquivalenceOverBase E := by
  -- Unpack the split model as a based equivalence to a Cat-valued co-Grothendieck projection.
  obtain ⟨F, e, he⟩ := splitCoGrothendieckModelBasedEquivalence (X := X)
  let Xcat : FibredCategoryOver C :=
    FibredCategoryOver.ofFunctor
      (Pseudofunctor.CoGrothendieck.forget (F.toPseudofunctor'))
  let eOwner : X.toBasedCategory ⥤ᵇ Xcat.toBasedCategory := e
  have heOwner : eOwner.IsEquivalenceOverBase := by
    simpa [eOwner, Xcat, FibredCategoryOver.toBasedCategory] using he
  have hcart : eOwner.PreservesStronglyCartesian :=
    basedFunctor_preservesStronglyCartesian_of_equivalence_over_base
      (p₁ := X.p) (p₂ := Xcat.p) eOwner heOwner
  let E : X ⟶ Xcat := FibredCategoryMor.ofBasedFunctor eOwner hcart
  -- Package the owner morphism and record that its equivalence predicate is still the based one.
  refine ⟨F, E, ?_⟩
  exact ofBasedFunctor_isEquivalenceOverBase eOwner heOwner hcart

/-- Helper for Chap08 Lemma 8 8 1: the split construction closes when the source owner is already
saturated enough to contain the co-Grothendieck model. -/
private theorem exists_stackification_of_split_saturated_fibred_category
    {X : FibredCategoryOver.{u, v, max u (max v uX), max v vX} C}
    [Functor.IsSplitFibredCategory X.p] :
    ∃ Y : StackOver.{u, v, max u (max v uX), max v vX} J,
      ∃ G : X ⟶ Y,
        FibredCategoryMor.IsStackification G := by
  -- In the saturated owner, the Cat-valued co-Grothendieck model and `X` live in the same
  -- fibred-category bicategory, so precomposition by the equivalence is available directly.
  obtain ⟨F, E, hE⟩ :=
    splitCoGrothendieckModelFibredEquivalence.{u, v, uX, vX} (X := X)
  obtain ⟨Y, Gcat, hGcat⟩ := exists_stackification_of_cat_presheaf_model (J := J) F
  refine ⟨Y, E ≫ Gcat, ?_⟩
  exact isStackification_comp_left_of_isEquivalenceOverBase_core (J := J) E hE Gcat hGcat

/-- Helper for Lemma 8.8.1: once the source fibred category is split, the source-faithful
two-stage construction produces a stackification. -/
private theorem exists_stackification_of_split_fibred_category
    {X : FibredCategoryOver.{u, v, max u (max v uX), max v vX} C}
    [Functor.IsSplitFibredCategory X.p] :
    ∃ Y : StackOver.{u, v, max u (max v uX), max v vX} J,
      ∃ G : X ⟶ Y,
        FibredCategoryMor.IsStackification G := by
  exact exists_stackification_of_split_saturated_fibred_category.{u, v, uX, vX} (J := J) (X := X)

/-- Helper for Lemma 8.8.1: precomposing a stackification with an equivalence over the source
preserves the stackification condition. -/
private theorem isStackification_comp_left_of_isEquivalenceOverBase
    {X₁ X₂ : FibredCategoryOver C} {Y : StackOver J}
    (E : X₁ ⟶ X₂)
    (hE : FibredCategoryMor.IsEquivalenceOverBase E)
    (G : X₂ ⟶ Y)
    (hG : FibredCategoryMor.IsStackification G) :
    FibredCategoryMor.IsStackification (E ≫ G) := by
  -- Reuse the earlier core lemma; the split-case construction needs this fact before the final
  -- public existence theorem, so the proof is recorded once in dependency order.
  exact isStackification_comp_left_of_isEquivalenceOverBase_core (J := J) E hE G hG

/-- Helper for Lemma 8.8.1: two stackifications admit a direct comparison morphism, without
re-routing through the stronger universal property for arbitrary stack targets. This is the
source-faithful existence datum needed for uniqueness up to unique `2`-isomorphism. -/
-- Route correction: the comparison is the essential-preimage of `G₂` under precomposition with
-- `G₁`. Lemma 8.8.3 packages the same descent construction as a precomposition equivalence, so the
-- local statement only has to extract that chosen lift.
private theorem stackification_comparison_exists
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (G₂ : X ⟶ Y₂)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    (hG₂ : FibredCategoryMor.IsStackification G₂) :
    ∃ H : Y₁ ⟶ Y₂,
      Nonempty
        ((stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂) := by
  -- The comparison construction only needs `G₁` as a stackification for the precomposition
  -- equivalence; `hG₂` stays in the interface because downstream uniqueness compares two
  -- stackification morphisms.
  let _ := hG₂
  letI : Functor.IsEquivalence
      (stackification_precompose_functor Y₂ G₁ : (Y₁ ⟶ Y₂) ⥤ (X ⟶ Y₂)) :=
    stackification_precompose_functor_isEquivalence Y₂ G₁ hG₁
  let e := (stackification_precompose_functor Y₂ G₁).asEquivalence
  refine ⟨e.inverse.obj G₂, ?_⟩
  change Nonempty (e.functor.obj (e.inverse.obj G₂) ≅ G₂)
  exact ⟨e.counitIso.app G₂⟩

/-- Helper for Lemma 8.8.1: uniqueness belongs to the comparison pair `(H, α)`, not to the raw
type of compatible isomorphisms for a fixed `H`. Given one comparison pair, every other pair is
connected to it by a unique `2`-isomorphism whose image under precomposition carries the second
comparison isomorphism to the first. -/
-- Route correction: this uniqueness statement should be proved directly coverwise from the
-- comparison pair, not by reintroducing the discarded arbitrary-target precomposition route.
-- TODO: compare two candidate comparison pairs on a fixed local `G₁`-model cover, show the local
-- components are forced by compatibility with `α` and `α'`, and globalize uniqueness with
-- `stack_cover_hom_ext` and `fibredCategoryMor_two_iso_ext`.
private theorem comparison_stackification_compatible_twoIso_unique_direct
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (G₂ : X ⟶ Y₂)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    (hG₂ : FibredCategoryMor.IsStackification G₂)
    (H : Y₁ ⟶ Y₂)
    (α : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂) :
    ∀ (H' : Y₁ ⟶ Y₂)
      (α' : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H' ≅ G₂),
      ∃! β : H ≅ H',
        ((stackification_comparison_precompose_functor (J := J) (G := G₁)).mapIso β) ≪≫ α' =
          α := by
  -- The assembly file contains the completed coverwise uniqueness argument; reuse that stable
  -- owner-level theorem instead of duplicating the descent proof in this item file.
  exact
    comparison_stackification_compatible_twoIso_unique_direct_assembly
      (J := J) G₁ G₂ hG₁ hG₂ H α

/-- Helper for Lemma 8.8.1: uniqueness belongs to the comparison pair `(H, α)`, not to the raw
type of compatible isomorphisms for a fixed `H`. Given one comparison pair, every other pair is
connected to it by a unique `2`-isomorphism whose image under precomposition carries the second
comparison isomorphism to the first. -/
private theorem comparison_stackification_compatible_twoIso_unique
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (G₂ : X ⟶ Y₂)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    (hG₂ : FibredCategoryMor.IsStackification G₂)
    (H : Y₁ ⟶ Y₂)
    (α : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂) :
    ∀ (H' : Y₁ ⟶ Y₂)
      (α' : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H' ≅ G₂),
      ∃! β : H ≅ H',
        ((stackification_comparison_precompose_functor (J := J) (G := G₁)).mapIso β) ≪≫ α' =
          α := by
  -- This is the same statement as the direct coverwise uniqueness proof.
  exact
    comparison_stackification_compatible_twoIso_unique_direct (J := J) G₁ G₂ hG₁ hG₂ H α

variable (X : FibredCategoryOver.{u, v, max u (max v uX), max v vX} C)

/-- Lemma 8.8.1 (1): every fibred category over a site admits a morphism to a stack whose induced
maps on fiberwise morphism presheaves identify the targets with the sheafifications of the
sources, and whose target objects are locally in the essential image on each fiber. -/
@[stacks 02ZN]
theorem exists_stackification :
    ∃ Y : StackOver.{u, v, max u (max v uX), max v vX} J,
      ∃ G : X ⟶ Y,
        FibredCategoryMor.IsStackification G := by
  -- Route correction: the existence proof has to follow the source's two-stage construction,
  -- first forcing local gluing on morphisms and then adjoining descent-data objects.
  -- Strictify first, so the remaining source-faithful blocker is only the split Cat-valued
  -- stackification construction promised by the source proof.
  obtain ⟨Xₛ, e, hXₛSplit⟩ := split_fibred_category_model_exists.{u, v, uX, vX} (C := C) X
  let E : X ⟶ Xₛ := by
    change FibredCategoryOver.ofFunctor X.p ⟶ Xₛ
    exact e.hom
  have hE : FibredCategoryMor.IsEquivalenceOverBase E := by
    change FibredCategoryMor.IsEquivalenceOverBase e.hom
    exact FibredCategoryOver.hom_isEquivalenceOverBase e
  letI : Functor.IsSplitFibredCategory Xₛ.p := hXₛSplit
  -- Apply the split-case construction, then transport the resulting stackification back across
  -- the strictification equivalence on the source.
  obtain ⟨Y, Gₛ, hGₛ⟩ :=
    exists_stackification_of_split_fibred_category.{u, v, uX, vX} (J := J) (X := Xₛ)
  refine ⟨Y, E ≫ Gₛ, ?_⟩
  exact isStackification_comp_left_of_isEquivalenceOverBase E hE Gₛ hGₛ

/-- Lemma 8.8.1 (2): a stackification of a fibred category over a site is unique in the
2-categorical sense. There is a comparison equivalence `H` and a compatible comparison
isomorphism `α`; moreover any other comparison pair `(H', α')` is connected to `(H, α)` by a
unique compatible `2`-isomorphism. This matches the source phrase that the stackification is
"determined up to unique 2-isomorphism" without incorrectly forcing the type of comparison
isomorphisms for one fixed `H` to be a subsingleton. -/
@[stacks 02ZN]
theorem stackification_unique_up_to_unique_twoIso
    {Y₁ Y₂ : StackOver.{u, v, max u (max v uX), max v vX} J}
    (G₁ : X ⟶ Y₁)
    (G₂ : X ⟶ Y₂)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    (hG₂ : FibredCategoryMor.IsStackification G₂) :
    ∃ H : Y₁ ⟶ Y₂,
      IsEquivalenceOverBase H ∧
        ∃ α : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂,
          ∀ (H' : Y₁ ⟶ Y₂)
            (α' : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H' ≅ G₂),
            ∃! β : H ≅ H',
              ((stackification_comparison_precompose_functor (J := J) (G := G₁)).mapIso β) ≪≫
                α' = α := by
  -- Route correction: choose the comparison morphism directly from the stackification data,
  -- rather than reviving the stronger universal property for every stack target.
  obtain ⟨H, ⟨α⟩⟩ := stackification_comparison_exists (J := J) G₁ G₂ hG₁ hG₂
  have hHeq : IsEquivalenceOverBase H :=
    comparison_stackification_isEquivalenceOverBase (J := J) G₁ G₂ hG₁ hG₂ H α
  refine ⟨H, hHeq, ?_⟩
  refine ⟨?_, ?_⟩
  · change (local_stackification_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂
    exact α
  · exact
      comparison_stackification_compatible_twoIso_unique_direct
        (J := J) G₁ G₂ hG₁ hG₂ H
        (by
          change (local_stackification_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂
          exact α)

end

end CategoryTheory
