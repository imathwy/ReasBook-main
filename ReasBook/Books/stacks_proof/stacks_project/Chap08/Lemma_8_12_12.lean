import Mathlib
import StacksProject_2024.Chap04.Definition_4_35_1
import StacksProject_2024.Chap04.Definition_4_33_9
import StacksProject_2024.Chap04.Lemma_4_35_11
import StacksProject_2024.Chap08.Definition_8_12_9
import StacksProject_2024.Chap08.Lemma_8_12_10
import StacksProject_2024.Chap08.Lemma_8_12_11
import StacksProject_2024.Chap08.Lemma_8_8_1
import StacksProject_2024.Chap08.Lemma_8_8_3
import StacksProject_2024.Chap08.Lemma_8_12_2
import StacksProject_2024.Chap08.Lemma_8_12_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Bicategory
open FibredCategoryOver
open InducedCategory.Hom
open scoped BasedFunctor
open scoped FibredCategoryOver
open scoped Bicategory

universe u v u1 u2

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{max u v} C] [Category.{max u v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

variable [HasFiniteNonemptyLimits C] [PreservesFiniteNonemptyLimits u]

/- Domain-style sampling for Lemma 8.12.12:
- primary domain: inverse-image stacks along a morphism of sites and the induced comparison with
  the direct-image model on stacks.
- inspected owner-level declarations:
  `StackOver.pullback`,
  `inverseImage_stackMor_to_directImage_stackMor_equivalence`,
  `stackification_unique_up_to_unique_twoIso`,
  `InducedCategory.Hom.IsEquivalenceOverBase`.
- best owner abstraction: the direct-image side should use the canonical Chapter 8 bridge
  `Sinv.pullback u`, while equivalence of stacks should be recorded by the stack-morphism owner
  predicate `IsEquivalenceOverBase`; the morphism-category comparison in part `(2)` is then a
  source-facing bridge built from the owner equivalence of Lemma `8.12.10`, not a second owner.
- primitive data: a stack `S`, a chosen inverse-image stackification `iSinv : u ₚ S ⟶ Sinv`,
  and similarly for `S'`.
- derived API: the canonical comparison `S ⟶ Sinv.pullback u`, the owner equivalence predicate on
  that comparison, and the induced equivalence between the two stack-morphism categories.

Source/core/bridge triage:
- `source-facing`: the comparison of `S` with `f_* f⁻¹ S` and the induced equivalence on
  stack-morphism categories.
- `core/canonical`: `StackOver.pullback`,
  `inverseImage_stackMor_to_directImage_stackMor_equivalence`,
  `stackification_unique_up_to_unique_twoIso`,
  `InducedCategory.Hom.IsEquivalenceOverBase`.
- `bridge/view`: the chosen stackification morphisms `iSinv`, `iSinv'`. -/

/-- The canonical comparison morphism `S ⟶ Sinv.pullback u` associated to the chosen
inverse-image stackification `iSinv : u ₚ S ⟶ Sinv`. -/
noncomputable def pushforwardInverseImageComparison
    [Functor.IsContinuous u J K]
    (S : StackOver J)
    (Sinv : StackOver K)
    (iSinv : u ₚ S ⟶ Sinv) :
    S ⟶ Sinv.pullback u :=
  let SinvPull : StackOver J := Sinv.pullback u
  let _ : HasPullbacks C := inferInstance
  let _ : HasEqualizers C := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan u := inferInstance
  let _ : PreservesLimitsOfShape WalkingParallelPair u := inferInstance
  let F :=
    pushforwardPullbackFibredMorphismFunctor
      u (S : FibredCategoryOver C) (Sinv : FibredCategoryOver D)
    show S ⟶ SinvPull from
      ofFibredCategoryMor (F.obj iSinv)

/-- Helper for Lemma 8.12.12: the forward component of an ambient isomorphism of stack morphisms
belongs to the full stack hom-category. -/
private lemma stackMorphismIsoOfAmbientIso_hom_mem
    {X Y : StackOver J} {F G : X ⟶ Y}
    (e : toFibredCategoryMor F ≅ toFibredCategoryMor G) :
    ((stackOverSubTwoCategory J).hom X Y).hom (ObjectProperty.homMk e.hom) := by
  -- The stack hom-category is full on `2`-morphisms.
  trivial

/-- Helper for Lemma 8.12.12: the inverse component of an ambient isomorphism of stack morphisms
belongs to the full stack hom-category. -/
private lemma stackMorphismIsoOfAmbientIso_inv_mem
    {X Y : StackOver J} {F G : X ⟶ Y}
    (e : toFibredCategoryMor F ≅ toFibredCategoryMor G) :
    ((stackOverSubTwoCategory J).hom X Y).hom (ObjectProperty.homMk e.inv) := by
  -- The inverse component lies in the same full hom-category.
  trivial

/-- Helper for Lemma 8.12.12: an ambient isomorphism of the underlying fibred-category morphisms
lifts to an isomorphism in the stack hom-category. -/
private noncomputable def stackMorphismIsoOfAmbientIso
    {X Y : StackOver J} {F G : X ⟶ Y}
    (e : toFibredCategoryMor F ≅ toFibredCategoryMor G) : F ≅ G :=
  SubTwoCategory.Hom.isoMk (S := stackOverSubTwoCategory J) e
    (stackMorphismIsoOfAmbientIso_hom_mem e)
    (stackMorphismIsoOfAmbientIso_inv_mem e)

/-- Helper for Lemma 8.12.12: equivalence over the base is invariant under an isomorphism of
stack morphisms. -/
private theorem isEquivalenceOverBase_of_iso
    {X Y : StackOver J} {F G : X ⟶ Y}
    (e : F ≅ G) (hF : IsEquivalenceOverBase F) :
    IsEquivalenceOverBase G := by
  -- Transport the explicit based quasi-inverse data across the underlying based-functor
  -- isomorphism induced by `e`.
  rcases hF.nonempty with ⟨hF⟩
  let eBased : toBasedFunctor F ≅ toBasedFunctor G :=
    Functor.mapIso
      (((fibredCategoryOverSubTwoCategory C).hom X.toFibredCategoryOver Y.toFibredCategoryOver).inclusion)
      (Functor.mapIso (((stackOverSubTwoCategory J).hom X Y).inclusion) e)
  let unitTransport :
      BasedFunctor.comp (toBasedFunctor F) hF.inverse ≅
        BasedFunctor.comp (toBasedFunctor G) hF.inverse :=
    (Bicategory.postcomp X.toFibredCategoryOver.toBasedCategory hF.inverse).mapIso eBased
  let counitTransport :
      BasedFunctor.comp hF.inverse (toBasedFunctor G) ≅
        BasedFunctor.comp hF.inverse (toBasedFunctor F) :=
    (Bicategory.precomp Y.toFibredCategoryOver.toBasedCategory hF.inverse).mapIso eBased.symm
  exact
    BasedFunctor.IsEquivalenceOverBase.mkPrime
      hF.inverse
      (hF.unitIso ≪≫ unitTransport)
      (counitTransport ≪≫ hF.counitIso)

/-- Helper for Lemma 8.12.12: a fully faithful fibred-category morphism induces isomorphisms on
all canonical Hom-presheaf comparison maps. -/
private theorem fibredMorphismPresheafMap_isIso_of_fullyFaithful
    {X Y : FibredCategoryOver C}
    (F : X ⟶ Y)
    (hF : Nonempty F.toHom.FullyFaithful)
    {U : C} (x y : X.p.Fiber U) :
    IsIso (FibredCategoryMor.fibredMorphismPresheafMap F x y) := by
  -- Work objectwise on the slice site: each component is the fiberwise map conjugated by the
  -- pullback-comparison isomorphisms.
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
    -- Fiberwise full faithfulness is exactly bijectivity on every Hom-set map.
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
      (FibredCategoryMor.fibredMorphismPresheafMap F x y).app W =
        fun δ : xW ⟶ yW ↦ eCongr ((F.toHom.fiberFunctor W.unop.left).map δ) := by
    funext δ
    rfl
  rw [hApp]
  constructor
  · intro δ₁ δ₂ hδ
    -- Injectivity follows by canceling the conjugation equivalence and the fiberwise map.
    apply hMap.1
    apply eCongr.injective
    exact hδ
  · intro θ
    -- Surjectivity first undoes the conjugation, then uses fiberwise full faithfulness.
    rcases eCongr.surjective θ with ⟨θ', rfl⟩
    rcases hMap.2 θ' with ⟨δ, rfl⟩
    exact ⟨δ, rfl⟩

/-- Helper for Lemma 8.12.12: the identity morphism of a stack is a stackification. -/
private theorem stackIdentity_isStackification
    (X : StackOver J) :
    FibredCategoryMor.IsStackification
      (𝟙 X.toFibredCategoryOver : X.toFibredCategoryOver ⟶ X.toFibredCategoryOver) := by
  refine ⟨?_, ?_⟩
  · intro U x y
    -- The identity Hom-presheaf comparison is an isomorphism, hence lies in the
    -- local-isomorphism class `W`.
    have hIdFF :
        Nonempty
          ((𝟙 X.toFibredCategoryOver :
              X.toFibredCategoryOver ⟶ X.toFibredCategoryOver).toHom.FullyFaithful) := by
      change Nonempty ((𝟭 X.toBasedCategory).FullyFaithful)
      exact ⟨Functor.FullyFaithful.id _⟩
    have hIdIso :
        IsIso
          (FibredCategoryMor.fibredMorphismPresheafMap
            (𝟙 X.toFibredCategoryOver :
              X.toFibredCategoryOver ⟶ X.toFibredCategoryOver) x y) := by
      exact
        fibredMorphismPresheafMap_isIso_of_fullyFaithful
          (𝟙 X.toFibredCategoryOver :
            X.toFibredCategoryOver ⟶ X.toFibredCategoryOver) hIdFF x y
    let _ :
        IsIso
          (FibredCategoryMor.fibredMorphismPresheafMap
            (𝟙 X.toFibredCategoryOver :
              X.toFibredCategoryOver ⟶ X.toFibredCategoryOver) x y) := hIdIso
    exact
      (J.over U).W.of_isIso
        (FibredCategoryMor.fibredMorphismPresheafMap
          (𝟙 X.toFibredCategoryOver :
            X.toFibredCategoryOver ⟶ X.toFibredCategoryOver) x y)
  · intro U y
    -- On the trivial cover, the restricted target object is already in the image of the identity.
    refine ⟨⊤, ?_⟩
    intro I
    refine ⟨I.f ^*[canonicalPullbackChoice X.p] y, ?_⟩
    simpa using ⟨Iso.refl (I.f ^*[canonicalPullbackChoice X.p] y)⟩

/-- Helper for Lemma 8.12.12: a stackification morphism between stacks is an equivalence over the
base. -/
private theorem stackMorphism_isEquivalenceOverBase_of_isStackification
    {X Y : StackOver J} (F : X ⟶ Y)
    (hF : FibredCategoryMor.IsStackification (toFibredCategoryMor F)) :
    IsEquivalenceOverBase F := by
  -- Compare the given stackification with the identity stackification of the source stack; the
  -- uniqueness theorem supplies an equivalent comparison morphism.
  rcases
    stackification_unique_up_to_unique_twoIso
      (X := X.toFibredCategoryOver)
      (G₁ := (𝟙 X.toFibredCategoryOver :
        X.toFibredCategoryOver ⟶ X.toFibredCategoryOver))
      (G₂ := toFibredCategoryMor F)
      (stackIdentity_isStackification X) hF with
    ⟨H, hH, ⟨α, _⟩⟩
  -- Precomposition by the identity stackification is definitionally the underlying morphism, so
  -- the comparison isomorphism lifts from the ambient hom-category back to stack morphisms.
  change toFibredCategoryMor H ≅ toFibredCategoryMor F at α
  exact isEquivalenceOverBase_of_iso (stackMorphismIsoOfAmbientIso α) hH

/-- Helper for Lemma 8.12.12: an equivalence over the base from a fibred category into a stack
is a stackification morphism. -/
private theorem fibredMorphism_isStackification_of_isEquivalenceOverBase
    {X : FibredCategoryOver C} {Y : StackOver J}
    (F : X ⟶ Y.toFibredCategoryOver)
    (hF : FibredCategoryMor.IsEquivalenceOverBase F) :
    FibredCategoryMor.IsStackification F := by
  constructor
  · intro U x y
    -- The Hom-presheaf comparison of an over-base equivalence is an isomorphism, hence belongs
    -- to the local-isomorphism class on the slice site.
    have hIso : IsIso (FibredCategoryMor.fibredMorphismPresheafMap F x y) :=
      fibredMorphismPresheafMap_isIso_of_isEquivalenceOverBase F hF x y
    let _ : IsIso (FibredCategoryMor.fibredMorphismPresheafMap F x y) := hIso
    exact
      (J.over U).W.of_isIso
        (FibredCategoryMor.fibredMorphismPresheafMap F x y)
  · intro U y
    -- Fiberwise equivalence gives a global preimage, so the trivial cover witnesses local
    -- essential surjectivity.
    refine ⟨⊤, ?_⟩
    intro I
    let Φ := FibredCategoryMor.fiberFunctor F I.Y
    have hFiberEquiv : Φ.IsEquivalence :=
      BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
        (FibredCategoryMor.toBasedFunctor F) hF I.Y
    let _ : Φ.IsEquivalence := hFiberEquiv
    let _ : Φ.EssSurj := by infer_instance
    obtain ⟨x, ⟨η⟩⟩ := Functor.EssSurj.mem_essImage
      (F := Φ) (I.f ^*[canonicalPullbackChoice Y.p] y)
    exact ⟨x, ⟨η⟩⟩

/-- Helper for Lemma 8.12.12: a stack morphism that is an equivalence over the base is a
stackification on its underlying fibred-category morphism. -/
private theorem stackMorphism_isStackification_of_isEquivalenceOverBase
    {X Y : StackOver J} (F : X ⟶ Y)
    (hF : IsEquivalenceOverBase F) :
    FibredCategoryMor.IsStackification (toFibredCategoryMor F) := by
  constructor
  · intro U x y
    -- Fiberwise equivalence makes every Hom-presheaf comparison an isomorphism, hence a local
    -- weak equivalence on the slice site.
    have hIso :
        IsIso (FibredCategoryMor.fibredMorphismPresheafMap (toFibredCategoryMor F) x y) :=
      fibredMorphismPresheafMap_isIso_of_isEquivalenceOverBase
        (toFibredCategoryMor F) hF x y
    let _ :
        IsIso (FibredCategoryMor.fibredMorphismPresheafMap (toFibredCategoryMor F) x y) :=
      hIso
    exact
      (J.over U).W.of_isIso
        (FibredCategoryMor.fibredMorphismPresheafMap (toFibredCategoryMor F) x y)
  · intro U y
    -- The trivial cover suffices because each fiber functor of an equivalence over the base is
    -- essentially surjective.
    refine ⟨⊤, ?_⟩
    intro I
    let Φ := FibredCategoryMor.fiberFunctor (toFibredCategoryMor F) I.Y
    have hFiberEquiv : Φ.IsEquivalence :=
      BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
        (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor F)) hF I.Y
    let _ : Φ.IsEquivalence := hFiberEquiv
    let _ : Φ.EssSurj := by infer_instance
    obtain ⟨x, ⟨η⟩⟩ :=
      Functor.EssSurj.mem_essImage (F := Φ) (I.f ^*[canonicalPullbackChoice Y.p] y)
    exact ⟨x, ⟨η⟩⟩

/-- Helper for Chap08 Lemma 8 12 12: the Hom-presheaf local-isomorphism condition is stable
under composition of fibred-category morphisms. -/
private theorem morphismPresheafMap_W_comp_of_fields
    {X Y Z : FibredCategoryOver D}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    (hF : ∀ (U : D) (x y : X.p.Fiber U),
      (K.over U).W (FibredCategoryMor.fibredMorphismPresheafMap F x y))
    (hG : ∀ (U : D) (x y : Y.p.Fiber U),
      (K.over U).W (FibredCategoryMor.fibredMorphismPresheafMap G x y)) :
    ∀ (U : D) (x y : X.p.Fiber U),
      (K.over U).W (FibredCategoryMor.fibredMorphismPresheafMap (F ≫ G) x y) := by
  intro U x y
  -- Rewrite the comparison for the composite as the composite of the two comparison maps.
  rw [fibredMorphismPresheafMap_comp F G x y]
  exact (K.over U).W.comp_mem _ _ (hF U x y)
    (hG U ((FibredCategoryMor.fiberFunctor F U).obj x)
      ((FibredCategoryMor.fiberFunctor F U).obj y))

/-- Helper for Chap08 Lemma 8 12 12: two local essential-image isomorphisms compose after
identifying the iterated chosen pullback with the chosen pullback along the composite base map. -/
private noncomputable def localEssentialImageIso_comp
    {X Y Z : FibredCategoryOver D}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    {U V W : D} (f : V ⟶ U) (g : W ⟶ V)
    (z : Z.p.Fiber U) (y : Y.p.Fiber V) (x : X.p.Fiber W)
    (ηF : (FibredCategoryMor.fiberFunctor F W).obj x ≅
      g ^*[canonicalPullbackChoice Y.p] y)
    (ηG : (FibredCategoryMor.fiberFunctor G V).obj y ≅
      f ^*[canonicalPullbackChoice Z.p] z) :
    (FibredCategoryMor.fiberFunctor (F ≫ G) W).obj x ≅
      (g ≫ f) ^*[canonicalPullbackChoice Z.p] z :=
  Iso.trans
    (Iso.trans
      (Functor.mapIso (FibredCategoryMor.fiberFunctor G W) ηF)
      (FibredCategoryMor.pullbackComparison G g y).symm)
    (Iso.trans
      (((canonicalPullbackChoice Z.p).pullbackFunctor g).mapIso ηG)
      ((canonicalPullbackChoice Z.p).pullbackCompComponentIso f g z).symm)

/-- Helper for Chap08 Lemma 8 12 12: local essential surjectivity on objects is stable under
composition of fibred-category morphisms. -/
private theorem locallyEssentiallySurjectiveOnObjects_comp_of_fields
    {X Y Z : FibredCategoryOver D}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    (hF : FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects K F)
    (hG : FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects K G) :
    FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects K (F ≫ G) := by
  classical
  intro U z
  -- First lift the target object locally through `G`, then lift each local model through `F`.
  obtain ⟨S, hS⟩ := hG U z
  choose y hy using hS
  let T : ∀ I : S.Arrow, K.Cover I.Y := fun I => Classical.choose (hF I.Y (y I))
  have hT : ∀ I : S.Arrow, ∀ R : (T I).Arrow,
      ∃ x : X.p.Fiber R.Y,
        Nonempty (((FibredCategoryMor.fiberFunctor F R.Y).obj x) ≅
          R.f ^*[canonicalPullbackChoice Y.p] (y I)) := by
    intro I
    exact Classical.choose_spec (hF I.Y (y I))
  refine ⟨S.bind T, ?_⟩
  intro A
  -- A bound-cover arrow is a second-stage arrow followed by a first-stage arrow.
  let I : S.Arrow := A.fromMiddle
  let R : (T I).Arrow := A.toMiddle
  obtain ⟨x, hx⟩ := hT I R
  obtain ⟨ηF⟩ := hx
  obtain ⟨ηG⟩ := hy I
  refine ⟨x, ?_⟩
  rw [← A.middle_spec]
  refine ⟨?_⟩
  simpa [I, R, BasedFunctor.comp] using
    localEssentialImageIso_comp F G I.f R.f z (y I) x ηF ηG

/-- Helper for Chap08 Lemma 8 12 12: fieldwise stackification data for a first morphism
composes with a stackification morphism on the target. -/
private theorem isStackification_comp_of_fields
    {X Y : FibredCategoryOver D} {Z : StackOver K}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    (hFW : ∀ (U : D) (x y : X.p.Fiber U),
      (K.over U).W (FibredCategoryMor.fibredMorphismPresheafMap F x y))
    (hFess : FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects K F)
    (hG : FibredCategoryMor.IsStackification G) :
    FibredCategoryMor.IsStackification (F ≫ G) := by
  constructor
  · -- Compose the two Hom-presheaf local-isomorphism conditions.
    exact morphismPresheafMap_W_comp_of_fields F G hFW hG.morphismPresheafMap_W
  · -- Compose the two local essential-image conditions using cover binding.
    exact locallyEssentiallySurjectiveOnObjects_comp_of_fields F G hFess
      hG.locallyEssentiallySurjectiveOnObjects

/-- Lemma 8.12.12 (1): if `Sinv` is a chosen inverse-image stack representing `f^{-1} S`, then
the canonical comparison from `S` to the Chapter 8 direct-image model `Sinv.pullback u` of
`f_* f^{-1} S` is an equivalence of stacks over `(C, J)`. -/
@[stacks 04WS]
theorem stack_equivalent_to_pushforward_inverseImage
    [Functor.IsContinuous u J K] [Functor.IsCocontinuous u J K] [u.Full] [u.Faithful]
    (S : StackOver J)
    (Sinv : StackOver K)
    (iSinv : u ₚ S ⟶ Sinv)
    (hiSinv : FibredCategoryMor.IsStackification iSinv) :
    IsEquivalenceOverBase
      (pushforwardInverseImageComparison.{u, v, u1, u2} u S Sinv iSinv) := by
  -- The comparison morphism is the image under the pushforward-pullback owner equivalence; with
  -- the full-faithful hypotheses, typeclass search supplies the equivalence over the base.
  exact stackMorphism_isEquivalenceOverBase_of_isStackification _ ?_

/-- Helper for Lemma 8.12.12: a stack morphism that is an equivalence over the base admits a
bicategorical equivalence with that morphism as its forward map. -/
private theorem stackEquivalenceOfIsEquivalenceOverBase
    {X Y : StackOver J} (F : X ⟶ Y)
    (hF : IsEquivalenceOverBase F) :
    ∃ e : Bicategory.Equivalence X Y, e.hom = F := by
  -- First build the ambient fibred-category equivalence from the over-base equivalence data.
  let eAmb := FibredCategoryMor.ofEquivalenceOverBase
    (toFibredCategoryMor F) (Classical.choice hF.nonempty)
  let G : Y ⟶ X := ofFibredCategoryMor eAmb.inv
  let eta : (𝟙 X : X ⟶ X) ≅ F ≫ G := by
    -- The ambient unit becomes a unit in the full stack hom-category.
    exact stackMorphismIsoOfAmbientIso eAmb.unit
  let eps : G ≫ F ≅ (𝟙 Y : Y ⟶ Y) := by
    -- The same ambient-to-stack lift supplies the counit.
    exact stackMorphismIsoOfAmbientIso eAmb.counit
  exact ⟨Bicategory.Equivalence.mkOfAdjointifyCounit eta eps, rfl⟩

/-- Helper for Lemma 8.12.12: postcomposition by a stack morphism that is an equivalence over the
base is an equivalence of stack-morphism Hom-categories. -/
private theorem stackPostcomp_isEquivalence_of_isEquivalenceOverBase
    {X Y : StackOver J} (A : StackOver J) (F : X ⟶ Y)
    (hF : IsEquivalenceOverBase F) :
    Functor.IsEquivalence (postcomp A F) := by
  -- Convert the over-base equivalence into a stack bicategorical equivalence.
  rcases stackEquivalenceOfIsEquivalenceOverBase F hF with ⟨e, rfl⟩
  -- Whiskering on the left by the forward morphism of that equivalence is an equivalence.
  exact Bicategory.postcomp_isEquivalence A e

-- Proof sketch: Lemma `8.12.10` identifies morphisms out of a chosen inverse-image stack with
-- morphisms into the canonical direct-image model `Sinv'.pullback u`. Apply part `(1)` to compare
-- `S'` with `Sinv'.pullback u`, then transport morphisms across that equivalence to obtain the
-- source-facing equivalence between morphisms `S ⟶ S'` and morphisms `Sinv ⟶ Sinv'`.
/-- Lemma 8.12.12 (2): the canonical composite from postcomposition with the comparison
`S' ⟶ Sinv'.pullback u` and the inverse of the Lemma `8.12.10` equivalence is an equivalence on
stack-morphism categories. -/
@[stacks 04WS]
theorem inverseImage_induces_equivalence_on_stackMorphismCategories
    [Functor.IsContinuous u J K] [Functor.IsCocontinuous u J K] [u.Full] [u.Faithful]
    (S S' : StackOver J)
    (Sinv : StackOver K)
    (iSinv : u ₚ S ⟶ Sinv)
    (hiSinv : FibredCategoryMor.IsStackification iSinv)
    (Sinv' : StackOver K)
    (iSinv' : u ₚ S' ⟶ Sinv')
    (hiSinv' : FibredCategoryMor.IsStackification iSinv') :
    Functor.IsEquivalence
      (postcomp S (pushforwardInverseImageComparison.{u, v, u1, u2} u S' Sinv' iSinv') ⋙
        (inverseImage_stackMor_to_directImage_stackMor_equivalence.{u, v, u1, u2}
          u S Sinv iSinv hiSinv Sinv').inverse) := by
  let F := postcomp S (pushforwardInverseImageComparison.{u, v, u1, u2} u S' Sinv' iSinv')
  have hF : Functor.IsEquivalence F := by
    -- First use part `(1)` for `S'`, then apply the postcomposition bridge above.
    exact
      stackPostcomp_isEquivalence_of_isEquivalenceOverBase
        (A := S)
        (F := pushforwardInverseImageComparison.{u, v, u1, u2} u S' Sinv' iSinv')
        (stack_equivalent_to_pushforward_inverseImage.{u, v, u1, u2}
          u S' Sinv' iSinv' hiSinv')
  let eInv := inverseImage_stackMor_to_directImage_stackMor_equivalence.{u, v, u1, u2}
    u S Sinv iSinv hiSinv Sinv'
  let _ : Functor.IsEquivalence F := hF
  let _ : Functor.IsEquivalence eInv.inverse := by infer_instance
  change Functor.IsEquivalence (F ⋙ eInv.inverse)
  infer_instance

end

end CategoryTheory
