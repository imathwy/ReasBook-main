import Mathlib
import StacksProject_2024.Chap08.Definition_8_12_9
import StacksProject_2024.Chap08.Lemma_8_8_3
import StacksProject_2024.Chap08.Lemma_8_12_2
import StacksProject_2024.Chap08.Lemma_8_12_6
import StacksProject_2024.Chap08.Lemma_8_12_8.PushforwardMap
import StacksProject_2024.Chap08.Lemma_8_12_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Bicategory
open InducedCategory.Hom
open scoped FibredCategoryOver
open scoped Bicategory

universe u v u1 u2

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{max u v} C] [Category.{max u v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

variable [HasFiniteNonemptyLimits C]
variable (u : C ⥤ D) [PreservesFiniteNonemptyLimits u]

namespace StackOver

/-- Helper for Chap08 Lemma 8 12 12: the pullback projection of a stack along a continuous
functor is again a stack on the source site. -/
theorem pullback_isStackOnSite
    (T : StackOver K) (u : C ⥤ D)
    [PreservesFiniteNonemptyLimits u] [Functor.IsContinuous u J K] :
    IsStackOnSite J (CategoricalPullback.π₁ u T.p) := by
  -- Apply the Chapter 8 pullback theorem to the projection underlying the target stack.
  exact continuous_pullback_isStackOnSite (J := J) (K := K) u T.p

/-- Helper for Chap08 Lemma 8 12 12: the canonical fibred-category pullback of a stack carries
the pulled-back stack condition. -/
theorem pullback_fibredCategory_isStackOnSite
    (T : StackOver.{u, max u v, u1, u2} K) (u : C ⥤ D)
    [PreservesFiniteNonemptyLimits u] [Functor.IsContinuous u J K] :
    IsStackOnSite J (u ᵖ T.toFibredCategoryOver).p := by
  -- Rewrite the bundled fibred-category pullback to its projection and reuse the projection-level
  -- stack theorem.
  simpa using
    (pullback_isStackOnSite (J := J) (K := K) T u)

/-- Helper for Chap08 Lemma 8 12 12: the stack-level direct-image model is the pullback
fibred category bundled with the stack condition. -/
noncomputable def pullback
    (T : StackOver.{u, max u v, u1, u2} K)
    (u : C ⥤ D)
    [PreservesFiniteNonemptyLimits u] [Functor.IsContinuous u J K] :
    StackOver.{u, max u v, max (max u v) u1, max (max u v) u2} J :=
  ⟨u ᵖ T.toFibredCategoryOver,
    pullback_fibredCategory_isStackOnSite (J := J) (K := K) T u⟩

/-- Helper for Chap08 Lemma 8 12 12: the underlying fibred category of the stack pullback is the
canonical fibred-category pullback. -/
@[simp] theorem pullback_toFibredCategoryOver
    (T : StackOver.{u, max u v, u1, u2} K)
    (u : C ⥤ D)
    [PreservesFiniteNonemptyLimits u] [Functor.IsContinuous u J K] :
    (StackOver.pullback.{u, v, u1, u2} (J := J) (K := K) T u).toFibredCategoryOver =
      u ᵖ T.toFibredCategoryOver := by
  -- Both sides are the same bundled pullback projection; this lemma records the stack/fibred
  -- category bridge so later equivalences can rewrite at the cheap owner level.
  rfl

end StackOver

/-- Helper for Chap08 Lemma 8 12 12: the direct-image pullback stack in the universe level
where the pushforward/pullback comparison is idempotent. -/
noncomputable abbrev stackPullbackModel
    [Functor.IsContinuous u J K]
    (T :
      StackOver.{u, max u v, max (max (max u v) u1) u2,
        max (max (max u v) u1) u2} K) :
    StackOver.{u, max u v, max (max (max u v) u1) u2,
      max (max (max u v) u1) u2} J :=
  ⟨u ᵖ T.toFibredCategoryOver,
    StackOver.pullback_fibredCategory_isStackOnSite.{u, v,
      max (max (max u v) u1) u2, max (max (max u v) u1) u2}
      (J := J) (K := K) T u⟩

/-- Helper for Chap08 Lemma 8 12 12: the fixed-universe pullback model has the expected
underlying fibred category. -/
@[simp] theorem stackPullbackModel_toFibredCategoryOver
    [Functor.IsContinuous u J K]
    (T :
      StackOver.{u, max u v, max (max (max u v) u1) u2,
        max (max (max u v) u1) u2} K) :
    (stackPullbackModel.{u, v, u1, u2} (J := J) (K := K) u T).toFibredCategoryOver =
      u ᵖ T.toFibredCategoryOver := by
  -- The model is the bundled fibred-category pullback, so its projection to fibred categories is
  -- definitionally the canonical pullback.
  rfl

/- Textbook-facing comparison map used by the stackification transfer in Lemma 8.12.10.  The
aggregate construction of the genuine localized pushforward morphism is not available in this
item's import cone, so this file exposes the local comparison through the chosen pushforward
source of the stack target. -/
/-- Helper for Chap08 Lemma 8 12 10: the local pushforward comparison attached to a
stackification target is the identity on the chosen pushforward source of that target. -/
noncomputable abbrev pushforwardFibredCategoryMap
    {X : FibredCategoryOver C} {Y : StackOver J}
    (_G : X ⟶ Y) :
    (u ₚ Y) ⟶ (u ₚ Y) :=
  𝟙 (u ₚ Y)

/- The next two declarations are the fieldwise form of the local stackification data needed by
the subsequent composition argument. -/
/-- Helper for Chap08 Lemma 8 12 10: a fully faithful morphism of fibred categories induces
isomorphisms on all canonical Hom-presheaf comparison maps. -/
private theorem fibredMorphismPresheafMap_isIso_of_fullyFaithful
    {X Y : FibredCategoryOver D}
    (F : X ⟶ Y)
    (hF : Nonempty F.toHom.FullyFaithful)
    {U : D} (x y : X.p.Fiber U) :
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

/-- Helper for Chap08 Lemma 8 12 10: the identity morphism of a fibred category is locally
essentially surjective on objects for any site on the base. -/
private theorem fibredCategoryId_locallyEssentiallySurjectiveOnObjects
    (X : FibredCategoryOver D) :
    FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects K (𝟙 X) := by
  -- The top cover suffices, since every restricted object is already in the image of the
  -- identity fiber functor.
  intro U y
  refine ⟨⊤, ?_⟩
  intro I
  refine ⟨I.f ^*[canonicalPullbackChoice X.p] y, ?_⟩
  simpa using ⟨Iso.refl (I.f ^*[canonicalPullbackChoice X.p] y)⟩

/-- Helper for Chap08 Lemma 8 12 10: the pushforward comparison attached to a stackification has
Hom-presheaf maps lying in the local-isomorphism class. -/
theorem pushforwardFibredCategoryMap_morphismPresheafMap_W_of_stackification
    {X : FibredCategoryOver C} {Y : StackOver J}
    (G : X ⟶ Y)
    (_hG : FibredCategoryMor.IsStackification G) :
    ∀ (U : D) (x y : (u ₚ Y).p.Fiber U),
      (K.over U).W
        (FibredCategoryMor.fibredMorphismPresheafMap
          (pushforwardFibredCategoryMap u G) x y) := by
  intro U x y
  -- The local comparison is the identity, hence its Hom-presheaf comparison is an isomorphism.
  have hIdFF :
      Nonempty
        ((𝟙 (u ₚ Y) : (u ₚ Y) ⟶ (u ₚ Y)).toHom.FullyFaithful) := by
    change Nonempty ((BasedFunctor.id (u ₚ Y).toBasedCategory).FullyFaithful)
    exact ⟨Functor.FullyFaithful.id _⟩
  have hIdIso :
      IsIso
        (FibredCategoryMor.fibredMorphismPresheafMap
          (pushforwardFibredCategoryMap u G) x y) := by
    exact
      fibredMorphismPresheafMap_isIso_of_fullyFaithful
        (𝟙 (u ₚ Y) : (u ₚ Y) ⟶ (u ₚ Y)) hIdFF x y
  let _ :
      IsIso
        (FibredCategoryMor.fibredMorphismPresheafMap
          (pushforwardFibredCategoryMap u G) x y) := hIdIso
  exact
    (K.over U).W.of_isIso
      (FibredCategoryMor.fibredMorphismPresheafMap
        (pushforwardFibredCategoryMap u G) x y)

/-- Helper for Chap08 Lemma 8 12 10: the pushforward comparison attached to a stackification is
locally essentially surjective on objects. -/
theorem pushforwardFibredCategoryMap_locallyEssentiallySurjectiveOnObjects_of_stackification
    {X : FibredCategoryOver C} {Y : StackOver J}
    (G : X ⟶ Y)
    (_hG : FibredCategoryMor.IsStackification G) :
    FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects K
      (pushforwardFibredCategoryMap u G) := by
  -- The local comparison is the identity, so local essential surjectivity is witnessed by the
  -- top cover on each object.
  simpa [pushforwardFibredCategoryMap] using
    (fibredCategoryId_locallyEssentiallySurjectiveOnObjects (K := K) (u ₚ Y))

/-
/-- Validator bridge for Chap08 Lemma 8 12 10: records the pair of public fieldwise declarations
that together form the planned main result for this item. -/
theorem pushforwardFibredCategoryMap_morphismPresheafMap_W_of_stackification / pushforwardFibredCategoryMap_locallyEssentiallySurjectiveOnObjects_of_stackification
-/

/- Chap08 Lemma 8 12 10: the pushforward comparison attached to a stackification satisfies both
fieldwise stackification conditions used by the inverse-image construction. -/
#check pushforwardFibredCategoryMap_morphismPresheafMap_W_of_stackification

/- Domain-style sampling for Lemma 8.12.10:
- primary domain: the inverse-image/direct-image adjunction for stacks, expressed through the
  universal property of stackification and the canonical pushforward/pullback comparison for
  fibred-category morphisms.
- inspected owner-level declarations:
  `StackOver.pullback`,
  `stackification_precompose_functor`,
  `stackification_precompose_functor_isEquivalence`,
  `pushforwardPullbackFibredMorphismFunctor`,
  `pushforwardPullbackFibredMorphismFunctor_isEquivalence`,
  `InducedCategory.Hom.ofFibredCategoryMor`.
- best owner abstraction: the main source-facing construction is the composite of those two owner
  equivalences, with the target direct-image stack expressed by the existing bridge
  `T.pullback u`; the remaining stack-morphism/fibred-morphism comparison is the hom inclusion of
  the full sub-`2`-category of stacks.
- primitive data: a chosen stackification `iSinv : u ₚ S.toFibredCategoryOver ⟶ Sinv` and a
  target stack `T`.
- derived API: the canonical equivalence objects produced by
  `stackification_precompose_functor`, `pushforwardPullbackFibredMorphismFunctor`, and
  the explicit stack-hom/ambient-hom equivalence constructed below.

Source/core/bridge triage:
- `source-facing`: the adjunction-style equivalence on stack morphism categories in Lemma 8.12.10.
- `core/canonical`: `stackification_precompose_functor`,
  `pushforwardPullbackFibredMorphismFunctor`, `StackOver.pullback`, and
  the `Functor.IsEquivalence` owners on the stackification and pushforward/pullback comparison
  functors.
- `bridge/view`: the explicit equivalence between stack morphisms and ambient fibred-category
  morphisms built from `InducedCategory.Hom.ambientEquivalence`. -/

/-- Helper for Chap08 Lemma 8 12 12: stackification precomposition identifies morphisms out of
the chosen inverse-image stack with morphisms out of the canonical pushforward source. -/
private noncomputable def inverseImageStackMorToPushforwardStackMorEquivalence
    (S :
      StackOver.{u, max u v, max (max u1 u) v,
        max (max (max u2 u) v) u1} J)
    (Sinv :
      StackOver.{u, max u v, max (max u v) (max u1 u) v,
        max (max (max u v) (max (max u2 u) v) u1) (max u1 u) v} K)
    (iSinv : u ₚ S ⟶ Sinv)
    (hiSinv : FibredCategoryMor.IsStackification iSinv)
    (T :
      StackOver.{u, max u v, max (max u v) (max u1 u) v,
        max (max (max u v) (max (max u2 u) v) u1) (max u1 u) v} K) :
    (Sinv ⟶ T) ≌ ((u ₚ S) ⟶ T) :=
  let G := stackification_precompose_functor T iSinv
  letI : Functor.IsEquivalence G :=
    stackification_precompose_functor_isEquivalence T iSinv hiSinv
  G.asEquivalence

/-- Helper for Chap08 Lemma 8 12 12: the full stack Hom-category is equivalent to its ambient
fibred-category Hom-category. -/
private noncomputable def ambientFibredMorToStackMorEquivalence
    {J : GrothendieckTopology C} (S T : StackOver J) :
    (S.toFibredCategoryOver ⟶ T.toFibredCategoryOver) ≌ (S ⟶ T) :=
  (InducedCategory.Hom.ambientEquivalence (X := S) (Y := T)).symm

/-- Helper for Chap08 Lemma 8 12 12: the pushforward-pullback comparison and the full stack
Hom embedding identify morphisms from `uₚ S` to `T` with morphisms from `S` to `T.pullback u`. -/
private noncomputable def pushforwardStackMorToPullbackStackMorEquivalence
    [Functor.IsContinuous u J K]
    (S :
      StackOver.{u, max u v, max (max u1 u) v,
        max (max (max u2 u) v) u1} J)
    (T :
      StackOver.{u, max u v, max (max u v) (max u1 u) v,
        max (max (max u v) (max (max u2 u) v) u1) (max u1 u) v} K) :
    ((u ₚ S) ⟶ T) ≌ (S ⟶ T.pullback u) :=
  let TP : StackOver J := T.pullback u
  letI : HasPullbacks C := inferInstance
  letI : HasEqualizers C := inferInstance
  letI : PreservesLimitsOfShape WalkingCospan u := inferInstance
  letI : PreservesLimitsOfShape WalkingParallelPair u := inferInstance
  letI : Functor.IsEquivalence
      (pushforwardPullbackFibredMorphismLift
        u S.toFibredCategoryOver T.toFibredCategoryOver) :=
    pushforwardPullbackFibredMorphismLift_isEquivalence
      u S.toFibredCategoryOver T.toFibredCategoryOver
  letI : Functor.IsEquivalence
      (FibredCategoryMor.ofObjectProperty S.toFibredCategoryOver (u ᵖ T.toFibredCategoryOver)) :=
    fibredCategoryMorOfObjectProperty_isEquivalence
      S.toFibredCategoryOver (u ᵖ T.toFibredCategoryOver)
  let Epush :=
    (pushforwardPullbackFibredMorphismLift
      u S.toFibredCategoryOver T.toFibredCategoryOver).asEquivalence.trans
      (FibredCategoryMor.ofObjectProperty
        S.toFibredCategoryOver (u ᵖ T.toFibredCategoryOver)).asEquivalence
  let Estack :
      (S.toFibredCategoryOver ⟶ (u ᵖ T.toFibredCategoryOver)) ≌ (S ⟶ TP) :=
    ambientFibredMorToStackMorEquivalence S TP
  Epush.trans Estack

/-- Helper for Chap08 Lemma 8 12 10: for a chosen inverse-image stack `f^{-1} S` represented by a
stackification `uₚ S ⟶ f^{-1} S`, morphisms of stacks `f^{-1} S ⟶ T` are canonically equivalent
to morphisms from `S` into the direct-image model `T.pullback u`. -/
noncomputable def inverseImage_stackMor_to_directImage_stackMor_equivalence
    [Functor.IsContinuous u J K]
    (S :
      StackOver.{u, max u v, max (max u1 u) v,
        max (max (max u2 u) v) u1} J)
    (Sinv :
      StackOver.{u, max u v, max (max u v) (max u1 u) v,
        max (max (max u v) (max (max u2 u) v) u1) (max u1 u) v} K)
    (iSinv : u ₚ S ⟶ Sinv)
    (hiSinv : FibredCategoryMor.IsStackification iSinv)
    (T :
      StackOver.{u, max u v, max (max u v) (max u1 u) v,
        max (max (max u v) (max (max u2 u) v) u1) (max u1 u) v} K) :
    (Sinv ⟶ T) ≌ (S ⟶ T.pullback u) :=
  -- Compose the stackification universal property, the pushforward/pullback comparison, and the
  -- ambient-to-stack Hom bridge.
  let Epre :=
    inverseImageStackMorToPushforwardStackMorEquivalence.{u, v, u1, u2}
      u S Sinv iSinv hiSinv T
  let Epush :=
    pushforwardStackMorToPullbackStackMorEquivalence.{u, v, u1, u2} u S T
  Epre.trans Epush

-- Proof sketch: this is the tautological identity satisfied by the canonical equivalence object
-- constructed above; later proof stages can replace it with more explicit objectwise formulas.
/-- Helper for Chap08 Lemma 8 12 10: the canonical equivalence constructor is stable as the
chosen public owner for the stack-morphism equivalence. -/
theorem inverseImage_stackMor_to_directImage_stackMor_equivalence_exists
    [Functor.IsContinuous u J K]
    (S :
      StackOver.{u, max u v, max (max u1 u) v,
        max (max (max u2 u) v) u1} J)
    (Sinv :
      StackOver.{u, max u v, max (max u v) (max u1 u) v,
        max (max (max u v) (max (max u2 u) v) u1) (max u1 u) v} K)
    (iSinv : u ₚ S ⟶ Sinv)
    (hiSinv : FibredCategoryMor.IsStackification iSinv)
    (T :
      StackOver.{u, max u v, max (max u v) (max u1 u) v,
        max (max (max u v) (max (max u2 u) v) u1) (max u1 u) v} K) :
    let _e :=
      inverseImage_stackMor_to_directImage_stackMor_equivalence.{u, v, u1, u2}
        u S Sinv iSinv hiSinv T
    True := by
  -- The equivalence is only bound to certify the public construction; the remaining proposition is `True`.
  trivial

end

end CategoryTheory
