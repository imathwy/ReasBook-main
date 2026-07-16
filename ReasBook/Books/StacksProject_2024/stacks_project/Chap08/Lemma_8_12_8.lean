import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_35_1
import StacksProject_2024.stacks_project.Chap08.Definition_8_12_4
import StacksProject_2024.stacks_project.Chap08.Lemma_8_12_5
import StacksProject_2024.stacks_project.Chap08.Lemma_8_12_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped FibredCategoryOver
open scoped Functor

universe u v w

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{v} C] [Category.{v} D]

section Pushforward

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/- Domain-style sampling for Lemma 8.12.8:
- primary domain: the pushforward/pullback comparison for morphisms of fibred categories, built
  from the localized pushforward construction and the canonical pullback fibred category.
- inspected owner-level declarations:
  `FibredCategoryOver.pushforward`,
  `FibredCategoryOver.pullback`,
  `Functor.pushforwardProjection`,
  `FibredCategoryMor.objectProperty`,
  `SubTwoCategory.Hom.toHom`,
  `FibredCategoryMor.ofBasedFunctor`,
  `FibredCategoryMor.ofObjectProperty`.
- best owner abstraction: the public bridge should live on `FibredCategoryMor` between the
  canonical bundled objects `u ₚ X` and `u ᵖ Y`, with the strongly-cartesian condition expressed
  through the owner property `FibredCategoryMor.objectProperty` and the underlying based-functor
  comparison derived from the existing owner APIs.
- primitive data: the localized pushforward projection `u.pushforwardProjection X.p`, the unit
  `X.S ⥤ (u ₚ X).S`, and the canonical pullback owner `u ᵖ Y`.
- derived API: `FibredCategoryOver.pushforward`, `pushforwardFibredCategoryMap`,
  `pushforwardFibredCategoryUnit`, and the comparison functor
  `pushforwardPullbackFibredMorphismFunctor`.

Source/core/bridge triage:
- `source-facing`: the equivalence
  `pushforwardPullbackFibredMorphismFunctor_isEquivalence`.
- `core/canonical`: `FibredCategoryOver.pullback`, `Functor.pushforwardProjection`,
  `FibredCategoryMor`.
- `bridge/view`: `FibredCategoryOver.pushforward`, `pushforwardFibredCategoryUnit`, and
  `pushforwardPullbackFibredMorphismFunctor`. -/
namespace FibredCategoryOver

/-- The fibred category over `D` obtained from `X` by the localized pushforward construction
`uₚ X`. -/
noncomputable abbrev pushforward
    (X : FibredCategoryOver C) :
    FibredCategoryOver D :=
  let p := u.pushforwardProjection X.p
  letI : p.IsFibered := inferInstance
  ofFunctor p

/- Textbook notation for the pushforward fibred category of `X` along `u`. -/
scoped infixr:100 " ₚ " => pushforward

/-- The projection of `uₚ X` is the canonical localized pushforward projection
`u.pushforwardProjection X.p`. -/
@[simp] theorem pushforward_p
    (X : FibredCategoryOver C) :
    (u ₚ X).p = u.pushforwardProjection X.p := rfl

end FibredCategoryOver

private abbrev pushforwardFibredCategoryMapPrelocalizedSquare
    {X Y : FibredCategoryOver C} (G : X ⟶ Y) :
    CategoricalPullback.CatCommSqOver
      (Comma.snd (𝟭 D) u) Y.p (u ₚₚ X.p) where
  fst := CategoricalPullback.π₁ (Comma.snd (𝟭 D) u) X.p
  snd := CategoricalPullback.π₂ (Comma.snd (𝟭 D) u) X.p ⋙ FibredCategoryMor.toFunctor G
  iso :=
    (CatCommSq.iso
      (CategoricalPullback.π₁ (Comma.snd (𝟭 D) u) X.p)
      (CategoricalPullback.π₂ (Comma.snd (𝟭 D) u) X.p)
      (Comma.snd (𝟭 D) u) X.p) ≪≫
      eqToIso (by rw [Functor.assoc, FibredCategoryMor.comm G])

private abbrev pushforwardFibredCategoryMapPrelocalizedFunctor
    {X Y : FibredCategoryOver C} (G : X ⟶ Y) :
    u ₚₚ X.p ⥤ u ₚₚ Y.p :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (Comma.snd (𝟭 D) u) Y.p (u ₚₚ X.p)).obj
      (pushforwardFibredCategoryMapPrelocalizedSquare u G)

private theorem pushforwardFibredCategoryMapPrelocalizedFunctor_invertsFractionProperty
    {X Y : FibredCategoryOver C} (G : X ⟶ Y) :
    (u.pushforwardFractions X.p).IsInvertedBy
      (pushforwardFibredCategoryMapPrelocalizedFunctor u G ⋙
        (u.pushforwardFractions Y.p).Q) := sorry

private noncomputable abbrev pushforwardFibredCategoryMapFunctor
    {X Y : FibredCategoryOver C} (G : X ⟶ Y) :
    (u.pushforwardFractions X.p).Localization ⥤
      (u.pushforwardFractions Y.p).Localization :=
  let L := (u.pushforwardFractions X.p).Q
  let _ : L.IsLocalization (u.pushforwardFractions X.p) := inferInstance
  Localization.lift
    (pushforwardFibredCategoryMapPrelocalizedFunctor u G ⋙
      (u.pushforwardFractions Y.p).Q)
    (pushforwardFibredCategoryMapPrelocalizedFunctor_invertsFractionProperty u G)
    L

private theorem pushforwardFibredCategoryMapFunctor_comm
    {X Y : FibredCategoryOver C} (G : X ⟶ Y) :
    pushforwardFibredCategoryMapFunctor u G ⋙ (u ₚ Y).p =
      (u ₚ X).p := sorry

private noncomputable abbrev pushforwardFibredCategoryMapBasedFunctor
    {X Y : FibredCategoryOver C} (G : X ⟶ Y) :
    (u ₚ X).toBasedCategory ⥤ᵇ
      (u ₚ Y).toBasedCategory where
  toFunctor := pushforwardFibredCategoryMapFunctor u G
  w := pushforwardFibredCategoryMapFunctor_comm u G

private theorem pushforwardFibredCategoryMapBasedFunctor_preservesStronglyCartesian
    {X Y : FibredCategoryOver C} (G : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian
      (pushforwardFibredCategoryMapBasedFunctor u G) := sorry

/-- The canonical morphism of localized pushforwards induced by a morphism of fibred categories
over `C`. -/
noncomputable abbrev pushforwardFibredCategoryMap
    {X Y : FibredCategoryOver C} (G : X ⟶ Y) :
    (u ₚ X) ⟶ (u ₚ Y) :=
  FibredCategoryMor.ofBasedFunctor
    (pushforwardFibredCategoryMapBasedFunctor u G)
    (pushforwardFibredCategoryMapBasedFunctor_preservesStronglyCartesian u G)

/-- The canonical functor from `X` to the prelocalized source category `uₚₚ X`. It sends
`x / U` to `(U, id_{u(U)}, x)`. -/
private abbrev pushforwardFibredCategoryUnitPrelocalized
    (u : C ⥤ D) (X : FibredCategoryOver C) :
    X.S ⥤ u ₚₚ X.p where
  obj x :=
    { fst :=
        { left := u.obj (X.p.obj x)
          right := X.p.obj x
          hom := 𝟙 (u.obj (X.p.obj x)) }
      snd := x
      iso := Iso.refl (X.p.obj x) }
  map {x y} f :=
    { fst :=
        { left := u.map (X.p.map f)
          right := X.p.map f }
      snd := f }

/-- The canonical functor from `X` to the localized pushforward fibred category `uₚ X`. -/
noncomputable abbrev pushforwardFibredCategoryUnit
    (X : FibredCategoryOver C) :
    X.S ⥤ (u ₚ X).S :=
  pushforwardFibredCategoryUnitPrelocalized u X ⋙
    (u.pushforwardFractions X.p).Q

-- Proof sketch: the prelocalized unit maps `x / U` to `(U, id_{u(U)}, x)`, whose image under
-- the prelocalized projection is `u.obj U`. Passing through the localization does not change the
-- resulting base functor.
/-- Composing the canonical unit `X ⥤ uₚ X` with the projection to `D` recovers `u ∘ X.p`. -/
theorem pushforwardFibredCategoryUnit_comp_projection
    (X : FibredCategoryOver C) :
    pushforwardFibredCategoryUnit u X ⋙ (u ₚ X).p = X.p ⋙ u := sorry

-- Proof sketch: the base-compatibility of `G` identifies `G ⋙ Y.p` with the projection of
-- `uₚ X`, and the previous theorem identifies the unit `X ⥤ uₚ X` followed by that projection
-- with `X.p ⋙ u`.
/-- The square determined by a based functor `uₚ X ⥤ T` commutes with the projections to `D`
after precomposing with the canonical unit `X ⥤ uₚ X`. -/
private theorem pushforwardPullbackComparisonSquare_comm
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (G : (u ₚ X).toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    ((Functor.whiskeringRight X.S C D).obj u).obj X.p =
      ((Functor.whiskeringRight X.S Y.S D).obj Y.p).obj
        (pushforwardFibredCategoryUnit u X ⋙ G.toFunctor) := sorry

/-- The commutative square over `u` and `Y.p` obtained from a based functor `uₚ X ⥤ T` by
precomposing with the canonical unit `X ⥤ uₚ X`. -/
private noncomputable abbrev pushforwardPullbackComparisonSquare
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (G : (u ₚ X).toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    CategoricalPullback.CatCommSqOver u Y.p X.S :=
  { fst := X.p
    snd := pushforwardFibredCategoryUnit u X ⋙ G.toFunctor
    iso := eqToIso (pushforwardPullbackComparisonSquare_comm u X Y G) }

/-- The ambient based-functor category of functors `uₚ X ⥤ Y`. -/
private abbrev pushforwardPullbackSourceBasedFunctorCategory
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D) :=
  (u ₚ X).toBasedCategory ⥤ᵇ Y.toBasedCategory

/-- The based functor `X ⥤ uᵖ Y` corresponding to a based functor `uₚ X ⥤ Y`. -/
private noncomputable abbrev pushforwardPullbackComparisonFunctorObj
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (G : pushforwardPullbackSourceBasedFunctorCategory u X Y) :
    X.toBasedCategory ⥤ᵇ (u ᵖ Y).toBasedCategory where
  toFunctor :=
    (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback u Y.p X.S).obj
      (pushforwardPullbackComparisonSquare u X Y G)

-- Proof sketch: the source and target pullback objects have the same `C`-component `X.p.obj x`.
-- The first component of the morphism is therefore the identity, and the square-compatibility of
-- the second component is exactly the commutativity condition for `τ` over the base `D`.
/-- The second component of the pullback comparison morphism is compatible with the pullback
structure isomorphisms. -/
private theorem pushforwardPullbackComparisonFunctorMapApp_w
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ : pushforwardPullbackSourceBasedFunctorCategory u X Y}
    (τ : G₁ ⟶ G₂) (x : X.S) :
    u.map (𝟙 (X.p.obj x)) ≫ ((pushforwardPullbackComparisonFunctorObj u X Y G₂).obj x).iso.hom =
      ((pushforwardPullbackComparisonFunctorObj u X Y G₁).obj x).iso.hom ≫
        Y.p.map (τ.app ((pushforwardFibredCategoryUnit u X).obj x)) := sorry

/-- The component at `x` of the natural transformation induced on pullback objects by a
transformation `τ : G₁ ⟶ G₂`. -/
private noncomputable abbrev pushforwardPullbackComparisonFunctorMapApp
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ : pushforwardPullbackSourceBasedFunctorCategory u X Y}
    (τ : G₁ ⟶ G₂) (x : X.S) :
    (pushforwardPullbackComparisonFunctorObj u X Y G₁).toFunctor.obj x ⟶
      (pushforwardPullbackComparisonFunctorObj u X Y G₂).toFunctor.obj x :=
  { fst := 𝟙 (X.p.obj x)
    snd := τ.app ((pushforwardFibredCategoryUnit u X).obj x)
    w := pushforwardPullbackComparisonFunctorMapApp_w u X Y τ x }

-- Proof sketch: naturality of `τ` after precomposition with the unit `X ⥤ uₚ X` gives the
-- naturality of the second component, while the first component is the identity on the base
-- object `X.p.obj x`.
/-- The pullback comparison morphisms induced from a based natural transformation are natural in
the source object of `X`. -/
private theorem pushforwardPullbackComparisonFunctor_map_naturality
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ : pushforwardPullbackSourceBasedFunctorCategory u X Y}
    (τ : G₁ ⟶ G₂) :
    ∀ {x y : X.S} (f : x ⟶ y),
      (pushforwardPullbackComparisonFunctorObj u X Y G₁).toFunctor.map f ≫
          pushforwardPullbackComparisonFunctorMapApp u X Y τ y =
        pushforwardPullbackComparisonFunctorMapApp u X Y τ x ≫
          (pushforwardPullbackComparisonFunctorObj u X Y G₂).toFunctor.map f := sorry

-- Proof sketch: each component of the induced transformation in the pullback category has first
-- component the identity on `X.p.obj x`, so it is vertical over the identity morphism in `C`.
/-- The pullback comparison component lies over the identity on the base object `X.p.obj x`. -/
private theorem pushforwardPullbackComparisonFunctorMapApp_isHomLift
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ : pushforwardPullbackSourceBasedFunctorCategory u X Y}
    (τ : G₁ ⟶ G₂) (x : X.S) :
    (u ᵖ Y).p.IsHomLift (𝟙 (X.p.obj x))
      (pushforwardPullbackComparisonFunctorMapApp u X Y τ x) := sorry

/-- The based natural transformation between the pullback comparison functors induced by
`τ : G₁ ⟶ G₂`. -/
private noncomputable abbrev pushforwardPullbackComparisonFunctorMap
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ : pushforwardPullbackSourceBasedFunctorCategory u X Y}
    (τ : G₁ ⟶ G₂) :
    pushforwardPullbackComparisonFunctorObj u X Y G₁ ⟶
      pushforwardPullbackComparisonFunctorObj u X Y G₂ where
  toNatTrans :=
    { app := fun x ↦ pushforwardPullbackComparisonFunctorMapApp u X Y τ x
      naturality := fun {_ _} f ↦
        pushforwardPullbackComparisonFunctor_map_naturality u X Y τ f }
  isHomLift' := pushforwardPullbackComparisonFunctorMapApp_isHomLift u X Y τ

-- Proof sketch: the map on morphisms is defined componentwise from the identity vertical
-- transformation and the given based natural transformation `τ`. Identity components remain
-- identity after passing to the pullback category.
/-- The pullback comparison construction preserves identity `2`-morphisms. -/
private theorem pushforwardPullbackBasedFunctor_map_id
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D) :
    ∀ G : pushforwardPullbackSourceBasedFunctorCategory u X Y,
      pushforwardPullbackComparisonFunctorMap u X Y (𝟙 G) =
        𝟙 (pushforwardPullbackComparisonFunctorObj u X Y G) := sorry

-- Proof sketch: both sides are defined objectwise; the second component is the vertical
-- composition of the components of `τ` and `σ` after precomposition with the unit `X ⥤ uₚ X`,
-- while the first component stays the identity on the base.
/-- The pullback comparison construction preserves composition of `2`-morphisms. -/
private theorem pushforwardPullbackBasedFunctor_map_comp
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D) :
    ∀ {G₁ G₂ G₃ : pushforwardPullbackSourceBasedFunctorCategory u X Y}
      (τ : G₁ ⟶ G₂) (σ : G₂ ⟶ G₃),
      pushforwardPullbackComparisonFunctorMap u X Y (τ ≫ σ) =
        pushforwardPullbackComparisonFunctorMap u X Y τ ≫
          pushforwardPullbackComparisonFunctorMap u X Y σ := sorry

/-- The ambient functor sending a based functor `uₚ X ⥤ T` to the induced based functor
`X ⥤ uᵖ T`. -/
private noncomputable abbrev pushforwardPullbackBasedFunctor
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D) :
    pushforwardPullbackSourceBasedFunctorCategory u X Y ⥤
      (X.toBasedCategory ⥤ᵇ (u ᵖ Y).toBasedCategory) where
  obj G := pushforwardPullbackComparisonFunctorObj u X Y G
  map τ := pushforwardPullbackComparisonFunctorMap u X Y τ
  map_id := pushforwardPullbackBasedFunctor_map_id u X Y
  map_comp := pushforwardPullbackBasedFunctor_map_comp u X Y

-- Proof sketch: if `G : uₚ X ⟶ Y` preserves strongly cartesian morphisms, then after
-- precomposing with the unit `X ⥤ uₚ X` the induced functor to `Y` sends strongly cartesian
-- arrows in `X` to strongly cartesian arrows in `Y`. Since the pullback fibred category `uᵖ Y`
-- detects strong cartesianness on the `Y`-component, the induced functor `X ⟶ uᵖ Y` is again a
-- morphism of fibred categories.
/-- The pullback comparison construction sends morphisms of fibred categories `uₚ X ⟶ Y` to
morphisms of fibred categories `X ⟶ uᵖ Y`. -/
private theorem pushforwardPullbackBasedFunctor_preservesStronglyCartesian
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (G : (u ₚ X) ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian
      (((((fibredCategoryOverSubTwoCategory D).hom (u ₚ X) Y).inclusion) ⋙
        pushforwardPullbackBasedFunctor u X Y).obj G) := sorry

private noncomputable abbrev pushforwardPullbackFibredMorphismLift
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D) :=
  (FibredCategoryMor.objectProperty X (u ᵖ Y)).lift
    ((((fibredCategoryOverSubTwoCategory D).hom (u ₚ X) Y).inclusion) ⋙
      pushforwardPullbackBasedFunctor u X Y)
    (fun G : (u ₚ X) ⟶ Y ↦
      show BasedFunctor.PreservesStronglyCartesian
          (((((fibredCategoryOverSubTwoCategory D).hom (u ₚ X) Y).inclusion) ⋙
            pushforwardPullbackBasedFunctor u X Y).obj G) from
        pushforwardPullbackBasedFunctor_preservesStronglyCartesian u X Y G)

/-- The canonical functor
`Mor_{Fib/D}(uₚ X, Y) ⥤ Mor_{Fib/C}(X, uᵖ Y)`. -/
noncomputable abbrev pushforwardPullbackFibredMorphismFunctor
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D) :
    ((u ₚ X) ⟶ Y) ⥤
      (X ⟶ (u ᵖ Y)) :=
  pushforwardPullbackFibredMorphismLift u X Y ⋙
    FibredCategoryMor.ofObjectProperty X (u ᵖ Y)

-- Proof sketch: the forward functor is the explicit construction `G ↦ H` from the text, obtained
-- by restricting `G : uₚ X ⟶ Y` along the canonical unit `X ⟶ uₚ X` and packaging the result as a
-- functor `X ⟶ uᵖ Y`. The inverse sends `H : X ⟶ uᵖ Y` to the functor `uₚ X ⟶ Y` induced from
-- the localization universal property of Lemma `4.27.16`, exactly as in the proof of the Stacks
-- Project lemma. The two constructions are mutually quasi-inverse on morphism categories.
/-- Lemma 8.12.8: if `C` has pullbacks and equalizers and `u : C ⥤ D` preserves them, then the
canonical functor from morphisms of fibred categories `uₚ X ⟶ Y` over `D` to morphisms of
fibred categories `X ⟶ uᵖ Y` over `C` is an equivalence of categories. -/
theorem pushforwardPullbackFibredMorphismFunctor_isEquivalence
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D) :
    Functor.IsEquivalence (pushforwardPullbackFibredMorphismFunctor u X Y) := sorry

end Pushforward

end

end CategoryTheory
