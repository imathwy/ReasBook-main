import Mathlib
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_8_12_6_Support (from Chap08) -/
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

namespace Functor

variable (u : C ⥤ D) (p : S ⥤ C) [p.IsFibered]
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- Lemma 8.12.6: with notation and assumptions as in Lemma `8.12.5`, the localized category
`u ₚ p` is a fibred category over `D` via its canonical projection
`u.pushforwardProjection p`. -/
theorem pushforwardProjection_isFibered_aux :
    (u.pushforwardProjection p).IsFibered := by
  sorry

end Functor

end

end CategoryTheory

/-! ### Lemma_8_12_7 (from Chap08) -/
open CategoryTheory.Limits

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-
Domain-style sampling for Lemma 8.12.7:
- primary domain: localized pushforward of a fibred category along a functor, with the groupoid
  structure read from the fibers of the canonical projection to `D`.
- inspected owner-level declarations:
  `Functor.pushforwardProjection`,
  `Functor.pushforwardProjection_isFibered`,
  `isFibredInGroupoids_of_isFibered_and_fiber_groupoid`,
  `MorphismProperty.Localization.exists_rightFraction`.
- best owner abstraction: the canonical owner predicate
  `IsFibredInGroupoids (u.pushforwardProjection p)`.
- primitive data: the canonical projection `u.pushforwardProjection p` and the already-canonical
  fibred structure from Lemma `8.12.6`, which itself is built from pullbacks, equalizers, and
  preservation of those two limit shapes.
- derived API: the source-facing theorem below and the derived typeclass instance.

Source/core/bridge triage:
- `source-facing`: `pushforwardProjection_isFibredInGroupoids`.
- `core/canonical`: `IsFibredInGroupoids`, `Functor.IsFibered`, and the fiberwise groupoid
  criterion from Chapter 4.
- `bridge/view`: the private fiberwise groupoid helper, whose proof uses the right-fraction
  presentation of morphisms in the localization but introduces no parallel pushforward owner. -/

namespace Functor

variable (u : C ⥤ D) (p : S ⥤ C) [IsFibredInGroupoids p]
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

-- Proof sketch: Lemma `8.12.6` gives that the localized projection is fibred. To upgrade from
-- fibred to fibred in groupoids, use Lemma `4.35.2`: it is enough to show that every fiber of the
-- localized projection is a groupoid. A morphism in a fiber of the localization is represented by
-- a right fraction in `u_{pp} S`. Its denominator already belongs to the fraction property, and
-- the fiber condition forces the numerator to be vertical over `D`; because `p` is fibred in
-- groupoids, that vertical numerator is also strongly cartesian, hence belongs to the same
-- fraction property and becomes invertible after localization.
private theorem pushforwardProjectionFiber_hom_isIso
    (V : D) {X Y : (u.pushforwardProjection p).Fiber V} (φ : X ⟶ Y) :
    IsIso φ := by
  sorry

private instance pushforwardProjection_fiber_isGroupoid
    (V : D) :
    IsGroupoid ((u.pushforwardProjection p).Fiber V) where
  all_isIso := pushforwardProjectionFiber_hom_isIso u p V

/-- Lemma 8.12.7: with notation and assumptions as in Lemma `8.12.6`, if `p : S ⥤ C` is fibred in
groupoids, then the localized category `u ₚ p` is fibred in groupoids over `D` via its canonical
projection `u.pushforwardProjection p`. -/
theorem pushforwardProjection_isFibredInGroupoids
    : IsFibredInGroupoids (u.pushforwardProjection p) := by
  refine
    isFibredInGroupoids_of_isFibered_and_fiber_groupoid
      (u.pushforwardProjection p) (pushforwardProjection_isFibered u p) ?_
  intro V
  infer_instance

instance
    : IsFibredInGroupoids (u.pushforwardProjection p) :=
  pushforwardProjection_isFibredInGroupoids u p

end Functor

end

end CategoryTheory

/-! ### Lemma_8_12_8 (from Chap08) -/
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

/-! ### Definition_8_12_9 (from Chap08) -/
open CategoryTheory
open CategoryTheory.Limits
universe u v

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{max u v} C] [Category.{max u v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

variable [HasFiniteNonemptyLimits C]

/- Domain-style sampling for Definition 8.12.9:
- primary domain: stackifications of fibred categories over a site, specialized here to the
  canonical pushforward fibred category attached to `X` along `u`.
- inspected owner-level declarations:
  `StackOver`,
  `FibredCategoryMor.IsStackification`,
  `Functor.pushforwardProjection`,
  `stackification_precompose_functor`,
  `Functor.IsEquivalence`.
- best owner abstraction: the source-facing inverse-image datum should use the chapter owner
  obtained by bundling the canonical projection `u.pushforwardProjection X.p` as a fibred
  category, together with a comparison morphism to `Y` and the morphism-owned predicate
  `FibredCategoryMor.IsStackification i`.
- primitive data: a target stack over `(D, K)`, a canonical comparison morphism from the bundled
  pushforward source to `Y`, and a proof that this morphism is a stackification.
- derived API: downstream universal-property equivalences recovered from the owner statement
  `Functor.IsEquivalence (stackification_precompose_functor _ i)` and its canonical
  `.asEquivalence`.

Source/core/bridge triage:
- `source-facing`: an inverse-image stack of `X` along `u`.
- `core/canonical`: `StackOver`, `Functor.pushforwardProjection`,
  `FibredCategoryMor.IsStackification`.
- `bridge/view`: the comparison morphism from the bundled pushforward source to `Y`. -/

variable (u : C ⥤ D) [PreservesFiniteNonemptyLimits u]
variable (X : StackOver J)
variable [(u.pushforwardProjection X.p).IsFibered]

/-- Helper for Definition 8.12.4: the source fibred category underlying an inverse-image stack
along `u` is the canonical bundled pushforward projection `u.pushforwardProjection X.p`. -/
noncomputable abbrev pushforward_source_over : FibredCategoryOver D :=
  FibredCategoryOver.ofFunctor (u.pushforwardProjection X.p)

-- Route correction: the metadata text points to Definition `8.12.4`, but the concrete file and
-- downstream Chapter 8 owner context require the inverse-image-stack packaging of Definition
-- `8.12.9`.
/-- Definition 8.12.9: an inverse-image stack of `X` along the morphism of sites represented by
`u` is a stack `Y` over `(D, K)` together with a morphism from the canonical pushforward fibred
category attached to `X` along `u` to `Y`, and a proof that this morphism is a stackification. -/
structure InverseImageStackAlong where
  /-- The chosen target stack over `(D, K)`. -/
  Y : StackOver K
  /-- The canonical comparison from the bundled pushforward source to the chosen target stack. -/
  i : pushforward_source_over u X ⟶ Y
  /-- The comparison morphism exhibits the target as a stackification of the pushforward source. -/
  hi : FibredCategoryMor.IsStackification i

end

end CategoryTheory

/-! ### Lemma_8_12_10 (from Chap08) -/
open CategoryTheory
open CategoryTheory.Limits
open Bicategory
open InducedCategory.Hom
open scoped FibredCategoryOver
open scoped Bicategory

universe u v

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{max u v} C] [Category.{max u v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

variable [HasFiniteNonemptyLimits C]
variable (u : C ⥤ D) [Functor.IsContinuous u J K] [PreservesFiniteNonemptyLimits u]

attribute [local instance] pushforwardPullbackFibredMorphismFunctor_isEquivalence

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

/-- The ambient equivalence identifying morphisms from `S` to the pullback stack `T.pullback u`
with ambient morphisms into the underlying pullback fibred category. -/
private noncomputable abbrev stackMor_pullback_ambientEquivalence
    (S : StackOver J) (T : StackOver K) :
    ((S : FibredCategoryOver C) ⟶ u ᵖ (T : FibredCategoryOver D)) ≌
      (S ⟶ T.pullback u) :=
  ((ambientEquivalence :
      (S ⟶ T.pullback u) ≌
        (S.toFibredCategoryOver ⟶ (T.pullback u).toFibredCategoryOver)).symm)

/-- Lemma 8.12.10: for a chosen inverse-image stack `f^{-1} S` represented by a stackification
`uₚ S ⟶ f^{-1} S`, morphisms of stacks `f^{-1} S ⟶ T` are canonically equivalent to morphisms
`S ⟶ f_* T`, modeled here by morphisms of stacks `S ⟶ T.pullback u`. -/
noncomputable def inverseImage_stackMor_to_directImage_stackMor_equivalence
    (S : StackOver J) (Sinv : StackOver K)
    (iSinv : u ₚ S ⟶ Sinv)
    (hiSinv : FibredCategoryMor.IsStackification iSinv)
    (T : StackOver K) :
    (Sinv ⟶ T) ≌ (S ⟶ T.pullback u) :=
  let _ : HasPullbacks C := inferInstance
  let _ : HasEqualizers C := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan u := inferInstance
  let _ : PreservesLimitsOfShape WalkingParallelPair u := inferInstance
  let G := stackification_precompose_functor T iSinv
  let _ : Functor.IsEquivalence G :=
    stackification_precompose_functor_isEquivalence T iSinv hiSinv
  let H :
      ((u ₚ (S : FibredCategoryOver C)) ⟶ (T : FibredCategoryOver D)) ⥤
        ((S : FibredCategoryOver C) ⟶ u ᵖ (T : FibredCategoryOver D)) :=
    pushforwardPullbackFibredMorphismFunctor
      u (S : FibredCategoryOver C) (T : FibredCategoryOver D)
  let eI := stackMor_pullback_ambientEquivalence u S T
  G.asEquivalence.trans (H.asEquivalence.trans eI)

-- Proof sketch: this is the tautological identity satisfied by the canonical equivalence object
-- constructed above; later proof stages can replace it with more explicit objectwise formulas.
/-- The canonical equivalence constructor of Lemma `8.12.10` is stable as the chosen public owner
for the stack-morphism equivalence. -/
theorem inverseImage_stackMor_to_directImage_stackMor_equivalence_exists
    (S : StackOver J) (Sinv : StackOver K)
    (iSinv : u ₚ S ⟶ Sinv)
    (hiSinv : FibredCategoryMor.IsStackification iSinv)
    (T : StackOver K) :
    let _e := inverseImage_stackMor_to_directImage_stackMor_equivalence u S Sinv iSinv hiSinv T
    True := sorry

end

end CategoryTheory

/-! ### Lemma_8_12_11 (from Chap08) -/
open CategoryTheory.Limits
open scoped CategoryTheory.FibredCategoryOver
universe u v

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{max u v} C] [Category.{max u v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [HasFiniteNonemptyLimits C]

/-
Domain-style sampling for Lemma 8.12.11:
- primary domain: stackifications of fibred categories and their functoriality under the
  localized pushforward construction along `u : C ⥤ D`.
- inspected owner-level declarations:
  `FibredCategoryMor.IsStackification`,
  `FibredCategoryOver.pushforward`,
  `pushforwardFibredCategoryMap`,
  `stackification_precompose_functor`,
  `Functor.IsEquivalence`.
- best owner abstraction: the public statement should stay on the owner predicate
  `FibredCategoryMor.IsStackification` for the canonical composite
  `pushforwardFibredCategoryMap u G ≫ iYinv`, rather than introducing a local comparison wrapper.
- primitive data: a stackification `G : X ⟶ Y`, a chosen inverse-image stackification
  `iYinv : u ₚ Y ⟶ Yinv`, and the induced canonical pushforward morphism
  `pushforwardFibredCategoryMap u G : u ₚ X ⟶ u ₚ Y`.
- derived API: the composed stackification statement below and, when needed downstream, the
  canonical equivalence object `(stackification_precompose_functor _ iYinv).asEquivalence`.

Source/core/bridge triage:
- `source-facing`: the theorem `inverseImageStackAlong_isStackification_of_stackification`.
- `core/canonical`: `FibredCategoryMor.IsStackification`, `FibredCategoryOver.pushforward`,
  `pushforwardFibredCategoryMap`.
- `bridge/view`: the canonical owner statement
  `Functor.IsEquivalence (stackification_precompose_functor _ iYinv)`, whose `.asEquivalence`
  supplies the universal-property perspective on these stackification morphisms. -/

-- Proof sketch: apply the localized pushforward construction to the stackification morphism
-- `G : X ⟶ Y`, obtaining the canonical morphism `uₚ X ⟶ uₚ Y`. Composing with the chosen
-- stackification morphism `i : uₚ Y ⟶ Yinv` gives the desired canonical
-- comparison map. The stackification properties are checked on morphism presheaves and local
-- essential surjectivity exactly as in the Stacks Project argument.
/-- Lemma 8.12.11: if `G : X ⟶ Y` exhibits the stack `Y` as a stackification of the fibred
category `X` over `(C, J)`, then for any stackification `i : uₚ Y ⟶ Yinv` representing an
inverse-image stack of `Y` along `u`, the canonical comparison morphism `uₚ X ⟶ Yinv` is a
stackification of `uₚ X`. -/
theorem inverseImageStackAlong_isStackification_of_stackification
    (u : C ⥤ D) [PreservesFiniteNonemptyLimits u]
    {X : FibredCategoryOver C} {Y : StackOver J}
    (G : X ⟶ Y)
    (hG : FibredCategoryMor.IsStackification G)
    {Yinv : StackOver K}
    (iYinv : u ₚ Y ⟶ Yinv)
    (hiYinv : FibredCategoryMor.IsStackification iYinv) :
    FibredCategoryMor.IsStackification (pushforwardFibredCategoryMap u G ≫ iYinv) := sorry

end

end CategoryTheory

/-! ### Lemma_8_12_12 (from Chap08) -/
open CategoryTheory
open CategoryTheory.Limits
open Bicategory
open FibredCategoryOver
open InducedCategory.Hom
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

/-- Lemma 8.12.12 (1): if `Sinv` is a chosen inverse-image stack representing `f^{-1} S`, then
the canonical comparison from `S` to the Chapter 8 direct-image model `Sinv.pullback u` of
`f_* f^{-1} S` is an equivalence of stacks over `(C, J)`. -/
theorem stack_equivalent_to_pushforward_inverseImage
    [Functor.IsContinuous u J K] [u.Full] [u.Faithful]
    (S : StackOver J)
    (Sinv : StackOver K)
    (iSinv : u ₚ S ⟶ Sinv)
    (hiSinv : FibredCategoryMor.IsStackification iSinv) :
    IsEquivalenceOverBase (pushforwardInverseImageComparison u S Sinv iSinv) :=
  sorry

-- Proof sketch: Lemma `8.12.10` identifies morphisms out of a chosen inverse-image stack with
-- morphisms into the canonical direct-image model `Sinv'.pullback u`. Apply part `(1)` to compare
-- `S'` with `Sinv'.pullback u`, then transport morphisms across that equivalence to obtain the
-- source-facing equivalence between morphisms `S ⟶ S'` and morphisms `Sinv ⟶ Sinv'`.
/-- Lemma 8.12.12 (2): the canonical composite from postcomposition with the comparison
`S' ⟶ Sinv'.pullback u` and the inverse of the Lemma `8.12.10` equivalence is an equivalence on
stack-morphism categories. -/
theorem inverseImage_induces_equivalence_on_stackMorphismCategories
    [Functor.IsContinuous u J K] [u.Full] [u.Faithful]
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
    sorry
  let eInv := inverseImage_stackMor_to_directImage_stackMor_equivalence.{u, v, u1, u2}
    u S Sinv iSinv hiSinv Sinv'
  let _ : Functor.IsEquivalence F := hF
  let _ : Functor.IsEquivalence eInv.inverse := by infer_instance
  change Functor.IsEquivalence (F ⋙ eInv.inverse)
  infer_instance

end

end CategoryTheory
