import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_8_8_3 (from Chap08) -/
universe u v

namespace CategoryTheory

open BasedFunctor

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver C} {S' X : StackOver J}

/- Domain-style sampling for Lemma 8.8.3:
- primary domain: the universal property of stackification in the `2`-category of fibred
  categories over a site, specialized to morphisms into a stack target.
- inspected owner-level declarations:
  `FibredCategoryMor`,
  `FibredCategoryMor.IsStackification`,
  `StackOver.InducedCategory.Hom.toFibredCategoryMor`,
  `SubTwoCategory.Hom.toHom`,
  `FibredCategoryMor.ofBasedFunctor`,
  `FibredCategoryMor.objectProperty`,
  `FibredCategoryMor.ofObjectProperty`,
  `Functor.IsEquivalence`.
- best owner abstraction: the induced precomposition functor
  `stackification_precompose_functor X G : (S' ⟶ X) ⥤ (S ⟶ X)`, together with the owner predicate
  `Functor.IsEquivalence`.
- primitive data: a stackification morphism `G : S ⟶ S'` and a target stack `X`.
- derived API: the induced functor on morphism categories and the canonical equivalence object
  `(stackification_precompose_functor X G).asEquivalence`.

Source/core/bridge triage:
- `source-facing`: the precomposition equivalence expressing the universal property of a
  stackification.
- `core/canonical`: `FibredCategoryMor.IsStackification`,
  `SubTwoCategory.Hom.toHom`, `FibredCategoryMor.ofBasedFunctor`,
  `Functor.IsEquivalence`.
- `bridge/view`: the temporary passage through based functors preserving strongly cartesian
  morphisms. -/

private abbrev forgetToFibredCategoryMor (S' X : StackOver J) :
    (S' ⟶ X) ⥤ FibredCategoryMor S'.toFibredCategoryOver X.toFibredCategoryOver :=
  ((stackOverSubTwoCategory J).hom S' X).inclusion

-- Proof sketch: left whiskering by the based functor underlying `G` leaves identity vertical
-- natural transformations unchanged.
private theorem stackification_precompose_based_map_id
    (G : FibredCategoryMor S S') :
    ∀ F : S'.toBasedCategory ⥤ᵇ X.toBasedCategory,
      BasedCategory.whiskerLeft G.toHom (𝟙 F) =
        𝟙 (BasedFunctor.comp G.toHom F) := sorry

-- Proof sketch: left whiskering by a fixed based functor commutes with vertical composition of
-- based natural transformations.
private theorem stackification_precompose_based_map_comp
    (G : FibredCategoryMor S S') :
    ∀ {F₁ F₂ F₃ : S'.toBasedCategory ⥤ᵇ X.toBasedCategory}
      (τ : F₁ ⟶ F₂) (σ : F₂ ⟶ F₃),
      BasedCategory.whiskerLeft G.toHom (τ ≫ σ) =
        BasedCategory.whiskerLeft G.toHom τ ≫
          BasedCategory.whiskerLeft G.toHom σ := sorry

private abbrev stackification_precompose_based_functor
    (G : FibredCategoryMor S S') :
    (S'.toBasedCategory ⥤ᵇ X.toBasedCategory) ⥤
      (S.toBasedCategory ⥤ᵇ X.toBasedCategory) where
  obj F := BasedFunctor.comp G.toHom F
  map τ := BasedCategory.whiskerLeft G.toHom τ
  map_id := stackification_precompose_based_map_id G
  map_comp := fun τ σ ↦ stackification_precompose_based_map_comp G τ σ

private abbrev stackification_precompose_stackMor_to_based
    (X : StackOver J)
    (G : FibredCategoryMor S S') :
    (S' ⟶ X) ⥤ (S.toBasedCategory ⥤ᵇ X.toBasedCategory) :=
  forgetToFibredCategoryMor S' X ⋙
    (((fibredCategoryOverSubTwoCategory C).hom S'.toFibredCategoryOver X.toFibredCategoryOver).inclusion) ⋙
    stackification_precompose_based_functor G

-- Proof sketch: both `G` and `H` preserve strongly cartesian morphisms, so their composite over
-- `C` does as well. This is exactly the owner object property
-- `FibredCategoryMor.objectProperty S X`.
private theorem stackification_precompose_preservesStronglyCartesian
    (G : FibredCategoryMor S S')
    (H : S' ⟶ X) :
    BasedFunctor.PreservesStronglyCartesian
      ((stackification_precompose_stackMor_to_based X G).obj H) := sorry

/-- Precomposition with `G : S ⟶ S'` sends a stack morphism `S' ⟶ X` to the induced owner
morphism `S ⟶ X`. -/
abbrev stackification_precompose_functor
    (X : StackOver J)
    (G : S ⟶ S') :
    (S' ⟶ X) ⥤ (S ⟶ X) :=
  (FibredCategoryMor.objectProperty S X).lift
      (stackification_precompose_stackMor_to_based X G)
      (fun H ↦ stackification_precompose_preservesStronglyCartesian G H) ⋙
    FibredCategoryMor.ofObjectProperty S X

/-- Lemma 8.8.3: if `G : S ⟶ S'` is a stackification morphism, then precomposition with `G`
induces an equivalence on morphism categories into any stack `X`. The canonical owner statement is
that `stackification_precompose_functor X G` is an equivalence of categories. -/
instance stackification_precompose_functor_isEquivalence
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G) :
    Functor.IsEquivalence
      (stackification_precompose_functor X G :
        (S' ⟶ X) ⥤ (S ⟶ X)) := sorry

end

end CategoryTheory

/-! ### Lemma_8_8_4 (from Chap08) -/
universe u v

namespace CategoryTheory

open Bicategory
open FibredCategoryOver
open scoped Bicategory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

variable {X Y Z : FibredCategoryOver C}
variable {X' Y' Z' : StackOver J}

namespace WideSubcategory

private abbrev toFibredCategoryMor {T S : StackOver J} (f : T ⟶ S) :=
  InducedCategory.Hom.toFibredCategoryMor f

end WideSubcategory

/- Domain-style sampling for Lemma 8.8.4:
- primary domain: stacks over a site together with bicategorical `2`-fibre products of fibred
  categories.
- inspected owner-level declarations:
  `FibredCategoryOver.twoFibreProduct`,
  `FibredCategoryOver.twoFibreProductSquare`,
  `FibredCategoryOver.twoFibreProduct_isTwoFibreProduct`,
  `BicategoricalTwoCommutativeSquare.postcompose`,
  `BicategoricalTwoCommutativeSquare.postcomposeRight`.
- best owner abstraction: the canonical comparison map should be derived from the owner square
  `FibredCategoryOver.twoFibreProductSquare` and the terminality of the pullback square for the
  lifted morphisms `f'` and `g'`; the old objectwise fiber construction is only bridge/view data.
- primitive data: the source pullback owner `twoFibreProduct f g`, the stackification maps
  `i`, `j`, `k`, and the ambient comparison `2`-isomorphisms `α`, `β`.
- derived API: the induced square over `f'` and `g'`, the terminal comparison morphism into the
  target pullback owner, and the resulting source-facing stackification theorem.

Source/core/bridge triage:
- `source-facing`: `twoFibreProduct_of_stackifications_isStackification`.
- `core/canonical`: `FibredCategoryOver.twoFibreProductSquare` together with
  `FibredCategoryOver.twoFibreProduct_isTwoFibreProduct`,
  `BicategoricalTwoCommutativeSquare.postcompose`,
  `BicategoricalTwoCommutativeSquare.postcomposeRight`.
- `bridge/view`: the induced square below and the terminal morphism
  `twoFibreProductOfStackificationsHom`. -/

private noncomputable def twoFibreProductOfStackificationsSquare
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (fF : FibredCategoryMor X'.toFibredCategoryOver Y'.toFibredCategoryOver)
    (gF : FibredCategoryMor Z'.toFibredCategoryOver Y'.toFibredCategoryOver)
    (α : i ≫ fF ≅ f ≫ j)
    (β : k ≫ gF ≅ g ≫ j) :
    BicategoricalTwoCommutativeSquare fF gF := by
  simpa using
    (((twoFibreProductSquare f g).postcompose β.symm).symm.postcomposeRight α.symm).symm

/-- The canonical morphism of fibred categories from the explicit `2`-fibre product of `f` and
`g` to the explicit `2`-fibre product of the chosen lifted morphisms `f'` and `g'`. -/
noncomputable def twoFibreProductOfStackificationsHom
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j) :
    FibredCategoryMor
      (twoFibreProduct f g)
      (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor) := by
  let fF : FibredCategoryMor X'.toFibredCategoryOver Y'.toFibredCategoryOver := f'.toFibredCategoryMor
  let gF : FibredCategoryMor Z'.toFibredCategoryOver Y'.toFibredCategoryOver := g'.toFibredCategoryMor
  let P := twoFibreProductOfStackificationsSquare f g i j k fF gF α β
  let Q := twoFibreProductSquare fF gF
  let _ : Bicategory.IsFinal Q :=
    twoFibreProduct_isTwoFibreProduct fF gF
  exact (show P ⟶ Q from ⊤_ (P ⟶ Q)).hom

-- Proof sketch: apply Lemma `8.4.6` to the chosen lifted morphisms `f' : X' ⟶ Y'` and
-- `g' : Z' ⟶ Y'` to put a stack structure on their explicit `2`-fibre product. The comparison
-- `2`-isomorphisms `α` and `β` already live on the ambient fibred-category morphisms
-- `f'.toFibredCategoryMor` and `g'.toFibredCategoryMor`, so they directly define the square
-- `twoFibreProductOfStackificationsSquare f g i j k f'.toFibredCategoryMor
-- g'.toFibredCategoryMor α β`. The canonical comparison map is
-- then the induced terminal morphism to the owner pullback square
-- `FibredCategoryOver.twoFibreProductSquare f'.toFibredCategoryMor g'.toFibredCategoryMor`.
/-- Lemma 8.8.4: if `i : X ⟶ X'`, `j : Y ⟶ Y'`, and `k : Z ⟶ Z'` are stackifications of fibred
categories over the site `(C, J)`, and if `f' : X' ⟶ Y'` and `g' : Z' ⟶ Y'` are chosen lifts of
`f : X ⟶ Y` and `g : Z ⟶ Y` together with comparison `2`-isomorphisms to the original
composites, then the induced canonical morphism from the explicit `2`-fibre product of `f` and
`g` to the explicit `2`-fibre product of `f'` and `g'` is a stackification. -/
theorem twoFibreProduct_of_stackifications_isStackification
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (hi : FibredCategoryMor.IsStackification i)
    (hj : FibredCategoryMor.IsStackification j)
    (hk : FibredCategoryMor.IsStackification k) :
    let target : StackOver J :=
      ⟨twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor, inferInstance⟩
    FibredCategoryMor.IsStackification
      (show FibredCategoryMor
          (twoFibreProduct f g)
          target
        from twoFibreProductOfStackificationsHom f g i j k f' g' α β) := sorry

end

end CategoryTheory

/-! ### Lemma_8_8_5 (from Chap08) -/
universe u v

namespace CategoryTheory

open CategoryOver FibredCategoryMor

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 8.8.5:
- primary domain: absolute inertia of fibred categories over a site and stackification morphisms.
- inspected owner-level declarations:
  `FibredCategoryOver.absoluteInertiaOver`,
  `CategoryOver.absoluteInertiaOverMap`,
  `absoluteInertiaStack`,
  `FibredCategoryMor.IsStackification`.
- best owner abstraction: the Chapter 4 fibred-category owner
  `FibredCategoryOver.absoluteInertiaOver`; the Chapter 4 based-category map
  `CategoryOver.absoluteInertiaOverMap` is only bridge/view data, and the Chapter 8 bundled stack
  target is `absoluteInertiaStack X'`.
- primitive data: a morphism `F : X ⟶ Y` of fibred categories and the canonical absolute inertia
  owner map induced by its underlying based functor over `C`.
- derived API: the strongly-cartesian preservation theorem below, the rebundled owner morphism
  `absoluteInertiaMap`, and the source-facing stackification theorem.

Source/core/bridge triage:
- `source-facing`: `absoluteInertia_of_stackification_isStackification`.
- `core/canonical`: `FibredCategoryOver.absoluteInertiaOver`, `absoluteInertiaStack`, and
  `FibredCategoryMor.IsStackification`.
- `bridge/view`: the Chapter 4 based-category map `CategoryOver.absoluteInertiaOverMap`, the
  preservation theorem below, and the rebundled induced morphism `absoluteInertiaMap`. -/

-- Proof sketch: view the absolute inertia as the relative inertia of the structure functor and
-- transport the preservation of strongly cartesian arrows along the explicit iterated `2`-fibre
-- product model of Lemma `4.34.1`.
/-- Helper for Lemma 8.8.5: a lift condition in the absolute inertia is equivalent to the same
lift condition on the underlying arrow in the ambient fibred category. -/
private theorem absolute_inertia_is_hom_lift_iff_underlying
    {Z : FibredCategoryOver C}
    {A B : (FibredCategoryOver.absoluteInertiaOver Z).S}
    {R S : C}
    {f : R ⟶ S}
    {φ : A ⟶ B} :
    (FibredCategoryOver.absoluteInertiaOver Z).p.IsHomLift f φ ↔
      Z.p.IsHomLift f φ.φ := by
  -- Unfolding the packaged absolute inertia exposes the same base projection on the underlying
  -- arrow in `Z`.
  constructor
  · intro h
    let _ : (FibredCategoryOver.absoluteInertiaOver Z).p.IsHomLift f φ := h
    refine IsHomLift.of_fac' Z.p f φ.φ
      (IsHomLift.domain_eq (FibredCategoryOver.absoluteInertiaOver Z).p f φ)
      (IsHomLift.codomain_eq (FibredCategoryOver.absoluteInertiaOver Z).p f φ) ?_
    simpa [CategoryOver.absoluteInertiaOver, CategoryOver.relativeInertiaOver,
      FibredCategoryOver.absoluteInertiaOver, FibredCategoryOver.relativeInertiaOver,
      relativeInertiaProjection] using
      (IsHomLift.fac' (FibredCategoryOver.absoluteInertiaOver Z).p f φ)
  · intro h
    let _ : Z.p.IsHomLift f φ.φ := h
    refine IsHomLift.of_fac' (FibredCategoryOver.absoluteInertiaOver Z).p f φ
      (IsHomLift.domain_eq Z.p f φ.φ)
      (IsHomLift.codomain_eq Z.p f φ.φ) ?_
    simpa [CategoryOver.absoluteInertiaOver, CategoryOver.relativeInertiaOver,
      FibredCategoryOver.absoluteInertiaOver, FibredCategoryOver.relativeInertiaOver,
      relativeInertiaProjection] using
      (IsHomLift.fac' Z.p f φ.φ)

/-- Helper for Lemma 8.8.5: the canonical relative diagonal over the base preserves strongly
cartesian morphisms. This is the public version of the Chapter 4 private bridge needed by the
explicit `2`-fibre-product model of inertia. -/
private theorem relative_diagonal_preservesStronglyCartesian
    {X Y : FibredCategoryOver C} (F : X ⟶ Y) :
    (BasedFunctor.relativeDiagonalOver
      (FibredCategoryMor.toBasedFunctor F)).PreservesStronglyCartesian := by
  -- The diagonal sends `φ` to `(φ, φ)`, so the self-pullback transport theorem applies to the
  -- two identical strongly cartesian components.
  intro a b φ hφ
  simpa [BasedFunctor.relativeDiagonalOver, relativeDiagonalOverRaw, relativeDiagonalFunctor,
      relativeDiagonalFunctorMap] using
    (self_pullback_hom_isStronglyCartesian_of_components (C := C) (X := X) (Y := Y) F
      ((BasedFunctor.relativeDiagonalOver (FibredCategoryMor.toBasedFunctor F)).map φ)
      hφ hφ)

/-- The canonical map on absolute inertia induced by a morphism of fibred categories preserves
strongly cartesian morphisms. -/
theorem absoluteInertiaOverMap_preservesStronglyCartesian
    {X Y : FibredCategoryOver C} (F : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian
      (absoluteInertiaOverMap (FibredCategoryMor.toBasedFunctor F)) := by
  -- TODO: reuse `absolute_inertia_is_hom_lift_iff_underlying` to prove the missing strong
  -- cartesian bridge in the absolute inertia, then finish by applying
  -- `FibredCategoryMor.map_stronglyCartesian` to the underlying arrow in `X`.
  sorry

/-- The absolute inertia of a bundled stack, viewed again as a bundled stack over `(C, J)`. -/
abbrev absoluteInertiaOfStack
    (Y : StackOver J) :
    StackOver J :=
  ⟨FibredCategoryOver.absoluteInertiaOver Y.toFibredCategoryOver, inferInstance⟩

/-- The canonical morphism on absolute inertia induced by a morphism from a fibred category to a
stack over `(C, J)`. -/
noncomputable abbrev absoluteInertiaMap
    {X : FibredCategoryOver C} {Y : StackOver J} (F : X ⟶ Y) :
    FibredCategoryMor
      (FibredCategoryOver.absoluteInertiaOver X)
      (absoluteInertiaOfStack Y).toFibredCategoryOver :=
  show FibredCategoryMor
      (FibredCategoryOver.absoluteInertiaOver X)
      (absoluteInertiaOfStack Y).toFibredCategoryOver
    from
      FibredCategoryMor.ofBasedFunctor
        (absoluteInertiaOverMap (FibredCategoryMor.toBasedFunctor F))
        (absoluteInertiaOverMap_preservesStronglyCartesian F)

-- Proof sketch: use Lemma `4.34.1` to identify absolute inertia with a `2`-fibre-product
-- construction, then apply Lemma `8.8.4` to the stackification morphism `i : X ⟶ X'`. Lemma
-- `8.7.1` supplies the canonical stack structure on the absolute inertia of the stack `X'`,
-- yielding the desired stackification statement for the induced inertia morphism.
/-- Lemma 8.8.5: if `i : X ⟶ X'` exhibits the stack `X'` as a stackification of the fibred
category `X` over the site `(C, J)`, then the induced morphism on absolute inertia exhibits the
absolute inertia of `X'` as a stackification of the absolute inertia of `X`. -/
theorem absoluteInertia_of_stackification_isStackification
    {X : FibredCategoryOver C} {X' : StackOver J}
    (i : X ⟶ X')
    (hi : FibredCategoryMor.IsStackification i) :
    FibredCategoryMor.IsStackification (absoluteInertiaMap i) := by
  -- Route correction: the remaining step is to identify `absoluteInertiaMap i` with the
  -- comparison map obtained by applying Lemma `8.8.4` to the public Chapter 4 explicit
  -- `2`-fibre-product model of absolute inertia. The local cartesian-preservation bridge above
  -- is already in place; the missing work is the public comparison-iso bookkeeping.
  --
  -- TODO: package the Chapter 4 equivalence
  -- `BasedFunctor.relativeInertiaToDiagonalPullback (FibredCategoryMor.toBasedFunctor (toBase X))`
  -- and its target-side analogue for `X'`, apply `twoFibreProduct_of_stackifications_isStackification`
  -- to the induced diagonal comparison, and then simplify the resulting owner morphism to
  -- `absoluteInertiaMap i`.
  sorry

end CategoryTheory
