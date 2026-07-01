import Mathlib
import stacks_project.Chap04.Lemma_4_34_1
import stacks_project.Chap04.«4_34_2_3»
import stacks_project.Chap08.Lemma_8_7_1
import stacks_project.Chap08.Lemma_8_8_1
import stacks_project.Chap08.Lemma_8_8_4

-- Declarations for this item will be appended below by the statement pipeline.

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
