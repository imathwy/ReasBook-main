import Mathlib
import stacks_project.Chap04.Definition_4_33_9
import stacks_project.Chap04.Definition_4_32_1
import stacks_project.Chap04.CanonicalFiberPseudofunctor
import stacks_project.Chap08.Lemma_8_2_3.PullbackComparisonNaturality

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite

universe u v uS vS

namespace CategoryTheory

open BasedFunctor

variable {C : Type u} [Category.{v} C]

-- Route correction: reuse the canonical Chapter 4 owner for `FibredCategoryOver`,
-- `FibredCategoryMor`, and `FibredCategoryMor.map_stronglyCartesian` instead of maintaining a
-- duplicate local copy in this Chapter 8 file.

/- Domain-style sampling for Lemma 8.2.3:
- primary domain: morphisms of fibred categories and the induced maps on the canonical Hom-
  presheaves attached to the fiber pseudofunctor;
- sampled owner-level declarations:
  `(X ⟶ Y)`,
  `BasedFunctor.fiberFunctor`,
  `canonicalFiberPseudofunctor`,
  `Pseudofunctor.presheafHom`.
- best owner abstraction: the ambient owner morphism `F : X ⟶ Y`, viewed through its induced
  fiber functors and the owner presheaf construction `Pseudofunctor.presheafHom`;
- primitive data: only the fibred-category morphism `F`;
- derived API: the comparison maps on pullbacks and the induced natural transformation on
  canonical Hom-presheaves.

Source/core/bridge triage:
- `source-facing`: the canonical morphism of Hom-presheaves from the source lemma;
- `core/canonical`: the ambient hom `X ⟶ Y`, `fiberFunctor`, and
  `Pseudofunctor.presheafHom`;
- `bridge/view`: `FibredCategoryMor.fibredMorphismPresheafMap`. -/

attribute [local instance] FibredCategoryOver.isFibred

variable {X Y : FibredCategoryOver C}

namespace FibredCategoryMor

-- Route correction: the generic pullback-comparison object and its vertical naturality squares
-- now live in the slim support owner `Lemma_8_2_3.PullbackComparisonNaturality`, so the rest of
-- this file only keeps the longer Hom-presheaf comparison chain.

/-- Helper for Lemma 8.2.3: the raw left `pullHom` flank, followed by the chosen `k`- and
`a`-pullback arrows, is already the chosen composite-leg `b`-pullback arrow in the target owner
category. -/
private theorem fibredMorphismPresheafMap_pullHom_left_raw_flank_factorization
    (F : X ⟶ Y) {D B A : C} (x : X.p.Fiber D)
    (a : B ⟶ D) (k : A ⟶ B) (b : A ⟶ D) (hk : k ≫ a = b) :
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          a.op.toLoc k.op.toLoc b.op.toLoc
          (comp_toLoc_eq a k b hk)).hom.toNatTrans.app
        ((F.toHom.fiberFunctor D).obj x)).1 ≫
        (canonicalPullbackChoice Y.p).map k
          (((canonicalFiberPseudofunctor Y.p).map a.op.toLoc).toFunctor.obj
            ((F.toHom.fiberFunctor D).obj x)) ≫
        (canonicalPullbackChoice Y.p).map a
          ((F.toHom.fiberFunctor D).obj x) =
      (canonicalPullbackChoice Y.p).map b
        ((F.toHom.fiberFunctor D).obj x) := by
  -- This is the owner-side factorization of the `mapComp'` hom component for the target
  -- canonical fiber pseudofunctor.
  exact
    canonicalFiberPseudofunctor_mapComp'_hom_app_fac
      (p := Y.p) (f := a) (g := k) (gf := b) (hgf := hk)
      ((F.toHom.fiberFunctor D).obj x)

/-- Helper for Lemma 8.2.3: after postcomposing the raw left `pullHom` boundary and the strict
composite-leg left boundary with the chosen `k`- and `a`-pullback arrows, both owner-level
composites reduce to the same chosen `b`-pullback arrow. -/
private theorem fibredMorphismPresheafMap_pullHom_left_boundary_postcompose_k_then_a_target
    (F : X ⟶ Y) {D B A : C} (x : X.p.Fiber D)
    (a : B ⟶ D) (k : A ⟶ B) (b : A ⟶ D) (hk : k ≫ a = b) :
    let raw :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          a.op.toLoc k.op.toLoc b.op.toLoc
          (comp_toLoc_eq a k b hk)).hom.toNatTrans.app
        ((F.toHom.fiberFunctor D).obj x)) ≫
        (((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map
          (pullbackComparison F a x).hom)
    let strict :=
      (pullbackComparison F b x).hom ≫
        (F.toHom.fiberFunctor A).map
          (((canonicalFiberPseudofunctor X.p).mapComp'
              a.op.toLoc k.op.toLoc b.op.toLoc
              (comp_toLoc_eq a k b hk)).hom.toNatTrans.app x) ≫
        (pullbackComparison F k
          (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x)).inv
    let tailk :=
      (canonicalPullbackChoice Y.p).map k
        ((F.toHom.fiberFunctor B).obj
          (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x))
    let taila := F.toHom.map ((canonicalPullbackChoice X.p).map a x)
    raw.1 ≫ tailk ≫ taila = strict.1 ≫ tailk ≫ taila := by
  sorry

/-- Helper for Lemma 8.2.3: after postcomposing the raw left `pullHom` boundary and the strict
composite-leg left boundary with the chosen target pullback arrow over `k`, the two owner-level
composites already agree. -/
private theorem fibredMorphismPresheafMap_pullHom_left_boundary_postcompose_k_target
    (F : X ⟶ Y) {D B A : C} (x : X.p.Fiber D)
    (a : B ⟶ D) (k : A ⟶ B) (b : A ⟶ D) (hk : k ≫ a = b) :
    let raw :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          a.op.toLoc k.op.toLoc b.op.toLoc
          (comp_toLoc_eq a k b hk)).hom.toNatTrans.app
        ((F.toHom.fiberFunctor D).obj x)) ≫
        (((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map
          (pullbackComparison F a x).hom)
    let strict :=
      (pullbackComparison F b x).hom ≫
        (F.toHom.fiberFunctor A).map
          (((canonicalFiberPseudofunctor X.p).mapComp'
              a.op.toLoc k.op.toLoc b.op.toLoc
              (comp_toLoc_eq a k b hk)).hom.toNatTrans.app x) ≫
        (pullbackComparison F k
          (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x)).inv
    let tail :=
      (canonicalPullbackChoice Y.p).map k
        ((F.toHom.fiberFunctor B).obj
          (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x))
    raw.1 ≫ tail = strict.1 ≫ tail := by
  let raw :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        a.op.toLoc k.op.toLoc b.op.toLoc
        (comp_toLoc_eq a k b hk)).hom.toNatTrans.app
      ((F.toHom.fiberFunctor D).obj x)) ≫
      (((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map
        (pullbackComparison F a x).hom)
  let strict :=
    (pullbackComparison F b x).hom ≫
      (F.toHom.fiberFunctor A).map
        (((canonicalFiberPseudofunctor X.p).mapComp'
            a.op.toLoc k.op.toLoc b.op.toLoc
            (comp_toLoc_eq a k b hk)).hom.toNatTrans.app x) ≫
      (pullbackComparison F k
        (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x)).inv
  let tail :=
    (canonicalPullbackChoice Y.p).map k
      ((F.toHom.fiberFunctor B).obj
        (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x))
  let taila := F.toHom.map ((canonicalPullbackChoice X.p).map a x)
  have htaila : Y.p.IsStronglyCartesian a taila := by
    -- Transport the chosen source pullback arrow over `a` across the fibred functor.
    change Y.p.IsStronglyCartesian a (F.toHom.map ((canonicalPullbackChoice X.p).map a x))
    exact
      map_stronglyCartesian_of_lift F a
        ((canonicalPullbackChoice X.p).map a x)
        ((canonicalPullbackChoice X.p).isStronglyCartesian a x)
  have htail : Y.p.IsHomLift k tail := by
    change
      Y.p.IsHomLift k
        ((canonicalPullbackChoice Y.p).map k
          ((F.toHom.fiberFunctor B).obj
            (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x)))
    exact
      ((canonicalPullbackChoice Y.p).isStronglyCartesian k
        ((F.toHom.fiberFunctor B).obj
          (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x))).toIsHomLift
  letI : Y.p.IsStronglyCartesian a taila := htaila
  letI : Y.p.IsHomLift (𝟙 A) raw.1 := raw.2
  letI : Y.p.IsHomLift (𝟙 A) strict.1 := strict.2
  letI : Y.p.IsHomLift k tail := htail
  have hrawtail : Y.p.IsHomLift k (raw.1 ≫ tail) := by
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ Y.p _ _ _
      A raw.1 raw.2 _ _ k tail htail
  have hstricttail : Y.p.IsHomLift k (strict.1 ≫ tail) := by
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ Y.p _ _ _
      A strict.1 strict.2 _ _ k tail htail
  have hpost : (raw.1 ≫ tail) ≫ taila = (strict.1 ≫ tail) ≫ taila := by
    -- Compare after composing with the common strongly cartesian leg over `a`.
    simpa only [Category.assoc] using
      fibredMorphismPresheafMap_pullHom_left_boundary_postcompose_k_then_a_target F x a k b hk
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ Y.p _ _ _ _
      a taila htaila _ _ k (raw.1 ≫ tail) (strict.1 ≫ tail) hrawtail hstricttail hpost

/-- Helper for Lemma 8.2.3: the raw left `pullHom` boundary is exactly the strict composite-leg
comparison shell after passing back to the fiber over the domain of `b`. -/
private theorem fibredMorphismPresheafMap_pullHom_left_boundary
    (F : X ⟶ Y) {D B A : C} (x : X.p.Fiber D)
    (a : B ⟶ D) (k : A ⟶ B) (b : A ⟶ D) (hk : k ≫ a = b) :
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          a.op.toLoc k.op.toLoc b.op.toLoc
          (comp_toLoc_eq a k b hk)).hom.toNatTrans.app
        ((F.toHom.fiberFunctor D).obj x)) ≫
    (((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map
          (pullbackComparison F a x).hom) =
      (pullbackComparison F b x).hom ≫
        (F.toHom.fiberFunctor A).map
          (((canonicalFiberPseudofunctor X.p).mapComp'
              a.op.toLoc k.op.toLoc b.op.toLoc
              (comp_toLoc_eq a k b hk)).hom.toNatTrans.app x) ≫
        (pullbackComparison F k
          (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x)).inv := by
  let raw :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        a.op.toLoc k.op.toLoc b.op.toLoc
        (comp_toLoc_eq a k b hk)).hom.toNatTrans.app
      ((F.toHom.fiberFunctor D).obj x)) ≫
      (((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map
        (pullbackComparison F a x).hom)
  let strict :=
    (pullbackComparison F b x).hom ≫
      (F.toHom.fiberFunctor A).map
        (((canonicalFiberPseudofunctor X.p).mapComp'
            a.op.toLoc k.op.toLoc b.op.toLoc
            (comp_toLoc_eq a k b hk)).hom.toNatTrans.app x) ≫
      (pullbackComparison F k
        (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x)).inv
  let tail :=
    (canonicalPullbackChoice Y.p).map k
      ((F.toHom.fiberFunctor B).obj
        (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x))
  have htail : Y.p.IsStronglyCartesian k tail := by
    -- Reuse the chosen target pullback arrow over the common leg `k`.
    change
      Y.p.IsStronglyCartesian k
        ((canonicalPullbackChoice Y.p).map k
          ((F.toHom.fiberFunctor B).obj
            (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x)))
    exact
      (canonicalPullbackChoice Y.p).isStronglyCartesian k
        ((F.toHom.fiberFunctor B).obj
          (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x))
  have hpost : raw.1 ≫ tail = strict.1 ≫ tail := by
    -- Reduce the fiber equality to the owner-level comparison after composing with the `k`-leg.
    change raw.1 ≫ tail = strict.1 ≫ tail
    exact fibredMorphismPresheafMap_pullHom_left_boundary_postcompose_k_target F x a k b hk
  -- Compare the two fiber morphisms via the common strongly cartesian arrow over `k`.
  apply Functor.Fiber.hom_ext
  change raw.1 = strict.1
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ Y.p _ _ _ _
      k tail htail _ _ (𝟙 A) raw.1 strict.1 raw.2 strict.2 hpost

/-- Helper for Lemma 8.2.3: after postcomposing the raw right `pullHom` boundary and the strict
composite-leg right boundary with the chosen `b`-pullback arrow, both owner-level composites
reduce to the same mapped source composite-leg factorization. -/
private theorem fibredMorphismPresheafMap_pullHom_right_boundary_postcompose_target
    (F : X ⟶ Y) {D B A : C} (y : X.p.Fiber D)
    (a : B ⟶ D) (k : A ⟶ B) (b : A ⟶ D) (hk : k ≫ a = b) :
    let raw :=
      (pullbackComparison F k
          (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y)).inv ≫
        (((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map
          (pullbackComparison F a y).inv) ≫
        (((canonicalFiberPseudofunctor Y.p).mapComp'
            a.op.toLoc k.op.toLoc b.op.toLoc
            (comp_toLoc_eq a k b hk)).inv.toNatTrans.app
          ((F.toHom.fiberFunctor D).obj y))
    let strict :=
      (F.toHom.fiberFunctor A).map
          (((canonicalFiberPseudofunctor X.p).mapComp'
              a.op.toLoc k.op.toLoc b.op.toLoc
              (comp_toLoc_eq a k b hk)).inv.toNatTrans.app y) ≫
        (pullbackComparison F b y).inv
    let tail :=
      (canonicalPullbackChoice Y.p).map b
        ((F.toHom.fiberFunctor D).obj y)
    raw.1 ≫ tail = strict.1 ≫ tail := by
  sorry

/-- Helper for Lemma 8.2.3: the raw right `pullHom` boundary is exactly the strict
composite-leg right shell after passing back to the fiber over the domain of `b`. -/
private theorem fibredMorphismPresheafMap_pullHom_right_boundary
    (F : X ⟶ Y) {D B A : C} (y : X.p.Fiber D)
    (a : B ⟶ D) (k : A ⟶ B) (b : A ⟶ D) (hk : k ≫ a = b) :
    (pullbackComparison F k
        (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y)).inv ≫
      (((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map
        (pullbackComparison F a y).inv) ≫
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          a.op.toLoc k.op.toLoc b.op.toLoc
          (comp_toLoc_eq a k b hk)).inv.toNatTrans.app
        ((F.toHom.fiberFunctor D).obj y)) =
    (F.toHom.fiberFunctor A).map
        (((canonicalFiberPseudofunctor X.p).mapComp'
            a.op.toLoc k.op.toLoc b.op.toLoc
            (comp_toLoc_eq a k b hk)).inv.toNatTrans.app y) ≫
      (pullbackComparison F b y).inv := by
  let raw :=
    (pullbackComparison F k
        (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y)).inv ≫
      (((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map
        (pullbackComparison F a y).inv) ≫
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          a.op.toLoc k.op.toLoc b.op.toLoc
          (comp_toLoc_eq a k b hk)).inv.toNatTrans.app
        ((F.toHom.fiberFunctor D).obj y))
  let strict :=
    (F.toHom.fiberFunctor A).map
        (((canonicalFiberPseudofunctor X.p).mapComp'
            a.op.toLoc k.op.toLoc b.op.toLoc
            (comp_toLoc_eq a k b hk)).inv.toNatTrans.app y) ≫
      (pullbackComparison F b y).inv
  let tail :=
    (canonicalPullbackChoice Y.p).map b
      ((F.toHom.fiberFunctor D).obj y)
  have htail : Y.p.IsStronglyCartesian b tail := by
    -- Reuse the chosen target pullback arrow over the composite leg `b`.
    change
      Y.p.IsStronglyCartesian b
        ((canonicalPullbackChoice Y.p).map b
          ((F.toHom.fiberFunctor D).obj y))
    exact
      (canonicalPullbackChoice Y.p).isStronglyCartesian b
        ((F.toHom.fiberFunctor D).obj y)
  have hpost : raw.1 ≫ tail = strict.1 ≫ tail := by
    -- Reduce the fiber equality to the owner-level postcomposed inverse-shell comparison.
    change raw.1 ≫ tail = strict.1 ≫ tail
    exact fibredMorphismPresheafMap_pullHom_right_boundary_postcompose_target F y a k b hk
  -- Compare the two fiber morphisms via the common strongly cartesian arrow over `b`.
  apply Functor.Fiber.hom_ext
  change raw.1 = strict.1
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ Y.p _ _ _ _
      b tail htail _ _ (𝟙 A) raw.1 strict.1 raw.2 strict.2 hpost

end FibredCategoryMor

/-- Helper for Lemma 8.2.3: composing in `C` and then passing to the locally discrete opposite is
the same as composing the corresponding `toLoc` arrows in the owner order used by `pullHom`. -/
private theorem comp_toLoc_eq
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf) :
    f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc := by
  -- Translate the composite equality to `LocallyDiscrete Cᵒᵖ`.
  simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
    congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hgf)

/-- Helper for Lemma 8.2.3: at a slice object `W : Over U`, the canonical Hom-presheaf map is
the comparison shell obtained by conjugating the mapped fiber morphism with pullback-comparison
isomorphisms. This isolates the objectwise part of the source proof from the remaining presheaf
naturality argument. -/
private noncomputable def fibredMorphismPresheafMapApp
    (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U) (W : Over U) :
    ((canonicalFiberPseudofunctor X.p).presheafHom x y).obj (op W) →
      ((canonicalFiberPseudofunctor Y.p).presheafHom
        ((F.toHom.fiberFunctor U).obj x)
        ((F.toHom.fiberFunctor U).obj y)).obj (op W) :=
  fun δ ↦
    (FibredCategoryMor.pullbackComparison F W.hom x).hom ≫
      (F.toHom.fiberFunctor W.left).map δ ≫
        (FibredCategoryMor.pullbackComparison F W.hom y).inv

/-- Helper for Lemma 8.2.3: after the two outer `pullHom` boundaries are normalized, the
remaining middle term is exactly the inverse naturality square for `pullbackComparison` over the
vertical morphism `δ`. -/
private theorem fibredMorphismPresheafMap_naturality_pointwise
    (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U)
    {W₁ W₂ : Over U} (α : op W₁ ⟶ op W₂)
    (δ : ((canonicalFiberPseudofunctor X.p).presheafHom x y).obj (op W₁)) :
    (((canonicalFiberPseudofunctor Y.p).presheafHom
        ((F.toHom.fiberFunctor U).obj x)
        ((F.toHom.fiberFunctor U).obj y)).map α)
      (fibredMorphismPresheafMapApp F x y W₁ δ) =
    fibredMorphismPresheafMapApp F x y W₂
      ((((canonicalFiberPseudofunctor X.p).presheafHom x y).map α) δ) := by
  sorry

/-- Helper for Lemma 8.2.3: the pointwise naturality proof packages to the exact
`NatTrans.naturality` field needed by `fibredMorphismPresheafMap`. -/
private theorem fibredMorphismPresheafMap_naturality
    (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U) :
    ∀ ⦃W₁ W₂ : (Over U)ᵒᵖ⦄ (α : W₁ ⟶ W₂),
      (((canonicalFiberPseudofunctor X.p).presheafHom x y).map α) ≫
          fibredMorphismPresheafMapApp F x y W₂.unop =
        fibredMorphismPresheafMapApp F x y W₁.unop ≫
          (((canonicalFiberPseudofunctor Y.p).presheafHom
              ((F.toHom.fiberFunctor U).obj x)
              ((F.toHom.fiberFunctor U).obj y)).map α) := by
  intro W₁ W₂ α
  funext δ
  -- Reduce function equality to the already proved pointwise comparison-shell equality.
  exact (fibredMorphismPresheafMap_naturality_pointwise F x y α δ).symm

/-- Lemma 8.2.3: a `1`-morphism of fibred categories over `C` induces the canonical morphism of
presheaves `Mor_{S₁}(x, y) ⟶ Mor_{S₂}(F(x), F(y))` on the slice category `C/U`. The source and
target are stated using the canonical Hom-presheaves from Definition `8.2.2`. -/
noncomputable def FibredCategoryMor.fibredMorphismPresheafMap
    (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U) :
    (canonicalFiberPseudofunctor X.p).presheafHom x y ⟶
      (canonicalFiberPseudofunctor Y.p).presheafHom
        (((F.toHom).fiberFunctor U).obj x)
        (((F.toHom).fiberFunctor U).obj y) :=
  { app := fun W ↦ fibredMorphismPresheafMapApp F x y W.unop
    naturality := fibredMorphismPresheafMap_naturality F x y }

end CategoryTheory
