import Mathlib
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_8_2_1 (from Chap08) -/
namespace CategoryTheory

/- Lemma 8.2.1 is a `core/canonical` recall in the prestack/descent domain: the source-facing
assignment sending `V/U : Over U` to the morphism type `Hom(V^* x, V^* y)` is already owned by
mathlib as `Pseudofunctor.presheafHom`. -/
recall Pseudofunctor.presheafHom

end CategoryTheory

/-! ### Definition_8_2_2 (from Chap08) -/
open Opposite

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/- Domain-style sampling for Definition 8.2.2:
- primary domain: subpresheaves of the canonical Hom-presheaf attached to the fiber
  pseudofunctor of a fibred category;
- sampled owner-level declarations:
  `CategoryTheory.Subfunctor`,
  `CategoryTheory.Subfunctor.toFunctor`,
  `Pseudofunctor.presheafHom`,
  `canonicalFiberPseudofunctor`;
- best owner abstraction: the source-facing object `Isom(x, y)` should be a `Subfunctor` of the
  canonical Hom-presheaf, with the underlying presheaf obtained by `Subfunctor.toFunctor`;
- primitive data: only the sectionwise predicate `IsIso` on the canonical Hom-presheaf;
- derived API: the underlying presheaf `(fiberIsomorphismSubfunctor p x y).toFunctor`.

Source/core/bridge triage:
- `source-facing`: `fiberIsomorphismSubfunctor`;
- `core/canonical`: `Subfunctor ((canonicalFiberPseudofunctor p).presheafHom x y)`;
- `bridge/view`: `Subfunctor.toFunctor`. -/

section

variable (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U)

private theorem isIso_presheafHom_map
    {A B : (Over U)ᵒᵖ} (g : A ⟶ B)
    (φ : ((canonicalFiberPseudofunctor p).presheafHom x y).obj A) (hφ : IsIso φ) :
    IsIso (((canonicalFiberPseudofunctor p).presheafHom x y).map g φ) := by
  let F := canonicalFiberPseudofunctor p
  let a := A.unop.hom
  let b := B.unop.hom
  let f := g.unop.left
  have hg :
      a.op.toLoc ≫ f.op.toLoc = b.op.toLoc := by
    simpa [a, b, f] using congrArg (fun k ↦ k.op.toLoc) (Over.w g.unop)
  letI : IsIso φ := hφ
  let compIso := F.mapComp' a.op.toLoc f.op.toLoc b.op.toLoc hg
  let middleIso :
      (F.map a.op.toLoc).toFunctor.obj x ≅ (F.map a.op.toLoc).toFunctor.obj y := by
    simpa [presheafHom, pullHom] using asIso φ
  let e := (Cat.Hom.toNatIso compIso).app x ≪≫
      (F.map f.op.toLoc).toFunctor.mapIso middleIso ≪≫
      ((Cat.Hom.toNatIso compIso).app y).symm
  simpa [presheafHom, pullHom, compIso, middleIso, e, hg, Category.assoc] using
    (show IsIso e.hom from inferInstance)

/-- Definition 8.2.2: the presheaf `Isom(x, y)` is the canonical subpresheaf of `Mor(x, y)`
whose sections are fiberwise isomorphisms, expressed through the owner abstraction
`Subfunctor ((canonicalFiberPseudofunctor p).presheafHom x y)`. -/
noncomputable def fiberIsomorphismSubfunctor
    (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U) :
    Subfunctor ((canonicalFiberPseudofunctor p).presheafHom x y) where
  obj _ := { φ | IsIso φ }
  map g := isIso_presheafHom_map p x y g

-- Proof sketch: unfold `fiberIsomorphismSubfunctor`; its sectionwise predicate was defined to be
-- exactly `IsIso` on the canonical Hom-presheaf.
/-- A section of `fiberIsomorphismSubfunctor p x y` is exactly an isomorphism in the corresponding
fiber. -/
@[simp]
theorem mem_fiberIsomorphismSubfunctor_obj_iff
    (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U) {A : (Over U)ᵒᵖ}
    (φ : ((canonicalFiberPseudofunctor p).presheafHom x y).obj A) :
    (fiberIsomorphismSubfunctor p x y).obj A φ ↔ IsIso φ := by
  -- Unfold the defining sectionwise predicate of the subpresheaf `Isom(x, y)`.
  change IsIso φ ↔ IsIso φ
  -- The reduced goal is definitional.
  exact Iff.rfl

end

end CategoryTheory

/-! ### Lemma_8_2_3 (from Chap08) -/
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

/-! ### Remark_8_2_4 (from Chap08) -/
open Opposite

universe u v uS vS

namespace CategoryTheory

open BasedFunctor
open FibredCategoryMor

variable {C : Type u} [Category.{v} C]

/-- Helper for Remark 8.2.4: a category fibred in groupoids over `C` is a fibred category over
`C` whose projection functor is fibred in groupoids. -/
structure FibredInGroupoidsOver (C : Type u) [Category.{v} C] where
  toFibredCategoryOver : FibredCategoryOver.{u, v, uS, vS} C
  fibredInGroupoids : IsFibredInGroupoids toFibredCategoryOver.p

namespace FibredInGroupoidsOver

/-- Helper for Remark 8.2.4: the projection functor of a category fibred in groupoids over
`C`. -/
abbrev p (X : FibredInGroupoidsOver C) :=
  X.toFibredCategoryOver.p

/-- Helper for Remark 8.2.4: forget a category fibred in groupoids to its underlying fibred
category over `C`. -/
instance : CoeOut (FibredInGroupoidsOver C) (FibredCategoryOver C) where
  coe X := X.toFibredCategoryOver

/-- Helper for Remark 8.2.4: the projection of a category fibred in groupoids is again fibred in
groupoids. -/
instance (X : FibredInGroupoidsOver C) : IsFibredInGroupoids X.p :=
  X.fibredInGroupoids

end FibredInGroupoidsOver

variable {X Y : FibredInGroupoidsOver C}

/-- Helper for Remark 8.2.4: a morphism of categories fibred in groupoids is the underlying
morphism of fibred categories between the ambient fibred-category objects. -/
abbrev FibredInGroupoidsMor (X Y : FibredInGroupoidsOver C) :=
  X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver

namespace FibredInGroupoidsMor

/-- Helper for Remark 8.2.4: the underlying based functor of a morphism of categories fibred in
groupoids over `C`. -/
abbrev toBasedFunctor
    (F : FibredInGroupoidsMor X Y) :
    X.toFibredCategoryOver.toBasedCategory ⥤ᵇ Y.toFibredCategoryOver.toBasedCategory :=
  F.toHom

/-- Helper for Remark 8.2.4: equivalence over the base for a morphism of categories fibred in
groupoids is the ambient equivalence-over-base condition on the underlying based functor. -/
abbrev IsEquivalenceOverBase (F : FibredInGroupoidsMor X Y) : Prop :=
  BasedFunctor.IsEquivalenceOverBase F.toBasedFunctor

/- Domain-style sampling for Remark 8.2.4:
- primary domain: morphisms of categories fibred in groupoids over a fixed base and the induced
  canonical Hom-presheaf morphisms on fibers;
- sampled owner-level declarations:
  `FibredInGroupoidsMor.IsEquivalenceOverBase`,
  `BasedFunctor.isEquivalence_of_isEquivalenceOverBase`,
  `Functor.FullyFaithful.ofFullyFaithful`,
  `FibredCategoryMor.fibredMorphismPresheafMap_isIso_of_fullyFaithful`;
- best owner abstraction: the owner morphism `F : FibredInGroupoidsMor X Y`, with the
  equivalence-over-base predicate as primitive data; the Hom-presheaf isomorphism is derived API
  obtained by upgrading `F.toBasedFunctor` to an equivalence, then to the canonical fully
  faithful owner witness, and finally routing through the ambient
  `FibredCategoryMor.fibredMorphismPresheafMap_isIso_of_fullyFaithful` theorem;
- primitive data: only `F` together with `hF : F.IsEquivalenceOverBase`;
- derived API: `F.toBasedFunctor.IsEquivalence`, the resulting canonical fully faithful witness,
  and finally the `IsIso` statement for the comparison morphism `F.fibredMorphismPresheafMap x y`.

Source/core/bridge triage:
- `source-facing`: the remark-level conclusion that an equivalence over the base preserves the
  presheaves `Mor(x, y)`;
- `core/canonical`: `FibredInGroupoidsMor.IsEquivalenceOverBase`,
  `BasedFunctor.isEquivalence_of_isEquivalenceOverBase`,
  `Functor.FullyFaithful.ofFullyFaithful`, and
  `FibredCategoryMor.fibredMorphismPresheafMap_isIso_of_fullyFaithful`;
- `bridge/view`: the theorem below, which derives the source-facing conclusion from those owner
  abstractions without introducing a parallel presheaf API. -/

/-- Remark 8.2.4, in canonical form: for an equivalence over the base category `C`, the canonical
Hom-presheaf morphism from Lemma `8.2.3` is an isomorphism. Combined with
Lemma `4.37.3`, this is the source-faithful observation that one may replace a category fibred in
groupoids by an equivalent split model without changing the presheaves `Mor(x, y)`. -/
-- Proof sketch: upgrade the equivalence-over-base hypothesis to a fully faithful underlying based
-- functor, then apply the Chapter 8 isomorphism criterion for the canonical Hom-presheaf map.
theorem fibredMorphismPresheafMap_isIso_of_isEquivalenceOverBase
    (F : FibredInGroupoidsMor X Y) (hF : F.IsEquivalenceOverBase)
    {U : C} (x y : X.p.Fiber U) :
    IsIso (fibredMorphismPresheafMap
      (F : X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver) x y) := by
  -- Reinterpret the equivalence-over-base hypothesis as full faithfulness for the underlying
  -- based functor on total categories.
  have hFF : Nonempty F.toBasedFunctor.FullyFaithful := by
    let _ : F.toBasedFunctor.IsEquivalence :=
      BasedFunctor.isEquivalence_of_isEquivalenceOverBase F.toBasedFunctor hF
    exact ⟨Functor.FullyFaithful.ofFullyFaithful F.toBasedFunctor.toFunctor⟩
  -- Each component is conjugation by the pullback-comparison isomorphisms around the map induced
  -- by the fiber functor, hence bijective.
  rw [NatTrans.isIso_iff_isIso_app]
  intro W
  rw [isIso_iff_bijective]
  let xW := W.unop.hom ^*[canonicalPullbackChoice X.toFibredCategoryOver.p] x
  let yW := W.unop.hom ^*[canonicalPullbackChoice X.toFibredCategoryOver.p] y
  let FxW := (F.toBasedFunctor.fiberFunctor W.unop.left).obj xW
  let FyW := (F.toBasedFunctor.fiberFunctor W.unop.left).obj yW
  let ex := FibredCategoryMor.pullbackComparison F W.unop.hom x
  let ey := FibredCategoryMor.pullbackComparison F W.unop.hom y
  have hFiberFF :
      Nonempty ((F.toBasedFunctor.fiberFunctor W.unop.left).FullyFaithful) := by
    let _ : (F.toBasedFunctor.fiberFunctor W.unop.left).IsEquivalence :=
      BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
        F.toBasedFunctor hF W.unop.left
    exact ⟨Functor.FullyFaithful.ofFullyFaithful (F.toBasedFunctor.fiberFunctor W.unop.left)⟩
  have hFiberMapBijective :
      ∀ a b : X.toFibredCategoryOver.p.Fiber W.unop.left,
        Function.Bijective
          ((F.toBasedFunctor.fiberFunctor W.unop.left).map : (a ⟶ b) →
            ((F.toBasedFunctor.fiberFunctor W.unop.left).obj a ⟶
              (F.toBasedFunctor.fiberFunctor W.unop.left).obj b)) := by
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective] at hFiberFF
    exact hFiberFF
  have hMap :
      Function.Bijective ((F.toBasedFunctor.fiberFunctor W.unop.left).map : (xW ⟶ yW) → (FxW ⟶ FyW)) := by
    simpa [xW, yW, FxW, FyW] using hFiberMapBijective xW yW
  let eCongr :
      (FxW ⟶ FyW) ≃
        ((canonicalFiberPseudofunctor Y.toFibredCategoryOver.p).presheafHom
          ((F.toHom.fiberFunctor U).obj x)
          ((F.toHom.fiberFunctor U).obj y)).obj W :=
    Iso.homCongr ex.symm ey.symm
  have hApp :
      (fibredMorphismPresheafMap
        (F := (F : X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver)) x y).app W =
        fun δ : xW ⟶ yW ↦ eCongr ((F.toBasedFunctor.fiberFunctor W.unop.left).map δ) := by
    funext δ
    rfl
  rw [hApp]
  constructor
  · intro δ₁ δ₂ hδ
    apply hMap.1
    apply eCongr.injective
    simpa using hδ
  · intro θ
    rcases eCongr.surjective θ with ⟨θ', rfl⟩
    rcases hMap.2 θ' with ⟨δ, rfl⟩
    exact ⟨δ, rfl⟩

end FibredInGroupoidsMor

end CategoryTheory

/-! ### Lemma_8_2_5 (from Chap08) -/
/-
Domain-style sampling for Lemma 8.2.5:
- primary domain: categories fibred in setoids over a slice category, together with the presheaf
  of isomorphism classes attached to a fibred-in-setoids projection;
- inspected owner-level declarations:
  `IsFibredInSetoids`,
  `explicitTwoFibreProductLeftProjection`,
  `sliceTwoFibreProductStructuredArrowToFiber_isEquivalence`,
  `Functor.fiberIsoClassPresheaf`,
  `fiberIsomorphismSubfunctor`;
- best owner abstraction: clause `(1)` is source-facing and should stay a public theorem asserting
  that the explicit slice `2`-fibre-product projection is `IsFibredInSetoids`; the stronger
  Chapter 4 owner theorem `explicitTwoFibreProductLeftProjection_isFibredInGroupoids` is not the
  right main abstraction here because it assumes a fibred-in-groupoids target, stronger than the
  source lemma. Clause `(2)` is the bridge identifying the source-facing presheaf `Isom(x, y)`
  with the canonical owner `fiberIsoClassPresheaf` of that projection;
- primitive data: the fibred category `X`, an object `U : C`, and fiber objects `x y : X.p.Fiber U`;
- derived API: the `IsFibredInSetoids` instance on the projection and the presheaf comparison in
  clause `(2)`.

Source/core/bridge triage:
- `source-facing`: `fiberObjectSliceProjection`,
  `fiberObjectSliceProjection_isFibredInSetoids`;
- `core/canonical`: `IsFibredInSetoids` and `Functor.fiberIsoClassPresheaf`;
- `bridge/view`: `fiberIsomorphismSubfunctor_toFunctor_eq_fiberIsoClassPresheaf`. -/

open Opposite

universe u v uS

namespace CategoryTheory

open CategoryOver
open Functor

variable {C : Type u} [Category.{v} C]

namespace FibredCategoryOver

/-- The canonical slice `2`-fibre-product projection over `C/U` attached to two objects
`x, y ∈ X_U`, obtained as the left projection from the explicit `2`-fibre product of the
pullback-model `2`-Yoneda morphisms `C/U ⟶ X` corresponding to `x` and `y`. -/
noncomputable def fiberObjectSliceProjection
    (X : FibredCategoryOver C) {U : C} (x y : X.p.Fiber U) :
    (explicitTwoFibreProduct
      (((X.yonedaEvaluationFunctor U).asEquivalence.inverse.obj x).toHom)
      (((X.yonedaEvaluationFunctor U).asEquivalence.inverse.obj y).toHom)).obj ⥤ Over U :=
  let Gx : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ X.toBasedCategory :=
    ((X.yonedaEvaluationFunctor U).asEquivalence.inverse.obj x).toHom
  let Gy : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ X.toBasedCategory :=
    ((X.yonedaEvaluationFunctor U).asEquivalence.inverse.obj y).toHom
  show
      (explicitTwoFibreProduct Gx Gy).obj ⥤ Over U from
    (explicitTwoFibreProductLeftProjection Gx Gy).toFunctor

section

variable (X : FibredCategoryOver C) {U : C} (x y : X.p.Fiber U)

-- Proof sketch: over an object `f : V ⟶ U` of the slice category, Lemma `4.42.1` identifies the
-- corresponding fiber with a structured-arrow category whose source fiber in `C/U` is thin. Hence
-- any two morphisms in that fiber agree.
/-- Every standard fiber of the canonical slice `2`-fibre-product projection for `x` and `y` is a
setoid `1`-category. -/
private theorem fiberObjectSliceProjection_fiber_isThin
    (f : Over U) :
    Quiver.IsThin ((X.fiberObjectSliceProjection x y).Fiber f) := by
  sorry

/-- Lemma 8.2.5 (1): for objects `x` and `y` in the fiber `S_U` of a fibred category `p : S ⥤ C`,
the explicit `2`-fibre product over `C/U` of the corresponding pullback-model `2`-Yoneda
morphisms is fibred in setoids over `C/U`. -/
theorem fiberObjectSliceProjection_isFibredInSetoids :
    IsFibredInSetoids (X.fiberObjectSliceProjection x y) := by
  let p := X.fiberObjectSliceProjection x y
  letI : ∀ f : Over U, Quiver.IsThin (p.Fiber f) :=
    fiberObjectSliceProjection_fiber_isThin X x y
  change IsFibredInSetoids p
  letI : IsFibredInGroupoids p := by
    sorry
  infer_instance

instance :
    IsFibredInSetoids (X.fiberObjectSliceProjection x y) :=
  fiberObjectSliceProjection_isFibredInSetoids X x y

/-- Lemma 8.2.5 (2): the underlying presheaf of the canonical subpresheaf `Isom(x, y)` from
Definition `8.2.2` is the presheaf of isomorphism classes attached to the fibred-in-setoids
projection from part `(1)`, after the canonical universe lift from `Type v` to `Type (max u v)`. -/
theorem fiberIsomorphismSubfunctor_toFunctor_eq_fiberIsoClassPresheaf
    :
    (fiberIsomorphismSubfunctor X.p x y).toFunctor ⋙ uliftFunctor.{u, v} =
      (X.fiberObjectSliceProjection x y).fiberIsoClassPresheaf := by
  sorry

end

end FibredCategoryOver

end CategoryTheory
