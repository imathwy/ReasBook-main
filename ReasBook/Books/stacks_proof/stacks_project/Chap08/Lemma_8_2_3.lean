import Mathlib
import StacksProject_2024.Chap04.Definition_4_33_9
import StacksProject_2024.Chap04.Definition_4_32_1
import StacksProject_2024.Chap04.CanonicalFiberPseudofunctor
import StacksProject_2024.Chap08.Lemma_8_2_3.PullbackComparisonNaturality

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
  let e := pullbackComparison F b x
  let ck :=
    pullbackComparison F k
      (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x)
  let ea := pullbackComparison F a x
  let leftRaw :=
    ((canonicalFiberPseudofunctor Y.p).mapComp'
      a.op.toLoc k.op.toLoc b.op.toLoc
      (comp_toLoc_eq a k b hk)).hom.toNatTrans.app
      ((F.toHom.fiberFunctor D).obj x)
  let leftSource :=
    ((canonicalFiberPseudofunctor X.p).mapComp'
      a.op.toLoc k.op.toLoc b.op.toLoc
      (comp_toLoc_eq a k b hk)).hom.toNatTrans.app
      x
  have hraw_expand :
      raw.1 =
        leftRaw.1 ≫
          ((((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map ea.hom)).1 := by
    rfl
  have hstrict_expand :
      strict.1 =
        e.hom.1 ≫ ((F.toHom.fiberFunctor A).map leftSource).1 ≫ ck.inv.1 := by
    rfl
  have hraw :
      raw.1 ≫ tailk ≫ taila =
        (canonicalPullbackChoice Y.p).map b ((F.toHom.fiberFunctor D).obj x) := by
    have hraw_flank :
        (leftRaw.1 ≫
            (canonicalPullbackChoice Y.p).map k
              (((canonicalFiberPseudofunctor Y.p).map a.op.toLoc).toFunctor.obj
                ((F.toHom.fiberFunctor D).obj x))) ≫
            (canonicalPullbackChoice Y.p).map a
              ((F.toHom.fiberFunctor D).obj x) =
          (canonicalPullbackChoice Y.p).map b
            ((F.toHom.fiberFunctor D).obj x) := by
      -- The target `mapComp'` hom component factors through the chosen composite-leg pullback.
      change
        ((((canonicalFiberPseudofunctor Y.p).mapComp'
            a.op.toLoc k.op.toLoc b.op.toLoc
            (comp_toLoc_eq a k b hk)).hom.toNatTrans.app
          ((F.toHom.fiberFunctor D).obj x)).1 ≫
          (canonicalPullbackChoice Y.p).map k
            (((canonicalFiberPseudofunctor Y.p).map a.op.toLoc).toFunctor.obj
              ((F.toHom.fiberFunctor D).obj x))) ≫
          (canonicalPullbackChoice Y.p).map a
            ((F.toHom.fiberFunctor D).obj x) =
        (canonicalPullbackChoice Y.p).map b
          ((F.toHom.fiberFunctor D).obj x)
      simpa only [Category.assoc] using
        canonicalFiberPseudofunctor_mapComp'_hom_app_fac
          (p := Y.p) (f := a) (g := k) (gf := b) (hgf := hk)
          ((F.toHom.fiberFunctor D).obj x)
    -- Normalize the raw shell to the chosen pullback arrow over the composite leg `b`.
    calc
      raw.1 ≫ tailk ≫ taila =
          leftRaw.1 ≫
            ((((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map ea.hom)).1 ≫
            tailk ≫
            taila := by
              rw [hraw_expand]
              simp only [Category.assoc]
      _ =
          leftRaw.1 ≫
            (((((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map ea.hom)).1 ≫
              tailk) ≫
            taila := by
              simp only [Category.assoc]
      _ =
          leftRaw.1 ≫
            (((canonicalPullbackChoice Y.p).map k
                (((canonicalFiberPseudofunctor Y.p).map a.op.toLoc).toFunctor.obj
                  ((F.toHom.fiberFunctor D).obj x))) ≫
              ea.hom.1) ≫
            taila := by
              exact
                congrArg (fun t ↦ leftRaw.1 ≫ t ≫ taila)
                  (canonical_pullbackFunctor_map_fac (p := Y.p) (f := k) (φ := ea.hom))
      _ =
          leftRaw.1 ≫
            (canonicalPullbackChoice Y.p).map k
              (((canonicalFiberPseudofunctor Y.p).map a.op.toLoc).toFunctor.obj
                ((F.toHom.fiberFunctor D).obj x)) ≫
            ea.hom.1 ≫
            taila := by
              simp only [Category.assoc]
      _ =
          (canonicalPullbackChoice Y.p).map b
            ((F.toHom.fiberFunctor D).obj x) := by
              have hposta :
                  leftRaw.1 ≫
                      (canonicalPullbackChoice Y.p).map k
                        (((canonicalFiberPseudofunctor Y.p).map a.op.toLoc).toFunctor.obj
                          ((F.toHom.fiberFunctor D).obj x)) ≫
                      ea.hom.1 ≫
                      taila =
                    (leftRaw.1 ≫
                      (canonicalPullbackChoice Y.p).map k
                        (((canonicalFiberPseudofunctor Y.p).map a.op.toLoc).toFunctor.obj
                          ((F.toHom.fiberFunctor D).obj x))) ≫
                      (canonicalPullbackChoice Y.p).map a
                        ((F.toHom.fiberFunctor D).obj x) := by
                simpa only [Category.assoc] using
                  congrArg
                    (fun t ↦
                      leftRaw.1 ≫
                        (canonicalPullbackChoice Y.p).map k
                          (((canonicalFiberPseudofunctor Y.p).map a.op.toLoc).toFunctor.obj
                            ((F.toHom.fiberFunctor D).obj x)) ≫
                        t)
                    (pullbackComparison_hom_postcompose F a x)
              exact hposta.trans hraw_flank
  have hstrict :
      strict.1 ≫ tailk ≫ taila =
        (canonicalPullbackChoice Y.p).map b
          ((F.toHom.fiberFunctor D).obj x) := by
    have hpostk :
        ck.inv.1 ≫ tailk =
          F.toHom.map ((canonicalPullbackChoice X.p).map k
            (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x)) := by
      -- Cancel the inverse comparison on the common `k` leg against the chosen target pullback.
      change
        (pullbackComparison F k
            (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x)).inv.1 ≫
          (canonicalPullbackChoice Y.p).map k
            ((F.toHom.fiberFunctor B).obj
              (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x)) =
        F.toHom.map ((canonicalPullbackChoice X.p).map k
          (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x))
      exact pullbackComparison_inv_postcompose_owner
        (F := F) (f := k)
        (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x)
    have hpostk' :
        (ck.inv.1 ≫ tailk) ≫ taila =
          F.toHom.map ((canonicalPullbackChoice X.p).map k
              (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x)) ≫
            taila := by
      exact congrArg (fun t ↦ t ≫ taila) hpostk
    -- Normalize the strict shell to the same chosen composite-leg pullback arrow.
    calc
      strict.1 ≫ tailk ≫ taila =
          e.hom.1 ≫ ((F.toHom.fiberFunctor A).map leftSource).1 ≫
            ck.inv.1 ≫
            tailk ≫
            taila := by
              rw [hstrict_expand]
              simp only [Category.assoc]
      _ =
          e.hom.1 ≫ ((F.toHom.fiberFunctor A).map leftSource).1 ≫
            (ck.inv.1 ≫ tailk) ≫
            taila := by
              simp only [Category.assoc]
      _ =
          e.hom.1 ≫ ((F.toHom.fiberFunctor A).map leftSource).1 ≫
            (ck.inv.1 ≫ tailk ≫ taila) := by
              simp only [Category.assoc]
      _ =
          e.hom.1 ≫ ((F.toHom.fiberFunctor A).map leftSource).1 ≫
            (F.toHom.map ((canonicalPullbackChoice X.p).map k
              (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x)) ≫
              taila) := by
              simpa only [Category.assoc] using
                congrArg
                  (fun t ↦ e.hom.1 ≫ ((F.toHom.fiberFunctor A).map leftSource).1 ≫ t)
                  hpostk'
      _ =
          e.hom.1 ≫
            F.toHom.map
              (leftSource.1 ≫
                (canonicalPullbackChoice X.p).map k
                  (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x) ≫
                (canonicalPullbackChoice X.p).map a x) := by
              simpa only [taila, Category.assoc] using
                congrArg
                  (fun t ↦ e.hom.1 ≫ t)
                  (functor_map_threefold_comp
                    F.toHom.toFunctor leftSource.1
                    ((canonicalPullbackChoice X.p).map k
                      (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x))
                    ((canonicalPullbackChoice X.p).map a x)).symm
      _ =
          e.hom.1 ≫ F.toHom.map ((canonicalPullbackChoice X.p).map b x) := by
              exact
                congrArg (fun t ↦ e.hom.1 ≫ F.toHom.map t)
                  (canonicalFiberPseudofunctor_mapComp'_hom_app_fac
                    (p := X.p) (f := a) (g := k) (gf := b) (hgf := hk) x)
      _ =
          (canonicalPullbackChoice Y.p).map b
            ((F.toHom.fiberFunctor D).obj x) := by
              exact pullbackComparison_hom_postcompose F b x
  -- Both boundary shells have the same owner-level normal form.
  exact hraw.trans hstrict.symm

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
  let e := pullbackComparison F b y
  let ck :=
    pullbackComparison F k
      (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y)
  let ea := pullbackComparison F a y
  let tailk :=
    (canonicalPullbackChoice Y.p).map k
      (((canonicalFiberPseudofunctor Y.p).map a.op.toLoc).toFunctor.obj
        ((F.toHom.fiberFunctor D).obj y))
  let taila := (canonicalPullbackChoice Y.p).map a ((F.toHom.fiberFunctor D).obj y)
  let sourceTailk :=
    F.toHom.map ((canonicalPullbackChoice X.p).map k
      (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y))
  let sourceTaila := F.toHom.map ((canonicalPullbackChoice X.p).map a y)
  let rightSource :=
    ((canonicalFiberPseudofunctor X.p).mapComp'
      a.op.toLoc k.op.toLoc b.op.toLoc (comp_toLoc_eq a k b hk)).inv.toNatTrans.app
      y
  have hraw_expand :
      raw.1 =
        ck.inv.1 ≫
          ((((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map ea.inv)).1 ≫
          (((canonicalFiberPseudofunctor Y.p).mapComp'
              a.op.toLoc k.op.toLoc b.op.toLoc
              (comp_toLoc_eq a k b hk)).inv.toNatTrans.app
            ((F.toHom.fiberFunctor D).obj y)).1 := by
    rfl
  have hstrict_expand :
      strict.1 = ((F.toHom.fiberFunctor A).map rightSource).1 ≫ e.inv.1 := by
    rfl
  have hraw :
      raw.1 ≫ tail = sourceTailk ≫ sourceTaila := by
    have hmap_tailk :
        ((((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map ea.inv)).1 ≫
            tailk =
          (canonicalPullbackChoice Y.p).map k
              ((F.toHom.fiberFunctor B).obj
                (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y)) ≫
            ea.inv.1 := by
      -- Pullback-functor naturality rewrites the mapped inverse comparison over the `k` leg.
      change
        (((((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map
              (pullbackComparison F a y).inv)).1) ≫
            (canonicalPullbackChoice Y.p).map k
              (((canonicalFiberPseudofunctor Y.p).map a.op.toLoc).toFunctor.obj
                ((F.toHom.fiberFunctor D).obj y)) =
          (canonicalPullbackChoice Y.p).map k
              ((F.toHom.fiberFunctor B).obj
                (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y)) ≫
            (pullbackComparison F a y).inv.1
      exact canonical_pullbackFunctor_map_fac (p := Y.p) (f := k) (φ := ea.inv)
    have hsourceTailk :
        ck.inv.1 ≫
            (canonicalPullbackChoice Y.p).map k
              ((F.toHom.fiberFunctor B).obj
                (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y)) =
          sourceTailk := by
      -- Cancel the inverse comparison against the chosen target pullback on the common `k` leg.
      change
        (pullbackComparison F k
            (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y)).inv.1 ≫
          (canonicalPullbackChoice Y.p).map k
            ((F.toHom.fiberFunctor B).obj
              (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y)) =
        sourceTailk
      exact pullbackComparison_inv_postcompose_owner
        (F := F) (f := k)
        (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y)
    have hmap_tailk' :
        (((((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map ea.inv)).1 ≫
            tailk) ≫ taila =
          ((canonicalPullbackChoice Y.p).map k
              ((F.toHom.fiberFunctor B).obj
                (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y)) ≫
            ea.inv.1) ≫
            taila := by
      exact congrArg (fun t ↦ t ≫ taila) hmap_tailk
    have hsourceTailk' :
        (ck.inv.1 ≫
            (canonicalPullbackChoice Y.p).map k
              ((F.toHom.fiberFunctor B).obj
                (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y))) ≫
            sourceTaila =
          sourceTailk ≫ sourceTaila := by
      exact congrArg (fun t ↦ t ≫ sourceTaila) hsourceTailk
    have hraw_mid :
        raw.1 ≫ tail =
          (ck.inv.1 ≫
            (canonicalPullbackChoice Y.p).map k
              ((F.toHom.fiberFunctor B).obj
                (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y))) ≫
            sourceTaila := by
      -- Normalize the raw inverse shell to the source composite-leg factorization transported by
      -- the fibred-category morphism.
      calc
      raw.1 ≫ tail =
          ck.inv.1 ≫
            ((((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map ea.inv)).1 ≫
            (((canonicalFiberPseudofunctor Y.p).mapComp'
                a.op.toLoc k.op.toLoc b.op.toLoc
                (comp_toLoc_eq a k b hk)).inv.toNatTrans.app
              ((F.toHom.fiberFunctor D).obj y)).1 ≫
            tail := by
              rw [hraw_expand]
              simp only [Category.assoc]
      _ =
          ck.inv.1 ≫
            ((((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map ea.inv)).1 ≫
            ((((canonicalFiberPseudofunctor Y.p).mapComp'
                a.op.toLoc k.op.toLoc b.op.toLoc
                (comp_toLoc_eq a k b hk)).inv.toNatTrans.app
              ((F.toHom.fiberFunctor D).obj y)).1 ≫
              tail) := by
              rfl
      _ =
          ck.inv.1 ≫
            ((((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map ea.inv)).1 ≫
            (tailk ≫ taila) := by
              exact
                congrArg
                  (fun t ↦
                    ck.inv.1 ≫
                      ((((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map
                        ea.inv)).1 ≫
                      t)
                  (canonicalFiberPseudofunctor_mapComp'_inv_app_fac
                    (p := Y.p) (f := a) (g := k) (gf := b) (hgf := hk)
                    ((F.toHom.fiberFunctor D).obj y))
      _ =
          ck.inv.1 ≫
            (((((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor.map ea.inv)).1 ≫
              tailk) ≫
            taila := by
              simp only [Category.assoc]
      _ =
          ck.inv.1 ≫
            (((canonicalPullbackChoice Y.p).map k
                ((F.toHom.fiberFunctor B).obj
                  (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y))) ≫
              ea.inv.1) ≫ taila := by
              simpa only [Category.assoc] using congrArg (fun t ↦ ck.inv.1 ≫ t) hmap_tailk'
      _ =
          ck.inv.1 ≫
            (canonicalPullbackChoice Y.p).map k
              ((F.toHom.fiberFunctor B).obj
                (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y)) ≫
            ea.inv.1 ≫
            taila := by
              simp only [Category.assoc]
      _ =
          ck.inv.1 ≫
            (canonicalPullbackChoice Y.p).map k
              ((F.toHom.fiberFunctor B).obj
                (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y)) ≫
            sourceTaila := by
              simpa only [sourceTaila, Category.assoc] using
                congrArg
                  (fun t ↦
                    ck.inv.1 ≫
                      (canonicalPullbackChoice Y.p).map k
                        ((F.toHom.fiberFunctor B).obj
                          (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y)) ≫
                      t)
                  (pullbackComparison_inv_postcompose_owner F a y)
      _ =
          (ck.inv.1 ≫
            (canonicalPullbackChoice Y.p).map k
              ((F.toHom.fiberFunctor B).obj
                (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y))) ≫
            sourceTaila := by
              simp only [Category.assoc]
    exact hraw_mid.trans hsourceTailk'
  have hstrict :
      strict.1 ≫ tail = sourceTailk ≫ sourceTaila := by
    have hstrict_tail :
        F.toHom.toFunctor.map rightSource.1 ≫
            F.toHom.toFunctor.map ((canonicalPullbackChoice X.p).map b y) =
          sourceTailk ≫ sourceTaila := by
      have hrightSource_fac :
          rightSource.1 ≫ (canonicalPullbackChoice X.p).map b y =
            ((canonicalPullbackChoice X.p).map k
                (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y)) ≫
              (canonicalPullbackChoice X.p).map a y := by
        -- The inverse `mapComp'` component in the source factors through the iterated pullbacks.
        exact
          canonicalFiberPseudofunctor_mapComp'_inv_app_fac
            (p := X.p) (f := a) (g := k) (gf := b) (hgf := hk) y
      rw [← Functor.map_comp]
      rw [hrightSource_fac]
      change
        F.toHom.toFunctor.map
            (((canonicalPullbackChoice X.p).map k
                (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y)) ≫
              (canonicalPullbackChoice X.p).map a y) =
          sourceTailk ≫ sourceTaila
      rw [Functor.map_comp]
      rfl
    have hstrict_mid :
        strict.1 ≫ tail =
          F.toHom.toFunctor.map rightSource.1 ≫
            F.toHom.toFunctor.map ((canonicalPullbackChoice X.p).map b y) := by
      -- The strict inverse shell reduces to the same mapped source composite-leg factorization.
      calc
      strict.1 ≫ tail =
          ((F.toHom.fiberFunctor A).map rightSource).1 ≫
            e.inv.1 ≫
            tail := by
            rw [hstrict_expand]
            simp only [Category.assoc]
      _ =
          ((F.toHom.fiberFunctor A).map rightSource).1 ≫
            (e.inv.1 ≫ tail) := by
            rfl
      _ =
          F.toHom.toFunctor.map rightSource.1 ≫
            F.toHom.toFunctor.map ((canonicalPullbackChoice X.p).map b y) := by
              exact
                congrArg (fun t ↦ F.toHom.toFunctor.map rightSource.1 ≫ t)
                  (pullbackComparison_inv_postcompose_owner F b y)
    exact hstrict_mid.trans hstrict_tail
  -- Both inverse boundary shells reduce to the same mapped source composite.
  exact hraw.trans hstrict.symm

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

/-- Helper for Chap08 Lemma 8 2 3: the transported comparison shell for a morphism in a
canonical Hom-presheaf is the comparison shell of the transported source morphism. -/
private theorem fibredMorphismPresheafMap_pullHom_normalized
    (F : X ⟶ Y) {D B A : C} (x y : X.p.Fiber D)
    (a : B ⟶ D) (k : A ⟶ B) (b : A ⟶ D) (hk : k ≫ a = b)
    (δ :
      ((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x ⟶
        ((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor Y.p)
        ((pullbackComparison F a x).hom ≫
          (F.toHom.fiberFunctor B).map δ ≫
          (pullbackComparison F a y).inv)
        k b b hk hk =
      (pullbackComparison F b x).hom ≫
        (F.toHom.fiberFunctor A).map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor X.p) δ k b b hk hk) ≫
        (pullbackComparison F b y).inv := by
  let FYk := ((canonicalFiberPseudofunctor Y.p).map k.op.toLoc).toFunctor
  let FXk := ((canonicalFiberPseudofunctor X.p).map k.op.toLoc).toFunctor
  let d := δ
  let e₁ := pullbackComparison F a x
  let e₂ := pullbackComparison F a y
  let eb₁ := pullbackComparison F b x
  let eb₂ := pullbackComparison F b y
  let ck₁ := pullbackComparison F k
    (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj x)
  let ck₂ := pullbackComparison F k
    (((canonicalFiberPseudofunctor X.p).map a.op.toLoc).toFunctor.obj y)
  let leftTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        a.op.toLoc k.op.toLoc b.op.toLoc
        (comp_toLoc_eq a k b hk)).hom.toNatTrans.app
      ((F.toHom.fiberFunctor D).obj x))
  let rightTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        a.op.toLoc k.op.toLoc b.op.toLoc
        (comp_toLoc_eq a k b hk)).inv.toNatTrans.app
      ((F.toHom.fiberFunctor D).obj y))
  let leftSource :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        a.op.toLoc k.op.toLoc b.op.toLoc
        (comp_toLoc_eq a k b hk)).hom.toNatTrans.app x)
  let rightSource :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        a.op.toLoc k.op.toLoc b.op.toLoc
        (comp_toLoc_eq a k b hk)).inv.toNatTrans.app y)
  have hunfolded :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor Y.p)
          (e₁.hom ≫ (F.toHom.fiberFunctor B).map d ≫ e₂.inv)
          k b b hk hk =
        leftTarget ≫ FYk.map (e₁.hom ≫ (F.toHom.fiberFunctor B).map d ≫ e₂.inv) ≫
          rightTarget := by
    -- Expand only the pseudofunctorial `pullHom` shell before normalizing its three factors.
    rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    rfl
  have hmap :
      FYk.map (e₁.hom ≫ (F.toHom.fiberFunctor B).map d ≫ e₂.inv) =
        FYk.map e₁.hom ≫ FYk.map ((F.toHom.fiberFunctor B).map d) ≫
          FYk.map e₂.inv := by
    -- The middle transported composite is just functoriality of a threefold composite.
    simpa only [FYk, d, e₁, e₂] using
      functor_map_threefold_comp FYk e₁.hom ((F.toHom.fiberFunctor B).map d) e₂.inv
  have hleft :
      leftTarget ≫ FYk.map e₁.hom =
        eb₁.hom ≫ (F.toHom.fiberFunctor A).map leftSource ≫ ck₁.inv := by
    -- Normalize the left boundary over the composite leg `b`.
    simpa only [FYk, e₁, eb₁, ck₁, leftTarget, leftSource] using
      fibredMorphismPresheafMap_pullHom_left_boundary F x a k b hk
  have hmid :
      ck₁.inv ≫ FYk.map ((F.toHom.fiberFunctor B).map d) =
        (F.toHom.fiberFunctor A).map (FXk.map d) ≫ ck₂.inv := by
    -- Move the source morphism across the `k`-leg pullback-comparison square.
    simpa only [FYk, FXk, d, ck₁, ck₂] using
      (pullbackComparison_inv_naturality_over_vertical (F := F) (f := k) (φ := d)).symm
  have hright :
      ck₂.inv ≫ FYk.map e₂.inv ≫ rightTarget =
        (F.toHom.fiberFunctor A).map rightSource ≫ eb₂.inv := by
    -- Normalize the right boundary over the same composite leg `b`.
    simpa only [FYk, e₂, eb₂, ck₂, rightTarget, rightSource] using
      fibredMorphismPresheafMap_pullHom_right_boundary F y a k b hk
  have hfold :
      (F.toHom.fiberFunctor A).map leftSource ≫
          (F.toHom.fiberFunctor A).map (FXk.map d) ≫
          (F.toHom.fiberFunctor A).map rightSource =
        (F.toHom.fiberFunctor A).map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor X.p) d k b b hk hk) := by
    -- Fold the three normalized source-side pieces back into the source `pullHom` shell.
    change
      (F.toHom.fiberFunctor A).map leftSource ≫
          (F.toHom.fiberFunctor A).map (FXk.map d) ≫
          (F.toHom.fiberFunctor A).map rightSource =
        (F.toHom.fiberFunctor A).map
          (leftSource ≫ FXk.map d ≫ rightSource)
    rw [functor_map_threefold_comp]
  have hright' :
      eb₁.hom ≫ (F.toHom.fiberFunctor A).map leftSource ≫
          (F.toHom.fiberFunctor A).map (FXk.map d) ≫
        (ck₂.inv ≫ FYk.map e₂.inv ≫ rightTarget) =
      eb₁.hom ≫ (F.toHom.fiberFunctor A).map leftSource ≫
          (F.toHom.fiberFunctor A).map (FXk.map d) ≫
        ((F.toHom.fiberFunctor A).map rightSource ≫ eb₂.inv) := by
    -- Freeze the normalized prefix while replacing the right boundary shell.
    simpa only [Category.assoc] using
      congrArg
        (fun t ↦ eb₁.hom ≫ (F.toHom.fiberFunctor A).map leftSource ≫
          (F.toHom.fiberFunctor A).map (FXk.map d) ≫ t)
        hright
  have hmap' :
      leftTarget ≫ FYk.map (e₁.hom ≫ (F.toHom.fiberFunctor B).map d ≫ e₂.inv) ≫
          rightTarget =
        leftTarget ≫ FYk.map e₁.hom ≫ FYk.map ((F.toHom.fiberFunctor B).map d) ≫
          FYk.map e₂.inv ≫ rightTarget := by
    -- Expand the mapped middle composite while preserving the two boundary factors.
    calc
      leftTarget ≫ FYk.map (e₁.hom ≫ (F.toHom.fiberFunctor B).map d ≫ e₂.inv) ≫
          rightTarget =
        leftTarget ≫
          (FYk.map e₁.hom ≫ FYk.map ((F.toHom.fiberFunctor B).map d) ≫
            FYk.map e₂.inv) ≫
          rightTarget := by
            exact congrArg (fun t ↦ leftTarget ≫ t ≫ rightTarget) hmap
      _ =
        leftTarget ≫ FYk.map e₁.hom ≫ FYk.map ((F.toHom.fiberFunctor B).map d) ≫
          FYk.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
  have hleft' :
      leftTarget ≫ FYk.map e₁.hom ≫ FYk.map ((F.toHom.fiberFunctor B).map d) ≫
          FYk.map e₂.inv ≫ rightTarget =
        eb₁.hom ≫ (F.toHom.fiberFunctor A).map leftSource ≫ ck₁.inv ≫
          FYk.map ((F.toHom.fiberFunctor B).map d) ≫ FYk.map e₂.inv ≫ rightTarget := by
    -- Replace the left boundary by its strict comparison shell.
    calc
      leftTarget ≫ FYk.map e₁.hom ≫ FYk.map ((F.toHom.fiberFunctor B).map d) ≫
          FYk.map e₂.inv ≫ rightTarget =
        (leftTarget ≫ FYk.map e₁.hom) ≫ FYk.map ((F.toHom.fiberFunctor B).map d) ≫
          FYk.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
      _ =
        (eb₁.hom ≫ (F.toHom.fiberFunctor A).map leftSource ≫ ck₁.inv) ≫
          FYk.map ((F.toHom.fiberFunctor B).map d) ≫ FYk.map e₂.inv ≫
          rightTarget := by
            exact congrArg
              (fun t ↦ t ≫ FYk.map ((F.toHom.fiberFunctor B).map d) ≫
                FYk.map e₂.inv ≫ rightTarget)
              hleft
      _ =
        eb₁.hom ≫ (F.toHom.fiberFunctor A).map leftSource ≫ ck₁.inv ≫
          FYk.map ((F.toHom.fiberFunctor B).map d) ≫ FYk.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
  have hmid' :
      eb₁.hom ≫ (F.toHom.fiberFunctor A).map leftSource ≫ ck₁.inv ≫
          FYk.map ((F.toHom.fiberFunctor B).map d) ≫ FYk.map e₂.inv ≫ rightTarget =
        eb₁.hom ≫ (F.toHom.fiberFunctor A).map leftSource ≫
          (F.toHom.fiberFunctor A).map (FXk.map d) ≫
          ck₂.inv ≫ FYk.map e₂.inv ≫ rightTarget := by
    -- Replace the middle shell by inverse naturality of the pullback comparison.
    calc
      eb₁.hom ≫ (F.toHom.fiberFunctor A).map leftSource ≫ ck₁.inv ≫
          FYk.map ((F.toHom.fiberFunctor B).map d) ≫ FYk.map e₂.inv ≫ rightTarget =
        eb₁.hom ≫ (F.toHom.fiberFunctor A).map leftSource ≫
          (ck₁.inv ≫ FYk.map ((F.toHom.fiberFunctor B).map d)) ≫
          FYk.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
      _ =
        eb₁.hom ≫ (F.toHom.fiberFunctor A).map leftSource ≫
          ((F.toHom.fiberFunctor A).map (FXk.map d) ≫ ck₂.inv) ≫
          FYk.map e₂.inv ≫ rightTarget := by
            exact congrArg
              (fun t ↦ eb₁.hom ≫ (F.toHom.fiberFunctor A).map leftSource ≫ t ≫
                FYk.map e₂.inv ≫ rightTarget)
              hmid
      _ =
        eb₁.hom ≫ (F.toHom.fiberFunctor A).map leftSource ≫
          (F.toHom.fiberFunctor A).map (FXk.map d) ≫
          ck₂.inv ≫ FYk.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
  have hsource_flat :
      eb₁.hom ≫ (F.toHom.fiberFunctor A).map leftSource ≫
          (F.toHom.fiberFunctor A).map (FXk.map d) ≫
          (F.toHom.fiberFunctor A).map rightSource ≫ eb₂.inv =
        eb₁.hom ≫
          (F.toHom.fiberFunctor A).map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (F := canonicalFiberPseudofunctor X.p) d k b b hk hk) ≫
          eb₂.inv := by
    -- Fold the normalized source shell while keeping the outer comparison maps fixed.
    calc
      eb₁.hom ≫ (F.toHom.fiberFunctor A).map leftSource ≫
          (F.toHom.fiberFunctor A).map (FXk.map d) ≫
          (F.toHom.fiberFunctor A).map rightSource ≫ eb₂.inv =
        eb₁.hom ≫
          ((F.toHom.fiberFunctor A).map leftSource ≫
            (F.toHom.fiberFunctor A).map (FXk.map d) ≫
            (F.toHom.fiberFunctor A).map rightSource) ≫
          eb₂.inv := by
            simp only [Category.assoc]
      _ =
        eb₁.hom ≫
          (F.toHom.fiberFunctor A).map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (F := canonicalFiberPseudofunctor X.p) d k b b hk hk) ≫
          eb₂.inv := by
            exact congrArg (fun t ↦ eb₁.hom ≫ t ≫ eb₂.inv) hfold
  have hprefix :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor Y.p)
          (e₁.hom ≫ (F.toHom.fiberFunctor B).map d ≫ e₂.inv)
          k b b hk hk =
        eb₁.hom ≫ (F.toHom.fiberFunctor A).map leftSource ≫
          (F.toHom.fiberFunctor A).map (FXk.map d) ≫
          ck₂.inv ≫ FYk.map e₂.inv ≫ rightTarget := by
    -- Chain the unfolded shell with the left and middle normalization steps.
    exact hunfolded.trans (hmap'.trans (hleft'.trans hmid'))
  exact
    hprefix.trans
      (hright'.trans
        (hsource_flat.trans rfl))

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
  let g := α.unop.left
  have hg : g ≫ W₁.hom = W₂.hom := by
    -- The over-category morphism equation reduces to the underlying left-leg equality.
    simpa [g] using α.unop.w
  -- Unfold the presheaf restriction to a `pullHom` shell, then use the normalized comparison
  -- computation proved in the fibred-category morphism namespace.
  change
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor Y.p)
        (fibredMorphismPresheafMapApp F x y W₁ δ)
        g W₂.hom W₂.hom hg hg =
      fibredMorphismPresheafMapApp F x y W₂
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p) δ g W₂.hom W₂.hom hg hg)
  simpa only [g, fibredMorphismPresheafMapApp] using
    FibredCategoryMor.fibredMorphismPresheafMap_pullHom_normalized
      F x y W₁.hom g W₂.hom hg δ

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

/-- Chap08 Lemma 8 2 3: a `1`-morphism of fibred categories over `C` induces the canonical
morphism of presheaves `Mor_{S₁}(x, y) ⟶ Mor_{S₂}(F(x), F(y))` on the slice category `C/U`.
The source and target are stated using the canonical Hom-presheaves from Definition `8.2.2`. -/
noncomputable def FibredCategoryMor.fibredMorphismPresheafMap
    (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U) :
    (canonicalFiberPseudofunctor X.p).presheafHom x y ⟶
      (canonicalFiberPseudofunctor Y.p).presheafHom
        (((F.toHom).fiberFunctor U).obj x)
        (((F.toHom).fiberFunctor U).obj y) :=
  { app := fun W ↦ fibredMorphismPresheafMapApp F x y W.unop
    naturality := fibredMorphismPresheafMap_naturality F x y }

end CategoryTheory
