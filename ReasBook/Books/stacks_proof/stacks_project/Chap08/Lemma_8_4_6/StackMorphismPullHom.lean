import StacksProject_2024.Chap08.Lemma_8_4_6.CanonicalPullbackComparison

universe u v

namespace CategoryTheory

open CategoryTheory.Limits
open InducedCategory.Hom
open CategoricalPullback
open scoped CategoricalPullback

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y S : StackOver J}

/-- Helper for Lemma 8.4.6: once the cocycle composite is reassociated to the literal
`comparison.inv ≫ comparison.hom` shell, the middle comparison pair cancels before the remaining
tail. -/
theorem stack_morphism_pullbackComparison_inv_hom_postcompose_normalized
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U Y : C} (g : Y ⟶ U) (x : A.p.Fiber U)
    {z : B.p.Fiber Y}
    (k :
      (FibredCategoryMor.fiberFunctor H Y).obj
          (((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor.obj x) ⟶ z) :
    (FibredCategoryMor.pullbackComparison (H) g x).inv ≫
      (FibredCategoryMor.pullbackComparison (H) g x).hom ≫
      k = k := by
  -- Use iso cancellation in exactly the postcomposed shape that appears in the cocycle proof.
  let e := FibredCategoryMor.pullbackComparison (H) g x
  change e.inv ≫ e.hom ≫ k = k
  simpa only [Category.assoc] using Iso.inv_hom_id_assoc e k

/-- Helper for Lemma 8.4.6: after postcomposing the raw left `pullHom` boundary and the strict
composite-leg left boundary with the chosen target pullback arrows over `g` and then `f`, both
owner-level composites reduce to the same composite-leg chosen pullback arrow. -/
theorem stack_morphism_pullbackComparison_pullHom_left_boundary_postcompose_g_then_f_target
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U Y Y' : C}
    (f : Y ⟶ U) (g : Y' ⟶ Y) (gf : Y' ⟶ U) (hgf : g ≫ f = gf)
    (x : A.p.Fiber U) :
    let raw :=
      (((canonicalFiberPseudofunctor B.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H U).obj x)) ≫
        (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (H) f x).hom)
    let strict :=
      (FibredCategoryMor.pullbackComparison (H) gf x).hom ≫
        (FibredCategoryMor.fiberFunctor H Y').map
          (((canonicalFiberPseudofunctor A.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
        (FibredCategoryMor.pullbackComparison (H) g
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x)).inv
    let tailg :=
      (canonicalPullbackChoice B.p).map g
        ((FibredCategoryMor.fiberFunctor H Y).obj
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x))
    let tailf := (H).toHom.map ((canonicalPullbackChoice A.p).map f x)
    raw.1 ≫ tailg ≫ tailf = strict.1 ≫ tailg ≫ tailf := by
  let raw :=
    (((canonicalFiberPseudofunctor B.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor H U).obj x)) ≫
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) f x).hom)
  let strict :=
    (FibredCategoryMor.pullbackComparison (H) gf x).hom ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
      (FibredCategoryMor.pullbackComparison (H) g
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x)).inv
  let tailg :=
    (canonicalPullbackChoice B.p).map g
      ((FibredCategoryMor.fiberFunctor H Y).obj
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x))
  let tailf := (H).toHom.map ((canonicalPullbackChoice A.p).map f x)
  let e := FibredCategoryMor.pullbackComparison (H) gf x
  let cg :=
    FibredCategoryMor.pullbackComparison (H) g
      (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x)
  let ef := FibredCategoryMor.pullbackComparison (H) f x
  let leftRaw :=
    ((canonicalFiberPseudofunctor B.p).mapComp'
      f.op.toLoc g.op.toLoc gf.op.toLoc
      (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor H U).obj x)
  let leftSource :=
    ((canonicalFiberPseudofunctor A.p).mapComp'
      f.op.toLoc g.op.toLoc gf.op.toLoc
      (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      x
  have hraw_expand :
      raw.1 =
        leftRaw.1 ≫
          ((((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map ef.hom)).1 := by
    rfl
  have hstrict_expand :
      strict.1 =
        e.hom.1 ≫ ((FibredCategoryMor.fiberFunctor H Y').map leftSource).1 ≫ cg.inv.1 := by
    rfl
  have hraw :
      raw.1 ≫ tailg ≫ tailf =
        (canonicalPullbackChoice B.p).map gf ((FibredCategoryMor.fiberFunctor H U).obj x) := by
    have hraw_flank :
        (leftRaw.1 ≫
            (canonicalPullbackChoice B.p).map g
              (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.obj
                ((FibredCategoryMor.fiberFunctor H U).obj x))) ≫
            (canonicalPullbackChoice B.p).map f
              ((FibredCategoryMor.fiberFunctor H U).obj x) =
          (canonicalPullbackChoice B.p).map gf
            ((FibredCategoryMor.fiberFunctor H U).obj x) := by
      simpa [leftRaw, Category.assoc] using
        canonicalFiberPseudofunctor_mapComp'_hom_app_fac
          (p := B.p) (f := f) (g := g) (gf := gf) (hgf := hgf) ((FibredCategoryMor.fiberFunctor H U).obj x)
    -- Normalize the raw shell to the chosen pullback arrow over the composite leg `gf`.
    calc
      raw.1 ≫ tailg ≫ tailf =
          leftRaw.1 ≫
            ((((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map ef.hom)).1 ≫
            tailg ≫
            tailf := by
              rw [hraw_expand]
              simp only [Category.assoc]
      _ =
          leftRaw.1 ≫
            (((((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map ef.hom)).1 ≫
              tailg) ≫
            tailf := by
              simp only [Category.assoc]
      _ =
          leftRaw.1 ≫
            (((canonicalPullbackChoice B.p).map g
                (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.obj
                  ((FibredCategoryMor.fiberFunctor H U).obj x))) ≫
              ef.hom.1) ≫
            tailf := by
              exact
                congrArg (fun t ↦ leftRaw.1 ≫ t ≫ tailf)
                  (canonical_pullbackFunctor_map_fac (p := B.p) (f := g) (φ := ef.hom))
      _ =
          leftRaw.1 ≫
            (canonicalPullbackChoice B.p).map g
              (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.obj
                ((FibredCategoryMor.fiberFunctor H U).obj x)) ≫
            ef.hom.1 ≫
            tailf := by
              simp only [Category.assoc]
      _ =
          (canonicalPullbackChoice B.p).map gf
            ((FibredCategoryMor.fiberFunctor H U).obj x) := by
              have hpostf :
                  leftRaw.1 ≫
                      (canonicalPullbackChoice B.p).map g
                        (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.obj
                          ((FibredCategoryMor.fiberFunctor H U).obj x)) ≫
                      ef.hom.1 ≫
                      tailf =
                    (leftRaw.1 ≫
                      (canonicalPullbackChoice B.p).map g
                        (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.obj
                          ((FibredCategoryMor.fiberFunctor H U).obj x))) ≫
                      (canonicalPullbackChoice B.p).map f
                        ((FibredCategoryMor.fiberFunctor H U).obj x) := by
                simpa only [Category.assoc] using
                  congrArg
                    (fun t ↦
                      leftRaw.1 ≫
                        (canonicalPullbackChoice B.p).map g
                          (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.obj
                            ((FibredCategoryMor.fiberFunctor H U).obj x)) ≫
                        t)
                    (FibredCategoryMor.pullbackComparison_hom_postcompose
                      (H) f x)
              exact hpostf.trans hraw_flank
  have hstrict :
      strict.1 ≫ tailg ≫ tailf =
        (canonicalPullbackChoice B.p).map gf
          ((FibredCategoryMor.fiberFunctor H U).obj x) := by
    have hpostg :
        cg.inv.1 ≫ tailg =
          (H).toHom.map ((canonicalPullbackChoice A.p).map g
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x)) := by
      -- Read the inverse comparison against the chosen target pullback arrow on the common `g` leg.
      change
        (FibredCategoryMor.pullbackComparison (H) g
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x)).inv.1 ≫
          (canonicalPullbackChoice B.p).map g
            ((FibredCategoryMor.fiberFunctor H Y).obj
              (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x)) =
        (H).toHom.map ((canonicalPullbackChoice A.p).map g
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x))
      exact FibredCategoryMor.pullbackComparison_inv_postcompose_owner
        (F := H) (f := g)
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x)
    have hpostg' :
        (cg.inv.1 ≫ tailg) ≫ tailf =
          (H).toHom.map ((canonicalPullbackChoice A.p).map g
              (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x)) ≫
            tailf := by
      exact congrArg (fun t ↦ t ≫ tailf) hpostg
    -- Normalize the strict shell by canceling the inverse comparison on the common `g` leg.
    calc
      strict.1 ≫ tailg ≫ tailf =
          e.hom.1 ≫ ((FibredCategoryMor.fiberFunctor H Y').map leftSource).1 ≫
            cg.inv.1 ≫
            tailg ≫
            tailf := by
              rw [hstrict_expand]
              simp only [Category.assoc]
      _ =
          e.hom.1 ≫ ((FibredCategoryMor.fiberFunctor H Y').map leftSource).1 ≫
            (cg.inv.1 ≫ tailg) ≫
            tailf := by
              simp only [Category.assoc]
      _ =
          e.hom.1 ≫ ((FibredCategoryMor.fiberFunctor H Y').map leftSource).1 ≫
            (cg.inv.1 ≫ tailg ≫ tailf) := by
              simp only [Category.assoc]
      _ =
          e.hom.1 ≫ ((FibredCategoryMor.fiberFunctor H Y').map leftSource).1 ≫
            ((H).toHom.map ((canonicalPullbackChoice A.p).map g
              (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x)) ≫
              tailf) := by
              simpa only [Category.assoc] using
                congrArg
                  (fun t ↦ e.hom.1 ≫ ((FibredCategoryMor.fiberFunctor H Y').map leftSource).1 ≫ t)
                  hpostg'
      _ =
          e.hom.1 ≫
            (H).toHom.map
              (leftSource.1 ≫
                (canonicalPullbackChoice A.p).map g
                  (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x) ≫
                (canonicalPullbackChoice A.p).map f x) := by
              simpa only [tailf, Category.assoc] using
                congrArg
                  (fun t ↦ e.hom.1 ≫ t)
                  (functor_map_threefold_comp
                    (H).toHom.toFunctor leftSource.1
                    ((canonicalPullbackChoice A.p).map g
                      (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x))
                    ((canonicalPullbackChoice A.p).map f x)).symm
      _ =
          e.hom.1 ≫ (H).toHom.map ((canonicalPullbackChoice A.p).map gf x) := by
              exact
                congrArg (fun t ↦ e.hom.1 ≫ (H).toHom.map t)
                  (canonicalFiberPseudofunctor_mapComp'_hom_app_fac
                    (p := A.p) (f := f) (g := g) (gf := gf) (hgf := hgf) x)
      _ =
          (canonicalPullbackChoice B.p).map gf
            ((FibredCategoryMor.fiberFunctor H U).obj x) := by
              exact FibredCategoryMor.pullbackComparison_hom_postcompose
                (H) gf x
  -- Both shells reduce to the same composite-leg chosen pullback arrow.
  exact hraw.trans hstrict.symm

/-- Helper for Lemma 8.4.6: after postcomposing the raw left `pullHom` boundary and the strict
composite-leg left boundary with the chosen target pullback arrow over `g`, the two owner-level
composites already agree. -/
theorem stack_morphism_pullbackComparison_pullHom_left_boundary_postcompose_g_target
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U Y Y' : C}
    (f : Y ⟶ U) (g : Y' ⟶ Y) (gf : Y' ⟶ U) (hgf : g ≫ f = gf)
    (x : A.p.Fiber U) :
    let raw :=
      (((canonicalFiberPseudofunctor B.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H U).obj x)) ≫
        (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (H) f x).hom)
    let strict :=
      (FibredCategoryMor.pullbackComparison (H) gf x).hom ≫
        (FibredCategoryMor.fiberFunctor H Y').map
          (((canonicalFiberPseudofunctor A.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
        (FibredCategoryMor.pullbackComparison (H) g
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x)).inv
    let tail :=
      (canonicalPullbackChoice B.p).map g
        ((FibredCategoryMor.fiberFunctor H Y).obj
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x))
    raw.1 ≫ tail = strict.1 ≫ tail := by
  let raw :=
    (((canonicalFiberPseudofunctor B.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor H U).obj x)) ≫
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) f x).hom)
  let strict :=
    (FibredCategoryMor.pullbackComparison (H) gf x).hom ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
      (FibredCategoryMor.pullbackComparison (H) g
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x)).inv
  let tail :=
    (canonicalPullbackChoice B.p).map g
      ((FibredCategoryMor.fiberFunctor H Y).obj
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x))
  let tailf := (H).toHom.map ((canonicalPullbackChoice A.p).map f x)
  have htailf : B.p.IsStronglyCartesian f tailf := by
    -- Transport the chosen source pullback lift over `f` across the stack morphism.
    change B.p.IsStronglyCartesian f
      ((H).toHom.map ((canonicalPullbackChoice A.p).map f x))
    exact
      FibredCategoryMor.map_stronglyCartesian_of_lift
        (H) f
        ((canonicalPullbackChoice A.p).map f x)
        ((canonicalPullbackChoice A.p).isStronglyCartesian f x)
  have htail : B.p.IsHomLift g tail := by
    change
      B.p.IsHomLift g
        ((canonicalPullbackChoice B.p).map g
          ((FibredCategoryMor.fiberFunctor H Y).obj
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x)))
    exact
      ((canonicalPullbackChoice B.p).isStronglyCartesian g
        ((FibredCategoryMor.fiberFunctor H Y).obj
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x))).toIsHomLift
  letI : B.p.IsStronglyCartesian f tailf := htailf
  letI : B.p.IsHomLift (𝟙 Y') raw.1 := raw.2
  letI : B.p.IsHomLift (𝟙 Y') strict.1 := strict.2
  letI : B.p.IsHomLift g tail := htail
  have hrawtail : B.p.IsHomLift g (raw.1 ≫ tail) := by
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ B.p _ _ _
      Y' raw.1 raw.2 _ _ g tail htail
  have hstricttail : B.p.IsHomLift g (strict.1 ≫ tail) := by
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ B.p _ _ _
      Y' strict.1 strict.2 _ _ g tail htail
  have hpost : (raw.1 ≫ tail) ≫ tailf = (strict.1 ≫ tail) ≫ tailf := by
    -- Compare after composing with the common strongly cartesian leg over `f`.
    simpa only [Category.assoc] using
      stack_morphism_pullbackComparison_pullHom_left_boundary_postcompose_g_then_f_target
        H f g gf hgf x
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ B.p _ _ _ _
      f tailf htailf _ _ g (raw.1 ≫ tail) (strict.1 ≫ tail) hrawtail hstricttail hpost

/-- Helper for Lemma 8.4.6: the raw left `pullHom` boundary is exactly the strict composite-leg
comparison shell after passing back to the fiber over the domain of `gf`. -/
theorem stack_morphism_pullbackComparison_pullHom_left_boundary
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U Y Y' : C}
    (f : Y ⟶ U) (g : Y' ⟶ Y) (gf : Y' ⟶ U) (hgf : g ≫ f = gf)
    (x : A.p.Fiber U) :
    (((canonicalFiberPseudofunctor B.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H U).obj x)) ≫
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) f x).hom) =
      (FibredCategoryMor.pullbackComparison (H) gf x).hom ≫
        (FibredCategoryMor.fiberFunctor H Y').map
          (((canonicalFiberPseudofunctor A.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
        (FibredCategoryMor.pullbackComparison (H) g
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x)).inv := by
  let raw :=
    (((canonicalFiberPseudofunctor B.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor H U).obj x)) ≫
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) f x).hom)
  let strict :=
    (FibredCategoryMor.pullbackComparison (H) gf x).hom ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
      (FibredCategoryMor.pullbackComparison (H) g
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x)).inv
  let tail :=
    (canonicalPullbackChoice B.p).map g
      ((FibredCategoryMor.fiberFunctor H Y).obj
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x))
  have htail : B.p.IsStronglyCartesian g tail := by
    -- Reuse the chosen target pullback arrow over the common leg `g`.
    change
      B.p.IsStronglyCartesian g
        ((canonicalPullbackChoice B.p).map g
          ((FibredCategoryMor.fiberFunctor H Y).obj
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x)))
    exact
      (canonicalPullbackChoice B.p).isStronglyCartesian g
        ((FibredCategoryMor.fiberFunctor H Y).obj
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x))
  have hpost : raw.1 ≫ tail = strict.1 ≫ tail := by
    -- Reduce the fiber equality to the owner-level comparison after composing with the `g`-leg.
    change raw.1 ≫ tail = strict.1 ≫ tail
    exact stack_morphism_pullbackComparison_pullHom_left_boundary_postcompose_g_target
      H f g gf hgf x
  -- Compare the two fiber morphisms via the common strongly cartesian arrow over `g`.
  apply Functor.Fiber.hom_ext
  change raw.1 = strict.1
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ B.p _ _ _ _
      g tail htail _ _ (𝟙 Y') raw.1 strict.1 raw.2 strict.2 hpost

/-- Helper for Lemma 8.4.6: after postcomposing the raw right `pullHom` boundary and the strict
composite-leg right boundary with the chosen `gf`-pullback arrow, both owner-level composites
reduce to the same mapped source composite-leg factorization. -/
theorem stack_morphism_pullbackComparison_pullHom_right_boundary_postcompose_target
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U Y Y' : C}
    (f : Y ⟶ U) (g : Y' ⟶ Y) (gf : Y' ⟶ U) (hgf : g ≫ f = gf)
    (y : A.p.Fiber U) :
    let raw :=
      (FibredCategoryMor.pullbackComparison (H) g
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)).inv ≫
        (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (H) f y).inv) ≫
        (((canonicalFiberPseudofunctor B.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H U).obj y))
    let strict :=
      (FibredCategoryMor.fiberFunctor H Y').map
          (((canonicalFiberPseudofunctor A.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y) ≫
        (FibredCategoryMor.pullbackComparison (H) gf y).inv
    let tail :=
      (canonicalPullbackChoice B.p).map gf
        ((FibredCategoryMor.fiberFunctor H U).obj y)
    raw.1 ≫ tail = strict.1 ≫ tail := by
  let raw :=
    (FibredCategoryMor.pullbackComparison (H) g
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)).inv ≫
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) f y).inv) ≫
      (((canonicalFiberPseudofunctor B.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H U).obj y))
  let strict :=
    (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y) ≫
      (FibredCategoryMor.pullbackComparison (H) gf y).inv
  let tail :=
    (canonicalPullbackChoice B.p).map gf
      ((FibredCategoryMor.fiberFunctor H U).obj y)
  let e := FibredCategoryMor.pullbackComparison (H) gf y
  let cg :=
    FibredCategoryMor.pullbackComparison (H) g
      (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)
  let ef := FibredCategoryMor.pullbackComparison (H) f y
  let tailg :=
    (canonicalPullbackChoice B.p).map g
      (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.obj
        ((FibredCategoryMor.fiberFunctor H U).obj y))
  let tailf := (canonicalPullbackChoice B.p).map f ((FibredCategoryMor.fiberFunctor H U).obj y)
  let sourceTailg :=
    (H).toHom.map ((canonicalPullbackChoice A.p).map g
      (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y))
  let sourceTailf := (H).toHom.map ((canonicalPullbackChoice A.p).map f y)
  let rightSource :=
    ((canonicalFiberPseudofunctor A.p).mapComp'
      f.op.toLoc g.op.toLoc gf.op.toLoc (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
      y
  have hraw_expand :
      raw.1 =
        cg.inv.1 ≫
          ((((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
          (((canonicalFiberPseudofunctor B.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor H U).obj y)).1 := by
    rfl
  have hstrict_expand :
      strict.1 = ((FibredCategoryMor.fiberFunctor H Y').map rightSource).1 ≫ e.inv.1 := by
    rfl
  have hraw :
      raw.1 ≫ tail = sourceTailg ≫ sourceTailf := by
    have hmap_tailg :
        ((((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
            tailg =
          (canonicalPullbackChoice B.p).map g
              ((FibredCategoryMor.fiberFunctor H Y).obj
                (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)) ≫
            ef.inv.1 := by
      -- Specialize pullback-functor naturality to the inverse comparison over the leg `g`.
      change
        (((((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
              (FibredCategoryMor.pullbackComparison (H) f y).inv)).1) ≫
            (canonicalPullbackChoice B.p).map g
              (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.obj
                ((FibredCategoryMor.fiberFunctor H U).obj y)) =
          (canonicalPullbackChoice B.p).map g
              ((FibredCategoryMor.fiberFunctor H Y).obj
                (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)) ≫
            (FibredCategoryMor.pullbackComparison (H) f y).inv.1
      exact canonical_pullbackFunctor_map_fac (p := B.p) (f := g) (φ := ef.inv)
    have hsourceTailg :
        cg.inv.1 ≫
            (canonicalPullbackChoice B.p).map g
              ((FibredCategoryMor.fiberFunctor H Y).obj
                (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)) =
          sourceTailg := by
      -- Read the inverse comparison against the chosen target pullback arrow on the common `g` leg.
      change
        (FibredCategoryMor.pullbackComparison (H) g
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)).inv.1 ≫
          (canonicalPullbackChoice B.p).map g
            ((FibredCategoryMor.fiberFunctor H Y).obj
              (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)) =
        sourceTailg
      exact FibredCategoryMor.pullbackComparison_inv_postcompose_owner
        (F := H) (f := g)
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)
    have hmap_tailg' :
        (((((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫ tailg) ≫
            tailf =
          ((canonicalPullbackChoice B.p).map g
              ((FibredCategoryMor.fiberFunctor H Y).obj
                (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)) ≫
            ef.inv.1) ≫
            tailf := by
      exact congrArg (fun t ↦ t ≫ tailf) hmap_tailg
    have hsourceTailg' :
        (cg.inv.1 ≫
            (canonicalPullbackChoice B.p).map g
              ((FibredCategoryMor.fiberFunctor H Y).obj
                (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y))) ≫
            sourceTailf =
          sourceTailg ≫ sourceTailf := by
      exact congrArg (fun t ↦ t ≫ sourceTailf) hsourceTailg
    have hraw_mid :
        raw.1 ≫ tail =
          (cg.inv.1 ≫
            (canonicalPullbackChoice B.p).map g
              ((FibredCategoryMor.fiberFunctor H Y).obj
                (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y))) ≫
            sourceTailf := by
      -- Normalize the raw inverse shell to the source composite-leg factorization transported by `H`.
      calc
      raw.1 ≫ tail =
          cg.inv.1 ≫
            ((((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
            (((canonicalFiberPseudofunctor B.p).mapComp'
                f.op.toLoc g.op.toLoc gf.op.toLoc
                (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor H U).obj y)).1 ≫
            tail := by
              rw [hraw_expand]
              simp only [Category.assoc]
      _ =
          cg.inv.1 ≫
            ((((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
            ((((canonicalFiberPseudofunctor B.p).mapComp'
                f.op.toLoc g.op.toLoc gf.op.toLoc
                (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor H U).obj y)).1 ≫
              tail) := by
              rfl
      _ =
          cg.inv.1 ≫
            ((((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
            (tailg ≫ tailf) := by
              exact
                congrArg
                  (fun t ↦
                    cg.inv.1 ≫
                      ((((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
                      t)
                  (canonicalFiberPseudofunctor_mapComp'_inv_app_fac
                    (p := B.p) (f := f) (g := g) (gf := gf) (hgf := hgf)
                    ((FibredCategoryMor.fiberFunctor H U).obj y))
      _ =
          cg.inv.1 ≫
            (((((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
              tailg) ≫
            tailf := by
              simp only [Category.assoc]
      _ =
          cg.inv.1 ≫
            (((canonicalPullbackChoice B.p).map g
                ((FibredCategoryMor.fiberFunctor H Y).obj
                  (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y))) ≫
              ef.inv.1) ≫ tailf := by
              simpa only [Category.assoc] using congrArg (fun t ↦ cg.inv.1 ≫ t) hmap_tailg'
      _ =
          cg.inv.1 ≫
            (canonicalPullbackChoice B.p).map g
              ((FibredCategoryMor.fiberFunctor H Y).obj
                (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)) ≫
            ef.inv.1 ≫
            tailf := by
              simp only [Category.assoc]
      _ =
          cg.inv.1 ≫
            (canonicalPullbackChoice B.p).map g
              ((FibredCategoryMor.fiberFunctor H Y).obj
                (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)) ≫
            sourceTailf := by
              simpa only [sourceTailf, Category.assoc] using
                congrArg
                  (fun t ↦
                    cg.inv.1 ≫
                      (canonicalPullbackChoice B.p).map g
                        ((FibredCategoryMor.fiberFunctor H Y).obj
                          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)) ≫
                      t)
                  (FibredCategoryMor.pullbackComparison_inv_postcompose_owner
                    (H) f y)
      _ =
          (cg.inv.1 ≫
            (canonicalPullbackChoice B.p).map g
              ((FibredCategoryMor.fiberFunctor H Y).obj
                (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y))) ≫
            sourceTailf := by
              simp only [Category.assoc]
    exact hraw_mid.trans hsourceTailg'
  have hstrict :
      strict.1 ≫ tail = sourceTailg ≫ sourceTailf := by
    have hstrict_tail :
        (H).toHom.toFunctor.map rightSource.1 ≫
            (H).toHom.toFunctor.map ((canonicalPullbackChoice A.p).map gf y) =
          sourceTailg ≫ sourceTailf := by
      rw [← Functor.map_comp]
      rw [show rightSource.1 ≫ (canonicalPullbackChoice A.p).map gf y =
          ((canonicalPullbackChoice A.p).map g
              (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)) ≫
            (canonicalPullbackChoice A.p).map f y by
            exact
              canonicalFiberPseudofunctor_mapComp'_inv_app_fac
                (p := A.p) (f := f) (g := g) (gf := gf) (hgf := hgf) y]
      change
        (H).toHom.toFunctor.map
            (((canonicalPullbackChoice A.p).map g
                (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)) ≫
              (canonicalPullbackChoice A.p).map f y) =
          sourceTailg ≫ sourceTailf
      rw [Functor.map_comp]
      rfl
    have hstrict_mid :
        strict.1 ≫ tail =
          (H).toHom.toFunctor.map rightSource.1 ≫
            (H).toHom.toFunctor.map ((canonicalPullbackChoice A.p).map gf y) := by
      -- The strict inverse shell reduces to the same mapped source composite-leg factorization.
      calc
      strict.1 ≫ tail =
          ((FibredCategoryMor.fiberFunctor H Y').map rightSource).1 ≫
            e.inv.1 ≫
            tail := by
            rw [hstrict_expand]
            simp only [Category.assoc]
      _ =
          ((FibredCategoryMor.fiberFunctor H Y').map rightSource).1 ≫
            (e.inv.1 ≫ tail) := by
            rfl
      _ =
          (H).toHom.toFunctor.map rightSource.1 ≫
            (H).toHom.toFunctor.map ((canonicalPullbackChoice A.p).map gf y) := by
              exact
                congrArg (fun t ↦ (H).toHom.toFunctor.map rightSource.1 ≫ t)
                  (FibredCategoryMor.pullbackComparison_inv_postcompose_owner
                    (H) gf y)
    exact hstrict_mid.trans hstrict_tail
  exact hraw.trans hstrict.symm

/-- Helper for Lemma 8.4.6: the raw right `pullHom` boundary is exactly the strict
composite-leg right shell after passing back to the fiber over the domain of `gf`. -/
theorem stack_morphism_pullbackComparison_pullHom_right_boundary
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U Y Y' : C}
    (f : Y ⟶ U) (g : Y' ⟶ Y) (gf : Y' ⟶ U) (hgf : g ≫ f = gf)
    (y : A.p.Fiber U) :
    (FibredCategoryMor.pullbackComparison (H) g
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)).inv ≫
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) f y).inv) ≫
      (((canonicalFiberPseudofunctor B.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H U).obj y)) =
    (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y) ≫
      (FibredCategoryMor.pullbackComparison (H) gf y).inv := by
  let raw :=
    (FibredCategoryMor.pullbackComparison (H) g
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)).inv ≫
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) f y).inv) ≫
      (((canonicalFiberPseudofunctor B.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H U).obj y))
  let strict :=
    (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y) ≫
      (FibredCategoryMor.pullbackComparison (H) gf y).inv
  let tail :=
    (canonicalPullbackChoice B.p).map gf
      ((FibredCategoryMor.fiberFunctor H U).obj y)
  have htail : B.p.IsStronglyCartesian gf tail := by
    -- Reuse the chosen target pullback arrow over the composite leg `gf`.
    change
      B.p.IsStronglyCartesian gf
        ((canonicalPullbackChoice B.p).map gf
          ((FibredCategoryMor.fiberFunctor H U).obj y))
    exact
      (canonicalPullbackChoice B.p).isStronglyCartesian gf
        ((FibredCategoryMor.fiberFunctor H U).obj y)
  have hpost : raw.1 ≫ tail = strict.1 ≫ tail := by
    -- Reduce the fiber equality to the owner-level postcomposed inverse-shell comparison.
    change raw.1 ≫ tail = strict.1 ≫ tail
    exact stack_morphism_pullbackComparison_pullHom_right_boundary_postcompose_target
      H f g gf hgf y
  -- Compare the two fiber morphisms via the common strongly cartesian arrow over `gf`.
  apply Functor.Fiber.hom_ext
  change raw.1 = strict.1
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ B.p _ _ _ _
      gf tail htail _ _ (𝟙 Y') raw.1 strict.1 raw.2 strict.2 hpost

end CategoryTheory
