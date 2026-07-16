import stacks_proof.stacks_project.Chap08.Lemma_8_4_3.PullbackComparisonNaturality
import stacks_proof.stacks_project.Chap08.Lemma_8_4_3.AmbientIsoClosure

open CategoryTheory
open CategoryTheory Functor
open Functor.IsPreFibered
open Functor.Fiber

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} {X : Type u₂} [Category.{v₁} C] [Category.{v₂} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C)
variable (P : ObjectProperty X)

variable [IsStackOnSite J p]

section RestrictedFibered

variable [(P.ι ⋙ p).IsFibered]

/-- Helper for Chap08 Lemma 8 4 3/RestrictedDescentForward: after postcomposing the raw
left boundary and the strict left boundary with the target pullback arrows over `g` and `f`,
both owner-level composites reduce to the chosen pullback arrow over `gf`. -/
private theorem fibredMorphismPullHomLeftBoundaryPostcomposeComposite
    {X₁ X₂ : FibredCategoryOver C} (F : X₁ ⟶ X₂) {U Y Y' : C}
    (f : Y ⟶ U) (g : Y' ⟶ Y) (gf : Y' ⟶ U) (hgf : g ≫ f = gf)
    (x : X₁.p.Fiber U) :
    let raw :=
      (((canonicalFiberPseudofunctor X₂.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((F.toHom.fiberFunctor U).obj x)) ≫
        (((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison F f x).hom)
    let strict :=
      (FibredCategoryMor.pullbackComparison F gf x).hom ≫
        (F.toHom.fiberFunctor Y').map
          (((canonicalFiberPseudofunctor X₁.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
        (FibredCategoryMor.pullbackComparison F g
          (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x)).inv
    let tailg :=
      (canonicalPullbackChoice X₂.p).map g
        ((F.toHom.fiberFunctor Y).obj
          (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x))
    let tailf := F.toHom.map ((canonicalPullbackChoice X₁.p).map f x)
    raw.1 ≫ tailg ≫ tailf = strict.1 ≫ tailg ≫ tailf := by
  let raw :=
    (((canonicalFiberPseudofunctor X₂.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((F.toHom.fiberFunctor U).obj x)) ≫
      (((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison F f x).hom)
  let strict :=
    (FibredCategoryMor.pullbackComparison F gf x).hom ≫
      (F.toHom.fiberFunctor Y').map
        (((canonicalFiberPseudofunctor X₁.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
      (FibredCategoryMor.pullbackComparison F g
        (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x)).inv
  let tailg :=
    (canonicalPullbackChoice X₂.p).map g
      ((F.toHom.fiberFunctor Y).obj
        (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x))
  let tailf := F.toHom.map ((canonicalPullbackChoice X₁.p).map f x)
  let e := FibredCategoryMor.pullbackComparison F gf x
  let cg :=
    FibredCategoryMor.pullbackComparison F g
      (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x)
  let ef := FibredCategoryMor.pullbackComparison F f x
  let leftRaw :=
    ((canonicalFiberPseudofunctor X₂.p).mapComp'
      f.op.toLoc g.op.toLoc gf.op.toLoc
      (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((F.toHom.fiberFunctor U).obj x)
  let leftSource :=
    ((canonicalFiberPseudofunctor X₁.p).mapComp'
      f.op.toLoc g.op.toLoc gf.op.toLoc
      (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x
  have hraw_expand :
      raw.1 =
        leftRaw.1 ≫
          ((((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map ef.hom)).1 := by
    rfl
  have hstrict_expand :
      strict.1 =
        e.hom.1 ≫ ((F.toHom.fiberFunctor Y').map leftSource).1 ≫ cg.inv.1 := by
    rfl
  have hraw :
      raw.1 ≫ tailg ≫ tailf =
        (canonicalPullbackChoice X₂.p).map gf ((F.toHom.fiberFunctor U).obj x) := by
    have hraw_flank :
        (leftRaw.1 ≫
            (canonicalPullbackChoice X₂.p).map g
              (((canonicalFiberPseudofunctor X₂.p).map f.op.toLoc).toFunctor.obj
                ((F.toHom.fiberFunctor U).obj x))) ≫
            (canonicalPullbackChoice X₂.p).map f
              ((F.toHom.fiberFunctor U).obj x) =
          (canonicalPullbackChoice X₂.p).map gf
            ((F.toHom.fiberFunctor U).obj x) := by
      -- The target `mapComp'.hom` component factors through the chosen composite-leg pullback.
      change
        ((((canonicalFiberPseudofunctor X₂.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
          ((F.toHom.fiberFunctor U).obj x)).1 ≫
          (canonicalPullbackChoice X₂.p).map g
            (((canonicalFiberPseudofunctor X₂.p).map f.op.toLoc).toFunctor.obj
              ((F.toHom.fiberFunctor U).obj x))) ≫
          (canonicalPullbackChoice X₂.p).map f
            ((F.toHom.fiberFunctor U).obj x) =
        (canonicalPullbackChoice X₂.p).map gf
          ((F.toHom.fiberFunctor U).obj x)
      simpa only [Category.assoc] using
        FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
          (p := X₂.p) (f := f) (g := g) (gf := gf) (hgf := hgf)
          ((F.toHom.fiberFunctor U).obj x)
    -- Normalize the raw shell to the chosen pullback arrow over the composite leg `gf`.
    calc
      raw.1 ≫ tailg ≫ tailf =
          leftRaw.1 ≫
            ((((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map ef.hom)).1 ≫
            tailg ≫
            tailf := by
              rw [hraw_expand]
              simp only [Category.assoc]
      _ =
          leftRaw.1 ≫
            (((((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map ef.hom)).1 ≫
              tailg) ≫
            tailf := by
              simp only [Category.assoc]
      _ =
          leftRaw.1 ≫
            (((canonicalPullbackChoice X₂.p).map g
                (((canonicalFiberPseudofunctor X₂.p).map f.op.toLoc).toFunctor.obj
                  ((F.toHom.fiberFunctor U).obj x))) ≫
              ef.hom.1) ≫
            tailf := by
              exact
                congrArg (fun t ↦ leftRaw.1 ≫ t ≫ tailf)
                  (FibredCategoryMor.canonical_pullbackFunctor_map_fac
                    (p := X₂.p) (f := g) (φ := ef.hom))
      _ =
          leftRaw.1 ≫
            (canonicalPullbackChoice X₂.p).map g
              (((canonicalFiberPseudofunctor X₂.p).map f.op.toLoc).toFunctor.obj
                ((F.toHom.fiberFunctor U).obj x)) ≫
            ef.hom.1 ≫
            tailf := by
              simp only [Category.assoc]
      _ =
          (canonicalPullbackChoice X₂.p).map gf
            ((F.toHom.fiberFunctor U).obj x) := by
              have hpostf :
                  leftRaw.1 ≫
                      (canonicalPullbackChoice X₂.p).map g
                        (((canonicalFiberPseudofunctor X₂.p).map f.op.toLoc).toFunctor.obj
                          ((F.toHom.fiberFunctor U).obj x)) ≫
                      ef.hom.1 ≫
                      tailf =
                    (leftRaw.1 ≫
                      (canonicalPullbackChoice X₂.p).map g
                        (((canonicalFiberPseudofunctor X₂.p).map f.op.toLoc).toFunctor.obj
                          ((F.toHom.fiberFunctor U).obj x))) ≫
                      (canonicalPullbackChoice X₂.p).map f
                        ((F.toHom.fiberFunctor U).obj x) := by
                simpa only [Category.assoc] using
                  congrArg
                    (fun t ↦
                      leftRaw.1 ≫
                        (canonicalPullbackChoice X₂.p).map g
                          (((canonicalFiberPseudofunctor X₂.p).map f.op.toLoc).toFunctor.obj
                            ((F.toHom.fiberFunctor U).obj x)) ≫
                        t)
                    (FibredCategoryMor.pullbackComparison_hom_postcompose
                      F f x)
              exact hpostf.trans hraw_flank
  have hstrict :
      strict.1 ≫ tailg ≫ tailf =
        (canonicalPullbackChoice X₂.p).map gf
          ((F.toHom.fiberFunctor U).obj x) := by
    have hpostg :
        cg.inv.1 ≫ tailg =
          F.toHom.map ((canonicalPullbackChoice X₁.p).map g
            (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x)) := by
      -- Cancel the inverse comparison on the common `g` leg against the chosen target pullback.
      change
        (FibredCategoryMor.pullbackComparison F g
            (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x)).inv.1 ≫
          (canonicalPullbackChoice X₂.p).map g
            ((F.toHom.fiberFunctor Y).obj
              (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x)) =
        F.toHom.map ((canonicalPullbackChoice X₁.p).map g
          (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x))
      exact FibredCategoryMor.pullbackComparison_inv_postcompose_owner
        (F := F) (f := g)
        (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x)
    have hpostg' :
        (cg.inv.1 ≫ tailg) ≫ tailf =
          F.toHom.map ((canonicalPullbackChoice X₁.p).map g
              (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x)) ≫
            tailf := by
      exact congrArg (fun t ↦ t ≫ tailf) hpostg
    -- Normalize the strict shell to the same chosen composite-leg pullback arrow.
    calc
      strict.1 ≫ tailg ≫ tailf =
          e.hom.1 ≫ ((F.toHom.fiberFunctor Y').map leftSource).1 ≫
            cg.inv.1 ≫
            tailg ≫
            tailf := by
              rw [hstrict_expand]
              simp only [Category.assoc]
      _ =
          e.hom.1 ≫ ((F.toHom.fiberFunctor Y').map leftSource).1 ≫
            (cg.inv.1 ≫ tailg) ≫
            tailf := by
              simp only [Category.assoc]
      _ =
          e.hom.1 ≫ ((F.toHom.fiberFunctor Y').map leftSource).1 ≫
            (cg.inv.1 ≫ tailg ≫ tailf) := by
              simp only [Category.assoc]
      _ =
          e.hom.1 ≫ ((F.toHom.fiberFunctor Y').map leftSource).1 ≫
            (F.toHom.map ((canonicalPullbackChoice X₁.p).map g
              (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x)) ≫
              tailf) := by
              simpa only [Category.assoc] using
                congrArg
                  (fun t ↦ e.hom.1 ≫ ((F.toHom.fiberFunctor Y').map leftSource).1 ≫ t)
                  hpostg'
      _ =
          e.hom.1 ≫
            F.toHom.map
              (leftSource.1 ≫
                (canonicalPullbackChoice X₁.p).map g
                  (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x) ≫
                (canonicalPullbackChoice X₁.p).map f x) := by
              simpa only [tailf, Category.assoc] using
                congrArg
                  (fun t ↦ e.hom.1 ≫ t)
                  (functor_map_threefold_comp
                    F.toHom.toFunctor leftSource.1
                    ((canonicalPullbackChoice X₁.p).map g
                      (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x))
                    ((canonicalPullbackChoice X₁.p).map f x)).symm
      _ =
          e.hom.1 ≫ F.toHom.map ((canonicalPullbackChoice X₁.p).map gf x) := by
              exact
                congrArg (fun t ↦ e.hom.1 ≫ F.toHom.map t)
                  (FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
                    (p := X₁.p) (f := f) (g := g) (gf := gf) (hgf := hgf) x)
      _ =
          (canonicalPullbackChoice X₂.p).map gf
            ((F.toHom.fiberFunctor U).obj x) := by
              exact FibredCategoryMor.pullbackComparison_hom_postcompose
                F gf x
  -- Both boundary shells have the same owner-level normal form.
  exact hraw.trans hstrict.symm

/-- Helper for Chap08 Lemma 8 4 3/RestrictedDescentForward: after postcomposing the raw
left boundary and the strict left boundary with the target pullback arrow over `g`, the
owner-level composites already agree. -/
private theorem fibredMorphismPullHomLeftBoundaryPostcompose
    {X₁ X₂ : FibredCategoryOver C} (F : X₁ ⟶ X₂) {U Y Y' : C}
    (f : Y ⟶ U) (g : Y' ⟶ Y) (gf : Y' ⟶ U) (hgf : g ≫ f = gf)
    (x : X₁.p.Fiber U) :
    let raw :=
      (((canonicalFiberPseudofunctor X₂.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((F.toHom.fiberFunctor U).obj x)) ≫
        (((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison F f x).hom)
    let strict :=
      (FibredCategoryMor.pullbackComparison F gf x).hom ≫
        (F.toHom.fiberFunctor Y').map
          (((canonicalFiberPseudofunctor X₁.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
        (FibredCategoryMor.pullbackComparison F g
          (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x)).inv
    let tail :=
      (canonicalPullbackChoice X₂.p).map g
        ((F.toHom.fiberFunctor Y).obj
          (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x))
    raw.1 ≫ tail = strict.1 ≫ tail := by
  let raw :=
    (((canonicalFiberPseudofunctor X₂.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((F.toHom.fiberFunctor U).obj x)) ≫
      (((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison F f x).hom)
  let strict :=
    (FibredCategoryMor.pullbackComparison F gf x).hom ≫
      (F.toHom.fiberFunctor Y').map
        (((canonicalFiberPseudofunctor X₁.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
      (FibredCategoryMor.pullbackComparison F g
        (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x)).inv
  let tail :=
    (canonicalPullbackChoice X₂.p).map g
      ((F.toHom.fiberFunctor Y).obj
        (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x))
  let tailf := F.toHom.map ((canonicalPullbackChoice X₁.p).map f x)
  have htailf : X₂.p.IsStronglyCartesian f tailf := by
    -- Transport the chosen source pullback arrow over `f` across the fibred morphism.
    change X₂.p.IsStronglyCartesian f
      (F.toHom.map ((canonicalPullbackChoice X₁.p).map f x))
    exact
      FibredCategoryMor.map_stronglyCartesian_of_lift
        F f
        ((canonicalPullbackChoice X₁.p).map f x)
        ((canonicalPullbackChoice X₁.p).isStronglyCartesian f x)
  have htail : X₂.p.IsHomLift g tail := by
    change
      X₂.p.IsHomLift g
        ((canonicalPullbackChoice X₂.p).map g
          ((F.toHom.fiberFunctor Y).obj
            (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x)))
    exact
      ((canonicalPullbackChoice X₂.p).isStronglyCartesian g
        ((F.toHom.fiberFunctor Y).obj
          (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x))).toIsHomLift
  letI : X₂.p.IsStronglyCartesian f tailf := htailf
  letI : X₂.p.IsHomLift (𝟙 Y') raw.1 := raw.2
  letI : X₂.p.IsHomLift (𝟙 Y') strict.1 := strict.2
  letI : X₂.p.IsHomLift g tail := htail
  have hrawtail : X₂.p.IsHomLift g (raw.1 ≫ tail) := by
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ X₂.p _ _ _
      Y' raw.1 raw.2 _ _ g tail htail
  have hstricttail : X₂.p.IsHomLift g (strict.1 ≫ tail) := by
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ X₂.p _ _ _
      Y' strict.1 strict.2 _ _ g tail htail
  have hpost : (raw.1 ≫ tail) ≫ tailf = (strict.1 ≫ tail) ≫ tailf := by
    -- Compare after composing with the common strongly cartesian leg over `f`.
    simpa only [Category.assoc] using
      fibredMorphismPullHomLeftBoundaryPostcomposeComposite F f g gf hgf x
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ X₂.p _ _ _ _
      f tailf htailf _ _ g (raw.1 ≫ tail) (strict.1 ≫ tail) hrawtail hstricttail hpost

/-- Helper for Chap08 Lemma 8 4 3/RestrictedDescentForward: the left `mapComp'.hom`
boundary for a fibred morphism is the strict composite-leg comparison shell. -/
private theorem fibredMorphismPullHomLeftBoundary
    {X₁ X₂ : FibredCategoryOver C} (F : X₁ ⟶ X₂) {U Y Y' : C}
    (f : Y ⟶ U) (g : Y' ⟶ Y) (gf : Y' ⟶ U) (hgf : g ≫ f = gf)
    (x : X₁.p.Fiber U) :
    (((canonicalFiberPseudofunctor X₂.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((F.toHom.fiberFunctor U).obj x)) ≫
      (((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison F f x).hom) =
      (FibredCategoryMor.pullbackComparison F gf x).hom ≫
        (F.toHom.fiberFunctor Y').map
          (((canonicalFiberPseudofunctor X₁.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
        (FibredCategoryMor.pullbackComparison F g
          (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x)).inv := by
  let raw :=
    (((canonicalFiberPseudofunctor X₂.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((F.toHom.fiberFunctor U).obj x)) ≫
      (((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison F f x).hom)
  let strict :=
    (FibredCategoryMor.pullbackComparison F gf x).hom ≫
      (F.toHom.fiberFunctor Y').map
        (((canonicalFiberPseudofunctor X₁.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
      (FibredCategoryMor.pullbackComparison F g
        (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x)).inv
  let tail :=
    (canonicalPullbackChoice X₂.p).map g
      ((F.toHom.fiberFunctor Y).obj
        (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x))
  have htail : X₂.p.IsStronglyCartesian g tail := by
    -- Use the chosen target pullback arrow over the common leg `g` for fiber extensionality.
    change
      X₂.p.IsStronglyCartesian g
        ((canonicalPullbackChoice X₂.p).map g
          ((F.toHom.fiberFunctor Y).obj
            (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x)))
    exact
      (canonicalPullbackChoice X₂.p).isStronglyCartesian g
        ((F.toHom.fiberFunctor Y).obj
          (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x))
  have hpost : raw.1 ≫ tail = strict.1 ≫ tail := by
    -- Reduce the fiber equality to the owner-level comparison after composing with the `g` tail.
    change raw.1 ≫ tail = strict.1 ≫ tail
    exact fibredMorphismPullHomLeftBoundaryPostcompose F f g gf hgf x
  apply Functor.Fiber.hom_ext
  change raw.1 = strict.1
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ X₂.p _ _ _ _
      g tail htail _ _ (𝟙 Y') raw.1 strict.1 raw.2 strict.2 hpost

namespace FibredCategoryMor

/-- Helper for Chap08 Lemma 8 4 3/RestrictedDescentForward: public API for the left
`pullHom` boundary of a fibred morphism, reusing the internal strongly-cartesian comparison
proof. -/
theorem pullHomLeftBoundary
    {X₁ X₂ : FibredCategoryOver C} (F : X₁ ⟶ X₂) {U Y Y' : C}
    (f : Y ⟶ U) (g : Y' ⟶ Y) (gf : Y' ⟶ U) (hgf : g ≫ f = gf)
    (x : X₁.p.Fiber U) :
    (((canonicalFiberPseudofunctor X₂.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((F.toHom.fiberFunctor U).obj x)) ≫
      (((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison F f x).hom) =
      (FibredCategoryMor.pullbackComparison F gf x).hom ≫
        (F.toHom.fiberFunctor Y').map
          (((canonicalFiberPseudofunctor X₁.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
        (FibredCategoryMor.pullbackComparison F g
          (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj x)).inv := by
  -- The public theorem is only an API wrapper around the already-proved private boundary.
  exact fibredMorphismPullHomLeftBoundary F f g gf hgf x

end FibredCategoryMor

/-- Helper for Chap08 Lemma 8 4 3/RestrictedDescentForward: after postcomposing the raw
right boundary and the strict right boundary with the chosen target pullback arrow over `gf`,
both owner-level composites reduce to the mapped source composite pullback factorization. -/
private theorem fibredMorphismPullHomRightBoundaryPostcompose
    {X₁ X₂ : FibredCategoryOver C} (F : X₁ ⟶ X₂) {U Y Y' : C}
    (f : Y ⟶ U) (g : Y' ⟶ Y) (gf : Y' ⟶ U) (hgf : g ≫ f = gf)
    (y : X₁.p.Fiber U) :
    let raw :=
      (FibredCategoryMor.pullbackComparison F g
          (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y)).inv ≫
        (((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison F f y).inv) ≫
        (((canonicalFiberPseudofunctor X₂.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
          ((F.toHom.fiberFunctor U).obj y))
    let strict :=
      (F.toHom.fiberFunctor Y').map
          (((canonicalFiberPseudofunctor X₁.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y) ≫
        (FibredCategoryMor.pullbackComparison F gf y).inv
    let tail :=
      (canonicalPullbackChoice X₂.p).map gf
        ((F.toHom.fiberFunctor U).obj y)
    raw.1 ≫ tail = strict.1 ≫ tail := by
  let raw :=
    (FibredCategoryMor.pullbackComparison F g
        (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y)).inv ≫
      (((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison F f y).inv) ≫
      (((canonicalFiberPseudofunctor X₂.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((F.toHom.fiberFunctor U).obj y))
  let strict :=
    (F.toHom.fiberFunctor Y').map
        (((canonicalFiberPseudofunctor X₁.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y) ≫
      (FibredCategoryMor.pullbackComparison F gf y).inv
  let tail :=
    (canonicalPullbackChoice X₂.p).map gf
      ((F.toHom.fiberFunctor U).obj y)
  let e := FibredCategoryMor.pullbackComparison F gf y
  let cg :=
    FibredCategoryMor.pullbackComparison F g
      (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y)
  let ef := FibredCategoryMor.pullbackComparison F f y
  let tailg :=
    (canonicalPullbackChoice X₂.p).map g
      (((canonicalFiberPseudofunctor X₂.p).map f.op.toLoc).toFunctor.obj
        ((F.toHom.fiberFunctor U).obj y))
  let tailf := (canonicalPullbackChoice X₂.p).map f ((F.toHom.fiberFunctor U).obj y)
  let sourceTailg :=
    F.toHom.map ((canonicalPullbackChoice X₁.p).map g
      (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y))
  let sourceTailf := F.toHom.map ((canonicalPullbackChoice X₁.p).map f y)
  let rightSource :=
    ((canonicalFiberPseudofunctor X₁.p).mapComp'
      f.op.toLoc g.op.toLoc gf.op.toLoc
      (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y
  have hraw_expand :
      raw.1 =
        cg.inv.1 ≫
          ((((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
          (((canonicalFiberPseudofunctor X₂.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
            ((F.toHom.fiberFunctor U).obj y)).1 := by
    rfl
  have hstrict_expand :
      strict.1 = ((F.toHom.fiberFunctor Y').map rightSource).1 ≫ e.inv.1 := by
    rfl
  have hraw :
      raw.1 ≫ tail = sourceTailg ≫ sourceTailf := by
    have hmap_tailg :
        ((((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
            tailg =
          (canonicalPullbackChoice X₂.p).map g
              ((F.toHom.fiberFunctor Y).obj
                (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y)) ≫
            ef.inv.1 := by
      -- Pullback-functor naturality rewrites the mapped inverse comparison over the `g` leg.
      change
        (((((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map
              (FibredCategoryMor.pullbackComparison F f y).inv)).1) ≫
            (canonicalPullbackChoice X₂.p).map g
              (((canonicalFiberPseudofunctor X₂.p).map f.op.toLoc).toFunctor.obj
                ((F.toHom.fiberFunctor U).obj y)) =
          (canonicalPullbackChoice X₂.p).map g
              ((F.toHom.fiberFunctor Y).obj
                (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y)) ≫
            (FibredCategoryMor.pullbackComparison F f y).inv.1
      exact FibredCategoryMor.canonical_pullbackFunctor_map_fac (p := X₂.p) (f := g)
        (φ := ef.inv)
    have hsourceTailg :
        cg.inv.1 ≫
            (canonicalPullbackChoice X₂.p).map g
              ((F.toHom.fiberFunctor Y).obj
                (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y)) =
          sourceTailg := by
      -- Cancel the inverse comparison against the chosen target pullback on the common `g` leg.
      change
        (FibredCategoryMor.pullbackComparison F g
            (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y)).inv.1 ≫
          (canonicalPullbackChoice X₂.p).map g
            ((F.toHom.fiberFunctor Y).obj
              (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y)) =
        sourceTailg
      exact FibredCategoryMor.pullbackComparison_inv_postcompose_owner
        (F := F) (f := g)
        (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y)
    have hmap_tailg' :
        (((((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
            tailg) ≫ tailf =
          ((canonicalPullbackChoice X₂.p).map g
              ((F.toHom.fiberFunctor Y).obj
                (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y)) ≫
            ef.inv.1) ≫
            tailf := by
      exact congrArg (fun t ↦ t ≫ tailf) hmap_tailg
    have hsourceTailg' :
        (cg.inv.1 ≫
            (canonicalPullbackChoice X₂.p).map g
              ((F.toHom.fiberFunctor Y).obj
                (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y))) ≫
            sourceTailf =
          sourceTailg ≫ sourceTailf := by
      exact congrArg (fun t ↦ t ≫ sourceTailf) hsourceTailg
    have hraw_mid :
        raw.1 ≫ tail =
          (cg.inv.1 ≫
            (canonicalPullbackChoice X₂.p).map g
              ((F.toHom.fiberFunctor Y).obj
                (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y))) ≫
            sourceTailf := by
      -- Normalize the raw inverse shell to the source composite-leg factorization transported by
      -- the fibred morphism.
      calc
      raw.1 ≫ tail =
          cg.inv.1 ≫
            ((((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
            (((canonicalFiberPseudofunctor X₂.p).mapComp'
                f.op.toLoc g.op.toLoc gf.op.toLoc
                (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
              ((F.toHom.fiberFunctor U).obj y)).1 ≫
            tail := by
              rw [hraw_expand]
              simp only [Category.assoc]
      _ =
          cg.inv.1 ≫
            ((((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
            ((((canonicalFiberPseudofunctor X₂.p).mapComp'
                f.op.toLoc g.op.toLoc gf.op.toLoc
                (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
              ((F.toHom.fiberFunctor U).obj y)).1 ≫
              tail) := by
              rfl
      _ =
          cg.inv.1 ≫
            ((((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
            (tailg ≫ tailf) := by
              exact
                congrArg
                  (fun t ↦
                    cg.inv.1 ≫
                      ((((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map
                        ef.inv)).1 ≫
                      t)
                  (FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
                    (p := X₂.p) (f := f) (g := g) (gf := gf) (hgf := hgf)
                    ((F.toHom.fiberFunctor U).obj y))
      _ =
          cg.inv.1 ≫
            (((((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
              tailg) ≫
            tailf := by
              simp only [Category.assoc]
      _ =
          cg.inv.1 ≫
            (((canonicalPullbackChoice X₂.p).map g
                ((F.toHom.fiberFunctor Y).obj
                  (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y))) ≫
              ef.inv.1) ≫ tailf := by
              simpa only [Category.assoc] using congrArg (fun t ↦ cg.inv.1 ≫ t) hmap_tailg'
      _ =
          cg.inv.1 ≫
            (canonicalPullbackChoice X₂.p).map g
              ((F.toHom.fiberFunctor Y).obj
                (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y)) ≫
            ef.inv.1 ≫
            tailf := by
              simp only [Category.assoc]
      _ =
          cg.inv.1 ≫
            (canonicalPullbackChoice X₂.p).map g
              ((F.toHom.fiberFunctor Y).obj
                (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y)) ≫
            sourceTailf := by
              simpa only [sourceTailf, Category.assoc] using
                congrArg
                  (fun t ↦
                    cg.inv.1 ≫
                      (canonicalPullbackChoice X₂.p).map g
                        ((F.toHom.fiberFunctor Y).obj
                          (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y)) ≫
                      t)
                  (FibredCategoryMor.pullbackComparison_inv_postcompose_owner
                    F f y)
      _ =
          (cg.inv.1 ≫
            (canonicalPullbackChoice X₂.p).map g
              ((F.toHom.fiberFunctor Y).obj
                (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y))) ≫
            sourceTailf := by
              simp only [Category.assoc]
    exact hraw_mid.trans hsourceTailg'
  have hstrict :
      strict.1 ≫ tail = sourceTailg ≫ sourceTailf := by
    have hstrict_tail :
        F.toHom.toFunctor.map rightSource.1 ≫
            F.toHom.toFunctor.map ((canonicalPullbackChoice X₁.p).map gf y) =
          sourceTailg ≫ sourceTailf := by
      have hrightSource_fac :
          rightSource.1 ≫ (canonicalPullbackChoice X₁.p).map gf y =
            ((canonicalPullbackChoice X₁.p).map g
                (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y)) ≫
              (canonicalPullbackChoice X₁.p).map f y := by
        -- The source inverse `mapComp'` component factors through the iterated pullbacks.
        exact
          FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
            (p := X₁.p) (f := f) (g := g) (gf := gf) (hgf := hgf) y
      rw [← Functor.map_comp]
      rw [hrightSource_fac]
      change
        F.toHom.toFunctor.map
            (((canonicalPullbackChoice X₁.p).map g
                (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y)) ≫
              (canonicalPullbackChoice X₁.p).map f y) =
          sourceTailg ≫ sourceTailf
      rw [Functor.map_comp]
      rfl
    have hstrict_mid :
        strict.1 ≫ tail =
          F.toHom.toFunctor.map rightSource.1 ≫
            F.toHom.toFunctor.map ((canonicalPullbackChoice X₁.p).map gf y) := by
      -- The strict inverse shell reduces to the same mapped source composite-leg factorization.
      calc
      strict.1 ≫ tail =
          ((F.toHom.fiberFunctor Y').map rightSource).1 ≫
            e.inv.1 ≫
            tail := by
            rw [hstrict_expand]
            simp only [Category.assoc]
      _ =
          ((F.toHom.fiberFunctor Y').map rightSource).1 ≫
            (e.inv.1 ≫ tail) := by
            rfl
      _ =
          F.toHom.toFunctor.map rightSource.1 ≫
            F.toHom.toFunctor.map ((canonicalPullbackChoice X₁.p).map gf y) := by
              exact
                congrArg (fun t ↦ F.toHom.toFunctor.map rightSource.1 ≫ t)
                  (FibredCategoryMor.pullbackComparison_inv_postcompose_owner F gf y)
    exact hstrict_mid.trans hstrict_tail
  -- Both inverse boundary shells reduce to the same mapped source composite.
  exact hraw.trans hstrict.symm

/-- Helper for Chap08 Lemma 8 4 3/RestrictedDescentForward: the right `mapComp'.inv`
boundary for a fibred morphism is the strict source-side inverse boundary followed by the
composite-leg comparison inverse. -/
private theorem fibredMorphismPullHomRightBoundary
    {X₁ X₂ : FibredCategoryOver C} (F : X₁ ⟶ X₂) {U Y Y' : C}
    (f : Y ⟶ U) (g : Y' ⟶ Y) (gf : Y' ⟶ U) (hgf : g ≫ f = gf)
    (y : X₁.p.Fiber U) :
    (FibredCategoryMor.pullbackComparison F g
        (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y)).inv ≫
      (((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison F f y).inv) ≫
      (((canonicalFiberPseudofunctor X₂.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((F.toHom.fiberFunctor U).obj y)) =
    (F.toHom.fiberFunctor Y').map
        (((canonicalFiberPseudofunctor X₁.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y) ≫
      (FibredCategoryMor.pullbackComparison F gf y).inv := by
  let raw :=
    (FibredCategoryMor.pullbackComparison F g
        (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y)).inv ≫
      (((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison F f y).inv) ≫
      (((canonicalFiberPseudofunctor X₂.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((F.toHom.fiberFunctor U).obj y))
  let strict :=
    (F.toHom.fiberFunctor Y').map
        (((canonicalFiberPseudofunctor X₁.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y) ≫
      (FibredCategoryMor.pullbackComparison F gf y).inv
  let tail :=
    (canonicalPullbackChoice X₂.p).map gf
      ((F.toHom.fiberFunctor U).obj y)
  have htail : X₂.p.IsStronglyCartesian gf tail := by
    -- Use the chosen target pullback arrow over the composite leg `gf`.
    change
      X₂.p.IsStronglyCartesian gf
        ((canonicalPullbackChoice X₂.p).map gf
          ((F.toHom.fiberFunctor U).obj y))
    exact
      (canonicalPullbackChoice X₂.p).isStronglyCartesian gf
        ((F.toHom.fiberFunctor U).obj y)
  have hpost : raw.1 ≫ tail = strict.1 ≫ tail := by
    -- Reduce the fiber equality to the owner-level postcomposed inverse-shell comparison.
    change raw.1 ≫ tail = strict.1 ≫ tail
    exact fibredMorphismPullHomRightBoundaryPostcompose F f g gf hgf y
  apply Functor.Fiber.hom_ext
  change raw.1 = strict.1
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ X₂.p _ _ _ _
      gf tail htail _ _ (𝟙 Y') raw.1 strict.1 raw.2 strict.2 hpost

namespace FibredCategoryMor

/-- Helper for Chap08 Lemma 8 4 3/RestrictedDescentForward: public API for the right
`pullHom` boundary of a fibred morphism, reusing the internal strongly-cartesian comparison
proof. -/
theorem pullHomRightBoundary
    {X₁ X₂ : FibredCategoryOver C} (F : X₁ ⟶ X₂) {U Y Y' : C}
    (f : Y ⟶ U) (g : Y' ⟶ Y) (gf : Y' ⟶ U) (hgf : g ≫ f = gf)
    (y : X₁.p.Fiber U) :
    (FibredCategoryMor.pullbackComparison F g
        (((canonicalFiberPseudofunctor X₁.p).map f.op.toLoc).toFunctor.obj y)).inv ≫
      (((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison F f y).inv) ≫
      (((canonicalFiberPseudofunctor X₂.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((F.toHom.fiberFunctor U).obj y)) =
    (F.toHom.fiberFunctor Y').map
        (((canonicalFiberPseudofunctor X₁.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (FibredCategoryMor.comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y) ≫
      (FibredCategoryMor.pullbackComparison F gf y).inv := by
  -- The public theorem is only an API wrapper around the already-proved private boundary.
  exact fibredMorphismPullHomRightBoundary F f g gf hgf y

end FibredCategoryMor

/-- Chap08 Lemma 8 4 3/RestrictedDescentForward: a fibred morphism sends a comparison-
conjugated two-leg overlap morphism to the comparison-conjugated pullback of that morphism. -/
private theorem fibredMorphismPullHom_conjugatedComparison
    {X₁ X₂ : FibredCategoryOver C} (F : X₁ ⟶ X₂) {U₁ U₂ Y Y' : C}
    (x : X₁.p.Fiber U₁) (y : X₁.p.Fiber U₂)
    (f₁ : Y ⟶ U₁) (f₂ : Y ⟶ U₂) (g : Y' ⟶ Y)
    (gf₁ : Y' ⟶ U₁) (gf₂ : Y' ⟶ U₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (δ :
      ((canonicalFiberPseudofunctor X₁.p).map f₁.op.toLoc).toFunctor.obj x ⟶
        ((canonicalFiberPseudofunctor X₁.p).map f₂.op.toLoc).toFunctor.obj y) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X₂.p)
        ((FibredCategoryMor.pullbackComparison F f₁ x).hom ≫
          (F.toHom.fiberFunctor Y).map δ ≫
          (FibredCategoryMor.pullbackComparison F f₂ y).inv)
        g gf₁ gf₂ hgf₁ hgf₂ =
      (FibredCategoryMor.pullbackComparison F gf₁ x).hom ≫
        (F.toHom.fiberFunctor Y').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor X₁.p) δ g gf₁ gf₂ hgf₁ hgf₂) ≫
        (FibredCategoryMor.pullbackComparison F gf₂ y).inv := by
  -- Expand the target `pullHom` once, split the functorial image of the threefold composite,
  -- normalize the left/middle/right factors, and fold the source-side shell back to `pullHom`.
  let FYg := ((canonicalFiberPseudofunctor X₂.p).map g.op.toLoc).toFunctor
  let FXg := ((canonicalFiberPseudofunctor X₁.p).map g.op.toLoc).toFunctor
  let d := δ
  let e₁ := FibredCategoryMor.pullbackComparison F f₁ x
  let e₂ := FibredCategoryMor.pullbackComparison F f₂ y
  let eg₁ := FibredCategoryMor.pullbackComparison F gf₁ x
  let eg₂ := FibredCategoryMor.pullbackComparison F gf₂ y
  let cg₁ := FibredCategoryMor.pullbackComparison F g
    (((canonicalFiberPseudofunctor X₁.p).map f₁.op.toLoc).toFunctor.obj x)
  let cg₂ := FibredCategoryMor.pullbackComparison F g
    (((canonicalFiberPseudofunctor X₁.p).map f₂.op.toLoc).toFunctor.obj y)
  let leftTarget :=
    (((canonicalFiberPseudofunctor X₂.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      ((F.toHom.fiberFunctor U₁).obj x))
  let rightTarget :=
    (((canonicalFiberPseudofunctor X₂.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      ((F.toHom.fiberFunctor U₂).obj y))
  let leftSource :=
    (((canonicalFiberPseudofunctor X₁.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app x)
  let rightSource :=
    (((canonicalFiberPseudofunctor X₁.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app y)
  have hunfolded :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X₂.p)
          (e₁.hom ≫ (F.toHom.fiberFunctor Y).map d ≫ e₂.inv)
          g gf₁ gf₂ hgf₁ hgf₂ =
        leftTarget ≫ FYg.map (e₁.hom ≫ (F.toHom.fiberFunctor Y).map d ≫ e₂.inv) ≫
          rightTarget := by
    -- Put the target pullback map into the explicit `mapComp'.hom ≫ map ≫ mapComp'.inv` form.
    rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    rfl
  have hmap :
      FYg.map (e₁.hom ≫ (F.toHom.fiberFunctor Y).map d ≫ e₂.inv) =
        FYg.map e₁.hom ≫ FYg.map ((F.toHom.fiberFunctor Y).map d) ≫
          FYg.map e₂.inv := by
    -- The only functoriality in the target shell is the image of this visible threefold composite.
    simpa only [FYg, d, e₁, e₂] using
      functor_map_threefold_comp FYg e₁.hom ((F.toHom.fiberFunctor Y).map d) e₂.inv
  have hleft :
      leftTarget ≫ FYg.map e₁.hom =
        eg₁.hom ≫ (F.toHom.fiberFunctor Y').map leftSource ≫ cg₁.inv := by
    -- Normalize the left `mapComp'.hom` boundary over `gf₁`.
    simpa only [FYg, e₁, eg₁, cg₁, leftTarget, leftSource] using
      fibredMorphismPullHomLeftBoundary F f₁ g gf₁ hgf₁ x
  have hmid :
      cg₁.inv ≫ FYg.map ((F.toHom.fiberFunctor Y).map d) =
        (F.toHom.fiberFunctor Y').map (FXg.map d) ≫ cg₂.inv := by
    -- Move the middle vertical morphism across the `g`-leg comparison square.
    simpa only [FYg, FXg, d, cg₁, cg₂] using
      (FibredCategoryMor.pullbackComparison_inv_naturality_over_vertical
        (F := F) (f := g) (φ := d)).symm
  have hright :
      cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget =
        (F.toHom.fiberFunctor Y').map rightSource ≫ eg₂.inv := by
    -- Normalize the right `mapComp'.inv` boundary over `gf₂`.
    simpa only [FYg, e₂, eg₂, cg₂, rightTarget, rightSource] using
      fibredMorphismPullHomRightBoundary F f₂ g gf₂ hgf₂ y
  have hfold :
      (F.toHom.fiberFunctor Y').map leftSource ≫
          (F.toHom.fiberFunctor Y').map (FXg.map d) ≫
          (F.toHom.fiberFunctor Y').map rightSource =
        (F.toHom.fiberFunctor Y').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor X₁.p) d g gf₁ gf₂ hgf₁ hgf₂) := by
    -- Fold the normalized source-side shell back into the source pseudofunctorial pullback.
    change
      (F.toHom.fiberFunctor Y').map leftSource ≫
          (F.toHom.fiberFunctor Y').map (FXg.map d) ≫
          (F.toHom.fiberFunctor Y').map rightSource =
        (F.toHom.fiberFunctor Y').map (leftSource ≫ FXg.map d ≫ rightSource)
    rw [functor_map_threefold_comp]
  have hmap' :
      leftTarget ≫ FYg.map (e₁.hom ≫ (F.toHom.fiberFunctor Y).map d ≫ e₂.inv) ≫
          rightTarget =
        leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((F.toHom.fiberFunctor Y).map d) ≫
          FYg.map e₂.inv ≫ rightTarget := by
    -- Reassociate the split target shell into the linear form used by the boundary rewrites.
    calc
      leftTarget ≫ FYg.map (e₁.hom ≫ (F.toHom.fiberFunctor Y).map d ≫ e₂.inv) ≫
          rightTarget =
        leftTarget ≫
          (FYg.map e₁.hom ≫ FYg.map ((F.toHom.fiberFunctor Y).map d) ≫
            FYg.map e₂.inv) ≫
          rightTarget := by
            exact congrArg (fun t ↦ leftTarget ≫ t ≫ rightTarget) hmap
      _ =
        leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((F.toHom.fiberFunctor Y).map d) ≫
          FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
  have hleft' :
      leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((F.toHom.fiberFunctor Y).map d) ≫
          FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ (F.toHom.fiberFunctor Y').map leftSource ≫ cg₁.inv ≫
          FYg.map ((F.toHom.fiberFunctor Y).map d) ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Replace the left boundary while the remaining middle and right factors stay fixed.
    calc
      leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((F.toHom.fiberFunctor Y).map d) ≫
          FYg.map e₂.inv ≫ rightTarget =
        (leftTarget ≫ FYg.map e₁.hom) ≫ FYg.map ((F.toHom.fiberFunctor Y).map d) ≫
          FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
      _ =
        (eg₁.hom ≫ (F.toHom.fiberFunctor Y').map leftSource ≫ cg₁.inv) ≫
          FYg.map ((F.toHom.fiberFunctor Y).map d) ≫ FYg.map e₂.inv ≫ rightTarget := by
            exact congrArg
              (fun t ↦ t ≫ FYg.map ((F.toHom.fiberFunctor Y).map d) ≫
                FYg.map e₂.inv ≫ rightTarget)
              hleft
      _ =
        eg₁.hom ≫ (F.toHom.fiberFunctor Y').map leftSource ≫ cg₁.inv ≫
          FYg.map ((F.toHom.fiberFunctor Y).map d) ≫ FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
  have hmid' :
      eg₁.hom ≫ (F.toHom.fiberFunctor Y').map leftSource ≫ cg₁.inv ≫
          FYg.map ((F.toHom.fiberFunctor Y).map d) ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ (F.toHom.fiberFunctor Y').map leftSource ≫
          (F.toHom.fiberFunctor Y').map (FXg.map d) ≫
          cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Insert the inverse-naturality square for the middle morphism and reflatten.
    calc
      eg₁.hom ≫ (F.toHom.fiberFunctor Y').map leftSource ≫ cg₁.inv ≫
          FYg.map ((F.toHom.fiberFunctor Y).map d) ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ (F.toHom.fiberFunctor Y').map leftSource ≫
          (cg₁.inv ≫ FYg.map ((F.toHom.fiberFunctor Y).map d)) ≫
          FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
      _ =
        eg₁.hom ≫ (F.toHom.fiberFunctor Y').map leftSource ≫
          ((F.toHom.fiberFunctor Y').map (FXg.map d) ≫ cg₂.inv) ≫
          FYg.map e₂.inv ≫ rightTarget := by
            exact congrArg
              (fun t ↦ eg₁.hom ≫ (F.toHom.fiberFunctor Y').map leftSource ≫ t ≫
                FYg.map e₂.inv ≫ rightTarget)
              hmid
      _ =
        eg₁.hom ≫ (F.toHom.fiberFunctor Y').map leftSource ≫
          (F.toHom.fiberFunctor Y').map (FXg.map d) ≫
          cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
  have hright' :
      eg₁.hom ≫ (F.toHom.fiberFunctor Y').map leftSource ≫
          (F.toHom.fiberFunctor Y').map (FXg.map d) ≫
          cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ (F.toHom.fiberFunctor Y').map leftSource ≫
          (F.toHom.fiberFunctor Y').map (FXg.map d) ≫
          (F.toHom.fiberFunctor Y').map rightSource ≫ eg₂.inv := by
    -- Replace the normalized right boundary under the already fixed source-side prefix.
    simpa only [Category.assoc] using
      congrArg
        (fun t ↦ eg₁.hom ≫ (F.toHom.fiberFunctor Y').map leftSource ≫
          (F.toHom.fiberFunctor Y').map (FXg.map d) ≫ t)
        hright
  have hsource_flat :
      eg₁.hom ≫ (F.toHom.fiberFunctor Y').map leftSource ≫
          (F.toHom.fiberFunctor Y').map (FXg.map d) ≫
          (F.toHom.fiberFunctor Y').map rightSource ≫ eg₂.inv =
        eg₁.hom ≫
          (F.toHom.fiberFunctor Y').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (F := canonicalFiberPseudofunctor X₁.p) d g gf₁ gf₂ hgf₁ hgf₂) ≫
          eg₂.inv := by
    -- Apply the folded source shell under the fixed comparison whiskers.
    calc
      eg₁.hom ≫ (F.toHom.fiberFunctor Y').map leftSource ≫
          (F.toHom.fiberFunctor Y').map (FXg.map d) ≫
          (F.toHom.fiberFunctor Y').map rightSource ≫ eg₂.inv =
        eg₁.hom ≫
          ((F.toHom.fiberFunctor Y').map leftSource ≫
            (F.toHom.fiberFunctor Y').map (FXg.map d) ≫
            (F.toHom.fiberFunctor Y').map rightSource) ≫
          eg₂.inv := by
            simp only [Category.assoc]
      _ =
        eg₁.hom ≫
          (F.toHom.fiberFunctor Y').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (F := canonicalFiberPseudofunctor X₁.p) d g gf₁ gf₂ hgf₁ hgf₂) ≫
          eg₂.inv := by
            exact congrArg (fun t ↦ eg₁.hom ≫ t ≫ eg₂.inv) hfold
  have hprefix :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X₂.p)
          (e₁.hom ≫ (F.toHom.fiberFunctor Y).map d ≫ e₂.inv)
          g gf₁ gf₂ hgf₁ hgf₂ =
        eg₁.hom ≫ (F.toHom.fiberFunctor Y').map leftSource ≫
          (F.toHom.fiberFunctor Y').map (FXg.map d) ≫
          cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Chain the unfolded target shell through the left and middle normalizations.
    exact hunfolded.trans (hmap'.trans (hleft'.trans hmid'))
  exact
    hprefix.trans
      (hright'.trans
        (hsource_flat.trans rfl))

/-- Helper for Lemma 8.4.3: the forward overlap map is the comparison-conjugated image of the
restricted overlap morphism inside the ambient inverse-image fiber. -/
noncomputable def restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.obj
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₁.Y).obj
          (D.obj I₁)).obj) ⟶
      (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.obj
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₂.Y).obj
          (D.obj I₂)).obj) :=
  (restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).inv ≫
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
      (D.hom q f₁ f₂ hf₁ hf₂)).hom ≫
    (restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₂ (D.obj I₂)).hom

/-- Helper for Lemma 8.4.3: the comparison-conjugated forward overlap map satisfies the fixed-
cover pullback law once the two boundary comparison maps are rewritten by naturality. -/
theorem restricted_cover_descent_isoClosure_obj_hom_pullHom_hom
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D q' gf₁ gf₂
        (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
  -- First apply the generic comparison-shell normalization for the inclusion fibred morphism.
  let H := fullSubcategory_inclusion_fibredMor (J := J) (p := p) (P := P) hpullback
  let d := D.hom q f₁ f₂ hf₁ hf₂
  let d' :=
    D.hom q' gf₁ gf₂
      (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
      (by rw [← hq, ← hgf₂, Category.assoc, hf₂])
  have hshell :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
            (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ =
        (restricted_pullback_vs_ambient_pullback_comparison
            (J := J) (p := p) (P := P) hpullback gf₁ (D.obj I₁)).inv ≫
          ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              d g gf₁ gf₂ hgf₁ hgf₂)).hom ≫
          (restricted_pullback_vs_ambient_pullback_comparison
            (J := J) (p := p) (P := P) hpullback gf₂ (D.obj I₂)).hom := by
    simpa only [H, d, restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison,
      restricted_pullback_vs_ambient_pullback_comparison] using
      fibredMorphismPullHom_conjugatedComparison
        (F := H) (x := D.obj I₁) (y := D.obj I₂)
        (f₁ := f₁) (f₂ := f₂) (g := g) (gf₁ := gf₁) (gf₂ := gf₂)
        (hgf₁ := hgf₁) (hgf₂ := hgf₂) (δ := d)
  have hmid :
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            d g gf₁ gf₂ hgf₁ hgf₂)).hom =
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y').map d').hom := by
    -- Transport the source descent datum's pullback law through the restricted-fiber functor.
    exact
      congrArg
        (fun k ↦ ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y').map k).hom)
        (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
  have hreplace :
      (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback gf₁ (D.obj I₁)).inv ≫
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            d g gf₁ gf₂ hgf₁ hgf₂)).hom ≫
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback gf₂ (D.obj I₂)).hom =
      (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback gf₁ (D.obj I₁)).inv ≫
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y').map d').hom ≫
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback gf₂ (D.obj I₂)).hom := by
    -- Substitute the transported source descent morphism into the normalized shell.
    exact congrArg
      (fun k ↦
        (restricted_pullback_vs_ambient_pullback_comparison
            (J := J) (p := p) (P := P) hpullback gf₁ (D.obj I₁)).inv ≫
          k ≫
          (restricted_pullback_vs_ambient_pullback_comparison
            (J := J) (p := p) (P := P) hpullback gf₂ (D.obj I₂)).hom)
      hmid
  have hfinal :
      (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback gf₁ (D.obj I₁)).inv ≫
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y').map d').hom ≫
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback gf₂ (D.obj I₂)).hom =
      restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D q' gf₁ gf₂
        (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
    rfl
  exact hshell.trans (hreplace.trans hfinal)

/-- Helper for Lemma 8.4.3: on equal legs, the comparison-conjugated forward overlap map reduces
to the identity after the comparison shell cancels. -/
theorem restricted_cover_descent_isoClosure_obj_hom_self
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I : S.Arrow} (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D q g g hg hg =
      𝟙 _ := by
  -- Expand the conjugation shell, cancel the comparison isomorphisms, and reduce to the
  -- restricted descent identity axiom on the middle morphism.
  let e :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback g (D.obj I)
  have hmid :
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
          (D.hom q g g hg hg)).hom = 𝟙 _ := by
    calc
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
          (D.hom q g g hg hg)).hom =
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
          (𝟙
            (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map g.op.toLoc).toFunctor.obj
              (D.obj I)))).hom := by
          rw [D.hom_self q g hg]
      _ = 𝟙 _ := by
          rfl
  calc
    restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D q g g hg hg =
      e.inv ≫
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
          (D.hom q g g hg hg)).hom ≫
        e.hom := by
          rfl
    _ = e.inv ≫ 𝟙 _ ≫ e.hom := by
          exact congrArg (fun k ↦ e.inv ≫ k ≫ e.hom) hmid
    _ = 𝟙 _ := by
          simp

/-- Helper for Lemma 8.4.3: the comparison-conjugated forward overlap maps satisfy the cocycle
relation after the boundary comparison maps telescope. -/
theorem restricted_cover_descent_isoClosure_obj_hom_comp
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ I₃ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (hf₃ : f₃ ≫ I₃.f = q := by cat_disch) :
    restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂ ≫
      restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D q f₂ f₃ hf₂ hf₃ =
    restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₃ hf₁ hf₃ := by
  -- Reassociate the two conjugated shells so the middle comparison pair cancels, then the
  -- remaining core is exactly the restricted descent cocycle relation.
  let F := restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y
  let e₁ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)
  let e₂ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₂ (D.obj I₂)
  let e₃ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₃ (D.obj I₃)
  let d₁₂ := D.hom q f₁ f₂ hf₁ hf₂
  let d₂₃ := D.hom q f₂ f₃ hf₂ hf₃
  let d₁₃ := D.hom q f₁ f₃ hf₁ hf₃
  have hnormalize :
      restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂ ≫
        restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
          (J := J) (p := p) (P := P) hpullback S D q f₂ f₃ hf₂ hf₃ =
      e₁.inv ≫ (F.map d₁₂).hom ≫ e₂.hom ≫ e₂.inv ≫ (F.map d₂₃).hom ≫ e₃.hom := by
    change ((e₁.inv ≫ (F.map d₁₂).hom ≫ e₂.hom) ≫
        (e₂.inv ≫ (F.map d₂₃).hom ≫ e₃.hom)) =
      e₁.inv ≫ (F.map d₁₂).hom ≫ e₂.hom ≫ e₂.inv ≫ (F.map d₂₃).hom ≫ e₃.hom
    simp only [Category.assoc]
  have hassoc_cancel :
      e₁.inv ≫ (F.map d₁₂).hom ≫ e₂.hom ≫ e₂.inv ≫ (F.map d₂₃).hom ≫ e₃.hom =
        ((e₁.inv ≫ (F.map d₁₂).hom) ≫ (e₂.hom ≫ e₂.inv)) ≫ (F.map d₂₃).hom ≫ e₃.hom := by
    simp only [Category.assoc]
  have hcancel₁ :
      ((e₁.inv ≫ (F.map d₁₂).hom) ≫ (e₂.hom ≫ e₂.inv)) ≫ (F.map d₂₃).hom ≫ e₃.hom =
        ((e₁.inv ≫ (F.map d₁₂).hom) ≫ 𝟙 _) ≫ (F.map d₂₃).hom ≫ e₃.hom := by
    simpa only [F] using
      congrArg
        (fun k ↦ ((e₁.inv ≫ (F.map d₁₂).hom) ≫ k) ≫ (F.map d₂₃).hom ≫ e₃.hom)
        e₂.hom_inv_id
  have hcancel₂ :
      ((e₁.inv ≫ (F.map d₁₂).hom) ≫ 𝟙 _) ≫ (F.map d₂₃).hom ≫ e₃.hom =
        e₁.inv ≫ (F.map d₁₂).hom ≫ (F.map d₂₃).hom ≫ e₃.hom := by
    simp only [Category.id_comp, Category.assoc]
  have hcancel :
      e₁.inv ≫ (F.map d₁₂).hom ≫ e₂.hom ≫ e₂.inv ≫ (F.map d₂₃).hom ≫ e₃.hom =
        e₁.inv ≫ (F.map d₁₂).hom ≫ (F.map d₂₃).hom ≫ e₃.hom := by
    exact hassoc_cancel.trans (hcancel₁.trans hcancel₂)
  have hmap_comp :
      (F.map d₁₂).hom ≫ (F.map d₂₃).hom = (F.map d₁₃).hom := by
    have hmap_comp_fiber : F.map d₁₂ ≫ F.map d₂₃ = F.map d₁₃ := by
      simpa only [Functor.map_comp, d₁₂, d₂₃, d₁₃] using congrArg F.map
        (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)
    exact congrArg (fun k ↦ k.hom) hmap_comp_fiber
  have hassoc_map :
      e₁.inv ≫ (F.map d₁₂).hom ≫ (F.map d₂₃).hom ≫ e₃.hom =
        e₁.inv ≫ ((F.map d₁₂).hom ≫ (F.map d₂₃).hom) ≫ e₃.hom := by
    simp only [Category.assoc]
  have hmap :
      e₁.inv ≫ ((F.map d₁₂).hom ≫ (F.map d₂₃).hom) ≫ e₃.hom =
        e₁.inv ≫ (F.map d₁₃).hom ≫ e₃.hom := by
    exact congrArg (fun k ↦ e₁.inv ≫ k ≫ e₃.hom) hmap_comp
  have hfinal :
      e₁.inv ≫ (F.map d₁₃).hom ≫ e₃.hom =
        restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₃ hf₁ hf₃ := by
    rfl
  exact hnormalize.trans (hcancel.trans (hassoc_map.trans (hmap.trans hfinal)))

/-- Helper for Lemma 8.4.3: a morphism of restricted descent data commutes with the new forward
comparison-conjugated overlap maps. -/
theorem restricted_cover_descent_to_isoClosure_map_comm_via_pullbackComparison
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    {D₁ D₂ : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData (fun I : S.Arrow ↦ I.f))}
    (φ : D₁ ⟶ D₂)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₁.Y).map
          (φ.hom I₁)).hom ≫
      restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D₂ q f₁ f₂ hf₁ hf₂ =
    restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D₁ q f₁ f₂ hf₁ hf₂ ≫
      ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₂.Y).map
          (φ.hom I₂)).hom := by
  -- TODO: rewrite both overlap maps to the same comparison-conjugated shell, move the boundary
  -- terms by the pullback-comparison naturality lemmas, and apply `φ.comm` to the middle term.
  let F := restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y
  let α₁ :=
    ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₁.Y).map
        (φ.hom I₁)).hom
  let α₂ :=
    ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₂.Y).map
        (φ.hom I₂)).hom
  let β₁ :=
    F.map
      (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₁.op.toLoc).toFunctor.map
        (φ.hom I₁))
  let β₂ :=
    F.map
      (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₂.op.toLoc).toFunctor.map
        (φ.hom I₂))
  let e₁₁ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₁ (D₁.obj I₁)
  let e₁₂ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₁ (D₂.obj I₁)
  let e₂₁ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₂ (D₁.obj I₂)
  let e₂₂ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₂ (D₂.obj I₂)
  let d₁ := D₁.hom q f₁ f₂ hf₁ hf₂
  let d₂ := D₂.hom q f₁ f₂ hf₁ hf₂
  have hleft :
      α₁ ≫ e₁₂.inv = e₁₁.inv ≫ β₁.hom := by
    simpa only [α₁, β₁, e₁₁, e₁₂,
      restricted_pullback_vs_ambient_pullback_comparison] using
      (fullSubcategory_inclusion_pullbackComparison_naturality_over_vertical
        (J := J) (p := p) (P := P) hpullback (f := f₁) (φ := φ.hom I₁))
  have hmid :
      β₁.hom ≫ (F.map d₂).hom = (F.map d₁).hom ≫ β₂.hom := by
    have hmid_fiber : β₁ ≫ F.map d₂ = F.map d₁ ≫ β₂ := by
      calc
        β₁ ≫ F.map d₂ =
            F.map
              ((((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₁.op.toLoc).toFunctor.map
                  (φ.hom I₁)) ≫ d₂) := by
              dsimp [β₁]
              rw [← F.map_comp]
        _ = F.map
              (d₁ ≫
                (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₂.op.toLoc).toFunctor.map
                  (φ.hom I₂))) := by
              simpa only [d₁, d₂] using congrArg F.map (φ.comm q f₁ f₂ hf₁ hf₂)
        _ = F.map d₁ ≫ β₂ := by
              dsimp [β₂]
              rw [F.map_comp]
    exact congrArg (fun k ↦ k.hom) hmid_fiber
  have hright :
      e₂₁.hom ≫ α₂ = β₂.hom ≫ e₂₂.hom := by
    simpa only [α₂, β₂, e₂₁, e₂₂,
      restricted_pullback_vs_ambient_pullback_comparison] using
      (fullSubcategory_inclusion_pullbackComparison_inv_naturality_over_vertical
        (J := J) (p := p) (P := P) hpullback (f := f₂) (φ := φ.hom I₂)).symm
  have hlast :
      (e₁₁.inv ≫ (F.map d₁).hom ≫ e₂₁.hom) ≫ α₂ =
        restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
          (J := J) (p := p) (P := P) hpullback S D₁ q f₁ f₂ hf₁ hf₂ ≫ α₂ := by
    rfl
  have hchain :
      α₁ ≫
          restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
            (J := J) (p := p) (P := P) hpullback S D₂ q f₁ f₂ hf₁ hf₂ =
        (e₁₁.inv ≫ (F.map d₁).hom ≫ e₂₁.hom) ≫ α₂ := by
    calc
      α₁ ≫
          restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
            (J := J) (p := p) (P := P) hpullback S D₂ q f₁ f₂ hf₁ hf₂ =
        α₁ ≫ e₁₂.inv ≫ (F.map d₂).hom ≫ e₂₂.hom := by
          rfl
      _ = (α₁ ≫ e₁₂.inv) ≫ (F.map d₂).hom ≫ e₂₂.hom := by
          simp only [Category.assoc]
      _ = (e₁₁.inv ≫ β₁.hom) ≫ (F.map d₂).hom ≫ e₂₂.hom := by
          exact congrArg (fun k ↦ k ≫ (F.map d₂).hom ≫ e₂₂.hom) hleft
      _ = e₁₁.inv ≫ (β₁.hom ≫ (F.map d₂).hom) ≫ e₂₂.hom := by
          simp only [Category.assoc]
      _ = e₁₁.inv ≫ ((F.map d₁).hom ≫ β₂.hom) ≫ e₂₂.hom := by
          exact congrArg (fun k ↦ e₁₁.inv ≫ k ≫ e₂₂.hom) hmid
      _ = e₁₁.inv ≫ (F.map d₁).hom ≫ (β₂.hom ≫ e₂₂.hom) := by
          simp only [Category.assoc]
      _ = e₁₁.inv ≫ (F.map d₁).hom ≫ (e₂₁.hom ≫ α₂) := by
          exact congrArg (fun k ↦ e₁₁.inv ≫ (F.map d₁).hom ≫ k) hright.symm
      _ = e₁₁.inv ≫ (F.map d₁).hom ≫ e₂₁.hom ≫ α₂ := by
          rfl
      _ = (e₁₁.inv ≫ (F.map d₁).hom ≫ e₂₁.hom) ≫ α₂ := by
          simp only [Category.assoc]
  exact hchain.trans hlast

end RestrictedFibered

end
