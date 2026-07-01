import stacks_project.Chap08.Lemma_8_5_3_PullbackNaturality

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

open BasedFunctor Functor IsStronglyCartesian

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/-- Helper for Lemma 8.5.3: forgetting one associated-groupoid overlap map to the ambient fibred
category is the usual conjugation by the inclusion pullback-comparison isomorphisms. -/
noncomputable abbrev associated_groupoid_cover_forget_hom
    [p.IsFibered] {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
      (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.obj
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) I₁.Y).obj
          (D.obj I₁))) ⟶
      (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.obj
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) I₂.Y).obj
          (D.obj I₂))) :=
  let ι := associated_groupoid_inclusion (p := p)
  (fibred_morphism_pullbackComparison (C := C) ι f₁ (D.obj I₁)).hom ≫
    (FibredCategoryMor.fiberFunctor ι Y).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
    (fibred_morphism_pullbackComparison (C := C) ι f₂ (D.obj I₂)).inv

/-- Helper for Lemma 8.5.3: after postcomposing the raw left `pullHom` boundary and the strict
comparison shell with the chosen `g`- and `f`-pullback arrows, both owner-level composites reduce
to the same composite-leg chosen pullback arrow. -/
private theorem associated_groupoid_pullbackComparison_pullHom_left_boundary_postcompose_g_then_f_target
    [p.IsFibered] {U Y Y' : C}
    (f : Y ⟶ U) (g : Y' ⟶ Y) (gf : Y' ⟶ U) (hgf : g ≫ f = gf)
    (x : (stronglyCartesianProjection p).Fiber U) :
    let raw :=
      (((canonicalFiberPseudofunctor p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).obj x)) ≫
        (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map
          (fibred_morphism_pullbackComparison
            (associated_groupoid_inclusion (p := p)) f x).hom)
    let strict :=
      (fibred_morphism_pullbackComparison
          (associated_groupoid_inclusion (p := p)) gf x).hom ≫
        (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y').map
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
        (fibred_morphism_pullbackComparison
          (associated_groupoid_inclusion (p := p)) g
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
            x)).inv
    let tailg :=
      (canonicalPullbackChoice p).map g
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y).obj
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
            x))
    let tailf := (associated_groupoid_inclusion (p := p)).toHom.map
      ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x)
    raw.1 ≫ tailg ≫ tailf = strict.1 ≫ tailg ≫ tailf := by
  let ι := associated_groupoid_inclusion (p := p)
  let e :=
    fibred_morphism_pullbackComparison ι gf x
  let cg :=
    fibred_morphism_pullbackComparison ι g
      (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
        x)
  let ef := fibred_morphism_pullbackComparison ι f x
  let leftRaw :=
    ((canonicalFiberPseudofunctor p).mapComp'
      f.op.toLoc g.op.toLoc gf.op.toLoc
      (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor ι U).obj x)
  let leftSource :=
    ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).mapComp'
      f.op.toLoc g.op.toLoc gf.op.toLoc
      (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      x
  let raw := leftRaw ≫
    (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map ef.hom)
  let strict := e.hom ≫
    (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫
    cg.inv
  let tailg :=
    (canonicalPullbackChoice p).map g
      ((FibredCategoryMor.fiberFunctor ι Y).obj
        (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
          x))
  let tailf := ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x)
  have hraw :
      raw.1 ≫ tailg ≫ tailf =
        (canonicalPullbackChoice p).map gf
          ((FibredCategoryMor.fiberFunctor ι U).obj x) := by
    have hraw_flank :
        (leftRaw.1 ≫
            (canonicalPullbackChoice p).map g
              (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj
                ((FibredCategoryMor.fiberFunctor ι U).obj x))) ≫
            (canonicalPullbackChoice p).map f
              ((FibredCategoryMor.fiberFunctor ι U).obj x) =
          (canonicalPullbackChoice p).map gf
            ((FibredCategoryMor.fiberFunctor ι U).obj x) := by
      -- The left comparison component already factors through the chosen ambient pullback over
      -- the composite leg `gf`.
      simpa [leftRaw, Category.assoc] using
        canonicalFiberPseudofunctor_mapComp'_hom_app_fac
          (q := p) (f := f) (g := g) (gf := gf) (hgf := hgf)
          ((FibredCategoryMor.fiberFunctor ι U).obj x)
    -- Normalize the raw shell by first postcomposing the forgotten `f` comparison with the
    -- ambient `g`-pullback arrow, then the ambient `f`-pullback arrow.
    calc
      raw.1 ≫ tailg ≫ tailf =
          leftRaw.1 ≫
            ((((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map ef.hom)).1 ≫
            tailg ≫
            tailf := by
              change
                (leftRaw.1 ≫
                    (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map ef.hom).1) ≫
                  tailg ≫
                  tailf =
                leftRaw.1 ≫
                  ((((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map ef.hom)).1 ≫
                  tailg ≫
                  tailf
              simp only [Category.assoc]
      _ =
          leftRaw.1 ≫
            (((((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map ef.hom)).1 ≫
              tailg) ≫
            tailf := by
              simp only [Category.assoc]
      _ =
          leftRaw.1 ≫
            (((canonicalPullbackChoice p).map g
                (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj
                  ((FibredCategoryMor.fiberFunctor ι U).obj x))) ≫
              ef.hom.1) ≫
            tailf := by
              exact
                congrArg (fun t ↦ leftRaw.1 ≫ t ≫ tailf)
                  (canonical_pullbackFunctor_map_fac (q := p) (f := g) (φ := ef.hom))
      _ =
          leftRaw.1 ≫
            (canonicalPullbackChoice p).map g
              (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj
                ((FibredCategoryMor.fiberFunctor ι U).obj x)) ≫
            ef.hom.1 ≫
            tailf := by
              simp only [Category.assoc]
      _ =
          (canonicalPullbackChoice p).map gf
            ((FibredCategoryMor.fiberFunctor ι U).obj x) := by
              have hpostf :
                  leftRaw.1 ≫
                      (canonicalPullbackChoice p).map g
                        (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj
                          ((FibredCategoryMor.fiberFunctor ι U).obj x)) ≫
                      ef.hom.1 ≫
                      tailf =
                    (leftRaw.1 ≫
                      (canonicalPullbackChoice p).map g
                        (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj
                          ((FibredCategoryMor.fiberFunctor ι U).obj x))) ≫
                      (canonicalPullbackChoice p).map f
                        ((FibredCategoryMor.fiberFunctor ι U).obj x) := by
                simpa only [tailf, Category.assoc] using
                  congrArg
                    (fun t ↦
                      leftRaw.1 ≫
                        (canonicalPullbackChoice p).map g
                          (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj
                            ((FibredCategoryMor.fiberFunctor ι U).obj x)) ≫
                        t)
                    (associated_groupoid_pullbackComparison_hom_postcompose
                      (p := p) (f := f) x)
              exact hpostf.trans hraw_flank
  have hstrict :
      strict.1 ≫ tailg ≫ tailf =
        (canonicalPullbackChoice p).map gf
          ((FibredCategoryMor.fiberFunctor ι U).obj x) := by
    have hpostg :
        cg.inv.1 ≫ tailg =
          ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map g
            (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
              x)) := by
      -- Rewrite the inverse `g` comparison against the common ambient `g`-pullback arrow.
      simpa only [tailg] using
        associated_groupoid_pullbackComparison_inv_postcompose_owner
          (p := p) (f := g)
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
            x)
    have hpostg' :
        (cg.inv.1 ≫ tailg) ≫ tailf =
          ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map g
              (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
                x)) ≫
            tailf := by
      exact congrArg (fun t ↦ t ≫ tailf) hpostg
    -- Normalize the strict shell by canceling the inverse comparison on the common `g` leg.
    calc
      strict.1 ≫ tailg ≫ tailf =
          e.hom.1 ≫ ((FibredCategoryMor.fiberFunctor ι Y').map leftSource).1 ≫
            cg.inv.1 ≫
            tailg ≫
            tailf := by
              change
                (e.hom.1 ≫
                    ((FibredCategoryMor.fiberFunctor ι Y').map leftSource).1 ≫
                    cg.inv.1) ≫
                  tailg ≫
                  tailf =
                e.hom.1 ≫
                  ((FibredCategoryMor.fiberFunctor ι Y').map leftSource).1 ≫
                  cg.inv.1 ≫
                  tailg ≫
                  tailf
              simp only [Category.assoc]
      _ =
          e.hom.1 ≫ ((FibredCategoryMor.fiberFunctor ι Y').map leftSource).1 ≫
            (cg.inv.1 ≫ tailg) ≫
            tailf := by
              simp only [Category.assoc]
      _ =
          e.hom.1 ≫ ((FibredCategoryMor.fiberFunctor ι Y').map leftSource).1 ≫
            (cg.inv.1 ≫ tailg ≫ tailf) := by
              simp only [Category.assoc]
      _ =
          e.hom.1 ≫ ((FibredCategoryMor.fiberFunctor ι Y').map leftSource).1 ≫
            (ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map g
              (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
                x)) ≫
              tailf) := by
              simpa only [Category.assoc] using
                congrArg
                  (fun t ↦ e.hom.1 ≫ ((FibredCategoryMor.fiberFunctor ι Y').map leftSource).1 ≫ t)
                  hpostg'
      _ =
          e.hom.1 ≫
            (ι.toHom.map leftSource.1 ≫
              ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map g
                (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
                  x)) ≫
              tailf) := by
              rfl
      _ =
          e.hom.1 ≫
            ι.toHom.map
              (leftSource.1 ≫
                (canonicalPullbackChoice (stronglyCartesianProjection p)).map g
                  (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
                    x) ≫
                (canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) := by
              simpa only [tailf, Category.assoc] using
                  congrArg
                    (fun t ↦ e.hom.1 ≫ t)
                  (functor_map_threefold_comp ι.toHom.toFunctor leftSource.1
                    ((canonicalPullbackChoice (stronglyCartesianProjection p)).map g
                      (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
                        x))
                    ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x)).symm
      _ =
          e.hom.1 ≫
            ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map gf x) := by
              exact
                congrArg (fun t ↦ e.hom.1 ≫ ι.toHom.map t)
                  (canonicalFiberPseudofunctor_mapComp'_hom_app_fac
                    (q := stronglyCartesianProjection p) (f := f) (g := g) (gf := gf)
                    (hgf := hgf) x)
      _ =
          (canonicalPullbackChoice p).map gf
            ((FibredCategoryMor.fiberFunctor ι U).obj x) := by
              exact associated_groupoid_pullbackComparison_hom_postcompose
                (p := p) (f := gf) x
  -- Both owner-level shells reduce to the same chosen ambient pullback over `gf`.
  exact hraw.trans hstrict.symm

/-- Helper for Lemma 8.5.3: after postcomposing the raw left `pullHom` boundary and the strict
comparison shell with the chosen ambient pullback arrow over `g`, the two owner-level composites
already agree. -/
private theorem associated_groupoid_pullbackComparison_pullHom_left_boundary_postcompose_g_target
    [p.IsFibered] {U Y Y' : C}
    (f : Y ⟶ U) (g : Y' ⟶ Y) (gf : Y' ⟶ U) (hgf : g ≫ f = gf)
    (x : (stronglyCartesianProjection p).Fiber U) :
    let raw :=
      (((canonicalFiberPseudofunctor p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).obj x)) ≫
        (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map
          (fibred_morphism_pullbackComparison
            (associated_groupoid_inclusion (p := p)) f x).hom)
    let strict :=
      (fibred_morphism_pullbackComparison
          (associated_groupoid_inclusion (p := p)) gf x).hom ≫
        (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y').map
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
        (fibred_morphism_pullbackComparison
          (associated_groupoid_inclusion (p := p)) g
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
            x)).inv
    let tail :=
      (canonicalPullbackChoice p).map g
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y).obj
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
            x))
    raw.1 ≫ tail = strict.1 ≫ tail := by
  let ι := associated_groupoid_inclusion (p := p)
  let raw :=
    (((canonicalFiberPseudofunctor p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor ι U).obj x)) ≫
      (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map
        (fibred_morphism_pullbackComparison ι f x).hom)
  let strict :=
    (fibred_morphism_pullbackComparison ι gf x).hom ≫
      (FibredCategoryMor.fiberFunctor ι Y').map
        (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
      (fibred_morphism_pullbackComparison ι g
        (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
          x)).inv
  let tail :=
    (canonicalPullbackChoice p).map g
      ((FibredCategoryMor.fiberFunctor ι Y).obj
        (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
          x))
  let tailf := ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x)
  have htailf : p.IsStronglyCartesian f tailf := by
    -- The forgotten associated pullback arrow over `f` stays strongly cartesian in the ambient
    -- fibred category.
    change p.IsStronglyCartesian f
      (ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x))
    exact
      associated_groupoid_inclusion_map_stronglyCartesian_of_lift
        (p := p) f
        ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x)
        ((canonicalPullbackChoice (stronglyCartesianProjection p)).isStronglyCartesian f x)
  have htail : p.IsHomLift g tail := by
    change
      p.IsHomLift g
        ((canonicalPullbackChoice p).map g
          ((FibredCategoryMor.fiberFunctor ι Y).obj
            (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
              x)))
    exact
      ((canonicalPullbackChoice p).isStronglyCartesian g
        ((FibredCategoryMor.fiberFunctor ι Y).obj
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
            x))).toIsHomLift
  letI : p.IsStronglyCartesian f tailf := htailf
  letI : p.IsHomLift (𝟙 Y') raw.1 := raw.2
  letI : p.IsHomLift (𝟙 Y') strict.1 := strict.2
  letI : p.IsHomLift g tail := htail
  have hrawtail : p.IsHomLift g (raw.1 ≫ tail) := by
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ p _ _ _
      Y' raw.1 raw.2 _ _ g tail htail
  have hstricttail : p.IsHomLift g (strict.1 ≫ tail) := by
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ p _ _ _
      Y' strict.1 strict.2 _ _ g tail htail
  have hpost : (raw.1 ≫ tail) ≫ tailf = (strict.1 ≫ tail) ≫ tailf := by
    -- Compare the two `g`-postcomposed shells after freezing the common ambient pullback arrow
    -- over `f`.
    simpa only [Category.assoc] using
      associated_groupoid_pullbackComparison_pullHom_left_boundary_postcompose_g_then_f_target
        (p := p) (f := f) (g := g) (gf := gf) (hgf := hgf) x
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      f tailf htailf _ _ g (raw.1 ≫ tail) (strict.1 ≫ tail) hrawtail hstricttail hpost

/-- Helper for Lemma 8.5.3: the raw left `pullHom` boundary is the strict composite-leg
comparison shell in the ambient fiber over the domain of `gf`. -/
private theorem associated_groupoid_pullbackComparison_pullHom_left_boundary
    [p.IsFibered] {U Y Y' : C}
    (f : Y ⟶ U) (g : Y' ⟶ Y) (gf : Y' ⟶ U) (hgf : g ≫ f = gf)
    (x : (stronglyCartesianProjection p).Fiber U) :
    (((canonicalFiberPseudofunctor p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).obj x)) ≫
      (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map
        (fibred_morphism_pullbackComparison
          (associated_groupoid_inclusion (p := p)) f x).hom) =
      (fibred_morphism_pullbackComparison
          (associated_groupoid_inclusion (p := p)) gf x).hom ≫
        (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y').map
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
      (fibred_morphism_pullbackComparison
        (associated_groupoid_inclusion (p := p)) g
        (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
          x)).inv := by
  let ι := associated_groupoid_inclusion (p := p)
  let raw :=
    (((canonicalFiberPseudofunctor p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor ι U).obj x)) ≫
      (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map
        (fibred_morphism_pullbackComparison ι f x).hom)
  let strict :=
    (fibred_morphism_pullbackComparison ι gf x).hom ≫
      (FibredCategoryMor.fiberFunctor ι Y').map
        (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
      (fibred_morphism_pullbackComparison ι g
        (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
          x)).inv
  let tail :=
    (canonicalPullbackChoice p).map g
      ((FibredCategoryMor.fiberFunctor ι Y).obj
        (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
          x))
  have htail : p.IsStronglyCartesian g tail := by
    -- The common ambient pullback arrow over `g` is the strongly cartesian leg used for the
    -- final cancellation.
    change
      p.IsStronglyCartesian g
        ((canonicalPullbackChoice p).map g
          ((FibredCategoryMor.fiberFunctor ι Y).obj
            (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
              x)))
    exact
      (canonicalPullbackChoice p).isStronglyCartesian g
        ((FibredCategoryMor.fiberFunctor ι Y).obj
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
            x))
  have hpost : raw.1 ≫ tail = strict.1 ≫ tail := by
    -- Reduce the fiber equality to the owner-level comparison after composing with the common
    -- ambient `g`-pullback arrow.
    exact
      associated_groupoid_pullbackComparison_pullHom_left_boundary_postcompose_g_target
        (p := p) (f := f) (g := g) (gf := gf) (hgf := hgf) x
  apply Functor.Fiber.hom_ext
  change raw.1 = strict.1
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      g tail htail _ _ (𝟙 Y') raw.1 strict.1 raw.2 strict.2 hpost

/-- Helper for Lemma 8.5.3: the raw right `pullHom` boundary is the strict composite-leg right
comparison shell after passing back to the ambient fiber over the common refinement leg. -/
private theorem associated_groupoid_pullbackComparison_pullHom_right_boundary
    [p.IsFibered] {U Y Y' : C}
    (f : Y ⟶ U) (g : Y' ⟶ Y) (gf : Y' ⟶ U) (hgf : g ≫ f = gf)
    (x : (stronglyCartesianProjection p).Fiber U) :
    (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) g
        (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
          x)).inv ≫
      (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map
        (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f x).inv) ≫
      (((canonicalFiberPseudofunctor p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).obj x)) =
    (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y').map
        (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app x) ≫
      (fibred_morphism_pullbackComparison
        (associated_groupoid_inclusion (p := p)) gf x).inv := by
  let ι := associated_groupoid_inclusion (p := p)
  let raw :=
    (fibred_morphism_pullbackComparison ι g
        (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
          x)).inv ≫
      (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map
        (fibred_morphism_pullbackComparison ι f x).inv) ≫
      (((canonicalFiberPseudofunctor p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor ι U).obj x))
  let strict :=
    (FibredCategoryMor.fiberFunctor ι Y').map
        (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app x) ≫
      (fibred_morphism_pullbackComparison ι gf x).inv
  let tail :=
    (canonicalPullbackChoice p).map gf
      ((FibredCategoryMor.fiberFunctor ι U).obj x)
  have htail : p.IsStronglyCartesian gf tail := by
    -- Reuse the chosen ambient pullback arrow over the composite leg `gf`.
    change
      p.IsStronglyCartesian gf
        ((canonicalPullbackChoice p).map gf
          ((FibredCategoryMor.fiberFunctor ι U).obj x))
    exact
      (canonicalPullbackChoice p).isStronglyCartesian gf
        ((FibredCategoryMor.fiberFunctor ι U).obj x)
  have hpost :
      raw.1 ≫ tail = strict.1 ≫ tail := by
    let e := fibred_morphism_pullbackComparison ι gf x
    let cg := fibred_morphism_pullbackComparison ι g
      (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
        x)
    let ef := fibred_morphism_pullbackComparison ι f x
    let tailg :=
      (canonicalPullbackChoice p).map g
        (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj
          ((FibredCategoryMor.fiberFunctor ι U).obj x))
    let tailf := (canonicalPullbackChoice p).map f
      ((FibredCategoryMor.fiberFunctor ι U).obj x)
    let sourceTailg := ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map g
      (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj x))
    let sourceTailf := ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x)
    let rightSource :=
      ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app x
    have hraw_expand :
        raw.1 =
          cg.inv.1 ≫
            ((((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
            (((canonicalFiberPseudofunctor p).mapComp'
                f.op.toLoc g.op.toLoc gf.op.toLoc
                (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
              ((FibredCategoryMor.fiberFunctor ι U).obj x)).1 := by
      rfl
    have hstrict_expand :
        strict.1 = ((FibredCategoryMor.fiberFunctor ι Y').map rightSource).1 ≫ e.inv.1 := by
      rfl
    have hraw :
        raw.1 ≫ tail = sourceTailg ≫ sourceTailf := by
      have hmap_tailg :
          ((((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫ tailg =
            (canonicalPullbackChoice p).map g
                ((FibredCategoryMor.fiberFunctor ι Y).obj
                  (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
                    x)) ≫
              ef.inv.1 := by
        change
          (((((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map
                (fibred_morphism_pullbackComparison ι f x).inv)).1) ≫
              (canonicalPullbackChoice p).map g
                (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj
                  ((FibredCategoryMor.fiberFunctor ι U).obj x)) =
            (canonicalPullbackChoice p).map g
                ((FibredCategoryMor.fiberFunctor ι Y).obj
                  (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
                    x)) ≫
              (fibred_morphism_pullbackComparison ι f x).inv.1
        exact canonical_pullbackFunctor_map_fac (q := p) (f := g) (φ := ef.inv)
      have hsourceTailg :
          cg.inv.1 ≫
              (canonicalPullbackChoice p).map g
                ((FibredCategoryMor.fiberFunctor ι Y).obj
                  (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
                    x)) =
            sourceTailg := by
        change
          (fibred_morphism_pullbackComparison ι g
              (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
                x)).inv.1 ≫
            (canonicalPullbackChoice p).map g
              ((FibredCategoryMor.fiberFunctor ι Y).obj
                (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
                  x)) =
          sourceTailg
        exact
          associated_groupoid_pullbackComparison_inv_postcompose_owner
            (p := p) (f := g)
            (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
              x)
      have hmap_tailg' :
          (((((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫ tailg) ≫
              tailf =
            ((canonicalPullbackChoice p).map g
                ((FibredCategoryMor.fiberFunctor ι Y).obj
                  (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
                    x)) ≫
              ef.inv.1) ≫
              tailf := by
        exact congrArg (fun t ↦ t ≫ tailf) hmap_tailg
      have hsourceTailg' :
          (cg.inv.1 ≫
              (canonicalPullbackChoice p).map g
                ((FibredCategoryMor.fiberFunctor ι Y).obj
                  (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
                    x))) ≫
              sourceTailf =
            sourceTailg ≫ sourceTailf := by
        exact congrArg (fun t ↦ t ≫ sourceTailf) hsourceTailg
      have hraw_mid :
          raw.1 ≫ tail =
            (cg.inv.1 ≫
              (canonicalPullbackChoice p).map g
                ((FibredCategoryMor.fiberFunctor ι Y).obj
                  (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
                    x))) ≫
              sourceTailf := by
        calc
          raw.1 ≫ tail =
              cg.inv.1 ≫
                ((((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
                (((canonicalFiberPseudofunctor p).mapComp'
                    f.op.toLoc g.op.toLoc gf.op.toLoc
                    (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
                  ((FibredCategoryMor.fiberFunctor ι U).obj x)).1 ≫
                tail := by
                  rw [hraw_expand]
                  simp only [Category.assoc]
          _ =
              cg.inv.1 ≫
                ((((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
                ((((canonicalFiberPseudofunctor p).mapComp'
                    f.op.toLoc g.op.toLoc gf.op.toLoc
                    (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
                  ((FibredCategoryMor.fiberFunctor ι U).obj x)).1 ≫
                  tail) := by
                    rfl
          _ =
              cg.inv.1 ≫
                ((((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
                (tailg ≫ tailf) := by
                  exact
                    congrArg
                      (fun t ↦
                        cg.inv.1 ≫
                          ((((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
                          t)
                      (canonicalFiberPseudofunctor_mapComp'_inv_app_fac
                        (q := p) (f := f) (g := g) (gf := gf) (hgf := hgf)
                        ((FibredCategoryMor.fiberFunctor ι U).obj x))
          _ =
              cg.inv.1 ≫
                (((((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
                  tailg) ≫
                tailf := by
                  simp only [Category.assoc]
          _ =
              cg.inv.1 ≫
                (((canonicalPullbackChoice p).map g
                    ((FibredCategoryMor.fiberFunctor ι Y).obj
                      (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
                        x))) ≫
                  ef.inv.1) ≫ tailf := by
                  simpa only [Category.assoc] using
                    congrArg (fun t ↦ cg.inv.1 ≫ t) hmap_tailg'
          _ =
              cg.inv.1 ≫
                (canonicalPullbackChoice p).map g
                  ((FibredCategoryMor.fiberFunctor ι Y).obj
                    (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
                      x)) ≫
                ef.inv.1 ≫
                tailf := by
                  simp only [Category.assoc]
          _ =
              cg.inv.1 ≫
                (canonicalPullbackChoice p).map g
                  ((FibredCategoryMor.fiberFunctor ι Y).obj
                    (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
                      x)) ≫
                sourceTailf := by
                  simpa only [sourceTailf, Category.assoc] using
                    congrArg
                      (fun t ↦
                        cg.inv.1 ≫
                          (canonicalPullbackChoice p).map g
                            ((FibredCategoryMor.fiberFunctor ι Y).obj
                              (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
                                x)) ≫
                          t)
                      (associated_groupoid_pullbackComparison_inv_postcompose_owner
                        (p := p) (f := f) x)
          _ =
              (cg.inv.1 ≫
                (canonicalPullbackChoice p).map g
                  ((FibredCategoryMor.fiberFunctor ι Y).obj
                    (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj
                      x))) ≫
                sourceTailf := by
                  simp only [Category.assoc]
      exact hraw_mid.trans hsourceTailg'
    have hstrict :
        strict.1 ≫ tail = sourceTailg ≫ sourceTailf := by
      have hstrict_tail :
          ι.toHom.map rightSource.1 ≫
              ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map gf x) =
            sourceTailg ≫ sourceTailf := by
        have hcomp :
            rightSource.1 ≫ (canonicalPullbackChoice (stronglyCartesianProjection p)).map gf x =
              ((canonicalPullbackChoice (stronglyCartesianProjection p)).map g
                  (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj x)) ≫
                (canonicalPullbackChoice (stronglyCartesianProjection p)).map f x := by
          exact
            canonicalFiberPseudofunctor_mapComp'_inv_app_fac
              (q := stronglyCartesianProjection p) (f := f) (g := g) (gf := gf) (hgf := hgf) x
        simpa only [sourceTailg, sourceTailf, Functor.map_comp] using
          congrArg (fun t ↦ ι.toHom.map t) hcomp
      have hstrict_mid :
          strict.1 ≫ tail =
            ι.toHom.map rightSource.1 ≫
              ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map gf x) := by
        calc
          strict.1 ≫ tail =
              ((FibredCategoryMor.fiberFunctor ι Y').map rightSource).1 ≫
                e.inv.1 ≫
                tail := by
                  rw [hstrict_expand]
                  simp only [Category.assoc]
          _ =
              ((FibredCategoryMor.fiberFunctor ι Y').map rightSource).1 ≫
                (e.inv.1 ≫ tail) := by
                  rfl
          _ =
              ι.toHom.map rightSource.1 ≫
                ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map gf x) := by
                  exact
                    congrArg (fun t ↦ ι.toHom.map rightSource.1 ≫ t)
                      (associated_groupoid_pullbackComparison_inv_postcompose_owner
                        (p := p) (f := gf) x)
      exact hstrict_mid.trans hstrict_tail
    exact hraw.trans hstrict.symm
  apply Functor.Fiber.hom_ext
  change raw.1 = strict.1
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      gf tail htail _ _ (𝟙 Y') raw.1 strict.1 raw.2 strict.2 hpost

/-- Helper for Lemma 8.5.3: after forgetting the associated overlap map, the only remaining
`pullHom` task is the normalized comparison-conjugated shell around the source `pullHom`. -/
theorem associated_groupoid_cover_forget_pullHom_hom_normalized_shell
    [p.IsFibered] {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
      (fun I : S.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (associated_groupoid_cover_forget_hom
          (J := J) (p := p) S D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      (fibred_morphism_pullbackComparison
          (associated_groupoid_inclusion (p := p)) gf₁ (D.obj I₁)).hom ≫
        (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂) ≫
      (fibred_morphism_pullbackComparison
        (associated_groupoid_inclusion (p := p)) gf₂ (D.obj I₂)).inv := by
  let ι := associated_groupoid_inclusion (p := p)
  let _ := hq
  let FYg := ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor
  let FXg := ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map g.op.toLoc).toFunctor
  let d := D.hom q f₁ f₂ hf₁ hf₂
  let e₁ := fibred_morphism_pullbackComparison ι f₁ (D.obj I₁)
  let e₂ := fibred_morphism_pullbackComparison ι f₂ (D.obj I₂)
  let eg₁ := fibred_morphism_pullbackComparison ι gf₁ (D.obj I₁)
  let eg₂ := fibred_morphism_pullbackComparison ι gf₂ (D.obj I₂)
  let c₁ := fibred_morphism_pullbackComparison ι g
    (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f₁.op.toLoc).toFunctor.obj
      (D.obj I₁))
  let c₂ := fibred_morphism_pullbackComparison ι g
    (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f₂.op.toLoc).toFunctor.obj
      (D.obj I₂))
  let leftTarget :=
    (((canonicalFiberPseudofunctor p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor ι I₁.Y).obj (D.obj I₁)))
  let rightTarget :=
    (((canonicalFiberPseudofunctor p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor ι I₂.Y).obj (D.obj I₂)))
  let leftSource :=
    (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      (D.obj I₁))
  let rightSource :=
    (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      (D.obj I₂))
  have hunfolded :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (associated_groupoid_cover_forget_hom
            (J := J) (p := p) S D q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ =
        leftTarget ≫ FYg.map (e₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y).map d ≫ e₂.inv) ≫
          rightTarget := by
    -- Expand only the comparison-conjugated overlap map before normalizing the three shell pieces.
    rfl
  have hmap :
      FYg.map (e₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y).map d ≫ e₂.inv) =
        FYg.map e₁.hom ≫ FYg.map ((FibredCategoryMor.fiberFunctor ι Y).map d) ≫ FYg.map e₂.inv := by
    -- Split the single mapped threefold composite in the raw shell.
    simpa only [FYg, d, e₁, e₂] using
      functor_map_threefold_comp FYg e₁.hom ((FibredCategoryMor.fiberFunctor ι Y).map d) e₂.inv
  have hleft :
      leftTarget ≫ FYg.map e₁.hom =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫ c₁.inv := by
    -- Normalize the left boundary to the common refinement leg `gf₁`.
    simpa only [leftTarget, leftSource, FYg, eg₁, c₁] using
      associated_groupoid_pullbackComparison_pullHom_left_boundary
        (p := p) (f := f₁) (g := g) (gf := gf₁) (hgf := hgf₁) (x := D.obj I₁)
  have hmid :
      c₁.inv ≫ FYg.map ((FibredCategoryMor.fiberFunctor ι Y).map d) =
        (FibredCategoryMor.fiberFunctor ι Y').map (FXg.map d) ≫ c₂.inv := by
    -- Move the middle overlap morphism across the pullback comparison for the common leg `g`.
    simpa only [FYg, FXg, d, c₁, c₂] using
      (associated_groupoid_pullbackComparison_inv_naturality_over_vertical
        (p := p) (f := g) (φ := d)).symm
  have hright :
      c₂.inv ≫ FYg.map e₂.inv ≫ rightTarget =
        (FibredCategoryMor.fiberFunctor ι Y').map rightSource ≫ eg₂.inv := by
    -- Normalize the symmetric right boundary to the common refinement leg `gf₂`.
    simpa only [FYg, e₂, eg₂, c₂, rightTarget, rightSource] using
      associated_groupoid_pullbackComparison_pullHom_right_boundary
        (p := p) (f := f₂) (g := g) (gf := gf₂) (hgf := hgf₂) (x := D.obj I₂)
  have hfold :
      (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor ι Y').map (FXg.map d) ≫
          (FibredCategoryMor.fiberFunctor ι Y').map rightSource =
        (FibredCategoryMor.fiberFunctor ι Y').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            d g gf₁ gf₂ hgf₁ hgf₂) := by
    -- Fold the three normalized source-side pieces back into the source `pullHom` shell.
    calc
      (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor ι Y').map (FXg.map d) ≫
          (FibredCategoryMor.fiberFunctor ι Y').map rightSource =
        (FibredCategoryMor.fiberFunctor ι Y').map (leftSource ≫ FXg.map d ≫ rightSource) := by
          rw [← Functor.map_comp, ← Functor.map_comp]
      _ =
        (FibredCategoryMor.fiberFunctor ι Y').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            d g gf₁ gf₂ hgf₁ hgf₂) := by
              simpa only [d] using
                congrArg
                  (fun k ↦ (FibredCategoryMor.fiberFunctor ι Y').map k)
                  (show leftSource ≫ FXg.map d ≫ rightSource =
                      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
                        d g gf₁ gf₂ hgf₁ hgf₂ by
                        rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom])
  have hmap' :
      leftTarget ≫ FYg.map (e₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y).map d ≫ e₂.inv) ≫
          rightTarget =
        leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((FibredCategoryMor.fiberFunctor ι Y).map d) ≫
          FYg.map e₂.inv ≫ rightTarget := by
    -- Freeze the two outer transport boundaries while expanding the middle mapped composite.
    calc
      leftTarget ≫ FYg.map (e₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y).map d ≫ e₂.inv) ≫
          rightTarget =
        leftTarget ≫
          (FYg.map e₁.hom ≫ FYg.map ((FibredCategoryMor.fiberFunctor ι Y).map d) ≫ FYg.map e₂.inv) ≫
            rightTarget := by
              exact congrArg (fun k ↦ leftTarget ≫ k ≫ rightTarget) hmap
      _ =
        leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((FibredCategoryMor.fiberFunctor ι Y).map d) ≫
          FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
  have hleft' :
      leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((FibredCategoryMor.fiberFunctor ι Y).map d) ≫
          FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫ c₁.inv ≫
          FYg.map ((FibredCategoryMor.fiberFunctor ι Y).map d) ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Replace the left boundary with the normalized comparison shell over `gf₁`.
    calc
      leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((FibredCategoryMor.fiberFunctor ι Y).map d) ≫
          FYg.map e₂.inv ≫ rightTarget =
        (leftTarget ≫ FYg.map e₁.hom) ≫ FYg.map ((FibredCategoryMor.fiberFunctor ι Y).map d) ≫
          FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
      _ =
        (eg₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫ c₁.inv) ≫
          FYg.map ((FibredCategoryMor.fiberFunctor ι Y).map d) ≫ FYg.map e₂.inv ≫ rightTarget := by
            exact congrArg
              (fun k ↦
                k ≫ FYg.map ((FibredCategoryMor.fiberFunctor ι Y).map d) ≫ FYg.map e₂.inv ≫
                  rightTarget)
              hleft
      _ =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫ c₁.inv ≫
          FYg.map ((FibredCategoryMor.fiberFunctor ι Y).map d) ≫ FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
  have hmid' :
      eg₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫ c₁.inv ≫
          FYg.map ((FibredCategoryMor.fiberFunctor ι Y).map d) ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor ι Y').map (FXg.map d) ≫
          c₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Replace the middle shell with the normalized `g`-transported source overlap map.
    calc
      eg₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫ c₁.inv ≫
          FYg.map ((FibredCategoryMor.fiberFunctor ι Y).map d) ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫
          (c₁.inv ≫ FYg.map ((FibredCategoryMor.fiberFunctor ι Y).map d)) ≫ FYg.map e₂.inv ≫
            rightTarget := by
              simp only [Category.assoc]
      _ =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫
          ((FibredCategoryMor.fiberFunctor ι Y').map (FXg.map d) ≫ c₂.inv) ≫ FYg.map e₂.inv ≫
            rightTarget := by
              exact congrArg
                (fun k ↦
                  eg₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫ k ≫ FYg.map e₂.inv ≫
                    rightTarget)
                hmid
      _ =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor ι Y').map (FXg.map d) ≫
          c₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
  have hright' :
      eg₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor ι Y').map (FXg.map d) ≫
          (c₂.inv ≫ FYg.map e₂.inv ≫ rightTarget) =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor ι Y').map (FXg.map d) ≫
          ((FibredCategoryMor.fiberFunctor ι Y').map rightSource ≫ eg₂.inv) := by
    -- Freeze the normalized left and middle factors while replacing the right boundary shell.
    simpa only [Category.assoc] using
      congrArg
        (fun k ↦
          eg₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫
            (FibredCategoryMor.fiberFunctor ι Y').map (FXg.map d) ≫ k)
        hright
  have hstep_source_flat :
      eg₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor ι Y').map (FXg.map d) ≫
          (FibredCategoryMor.fiberFunctor ι Y').map rightSource ≫ eg₂.inv =
        eg₁.hom ≫
          (FibredCategoryMor.fiberFunctor ι Y').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              d g gf₁ gf₂ hgf₁ hgf₂) ≫
          eg₂.inv := by
    -- After flattening associations, the source shell folds directly by `hfold`.
    calc
      eg₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor ι Y').map (FXg.map d) ≫
          (FibredCategoryMor.fiberFunctor ι Y').map rightSource ≫ eg₂.inv =
        eg₁.hom ≫
          ((FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫
            (FibredCategoryMor.fiberFunctor ι Y').map (FXg.map d) ≫
            (FibredCategoryMor.fiberFunctor ι Y').map rightSource) ≫
          eg₂.inv := by
            simp only [Category.assoc]
      _ =
        eg₁.hom ≫
          (FibredCategoryMor.fiberFunctor ι Y').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              d g gf₁ gf₂ hgf₁ hgf₂) ≫
          eg₂.inv := by
            exact congrArg (fun k ↦ eg₁.hom ≫ k ≫ eg₂.inv) hfold
  have hprefix :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (associated_groupoid_cover_forget_hom
            (J := J) (p := p) S D q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor ι Y').map (FXg.map d) ≫
          c₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Chain the unfolded shell expansion with the flattened left and middle normalization steps.
    exact hunfolded.trans (hmap'.trans (hleft'.trans hmid'))
  exact
    hprefix.trans
      (hright'.trans
        (hstep_source_flat.trans rfl))

/-- Helper for Lemma 8.5.3: after postcomposing the ambient fixed-cover overlap map with the
mapped `I₂`-comparison, the result is the owner normal form built from the forgotten associated
descent datum. -/
private theorem ambient_cover_toDescentData_ofObj_hom_postcompose_comparison
    [p.IsFibered] {U : C} (S : J.Cover U) (x : (stronglyCartesianProjection p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor p).toDescentData (fun I : S.Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).obj x)).hom
        q f₁ f₂ hf₁ hf₂ ≫
      (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
        (fibred_morphism_pullbackComparison
          (associated_groupoid_inclusion (p := p)) I₂.f x).hom) =
    ((((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
          (fibred_morphism_pullbackComparison
            (associated_groupoid_inclusion (p := p)) I₁.f x).hom) ≫
        associated_groupoid_cover_forget_hom
          (J := J) (p := p) S
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).toDescentData
            (fun I : S.Arrow ↦ I.f)).obj x)
          q f₁ f₂ hf₁ hf₂ ≫
      (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
          (fibred_morphism_pullbackComparison
            (associated_groupoid_inclusion (p := p)) I₂.f x).inv)) ≫
        (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
          (fibred_morphism_pullbackComparison
            (associated_groupoid_inclusion (p := p)) I₂.f x).hom) := by
  let ι := associated_groupoid_inclusion (p := p)
  let F₁ := ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor
  let F₂ := ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor
  let D :=
    ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).toDescentData
      (fun I : S.Arrow ↦ I.f)).obj x
  let e₁ := fibred_morphism_pullbackComparison ι I₁.f x
  let e₂ := fibred_morphism_pullbackComparison ι I₂.f x
  let eq₁ := fibred_morphism_pullbackComparison ι f₁ (D.obj I₁)
  let eq₂ := fibred_morphism_pullbackComparison ι f₂ (D.obj I₂)
  let eqq := fibred_morphism_pullbackComparison ι q x
  let leftSource :=
    (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).mapComp'
        I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
        (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x)
  let rightSource :=
    (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).mapComp'
        I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
        (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app x)
  let targetLeft :=
    (((canonicalFiberPseudofunctor p).mapComp'
        I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
        (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor ι U).obj x))
  let targetRight :=
    (((canonicalFiberPseudofunctor p).mapComp'
        I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
        (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor ι U).obj x))
  let core :=
    F₁.map e₁.hom ≫
      associated_groupoid_cover_forget_hom
        (J := J) (p := p) S D q f₁ f₂ hf₁ hf₂
  have hleft_raw :
      eq₁.inv ≫ F₁.map e₁.inv ≫ targetLeft =
        (FibredCategoryMor.fiberFunctor ι Y).map leftSource ≫ eqq.inv := by
    -- Normalize the left leg to the common `q`-comparison shell.
    simpa only [F₁, eq₁, e₁, leftSource, eqq, targetLeft] using
      associated_groupoid_pullbackComparison_pullHom_right_boundary
        (p := p) (f := I₁.f) (g := f₁) (gf := q) (hgf := hf₁) (x := x)
  have hleft_cancel₁ :
      F₁.map e₁.inv ≫ targetLeft =
        eq₁.hom ≫ ((FibredCategoryMor.fiberFunctor ι Y).map leftSource ≫ eqq.inv) := by
    -- Cancel the iterated `f₁`-comparison on the far left.
    exact (Iso.inv_comp_eq eq₁).1 (by simpa only [Category.assoc] using hleft_raw)
  have hleft :
      targetLeft =
        F₁.map e₁.hom ≫ eq₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y).map leftSource ≫ eqq.inv := by
    -- Cancel the mapped `I₁`-comparison to isolate the raw target left leg.
    exact
      (Iso.inv_comp_eq (F₁.mapIso e₁)).1 <| by
        simpa only [Category.assoc] using hleft_cancel₁
  have hright :
      targetRight ≫ F₂.map e₂.hom =
        eqq.hom ≫ (FibredCategoryMor.fiberFunctor ι Y).map rightSource ≫ eq₂.inv := by
    -- Normalize the right leg after the final mapped `I₂`-comparison postcomposition.
    simpa only [F₂, e₂, eqq, rightSource, eq₂] using
      associated_groupoid_pullbackComparison_pullHom_left_boundary
        (p := p) (f := I₂.f) (g := f₂) (gf := q) (hgf := hf₂) (x := x)
  have hq_cancel :
      eqq.inv ≫ eqq.hom ≫ ((FibredCategoryMor.fiberFunctor ι Y).map rightSource ≫ eq₂.inv) =
        (FibredCategoryMor.fiberFunctor ι Y).map rightSource ≫ eq₂.inv := by
    -- The inserted `q`-comparison inverse-hom pair cancels before the frozen right tail.
    calc
      eqq.inv ≫ eqq.hom ≫ ((FibredCategoryMor.fiberFunctor ι Y).map rightSource ≫ eq₂.inv) =
          (eqq.inv ≫ eqq.hom) ≫ ((FibredCategoryMor.fiberFunctor ι Y).map rightSource ≫ eq₂.inv) := by
            simp only [Category.assoc]
      _ = 𝟙 _ ≫ ((FibredCategoryMor.fiberFunctor ι Y).map rightSource ≫ eq₂.inv) := by
            exact congrArg (fun t ↦ t ≫ ((FibredCategoryMor.fiberFunctor ι Y).map rightSource ≫ eq₂.inv))
              eqq.inv_hom_id
      _ = (FibredCategoryMor.fiberFunctor ι Y).map rightSource ≫ eq₂.inv := by
            simp only [Category.id_comp]
  have hcore :
      (((canonicalFiberPseudofunctor p).toDescentData (fun I : S.Arrow ↦ I.f)).obj
            ((FibredCategoryMor.fiberFunctor ι U).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
          F₂.map e₂.hom =
        core := by
    -- Rewrite left and right legs to the common `q`-comparison shell, cancel that shell, and
    -- then fold the mapped source overlap back to the forgotten associated descent datum.
    let lhsOwner :=
      (((canonicalFiberPseudofunctor p).toDescentData (fun I : S.Arrow ↦ I.f)).obj
            ((FibredCategoryMor.fiberFunctor ι U).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
        F₂.map e₂.hom
    have hstart :
        lhsOwner = targetLeft ≫ (targetRight ≫ F₂.map e₂.hom) := by
      calc
        lhsOwner = (targetLeft ≫ targetRight) ≫ F₂.map e₂.hom := by
          rfl
        _ = targetLeft ≫ (targetRight ≫ F₂.map e₂.hom) := by
          simp only [Category.assoc]
    have hstep_right :
        lhsOwner =
          targetLeft ≫
            (eqq.hom ≫ (FibredCategoryMor.fiberFunctor ι Y).map rightSource ≫ eq₂.inv) := by
      exact hstart.trans (congrArg (fun k ↦ targetLeft ≫ k) hright)
    have hstep_left :
        lhsOwner =
          (F₁.map e₁.hom ≫ eq₁.hom ≫ (FibredCategoryMor.fiberFunctor ι Y).map leftSource ≫ eqq.inv) ≫
            (eqq.hom ≫ (FibredCategoryMor.fiberFunctor ι Y).map rightSource ≫ eq₂.inv) := by
      exact hstep_right.trans <|
        congrArg
          (fun k ↦ k ≫ (eqq.hom ≫ (FibredCategoryMor.fiberFunctor ι Y).map rightSource ≫ eq₂.inv))
          hleft
    have hstep_flat :
        lhsOwner =
          F₁.map e₁.hom ≫ eq₁.hom ≫
            ((FibredCategoryMor.fiberFunctor ι Y).map leftSource ≫ eqq.inv ≫ eqq.hom ≫
              (FibredCategoryMor.fiberFunctor ι Y).map rightSource ≫ eq₂.inv) := by
      simpa only [Category.assoc] using hstep_left
    have hstep_cancel :
        lhsOwner =
          F₁.map e₁.hom ≫ eq₁.hom ≫
            ((FibredCategoryMor.fiberFunctor ι Y).map leftSource ≫
              ((FibredCategoryMor.fiberFunctor ι Y).map rightSource ≫ eq₂.inv)) := by
      exact hstep_flat.trans <|
        congrArg
          (fun k ↦
            F₁.map e₁.hom ≫ eq₁.hom ≫ ((FibredCategoryMor.fiberFunctor ι Y).map leftSource ≫ k))
          hq_cancel
    have hstep_map :
        lhsOwner =
          F₁.map e₁.hom ≫ eq₁.hom ≫
            (FibredCategoryMor.fiberFunctor ι Y).map (leftSource ≫ rightSource) ≫ eq₂.inv := by
      have hstep_grouped :
          lhsOwner =
            F₁.map e₁.hom ≫ eq₁.hom ≫
              ((FibredCategoryMor.fiberFunctor ι Y).map leftSource ≫
                (FibredCategoryMor.fiberFunctor ι Y).map rightSource) ≫ eq₂.inv := by
        simpa only [Category.assoc] using hstep_cancel
      exact hstep_grouped.trans <|
        congrArg
          (fun k ↦ F₁.map e₁.hom ≫ eq₁.hom ≫ k ≫ eq₂.inv)
          ((FibredCategoryMor.fiberFunctor ι Y).map_comp leftSource rightSource).symm
    simpa only [lhsOwner, core, D] using hstep_map.trans rfl
  have htail : F₂.map e₂.inv ≫ F₂.map e₂.hom = 𝟙 _ := by
    -- The final mapped `I₂`-comparison pair cancels on the right.
    calc
      F₂.map e₂.inv ≫ F₂.map e₂.hom = F₂.map (e₂.inv ≫ e₂.hom) := by
        rw [← F₂.map_comp]
      _ = F₂.map (𝟙 _) := by
        exact congrArg F₂.map e₂.inv_hom_id
      _ = 𝟙 _ := by
        rw [F₂.map_id]
  have hinsert :
      core =
        ((((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
              (fibred_morphism_pullbackComparison
                (associated_groupoid_inclusion (p := p)) I₁.f x).hom) ≫
            associated_groupoid_cover_forget_hom
              (J := J) (p := p) S D q f₁ f₂ hf₁ hf₂ ≫
            (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
              (fibred_morphism_pullbackComparison
                (associated_groupoid_inclusion (p := p)) I₂.f x).inv)) ≫
          (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
            (fibred_morphism_pullbackComparison
              (associated_groupoid_inclusion (p := p)) I₂.f x).hom) := by
    -- Insert the final mapped inverse-hom identity on the right.
    calc
      core = core ≫ 𝟙 _ := by
        rw [Category.comp_id]
      _ = core ≫ (F₂.map e₂.inv ≫ F₂.map e₂.hom) := by
        exact congrArg (fun k ↦ core ≫ k) htail.symm
      _ = (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom := by
        simp only [Category.assoc]
      _ =
          ((((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
                (fibred_morphism_pullbackComparison
                  (associated_groupoid_inclusion (p := p)) I₁.f x).hom) ≫
              associated_groupoid_cover_forget_hom
                (J := J) (p := p) S D q f₁ f₂ hf₁ hf₂ ≫
              (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
                (fibred_morphism_pullbackComparison
                  (associated_groupoid_inclusion (p := p)) I₂.f x).inv)) ≫
            (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
              (fibred_morphism_pullbackComparison
                (associated_groupoid_inclusion (p := p)) I₂.f x).hom) := by
              simpa only [ι, core, D, F₁, F₂, e₁, e₂, Category.assoc]
  exact hcore.trans hinsert

/-- Helper for Lemma 8.5.3: the ambient fixed-cover overlap map is exactly the conjugate of the
forgotten associated overlap map by the inclusion pullback-comparison isomorphisms. -/
theorem ambient_cover_toDescentData_ofObj_hom_eq_comparison_conjugate
    [p.IsFibered] {U : C} (S : J.Cover U) (x : (stronglyCartesianProjection p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor p).toDescentData (fun I : S.Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).obj x)).hom
        q f₁ f₂ hf₁ hf₂ =
    (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
          (fibred_morphism_pullbackComparison
            (associated_groupoid_inclusion (p := p)) I₁.f x).hom) ≫
        associated_groupoid_cover_forget_hom
          (J := J) (p := p) S
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).toDescentData
            (fun I : S.Arrow ↦ I.f)).obj x)
          q f₁ f₂ hf₁ hf₂ ≫
    (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
          (fibred_morphism_pullbackComparison
            (associated_groupoid_inclusion (p := p)) I₂.f x).inv) := by
  let F₂ := ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor
  let e₂ := fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) I₂.f x
  -- Cancel the final mapped `I₂`-comparison after putting the right-hand side in owner normal form.
  exact
    (Iso.cancel_iso_hom_right _ _ (F₂.mapIso e₂)).1 <| by
      change
        ((((canonicalFiberPseudofunctor p).toDescentData (fun I : S.Arrow ↦ I.f)).obj
              ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).obj x)).hom
            q f₁ f₂ hf₁ hf₂) ≫
            F₂.map e₂.hom =
          ((((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
                (fibred_morphism_pullbackComparison
                  (associated_groupoid_inclusion (p := p)) I₁.f x).hom) ≫
              associated_groupoid_cover_forget_hom
                (J := J) (p := p) S
                (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).toDescentData
                  (fun I : S.Arrow ↦ I.f)).obj x)
                q f₁ f₂ hf₁ hf₂ ≫
              F₂.map e₂.inv) ≫
            F₂.map e₂.hom
      simpa only [F₂, e₂, Category.assoc] using
        ambient_cover_toDescentData_ofObj_hom_postcompose_comparison
          (J := J) (p := p) S x (q := q)
          (I₁ := I₁) (I₂ := I₂)
          (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)

/-- Helper for Lemma 8.5.3: forgetting an associated self-overlap morphism produces the identity. -/
theorem associated_groupoid_cover_forget_hom_self_map_id
    [p.IsFibered] {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
      (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I : S.Arrow} (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y).map
        (D.hom q g g hg hg) =
      𝟙
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y).obj
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map g.op.toLoc).toFunctor.obj
            (D.obj I))) := by
  -- Rewrite the source self-overlap map to the identity before mapping it through the fiber functor.
  calc
    (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y).map
        (D.hom q g g hg hg) =
      (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y).map
        (𝟙
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map g.op.toLoc).toFunctor.obj
            (D.obj I))) := by
          rw [D.hom_self q g hg]
    _ =
      𝟙
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y).obj
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map g.op.toLoc).toFunctor.obj
            (D.obj I))) := by
          exact
            (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y).map_id _

/-- Helper for Lemma 8.5.3: forgetting an associated self-overlap morphism produces the identity. -/
theorem associated_groupoid_cover_forget_hom_self
    [p.IsFibered] {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
      (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I : S.Arrow} (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    associated_groupoid_cover_forget_hom (J := J) (p := p) S D q g g hg hg = 𝟙 _ := by
  let e := fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) g (D.obj I)
  -- Route correction: normalize to the literal comparison-conjugated identity before cancelling.
  calc
    associated_groupoid_cover_forget_hom (J := J) (p := p) S D q g g hg hg =
      e.hom ≫
        (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y).map
          (D.hom q g g hg hg) ≫
        e.inv := by
          rfl
    _ =
      e.hom ≫
        𝟙
          ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y).obj
            (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map g.op.toLoc).toFunctor.obj
              (D.obj I))) ≫
        e.inv := by
          exact
            congrArg
              (fun k ↦ e.hom ≫ k ≫ e.inv)
              (associated_groupoid_cover_forget_hom_self_map_id
                (J := J) (p := p) S D q g hg)
    _ = 𝟙 _ := by
      convert (congrArg (fun k ↦ k ≫ e.inv) (Category.comp_id e.hom)).trans e.hom_inv_id
      · simp only [Category.comp_id]
      · convert Category.id_comp e.inv

/-- Helper for Lemma 8.5.3: transporting the source cocycle relation through the comparison
isomorphisms yields the target cocycle relation for one fixed cover. -/
theorem associated_groupoid_cover_forget_hom_comp
    [p.IsFibered] {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
      (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ I₃ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (hf₃ : f₃ ≫ I₃.f = q := by cat_disch) :
    associated_groupoid_cover_forget_hom (J := J) (p := p) S D q f₁ f₂ hf₁ hf₂ ≫
      associated_groupoid_cover_forget_hom (J := J) (p := p) S D q f₂ f₃ hf₂ hf₃ =
      associated_groupoid_cover_forget_hom (J := J) (p := p) S D q f₁ f₃ hf₁ hf₃ := by
  let F := FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y
  let e₁ := fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f₁ (D.obj I₁)
  let e₂ := fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f₂ (D.obj I₂)
  let e₃ := fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f₃ (D.obj I₃)
  let d₁₂ := D.hom q f₁ f₂ hf₁ hf₂
  let d₂₃ := D.hom q f₂ f₃ hf₂ hf₃
  let d₁₃ := D.hom q f₁ f₃ hf₁ hf₃
  -- Reassociate to the common comparison-conjugated normal form before using the source cocycle.
  have hnormalize :
      associated_groupoid_cover_forget_hom (J := J) (p := p) S D q f₁ f₂ hf₁ hf₂ ≫
          associated_groupoid_cover_forget_hom (J := J) (p := p) S D q f₂ f₃ hf₂ hf₃ =
        e₁.hom ≫ F.map d₁₂ ≫ e₂.inv ≫ e₂.hom ≫ F.map d₂₃ ≫ e₃.inv := by
    change ((e₁.hom ≫ F.map d₁₂ ≫ e₂.inv) ≫ (e₂.hom ≫ F.map d₂₃ ≫ e₃.inv)) =
      e₁.hom ≫ F.map d₁₂ ≫ e₂.inv ≫ e₂.hom ≫ F.map d₂₃ ≫ e₃.inv
    simp only [Category.assoc]
  have hassoc_cancel :
      e₁.hom ≫ F.map d₁₂ ≫ e₂.inv ≫ e₂.hom ≫ F.map d₂₃ ≫ e₃.inv =
        ((e₁.hom ≫ F.map d₁₂) ≫ (e₂.inv ≫ e₂.hom)) ≫ F.map d₂₃ ≫ e₃.inv := by
    simp only [Category.assoc]
  have hcancel₁ :
      ((e₁.hom ≫ F.map d₁₂) ≫ (e₂.inv ≫ e₂.hom)) ≫ F.map d₂₃ ≫ e₃.inv =
        ((e₁.hom ≫ F.map d₁₂) ≫ 𝟙 _) ≫ F.map d₂₃ ≫ e₃.inv := by
    simpa only [F] using
      congrArg
        (fun k ↦ ((e₁.hom ≫ F.map d₁₂) ≫ k) ≫ F.map d₂₃ ≫ e₃.inv)
        e₂.inv_hom_id
  have hcancel₂ :
      ((e₁.hom ≫ F.map d₁₂) ≫ 𝟙 _) ≫ F.map d₂₃ ≫ e₃.inv =
        e₁.hom ≫ F.map d₁₂ ≫ F.map d₂₃ ≫ e₃.inv := by
    simp only [Category.id_comp, Category.assoc]
  have hcancel :
      e₁.hom ≫ F.map d₁₂ ≫ e₂.inv ≫ e₂.hom ≫ F.map d₂₃ ≫ e₃.inv =
        e₁.hom ≫ F.map d₁₂ ≫ F.map d₂₃ ≫ e₃.inv := by
    exact hassoc_cancel.trans (hcancel₁.trans hcancel₂)
  have hmap_comp :
      F.map d₁₂ ≫ F.map d₂₃ = F.map d₁₃ := by
    simpa only [Functor.map_comp, d₁₂, d₂₃, d₁₃] using congrArg F.map
      (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)
  have hassoc_map :
      e₁.hom ≫ F.map d₁₂ ≫ F.map d₂₃ ≫ e₃.inv =
        e₁.hom ≫ (F.map d₁₂ ≫ F.map d₂₃) ≫ e₃.inv := by
    simp only [Category.assoc]
  have hmap :
      e₁.hom ≫ (F.map d₁₂ ≫ F.map d₂₃) ≫ e₃.inv =
        e₁.hom ≫ F.map d₁₃ ≫ e₃.inv := by
    exact congrArg (fun k ↦ e₁.hom ≫ k ≫ e₃.inv) hmap_comp
  have hfinal :
      e₁.hom ≫ F.map d₁₃ ≫ e₃.inv =
        associated_groupoid_cover_forget_hom (J := J) (p := p) S D q f₁ f₃ hf₁ hf₃ := by
    rfl
  exact hnormalize.trans (hcancel.trans (hassoc_map.trans (hmap.trans hfinal)))

/-- Helper for Lemma 8.5.3: a componentwise forgotten morphism of associated descent data is
compatible with the forgotten overlap maps. -/
theorem associated_groupoid_cover_forget_morphism_comm
    [p.IsFibered] {U : C} (S : J.Cover U)
    {D₁ D₂ :
      ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
        (fun I : S.Arrow ↦ I.f))}
    (φ : D₁ ⟶ D₂)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) I₁.Y).map
          (φ.hom I₁))) ≫
      associated_groupoid_cover_forget_hom (J := J) (p := p) S D₂ q f₁ f₂ hf₁ hf₂ =
      associated_groupoid_cover_forget_hom (J := J) (p := p) S D₁ q f₁ f₂ hf₁ hf₂ ≫
    (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
          ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) I₂.Y).map
            (φ.hom I₂))) := by
  let F := FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) Y
  let α₁ :=
    ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) I₁.Y).map (φ.hom I₁))
  let α₂ :=
    ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) I₂.Y).map (φ.hom I₂))
  let β₁ :=
    F.map
      (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f₁.op.toLoc).toFunctor.map
        (φ.hom I₁))
  let β₂ :=
    F.map
      (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f₂.op.toLoc).toFunctor.map
        (φ.hom I₂))
  let e₁₁ := fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f₁ (D₁.obj I₁)
  let e₁₂ := fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f₁ (D₂.obj I₁)
  let e₂₁ := fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f₂ (D₁.obj I₂)
  let e₂₂ := fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f₂ (D₂.obj I₂)
  let d₁ := D₁.hom q f₁ f₂ hf₁ hf₂
  let d₂ := D₂.hom q f₁ f₂ hf₁ hf₂
  have hleft :
      α₁ ≫ e₁₂.hom = e₁₁.hom ≫ β₁ := by
    -- Transport the left comparison shell across the forgotten vertical morphism.
    simpa only [α₁, β₁, e₁₁, e₁₂] using
      associated_groupoid_pullbackComparison_naturality_over_vertical
        (p := p) (f := f₁) (φ := φ.hom I₁)
  have hmid :
      β₁ ≫ F.map (D₂.hom q f₁ f₂ hf₁ hf₂) =
        F.map (D₁.hom q f₁ f₂ hf₁ hf₂) ≫ β₂ := by
    -- The middle square is exactly the source compatibility of `φ`, mapped into the ambient fiber.
    simpa only [β₁, β₂, F, Functor.map_comp] using
      congrArg F.map (φ.comm q f₁ f₂ hf₁ hf₂)
  have hright :
      β₂ ≫ e₂₂.inv = e₂₁.inv ≫ α₂ := by
    -- Transport the right comparison inverse across the forgotten vertical morphism.
    simpa only [α₂, β₂, e₂₁, e₂₂] using
      associated_groupoid_pullbackComparison_inv_naturality_over_vertical
        (p := p) (f := f₂) (φ := φ.hom I₂)
  -- Rewrite into the shared comparison-conjugated normal form and use `φ.comm` in the middle.
  have hnormalize_left :
      α₁ ≫ associated_groupoid_cover_forget_hom (J := J) (p := p) S D₂ q f₁ f₂ hf₁ hf₂ =
        (α₁ ≫ e₁₂.hom) ≫ F.map d₂ ≫ e₂₂.inv := by
    change α₁ ≫ (e₁₂.hom ≫ F.map d₂ ≫ e₂₂.inv) =
      (α₁ ≫ e₁₂.hom) ≫ F.map d₂ ≫ e₂₂.inv
    simp only [Category.assoc]
  have hleft' :
      (α₁ ≫ e₁₂.hom) ≫ F.map d₂ ≫ e₂₂.inv =
        (e₁₁.hom ≫ β₁) ≫ F.map d₂ ≫ e₂₂.inv := by
    exact congrArg (fun k ↦ k ≫ F.map d₂ ≫ e₂₂.inv) hleft
  have hassoc_left :
      (e₁₁.hom ≫ β₁) ≫ F.map d₂ ≫ e₂₂.inv =
        e₁₁.hom ≫ (β₁ ≫ F.map d₂) ≫ e₂₂.inv := by
    simp only [Category.assoc]
  have hmid' :
      e₁₁.hom ≫ (β₁ ≫ F.map d₂) ≫ e₂₂.inv =
        e₁₁.hom ≫ (F.map d₁ ≫ β₂) ≫ e₂₂.inv := by
    exact congrArg (fun k ↦ e₁₁.hom ≫ k ≫ e₂₂.inv) hmid
  have hassoc_mid :
      e₁₁.hom ≫ (F.map d₁ ≫ β₂) ≫ e₂₂.inv =
        e₁₁.hom ≫ F.map d₁ ≫ (β₂ ≫ e₂₂.inv) := by
    simp only [Category.assoc]
  have hright' :
      e₁₁.hom ≫ F.map d₁ ≫ (β₂ ≫ e₂₂.inv) =
        e₁₁.hom ≫ F.map d₁ ≫ (e₂₁.inv ≫ α₂) := by
    exact congrArg (fun k ↦ e₁₁.hom ≫ F.map d₁ ≫ k) hright
  have hnormalize_right :
      e₁₁.hom ≫ F.map d₁ ≫ (e₂₁.inv ≫ α₂) =
        associated_groupoid_cover_forget_hom (J := J) (p := p) S D₁ q f₁ f₂ hf₁ hf₂ ≫ α₂ := by
    change e₁₁.hom ≫ F.map d₁ ≫ (e₂₁.inv ≫ α₂) =
      (e₁₁.hom ≫ F.map d₁ ≫ e₂₁.inv) ≫ α₂
    simp only [Category.assoc]
  exact
    hnormalize_left.trans
      (hleft'.trans (hassoc_left.trans (hmid'.trans (hassoc_mid.trans (hright'.trans hnormalize_right)))))

end

end CategoryTheory
