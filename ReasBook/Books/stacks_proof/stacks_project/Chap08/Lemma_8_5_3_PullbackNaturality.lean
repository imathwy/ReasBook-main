import StacksProject_2024.Chap08.Lemma_8_5_3_Bridge

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

open BasedFunctor Functor IsStronglyCartesian

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/-- Helper for Lemma 8.5.3: the chosen pullback functor carries vertical morphisms to vertical
morphisms in the fiber over the domain. -/
theorem canonical_pullbackFunctor_map_fac
    {T : Type*} [Category T] (q : T ⥤ C) [q.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : q.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor q).map f.op.toLoc).toFunctor.map φ)).1 ≫
        (canonicalPullbackChoice q).map f y =
      (canonicalPullbackChoice q).map f x ≫ φ.1 := by
  -- Compare the chosen pullback of `y` with the factorization induced by `φ`.
  letI : q.IsHomLift (𝟙 U) φ.1 := φ.2
  have hpull : q.IsStronglyCartesian f ((canonicalPullbackChoice q).map f x) :=
    (canonicalPullbackChoice q).isStronglyCartesian f x
  letI : q.IsHomLift f ((canonicalPullbackChoice q).map f x) := hpull.toIsHomLift
  letI : q.IsHomLift f ((canonicalPullbackChoice q).map f x ≫ φ.1) :=
    IsHomLift.comp_lift_id_right' q f ((canonicalPullbackChoice q).map f x) U φ.1
  letI : q.IsStronglyCartesian f ((canonicalPullbackChoice q).map f y) :=
    (canonicalPullbackChoice q).isStronglyCartesian f y
  change
      IsStronglyCartesian.map q f ((canonicalPullbackChoice q).map f y)
        (Category.id_comp f).symm
        ((canonicalPullbackChoice q).map f x ≫ φ.1) ≫
          (canonicalPullbackChoice q).map f y =
        (canonicalPullbackChoice q).map f x ≫ φ.1
  exact
    IsStronglyCartesian.fac q f ((canonicalPullbackChoice q).map f y)
      (Category.id_comp f).symm
      ((canonicalPullbackChoice q).map f x ≫ φ.1)

/-- Helper for Lemma 8.5.3: composing two arrows in `C` and then passing to the locally discrete
opposite is the same as composing their `toLoc` images in the owner order used by `pullHom`. -/
theorem comp_toLoc_eq
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf) :
    f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc := by
  -- Translate the composite equality to the locally discrete opposite.
  simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
    congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hgf)

/-- Helper for Lemma 8.5.3: the hom component of the flexible pullback-composition comparison for
the canonical fiber pseudofunctor satisfies the same factorization identity as the chosen
pullback-composition comparison. -/
theorem canonicalFiberPseudofunctor_mapComp'_hom_app_fac
    {T : Type*} [Category T] (q : T ⥤ C) [q.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf)
    (x : q.Fiber D) :
    (((canonicalFiberPseudofunctor q).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x).1 ≫
        (canonicalPullbackChoice q).map g
          (((canonicalFiberPseudofunctor q).map f.op.toLoc).toFunctor.obj x) ≫
        (canonicalPullbackChoice q).map f x =
      (canonicalPullbackChoice q).map gf x := by
  -- Reduce the flexible comparison to the strict composite-leg comparison from the chosen
  -- pullback structure.
  subst gf
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp] using
    (canonicalPullbackChoice q).pullbackCompComponentIso_fac f g x

/-- Helper for Lemma 8.5.3: the inverse component of the flexible pullback-composition comparison
for the canonical fiber pseudofunctor factors the composite pullback arrow through the iterated
chosen pullback arrows. -/
theorem canonicalFiberPseudofunctor_mapComp'_inv_app_fac
    {T : Type*} [Category T] (q : T ⥤ C) [q.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf)
    (x : q.Fiber D) :
    (((canonicalFiberPseudofunctor q).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app x).1 ≫
        (canonicalPullbackChoice q).map gf x =
      (canonicalPullbackChoice q).map g
          (((canonicalFiberPseudofunctor q).map f.op.toLoc).toFunctor.obj x) ≫
        (canonicalPullbackChoice q).map f x := by
  -- Read the same comparison component in the inverse direction.
  subst gf
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp] using
    (canonicalPullbackChoice q).pullbackCompComponentIso_inv_fac f g x

/-- Helper for Lemma 8.5.3: a functor maps a visible threefold composite to the corresponding
threefold composite of mapped arrows. -/
theorem functor_map_threefold_comp
    {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    {W X Y Z : D} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    F.map (f ≫ g ≫ h) = F.map f ≫ F.map g ≫ F.map h := by
  -- Split the threefold composite into the two binary functoriality steps.
  rw [Functor.map_comp, Functor.map_comp]

/-- Helper for Lemma 8.5.3: mapping the source pullback factorization identity through the
associated-groupoid inclusion preserves the same factorization in the ambient total category. -/
private theorem associated_groupoid_map_canonical_pullbackFunctor_map_fac
    [p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : (stronglyCartesianProjection p).Fiber U} (φ : x ⟶ y) :
    (associated_groupoid_inclusion (p := p)).toHom.map
        ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) ≫
      (associated_groupoid_inclusion (p := p)).toHom.map φ.1 =
    (associated_groupoid_inclusion (p := p)).toHom.map
          ((((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map
              φ).1) ≫
        (associated_groupoid_inclusion (p := p)).toHom.map
          ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f y) := by
  let ι := associated_groupoid_inclusion (p := p)
  rw [← Functor.map_comp, ← Functor.map_comp]
  have hfac :
      ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) ≫ φ.1 =
        ((((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map
            φ).1) ≫
          (canonicalPullbackChoice (stronglyCartesianProjection p)).map f y := by
    exact
      (canonical_pullbackFunctor_map_fac
        (q := stronglyCartesianProjection p) (f := f) (x := x) (y := y) (φ := φ)).symm
  exact congrArg (fun k ↦ ι.toHom.map k) hfac

/-- Helper for Lemma 8.5.3: the hom-side pullback comparison for the inclusion is identified by
postcomposing with the chosen ambient strongly-cartesian pullback arrow. -/
theorem associated_groupoid_pullbackComparison_hom_postcompose
    [p.IsFibered] {U V : C} (f : V ⟶ U)
    (x : (stronglyCartesianProjection p).Fiber U) :
    (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f x).hom.1 ≫
        (associated_groupoid_inclusion (p := p)).toHom.map
          ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) =
      (canonicalPullbackChoice p).map f
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).obj x) := by
  exact
    fibred_morphism_pullbackComparison_hom_postcompose
      (F := associated_groupoid_inclusion (p := p)) (f := f) (x := x)

/-- Helper for Lemma 8.5.3: after postcomposing both candidate inclusion-comparison composites
with the common ambient pullback arrow, the owner-level composites agree. -/
theorem associated_groupoid_pullbackComparison_hom_postcompose_eq
    [p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : (stronglyCartesianProjection p).Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).map φ))).1 ≫
        (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f y).hom.1 ≫
        (associated_groupoid_inclusion (p := p)).toHom.map
          ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f y) =
      (((fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f x).hom.1 ≫
          ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) V).map
            (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ)).1) ≫
        (associated_groupoid_inclusion (p := p)).toHom.map
          ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f y)) := by
  let ι := associated_groupoid_inclusion (p := p)
  let lhs :=
    ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor ι U).map φ))).1 ≫
      (fibred_morphism_pullbackComparison ι f y).hom.1 ≫
      ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f y)
  let mid₁ :=
    ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor ι U).map φ))).1 ≫
      (canonicalPullbackChoice p).map f ((FibredCategoryMor.fiberFunctor ι U).obj y)
  let mid₂ :=
    (canonicalPullbackChoice p).map f ((FibredCategoryMor.fiberFunctor ι U).obj x) ≫
      ((FibredCategoryMor.fiberFunctor ι U).map φ).1
  let mid₃ :=
    ((fibred_morphism_pullbackComparison ι f x).hom.1 ≫
        ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x)) ≫
      ((FibredCategoryMor.fiberFunctor ι U).map φ).1
  let mid₄ :=
    (fibred_morphism_pullbackComparison ι f x).hom.1 ≫
      ((FibredCategoryMor.fiberFunctor ι V).map
        (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ)).1 ≫
      ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f y)
  let rhs :=
    ((fibred_morphism_pullbackComparison ι f x).hom.1 ≫
        ((FibredCategoryMor.fiberFunctor ι V).map
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ)).1) ≫
      ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f y)
  have h₁ : lhs = mid₁ := by
    exact
      congrArg
        (fun k ↦
          ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
              ((FibredCategoryMor.fiberFunctor ι U).map φ))).1 ≫ k)
        (associated_groupoid_pullbackComparison_hom_postcompose (p := p) f y)
  have h₂ : mid₁ = mid₂ := by
    change
      ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
          ((FibredCategoryMor.fiberFunctor ι U).map φ))).1 ≫
          (canonicalPullbackChoice p).map f ((FibredCategoryMor.fiberFunctor ι U).obj y) =
        (canonicalPullbackChoice p).map f ((FibredCategoryMor.fiberFunctor ι U).obj x) ≫
          ((FibredCategoryMor.fiberFunctor ι U).map φ).1
    exact canonical_pullbackFunctor_map_fac (q := p) f ((FibredCategoryMor.fiberFunctor ι U).map φ)
  have h₃ : mid₂ = mid₃ := by
    exact
      (congrArg
        (fun k ↦ k ≫ ((FibredCategoryMor.fiberFunctor ι U).map φ).1)
        (associated_groupoid_pullbackComparison_hom_postcompose (p := p) f x)).symm
  have h₄ : mid₃ = mid₄ := by
    calc
      (((fibred_morphism_pullbackComparison ι f x).hom.1 ≫
          ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x)) ≫
        ((FibredCategoryMor.fiberFunctor ι U).map φ).1) =
          (fibred_morphism_pullbackComparison ι f x).hom.1 ≫
            (ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) ≫
              ((FibredCategoryMor.fiberFunctor ι U).map φ).1) := by
            rw [Category.assoc]
      _ =
          (fibred_morphism_pullbackComparison ι f x).hom.1 ≫
            (ι.toHom.map
                ((((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ)).1 ≫
              ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f y)) := by
            exact
              congrArg
                (fun k ↦ (fibred_morphism_pullbackComparison ι f x).hom.1 ≫ k)
                (associated_groupoid_map_canonical_pullbackFunctor_map_fac
                  (p := p) (f := f) (φ := φ))
      _ =
          (fibred_morphism_pullbackComparison ι f x).hom.1 ≫
            ((FibredCategoryMor.fiberFunctor ι V).map
              (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ)).1 ≫
            ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f y) := by
            rfl
  have h₅ : mid₄ = rhs := by
    exact (Category.assoc _ _ _).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- Helper for Lemma 8.5.3: the inclusion pullback-comparison isomorphism is fiberwise natural
with respect to vertical morphisms in the associated groupoid projection. -/
private theorem associated_groupoid_pullbackComparison_hom_naturality_over_vertical
    [p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : (stronglyCartesianProjection p).Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).map φ))).1 ≫
      (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f y).hom.1 =
        (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f x).hom.1 ≫
          ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) V).map
            (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ)).1 := by
  let ι := associated_groupoid_inclusion (p := p)
  let ex := fibred_morphism_pullbackComparison ι f x
  let ey := fibred_morphism_pullbackComparison ι f y
  let η :
      ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj
          ((FibredCategoryMor.fiberFunctor ι U).obj x) ⟶
        ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj
          ((FibredCategoryMor.fiberFunctor ι U).obj y) :=
    ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor ι U).map φ)
  let θ :
      (FibredCategoryMor.fiberFunctor ι V).obj
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj x) ⟶
        (FibredCategoryMor.fiberFunctor ι V).obj
          (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.obj y) :=
    (FibredCategoryMor.fiberFunctor ι V).map
      (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ)
  let hcA := canonicalPullbackChoice (stronglyCartesianProjection p)
  let φF :
      ((FibredCategoryMor.fiberFunctor ι V).obj (f ^*[hcA] y)).1 ⟶
        ((FibredCategoryMor.fiberFunctor ι U).obj y).1 :=
    ι.toHom.map (hcA.map f y)
  have hφF : p.IsStronglyCartesian f φF := by
    change p.IsStronglyCartesian f (ι.toHom.map (hcA.map f y))
    exact
      associated_groupoid_inclusion_map_stronglyCartesian_of_lift
        (p := p) f (hcA.map f y) (hcA.isStronglyCartesian f y)
  letI : p.IsStronglyCartesian f φF := hφF
  letI : p.IsHomLift (𝟙 V) η.1 := by
    exact η.2
  letI : p.IsHomLift (𝟙 V) θ.1 := by
    exact θ.2
  letI : p.IsHomLift (𝟙 V) ex.hom.1 := ex.hom.2
  letI : p.IsHomLift (𝟙 V) ey.hom.1 := ey.hom.2
  letI : p.IsHomLift (𝟙 V) (η.1 ≫ ey.hom.1) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ p _ _ _ _ _
      (𝟙 V) η.1 η.2 V ey.hom.1 ey.hom.2
  letI : p.IsHomLift (𝟙 V) (ex.hom.1 ≫ θ.1) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ p _ _ _ _ _
      (𝟙 V) ex.hom.1 ex.hom.2 V θ.1 θ.2
  have hcomp :
      η.1 ≫ ey.hom.1 ≫ φF = (ex.hom.1 ≫ θ.1) ≫ φF := by
    simpa only [η, θ, φF, Category.assoc] using
      associated_groupoid_pullbackComparison_hom_postcompose_eq
        (p := p) (f := f) (φ := φ)
  have hηey : p.IsHomLift (𝟙 V) (η.1 ≫ ey.hom.1) := by infer_instance
  have hexθ : p.IsHomLift (𝟙 V) (ex.hom.1 ≫ θ.1) := by infer_instance
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      f φF inferInstance _ _ (𝟙 V) (η.1 ≫ ey.hom.1) (ex.hom.1 ≫ θ.1) hηey hexθ <| by
        rw [Category.assoc]
        exact hcomp

/-- Helper for Lemma 8.5.3: the inclusion pullback-comparison isomorphism is fiberwise natural
with respect to vertical morphisms in the associated groupoid projection. -/
theorem associated_groupoid_pullbackComparison_naturality_over_vertical
    [p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : (stronglyCartesianProjection p).Fiber U} (φ : x ⟶ y) :
    (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).map φ)) ≫
      (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f y).hom =
        (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f x).hom ≫
          (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) V).map
            (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ) := by
  -- Project the owner-level equality back into the fiber.
  apply Functor.Fiber.hom_ext
  exact associated_groupoid_pullbackComparison_hom_naturality_over_vertical
    (p := p) f φ

/-- Helper for Lemma 8.5.3: the inverse inclusion pullback-comparison isomorphism rewrites the
right comparison inverse into the exact form needed by the fixed-cover transport shell. -/
theorem associated_groupoid_pullbackComparison_inv_naturality_over_vertical
    [p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : (stronglyCartesianProjection p).Fiber U} (φ : x ⟶ y) :
    (FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) V).map
        (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ) ≫
      (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f y).inv =
        (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f x).inv ≫
          (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
            ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).map φ)) := by
  let ι := associated_groupoid_inclusion (p := p)
  let ex := fibred_morphism_pullbackComparison ι f x
  let ey := fibred_morphism_pullbackComparison ι f y
  let η :=
    ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor ι U).map φ)
  let θ :=
    (FibredCategoryMor.fiberFunctor ι V).map
      (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ)
  have hhom :
      η ≫ ey.hom = ex.hom ≫ θ := by
    simpa only [ex, ey, η, θ] using
      associated_groupoid_pullbackComparison_naturality_over_vertical
        (p := p) (f := f) (φ := φ)
  symm
  apply (Iso.eq_comp_inv ey).2
  -- Precompose by `ex.inv` so the left comparison isomorphism cancels.
  have hpre :
      ex.inv ≫
          ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
              ((FibredCategoryMor.fiberFunctor ι U).map φ)) ≫ ey.hom) =
        ex.inv ≫
          (ex.hom ≫
            (FibredCategoryMor.fiberFunctor ι V).map
              (((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).map f.op.toLoc).toFunctor.map φ)) := by
    exact congrArg (fun k ↦ ex.inv ≫ k) hhom
  simpa only [← Category.assoc, ex.inv_hom_id, Category.id_comp] using hpre

/-- Helper for Lemma 8.5.3: the inverse inclusion pullback-comparison identifies the chosen
ambient pullback arrow with the image of the chosen pullback arrow in the associated groupoid. -/
theorem associated_groupoid_pullbackComparison_inv_postcompose_owner
    [p.IsFibered] {U V : C} (f : V ⟶ U)
    (x : (stronglyCartesianProjection p).Fiber U) :
    (fibred_morphism_pullbackComparison (associated_groupoid_inclusion (p := p)) f x).inv.1 ≫
        (canonicalPullbackChoice p).map f
          ((FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U).obj x) =
      (associated_groupoid_inclusion (p := p)).toHom.map
        ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) := by
  let ι := associated_groupoid_inclusion (p := p)
  let e := fibred_morphism_pullbackComparison ι f x
  have h :=
    congrArg
      (fun k ↦ e.inv.1 ≫ k)
      (associated_groupoid_pullbackComparison_hom_postcompose (p := p) f x)
  have hcancel : e.inv.1 ≫ e.hom.1 = 𝟙 _ :=
    congrArg (fun k ↦ k.1) e.inv_hom_id
  have h' :
      e.inv.1 ≫
          (canonicalPullbackChoice p).map f ((FibredCategoryMor.fiberFunctor ι U).obj x) =
        e.inv.1 ≫ e.hom.1 ≫
          ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) := by
    exact h.symm
  have hassoc :
      e.inv.1 ≫ e.hom.1 ≫
          ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) =
        (e.inv.1 ≫ e.hom.1) ≫
          ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) := by
    rw [← Category.assoc]
  have hfinal :
      (e.inv.1 ≫ e.hom.1) ≫
          ι.toHom.map ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) =
        (associated_groupoid_inclusion (p := p)).toHom.map
          ((canonicalPullbackChoice (stronglyCartesianProjection p)).map f x) := by
      rw [hcancel, Category.id_comp]
      rfl
  exact h'.trans <| hassoc.trans hfinal

end

end CategoryTheory
