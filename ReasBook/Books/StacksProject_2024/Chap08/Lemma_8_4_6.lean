import stacks_project.Chap04.Lemma_4_31_7
import stacks_project.Chap04.Lemma_4_32_5
import stacks_project.Chap04.Lemma_4_33_10
import stacks_project.Chap04.Lemma_4_35_7
import stacks_project.Chap08.Definition_8_4_1
import stacks_project.Chap08.Definition_8_4_5
import stacks_project.Chap08.Lemma_8_4_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open CategoryTheory.Limits
open InducedCategory.Hom
open CategoricalPullback
open scoped CategoricalPullback

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y S : StackOver J}

/-- Helper for Lemma 8.4.6: the explicit stack-level `2`-fibre product projection is already
fibred, so the coverwise criterion from Lemma `8.4.2` applies directly to its canonical descent
functors. -/
private theorem stack_two_fibre_product_projection_isFibered
    (F : X ⟶ S) (G : Y ⟶ S) :
    (FibredCategoryOver.twoFibreProduct (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered :=
  FibredCategoryOver.isFibred
    (X := FibredCategoryOver.twoFibreProduct (toFibredCategoryMor F) (toFibredCategoryMor G))

section

variable {Xf Yf : FibredCategoryOver C}

attribute [local instance] FibredCategoryOver.isFibred

namespace FibredCategoryMor

/-- Helper for Lemma 8.4.6: a morphism of fibred categories carries a strongly cartesian lift
over `f` to a strongly cartesian lift over the same base arrow in the target. -/
theorem map_stronglyCartesian_of_lift
    (F : Xf ⟶ Yf) {a b : Xf.S} {U V : C} (f : V ⟶ U) (φ : a ⟶ b)
    (hφ : Xf.p.IsStronglyCartesian f φ) :
    Yf.p.IsStronglyCartesian f (F.toHom.map φ) := by
  -- Normalize the source lift to the projected base arrow before invoking the owner API.
  letI : Xf.p.IsHomLift f φ := hφ.toIsHomLift
  have hφ' : Xf.p.IsStronglyCartesian (Xf.p.map φ) φ := by
    subst_hom_lift Xf.p f φ
    simpa using hφ
  letI : Yf.p.IsHomLift f (F.toHom.map φ) := by
    infer_instance
  have hY :
      Yf.p.IsStronglyCartesian (Yf.p.map (F.toHom.map φ)) (F.toHom.map φ) :=
    FibredCategoryMor.map_stronglyCartesian F φ hφ'
  -- Transport the target statement back to the original base arrow `f`.
  subst_hom_lift Yf.p f (F.toHom.map φ)
  exact hY

/-- Helper for Lemma 8.4.6: a morphism of fibred categories admits the canonical comparison
isomorphism between pulling back after mapping and mapping after pulling back. -/
theorem pullbackComparison_exists
    (F : Xf ⟶ Yf) {U V : C} (f : V ⟶ U) (x : Xf.p.Fiber U) :
    ∃ e :
      f ^*[canonicalPullbackChoice Yf.p] ((F.toHom).fiberFunctor U).obj x ≅
        ((F.toHom).fiberFunctor V).obj (f ^*[canonicalPullbackChoice Xf.p] x),
      e.hom.1 ≫ F.toHom.map ((canonicalPullbackChoice Xf.p).map f x) =
        (canonicalPullbackChoice Yf.p).map f (((F.toHom).fiberFunctor U).obj x) := by
  let hcX := canonicalPullbackChoice Xf.p
  let hcY := canonicalPullbackChoice Yf.p
  let φ :
      (((F.toHom).fiberFunctor V).obj (f ^*[hcX] x)).1 ⟶
        (((F.toHom).fiberFunctor U).obj x).1 :=
    F.toHom.map (hcX.map f x)
  let ψ :
      (f ^*[hcY] (((F.toHom).fiberFunctor U).obj x)).1 ⟶
        (((F.toHom).fiberFunctor U).obj x).1 :=
    hcY.map f (((F.toHom).fiberFunctor U).obj x)
  have hφ : Yf.p.IsStronglyCartesian f φ :=
    FibredCategoryMor.map_stronglyCartesian_of_lift F f (hcX.map f x)
      (hcX.isStronglyCartesian f x)
  have hψ : Yf.p.IsStronglyCartesian f ψ :=
    hcY.isStronglyCartesian f (((F.toHom).fiberFunctor U).obj x)
  have hf : f = (Iso.refl V).hom ≫ f := by
    simp
  let e :
      (f ^*[hcY] (((F.toHom).fiberFunctor U).obj x)).1 ≅
        (((F.toHom).fiberFunctor V).obj (f ^*[hcX] x)).1 :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso Yf.p hf φ ψ
  letI : Yf.p.IsHomLift (𝟙 V) e.hom := by
    -- The comparison hom lies over the identity of the pullback base.
    change Yf.p.IsHomLift (Iso.refl V).hom e.hom
    exact Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift Yf.p hf φ ψ
  letI : Yf.p.IsHomLift (𝟙 V) e.inv := by
    -- The inverse component is vertical for the same reason.
    change Yf.p.IsHomLift (Iso.refl V).inv e.inv
    exact Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift Yf.p hf φ ψ
  let ehom :
      f ^*[hcY] (((F.toHom).fiberFunctor U).obj x) ⟶
        ((F.toHom).fiberFunctor V).obj (f ^*[hcX] x) :=
    Functor.Fiber.homMk Yf.p V e.hom
  let einv :
      ((F.toHom).fiberFunctor V).obj (f ^*[hcX] x) ⟶
        f ^*[hcY] (((F.toHom).fiberFunctor U).obj x) :=
    Functor.Fiber.homMk Yf.p V e.inv
  have hhom_inv : ehom ≫ einv = 𝟙 _ := by
    -- Forget the fiber packaging and use the inverse law of the owner comparison iso.
    apply Functor.Fiber.hom_ext
    change e.hom ≫ e.inv = 𝟙 _
    exact e.hom_inv_id
  have hinv_hom : einv ≫ ehom = 𝟙 _ := by
    -- The second inverse law is identical after forgetting the fiber wrapper.
    apply Functor.Fiber.hom_ext
    change e.inv ≫ e.hom = 𝟙 _
    exact e.inv_hom_id
  let eFiber :
      f ^*[hcY] (((F.toHom).fiberFunctor U).obj x) ≅
        ((F.toHom).fiberFunctor V).obj (f ^*[hcX] x) :=
    { hom := ehom
      inv := einv
      hom_inv_id := hhom_inv
      inv_hom_id := hinv_hom }
  refine ⟨eFiber, ?_⟩
  -- Read off the defining factorization identity from the owner comparison construction.
  change (Functor.IsStronglyCartesian.domainIsoOfBaseIso Yf.p hf φ ψ).hom ≫ φ = ψ
  rw [Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
  exact Functor.IsStronglyCartesian.fac Yf.p f φ hf ψ

/-- Helper for Lemma 8.4.6: the chosen canonical comparison identifies the pullback of `F(x)`
with the image under `F` of the chosen pullback of `x`. -/
noncomputable def pullbackComparison
    (F : Xf ⟶ Yf) {U V : C} (f : V ⟶ U) (x : Xf.p.Fiber U) :
    f ^*[canonicalPullbackChoice Yf.p] ((F.toHom).fiberFunctor U).obj x ≅
      ((F.toHom).fiberFunctor V).obj (f ^*[canonicalPullbackChoice Xf.p] x) :=
  Classical.choose (pullbackComparison_exists F f x)

/-- Helper for Lemma 8.4.6: postcomposing the hom part of the pullback-comparison isomorphism
with the image of the chosen source pullback arrow recovers the chosen target pullback arrow. -/
theorem pullbackComparison_hom_postcompose
    (F : Xf ⟶ Yf) {U V : C} (f : V ⟶ U) (x : Xf.p.Fiber U) :
    (pullbackComparison F f x).hom.1 ≫
        F.toHom.map ((canonicalPullbackChoice Xf.p).map f x) =
      (canonicalPullbackChoice Yf.p).map f (((F.toHom).fiberFunctor U).obj x) := by
  -- Unfold the chosen comparison only to expose the factorization identity proved above.
  change (Classical.choose (pullbackComparison_exists F f x)).hom.1 ≫
      F.toHom.map ((canonicalPullbackChoice Xf.p).map f x) =
    (canonicalPullbackChoice Yf.p).map f (((F.toHom).fiberFunctor U).obj x)
  exact Classical.choose_spec (pullbackComparison_exists F f x)

/-- Helper for Lemma 8.4.6: postcomposing the inverse comparison morphism with the chosen target
pullback arrow recovers the image of the chosen source pullback arrow. -/
private theorem pullbackComparison_inv_postcompose_owner
    (F : Xf ⟶ Yf) {U V : C} (f : V ⟶ U) (x : Xf.p.Fiber U) :
    (pullbackComparison F f x).inv.1 ≫
        (canonicalPullbackChoice Yf.p).map f (((F.toHom).fiberFunctor U).obj x) =
      F.toHom.map ((canonicalPullbackChoice Xf.p).map f x) := by
  -- Cancel the comparison isomorphism against its hom component before reading off the source map.
  have hid :
      (pullbackComparison F f x).inv.1 ≫ (pullbackComparison F f x).hom.1 =
        𝟙 ((((F.toHom).fiberFunctor V).obj
          (f ^*[canonicalPullbackChoice Xf.p] x)).1) := by
    exact congrArg (fun k ↦ k.1) (pullbackComparison F f x).inv_hom_id
  have hid_postcompose :
      ((pullbackComparison F f x).inv.1 ≫ (pullbackComparison F f x).hom.1) ≫
          F.toHom.map ((canonicalPullbackChoice Xf.p).map f x) =
        F.toHom.map ((canonicalPullbackChoice Xf.p).map f x) := by
    rw [hid, Category.id_comp]
    rfl
  have hcompose :
      (pullbackComparison F f x).inv.1 ≫
          (canonicalPullbackChoice Yf.p).map f (((F.toHom).fiberFunctor U).obj x) =
        ((pullbackComparison F f x).inv.1 ≫ (pullbackComparison F f x).hom.1) ≫
          F.toHom.map ((canonicalPullbackChoice Xf.p).map f x) := by
    -- Rewrite the target pullback arrow through the postcomposition identity of the hom component.
    calc
      (pullbackComparison F f x).inv.1 ≫
          (canonicalPullbackChoice Yf.p).map f (((F.toHom).fiberFunctor U).obj x) =
        (pullbackComparison F f x).inv.1 ≫
          ((pullbackComparison F f x).hom.1 ≫
            F.toHom.map ((canonicalPullbackChoice Xf.p).map f x)) := by
          rw [(pullbackComparison_hom_postcompose F f x).symm]
          rfl
      _ =
        ((pullbackComparison F f x).inv.1 ≫ (pullbackComparison F f x).hom.1) ≫
          F.toHom.map ((canonicalPullbackChoice Xf.p).map f x) := by
          exact (Category.assoc _ _ _).symm
  exact hcompose.trans hid_postcompose

end FibredCategoryMor

end

/-- Helper for Lemma 8.4.6: composing in `C` and then passing to the locally discrete opposite is
the same as composing the corresponding `toLoc` arrows in the owner order used by `pullHom`. -/
private theorem comp_toLoc_eq
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf) :
    f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc := by
  -- Translate the composite equality to `LocallyDiscrete Cᵒᵖ`.
  simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
    congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hgf)

/-- Helper for Lemma 8.4.6: a functor maps a visible threefold composite to the corresponding
threefold composite of mapped arrows. -/
private theorem functor_map_threefold_comp
    {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    {W X Y Z : D} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    F.map (f ≫ g ≫ h) = F.map f ≫ F.map g ≫ F.map h := by
  -- Split the threefold composite into two ordinary functoriality steps.
  rw [Functor.map_comp, Functor.map_comp]

/-- Helper for Lemma 8.4.6: the hom component of the flexible pullback-composition comparison for
the canonical fiber pseudofunctor satisfies the same factorization identity as the chosen
pullback-composition comparison. -/
private theorem canonicalFiberPseudofunctor_mapComp'_hom_app_fac
    {T : Type*} [Category T] (p : T ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf)
    (x : p.Fiber D) :
    (((canonicalFiberPseudofunctor p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x).1 ≫
        (canonicalPullbackChoice p).map g
          (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj x) ≫
        (canonicalPullbackChoice p).map f x =
      (canonicalPullbackChoice p).map gf x := by
  -- Reduce the flexible comparison to the chosen pullback-composition comparison.
  subst gf
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp] using
    (canonicalPullbackChoice p).pullbackCompComponentIso_fac f g x

/-- Helper for Lemma 8.4.6: the inverse component of the flexible pullback-composition
comparison for the canonical fiber pseudofunctor factors the composite pullback arrow through the
iterated chosen pullback arrows. -/
private theorem canonicalFiberPseudofunctor_mapComp'_inv_app_fac
    {T : Type*} [Category T] (p : T ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf)
    (x : p.Fiber D) :
    (((canonicalFiberPseudofunctor p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app x).1 ≫
        (canonicalPullbackChoice p).map gf x =
      (canonicalPullbackChoice p).map g
          (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj x) ≫
        (canonicalPullbackChoice p).map f x := by
  -- Read the same chosen pullback-composition comparison in the inverse direction.
  subst gf
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp] using
    (canonicalPullbackChoice p).pullbackCompComponentIso_inv_fac f g x

/-- Helper for Lemma 8.4.6: the canonical pullback functor on fibers is characterized by the
usual factorization identity through the chosen strongly cartesian pullback arrow. -/
private theorem canonical_pullbackFunctor_map_fac
    {T : Type*} [Category T] (p : T ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map φ)).1 ≫
        (canonicalPullbackChoice p).map f y =
      (canonicalPullbackChoice p).map f x ≫ φ.1 := by
  -- Compare the chosen pullback arrow of `y` with the universal factorization induced by `φ`.
  letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
  have hpull : p.IsStronglyCartesian f ((canonicalPullbackChoice p).map f x) :=
    (canonicalPullbackChoice p).isStronglyCartesian f x
  letI : p.IsHomLift f ((canonicalPullbackChoice p).map f x) := hpull.toIsHomLift
  letI : p.IsHomLift f ((canonicalPullbackChoice p).map f x ≫ φ.1) :=
    IsHomLift.comp_lift_id_right' p f ((canonicalPullbackChoice p).map f x) U φ.1
  letI : p.IsStronglyCartesian f ((canonicalPullbackChoice p).map f y) :=
    (canonicalPullbackChoice p).isStronglyCartesian f y
  change
      Functor.IsStronglyCartesian.map p f ((canonicalPullbackChoice p).map f y)
        (Category.id_comp f).symm
        ((canonicalPullbackChoice p).map f x ≫ φ.1) ≫
          (canonicalPullbackChoice p).map f y =
        (canonicalPullbackChoice p).map f x ≫ φ.1
  exact
    Functor.IsStronglyCartesian.fac p f ((canonicalPullbackChoice p).map f y)
      (Category.id_comp f).symm
      ((canonicalPullbackChoice p).map f x ≫ φ.1)

/-- Helper for Lemma 8.4.6: after postcomposing both sides with the chosen target pullback arrow,
the pullback-comparison square for a stack morphism reduces to the mapped source pullback
factorization identity. -/
private theorem map_canonical_pullbackFunctor_map_fac
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : A.p.Fiber U} (φ : x ⟶ y) :
    (H).toHom.map ((canonicalPullbackChoice A.p).map f x) ≫
        (H).toHom.map φ.1 =
      (H).toHom.map
          ((((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
        (H).toHom.map ((canonicalPullbackChoice A.p).map f y) := by
  -- Apply the stack morphism to the source pullback factorization and normalize the composites.
  rw [← Functor.map_comp, ← Functor.map_comp]
  have hfac :
      ((canonicalPullbackChoice A.p).map f x) ≫ φ.1 =
        ((((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
          (canonicalPullbackChoice A.p).map f y := by
    exact
      (canonical_pullbackFunctor_map_fac
        (p := A.p) (f := f) (x := x) (y := y) (φ := φ)).symm
  exact congrArg (fun k ↦ (H).toHom.map k) hfac

/-- Helper for Lemma 8.4.6: after postcomposing both sides with the chosen target pullback arrow,
the pullback-comparison square for a stack morphism reduces to the mapped source pullback
factorization identity. -/
private theorem stack_morphism_pullbackComparison_hom_postcompose_eq
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : A.p.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor H U).map φ))).1 ≫
        (FibredCategoryMor.pullbackComparison (H) f y).hom.1 ≫
        (H).toHom.map ((canonicalPullbackChoice A.p).map f y) =
      ((FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
          ((FibredCategoryMor.fiberFunctor H V).map
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1) ≫
        (H).toHom.map ((canonicalPullbackChoice A.p).map f y) := by
  -- Compare the two candidates only after postcomposing with the common strongly cartesian
  -- target, which is the source-faithful uniqueness step from Lemma `8.2.3`.
  let lhs :=
    ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor H U).map φ))).1 ≫
      (FibredCategoryMor.pullbackComparison (H) f y).hom.1 ≫
      (H).toHom.map ((canonicalPullbackChoice A.p).map f y)
  let mid₁ :=
    ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor H U).map φ))).1 ≫
      (canonicalPullbackChoice B.p).map f ((FibredCategoryMor.fiberFunctor H U).obj y)
  let mid₂ :=
    (canonicalPullbackChoice B.p).map f ((FibredCategoryMor.fiberFunctor H U).obj x) ≫
      ((FibredCategoryMor.fiberFunctor H U).map φ).1
  let mid₃ :=
    ((FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
        (H).toHom.map ((canonicalPullbackChoice A.p).map f x)) ≫
      ((FibredCategoryMor.fiberFunctor H U).map φ).1
  let mid₄ :=
    (FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
      ((FibredCategoryMor.fiberFunctor H V).map
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
      (H).toHom.map ((canonicalPullbackChoice A.p).map f y)
  let rhs :=
    ((FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
        ((FibredCategoryMor.fiberFunctor H V).map
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1) ≫
      (H).toHom.map ((canonicalPullbackChoice A.p).map f y)
  have h₁ : lhs = mid₁ := by
    -- Rewrite the comparison isomorphism at `y` to the canonical target pullback arrow.
    change
      ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
          ((FibredCategoryMor.fiberFunctor H U).map φ))).1 ≫
          (FibredCategoryMor.pullbackComparison (H) f y).hom.1 ≫
          (H).toHom.map ((canonicalPullbackChoice A.p).map f y) =
        ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
            ((FibredCategoryMor.fiberFunctor H U).map φ))).1 ≫
          (canonicalPullbackChoice B.p).map f ((FibredCategoryMor.fiberFunctor H U).obj y)
    exact
      congrArg
        (fun k ↦
          ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
              ((FibredCategoryMor.fiberFunctor H U).map φ))).1 ≫ k)
        (FibredCategoryMor.pullbackComparison_hom_postcompose (H) f y)
  have h₂ : mid₁ = mid₂ := by
    -- Pullback in the target fiber is already natural on the vertical morphism `H.map φ`.
    change
      ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
          ((FibredCategoryMor.fiberFunctor H U).map φ))).1 ≫
          (canonicalPullbackChoice B.p).map f ((FibredCategoryMor.fiberFunctor H U).obj y) =
        (canonicalPullbackChoice B.p).map f ((FibredCategoryMor.fiberFunctor H U).obj x) ≫
          ((FibredCategoryMor.fiberFunctor H U).map φ).1
    exact
      canonical_pullbackFunctor_map_fac
        (p := B.p) (f := f) (φ := (FibredCategoryMor.fiberFunctor H U).map φ)
  have h₃ : mid₂ = mid₃ := by
    -- Rewrite the target pullback arrow at `x` back through the comparison isomorphism.
    change
      (canonicalPullbackChoice B.p).map f ((FibredCategoryMor.fiberFunctor H U).obj x) ≫
          ((FibredCategoryMor.fiberFunctor H U).map φ).1 =
        (((FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
            (H).toHom.map ((canonicalPullbackChoice A.p).map f x)) ≫
          ((FibredCategoryMor.fiberFunctor H U).map φ).1)
    exact
      (congrArg
        (fun k ↦ k ≫ ((FibredCategoryMor.fiberFunctor H U).map φ).1)
        (FibredCategoryMor.pullbackComparison_hom_postcompose
          (H) f x)).symm
  have h₄ : mid₃ = mid₄ := by
    -- Map the source pullback factorization across `H` and then reassociate.
    calc
      (((FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
          (H).toHom.map ((canonicalPullbackChoice A.p).map f x)) ≫
        ((FibredCategoryMor.fiberFunctor H U).map φ).1) =
          (FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
            ((H).toHom.map ((canonicalPullbackChoice A.p).map f x) ≫
              ((FibredCategoryMor.fiberFunctor H U).map φ).1) := by
            rw [Category.assoc]
      _ =
          (FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
            ((H).toHom.map
                ((((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
              (H).toHom.map ((canonicalPullbackChoice A.p).map f y)) := by
            exact
              congrArg
                (fun k ↦
                  (FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫ k)
                (map_canonical_pullbackFunctor_map_fac
                  (H := H) (f := f) (φ := φ))
      _ =
          (FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
            ((FibredCategoryMor.fiberFunctor H V).map
              (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
            (H).toHom.map ((canonicalPullbackChoice A.p).map f y) := by
            rfl
  have h₅ : mid₄ = rhs := by
    -- Reassociate the right-hand composite into the packaged naturality shape.
    change
      (FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
          ((FibredCategoryMor.fiberFunctor H V).map
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
          (H).toHom.map ((canonicalPullbackChoice A.p).map f y) =
        ((FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
            ((FibredCategoryMor.fiberFunctor H V).map
              (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1) ≫
          (H).toHom.map ((canonicalPullbackChoice A.p).map f y)
    exact (Category.assoc _ _ _).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- Helper for Lemma 8.4.6: after forgetting to the total categories, the pullback-comparison
isomorphism for a stack morphism intertwines pullback of vertical morphisms with the image of the
pulled-back morphism. -/
private theorem stack_morphism_pullbackComparison_hom_naturality_over_vertical
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : A.p.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor H U).map φ))).1 ≫
      (FibredCategoryMor.pullbackComparison (H) f y).hom.1 =
        (FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
          ((FibredCategoryMor.fiberFunctor H V).map
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 := by
  -- Compare the two ambient arrows after postcomposing with the common strongly cartesian
  -- image of the chosen source pullback arrow.
  let ex := FibredCategoryMor.pullbackComparison (H) f x
  let ey := FibredCategoryMor.pullbackComparison (H) f y
  let η :
      ((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.obj
          ((FibredCategoryMor.fiberFunctor H U).obj x) ⟶
        ((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.obj
          ((FibredCategoryMor.fiberFunctor H U).obj y) :=
    ((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor H U).map φ)
  let θ :
      ((FibredCategoryMor.fiberFunctor H V).obj
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x)) ⟶
        ((FibredCategoryMor.fiberFunctor H V).obj
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)) :=
    ((FibredCategoryMor.fiberFunctor H V).map
      (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ))
  let φH :
      (((FibredCategoryMor.fiberFunctor H V).obj (f ^*[canonicalPullbackChoice A.p] y)).1 ⟶
        (((FibredCategoryMor.fiberFunctor H U).obj y).1)) :=
    (H).toHom.map ((canonicalPullbackChoice A.p).map f y)
  have hφH : B.p.IsStronglyCartesian f φH := by
    -- Transport the chosen source pullback lift across the stack morphism.
    change
      B.p.IsStronglyCartesian f
        ((H).toHom.map ((canonicalPullbackChoice A.p).map f y))
    exact
      FibredCategoryMor.map_stronglyCartesian_of_lift
        (H) f
        ((canonicalPullbackChoice A.p).map f y)
        ((canonicalPullbackChoice A.p).isStronglyCartesian f y)
  letI : B.p.IsStronglyCartesian f φH := hφH
  letI : B.p.IsHomLift (𝟙 V) η.1 := by
    exact η.2
  letI : B.p.IsHomLift (𝟙 V) θ.1 := by
    exact θ.2
  letI : B.p.IsHomLift (𝟙 V) ex.hom.1 := by
    exact ex.hom.2
  letI : B.p.IsHomLift (𝟙 V) ey.hom.1 := by
    exact ey.hom.2
  letI : B.p.IsHomLift (𝟙 V) (η.1 ≫ ey.hom.1) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ B.p _ _ _ _ _
      (𝟙 V) η.1 η.2 V ey.hom.1 ey.hom.2
  letI : B.p.IsHomLift (𝟙 V) (ex.hom.1 ≫ θ.1) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ B.p _ _ _ _ _
      (𝟙 V) ex.hom.1 ex.hom.2 V θ.1 θ.2
  have hcomp :
      η.1 ≫ ey.hom.1 ≫ φH = (ex.hom.1 ≫ θ.1) ≫ φH := by
    simpa only [η, θ, φH, Category.assoc] using
      stack_morphism_pullbackComparison_hom_postcompose_eq H f φ
  have hηey : B.p.IsHomLift (𝟙 V) (η.1 ≫ ey.hom.1) := by infer_instance
  have hexθ : B.p.IsHomLift (𝟙 V) (ex.hom.1 ≫ θ.1) := by infer_instance
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ B.p _ _ _ _
      f φH inferInstance _ _ (𝟙 V) (η.1 ≫ ey.hom.1) (ex.hom.1 ≫ θ.1) hηey hexθ <| by
        rw [Category.assoc]
        exact hcomp

/-- Helper for Lemma 8.4.6: the pullback-comparison isomorphism for a stack morphism is fiberwise
natured on vertical morphisms. -/
theorem stack_morphism_pullbackComparison_naturality_over_vertical
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : A.p.Fiber U} (φ : x ⟶ y) :
    (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor H U).map φ)) ≫
      (FibredCategoryMor.pullbackComparison (H) f y).hom =
        (FibredCategoryMor.pullbackComparison (H) f x).hom ≫
          (FibredCategoryMor.fiberFunctor H V).map
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ) := by
  -- Reduce the fiber statement to the owner-level equality above with `Functor.Fiber.hom_ext`.
  apply Functor.Fiber.hom_ext
  exact stack_morphism_pullbackComparison_hom_naturality_over_vertical H f φ

/-- Helper for Lemma 8.4.6: the inverse pullback-comparison isomorphism carries the vertical
naturality square into the conjugation form needed for fixed-cover descent-data transport. -/
theorem stack_morphism_pullbackComparison_inv_naturality_over_vertical
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : A.p.Fiber U} (φ : x ⟶ y) :
    (FibredCategoryMor.fiberFunctor H V).map
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ) ≫
      (FibredCategoryMor.pullbackComparison (H) f y).inv =
        (FibredCategoryMor.pullbackComparison (H) f x).inv ≫
          (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
            ((FibredCategoryMor.fiberFunctor H U).map φ)) := by
  -- Route correction: move the already proved hom-side square across the two comparison inverses.
  let ex := FibredCategoryMor.pullbackComparison (H) f x
  let ey := FibredCategoryMor.pullbackComparison (H) f y
  let η :=
    ((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor H U).map φ)
  let θ :=
    (FibredCategoryMor.fiberFunctor H V).map
      (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)
  have hhom : η ≫ ey.hom = ex.hom ≫ θ := by
    simpa only [ex, ey, η, θ] using
      stack_morphism_pullbackComparison_naturality_over_vertical H f φ
  symm
  apply (Iso.eq_comp_inv ey).2
  -- Precompose by `ex.inv` so the left comparison isomorphism cancels immediately.
  have hpre :
      ex.inv ≫
          ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
              ((FibredCategoryMor.fiberFunctor H U).map φ)) ≫ ey.hom) =
        ex.inv ≫
          (ex.hom ≫
            (FibredCategoryMor.fiberFunctor H V).map
              (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)) := by
    exact congrArg (fun k ↦ ex.inv ≫ k) hhom
  simpa only [← Category.assoc, ex.inv_hom_id, Category.id_comp] using hpre

/-- Helper for Lemma 8.4.6: once the cocycle composite is reassociated to the literal
`comparison.inv ≫ comparison.hom` shell, the middle comparison pair cancels before the remaining
tail. -/
private theorem stack_morphism_pullbackComparison_inv_hom_postcompose_normalized
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
private theorem stack_morphism_pullbackComparison_pullHom_left_boundary_postcompose_g_then_f_target
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
private theorem stack_morphism_pullbackComparison_pullHom_left_boundary_postcompose_g_target
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
private theorem stack_morphism_pullbackComparison_pullHom_left_boundary
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
private theorem stack_morphism_pullbackComparison_pullHom_right_boundary_postcompose_target
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
private theorem stack_morphism_pullbackComparison_pullHom_right_boundary
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

/-- Helper for Lemma 8.4.6: for a fixed cover, transport one overlap morphism by conjugating it
with the pullback-comparison isomorphisms of the stack morphism. -/
private noncomputable abbrev cover_descent_data_functor_hom_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.obj
        ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁))) ⟶
      (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.obj
        ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂))) := by
  -- Route correction: record the fixed-cover overlap map in one stable conjugation normal form so
  -- the later object, morphism, and comparison constructions all rewrite against the same term.
  simpa using
    (FibredCategoryMor.pullbackComparison (H) f₁ (D.obj I₁)).hom ≫
      (FibredCategoryMor.fiberFunctor H Y).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
      (FibredCategoryMor.pullbackComparison (H) f₂ (D.obj I₂)).inv

/-- Helper for Lemma 8.4.6: transporting the self-overlap morphism of descent data along a stack
morphism still yields the identity. -/
private theorem cover_descent_data_functor_hom_self_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I : T.Arrow} (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    cover_descent_data_functor_hom_of_stack_morphism (J := J) H T D q g g hg hg = 𝟙 _ := by
  -- Collapse the middle factor to the identity with `D.hom_self`, then cancel the comparison
  -- isomorphism on both sides.
  change
    (FibredCategoryMor.pullbackComparison (H) g (D.obj I)).hom ≫
        (FibredCategoryMor.fiberFunctor H Y).map (D.hom q g g hg hg) ≫
        (FibredCategoryMor.pullbackComparison (H) g (D.obj I)).inv =
      𝟙 _
  have hmid :
      (FibredCategoryMor.fiberFunctor H Y).map (D.hom q g g hg hg) =
        𝟙 ((FibredCategoryMor.fiberFunctor H Y).obj
          (((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor.obj (D.obj I))) := by
    rw [D.hom_self q g hg]
    exact (FibredCategoryMor.fiberFunctor H Y).map_id _
  let e := FibredCategoryMor.pullbackComparison (H) g (D.obj I)
  calc
    e.hom ≫
        (FibredCategoryMor.fiberFunctor H Y).map (D.hom q g g hg hg) ≫
        e.inv =
    e.hom ≫
        𝟙 ((FibredCategoryMor.fiberFunctor H Y).obj
          (((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor.obj (D.obj I))) ≫
        e.inv := by
          exact congrArg (fun k ↦ e.hom ≫ k ≫ e.inv) hmid
    _ = e.hom ≫
          (𝟙 ((FibredCategoryMor.fiberFunctor H Y).obj
            (((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor.obj (D.obj I))) ≫
            e.inv) := by
          rfl
    _ = e.hom ≫ e.inv := by
          exact congrArg (fun k ↦ e.hom ≫ k) (Category.id_comp e.inv)
    _ = 𝟙 _ := e.hom_inv_id

/-- Helper for Lemma 8.4.6: transporting the cocycle relation of descent data along a stack
morphism preserves the same cocycle equation. -/
private theorem cover_descent_data_functor_hom_comp_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ I₃ : T.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (hf₃ : f₃ ≫ I₃.f = q := by cat_disch) :
    cover_descent_data_functor_hom_of_stack_morphism (J := J) H T D q f₁ f₂ hf₁ hf₂ ≫
      cover_descent_data_functor_hom_of_stack_morphism (J := J) H T D q f₂ f₃ hf₂ hf₃ =
        cover_descent_data_functor_hom_of_stack_morphism (J := J) H T D q f₁ f₃ hf₁ hf₃ := by
  let F := FibredCategoryMor.fiberFunctor H Y
  let e₁ := FibredCategoryMor.pullbackComparison (H) f₁ (D.obj I₁)
  let e₂ := FibredCategoryMor.pullbackComparison (H) f₂ (D.obj I₂)
  let e₃ := FibredCategoryMor.pullbackComparison (H) f₃ (D.obj I₃)
  let d₁₂ := D.hom q f₁ f₂ hf₁ hf₂
  let d₂₃ := D.hom q f₂ f₃ hf₂ hf₃
  let d₁₃ := D.hom q f₁ f₃ hf₁ hf₃
  -- Rewrite both transported overlap maps into the shared comparison-conjugated normal form.
  have hnormalize :
      cover_descent_data_functor_hom_of_stack_morphism (J := J) H T D q f₁ f₂ hf₁ hf₂ ≫
          cover_descent_data_functor_hom_of_stack_morphism (J := J) H T D q f₂ f₃ hf₂ hf₃ =
        e₁.hom ≫ F.map d₁₂ ≫ e₂.inv ≫ e₂.hom ≫ F.map d₂₃ ≫ e₃.inv := by
    change ((e₁.hom ≫ F.map d₁₂ ≫ e₂.inv) ≫ (e₂.hom ≫ F.map d₂₃ ≫ e₃.inv)) =
      e₁.hom ≫ F.map d₁₂ ≫ e₂.inv ≫ e₂.hom ≫ F.map d₂₃ ≫ e₃.inv
    simp only [Category.assoc]
  -- Cancel the middle comparison pair before using the source cocycle identity.
  have hcancel_mid :
      e₂.inv ≫ e₂.hom ≫ F.map d₂₃ ≫ e₃.inv = F.map d₂₃ ≫ e₃.inv := by
    simpa only [F, Category.assoc] using
      stack_morphism_pullbackComparison_inv_hom_postcompose_normalized
        (H := H) f₂ (D.obj I₂) (k := F.map d₂₃ ≫ e₃.inv)
  have hcancel :
      e₁.hom ≫ F.map d₁₂ ≫ e₂.inv ≫ e₂.hom ≫ F.map d₂₃ ≫ e₃.inv =
        e₁.hom ≫ F.map d₁₂ ≫ F.map d₂₃ ≫ e₃.inv := by
    simpa only [Category.assoc] using
      congrArg (fun k ↦ e₁.hom ≫ F.map d₁₂ ≫ k) hcancel_mid
  have hmap_comp :
      F.map d₁₂ ≫ F.map d₂₃ = F.map d₁₃ := by
    calc
      F.map d₁₂ ≫ F.map d₂₃ = F.map (d₁₂ ≫ d₂₃) := by
        rw [← F.map_comp]
      _ = F.map d₁₃ := by
        simpa only [d₁₂, d₂₃, d₁₃] using
          congrArg F.map (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)
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
        cover_descent_data_functor_hom_of_stack_morphism (J := J) H T D q f₁ f₃ hf₁ hf₃ := by
    rfl
  exact hnormalize.trans (hcancel.trans (hassoc_map.trans (hmap.trans hfinal)))

/-- Helper for Lemma 8.4.6: the only unresolved fixed-cover object field for the descent-data
transport functor is the compatibility with further pullback. -/
private theorem cover_descent_data_functor_pullHom_right_tail_normalized
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (_hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    (FibredCategoryMor.pullbackComparison
        (H) gf₁ (D.obj I₁)).hom ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁)) ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor.map
          (D.hom q f₁ f₂ hf₁ hf₂)) ≫
      (FibredCategoryMor.pullbackComparison (H) g
        (((canonicalFiberPseudofunctor A.p).map f₂.op.toLoc).toFunctor.obj (D.obj I₂))).inv ≫
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison
          (H) f₂ (D.obj I₂)).inv) ≫
      (((canonicalFiberPseudofunctor B.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂))) =
    (FibredCategoryMor.pullbackComparison
        (H) gf₁ (D.obj I₁)).hom ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁)) ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor.map
          (D.hom q f₁ f₂ hf₁ hf₂)) ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app (D.obj I₂)) ≫
      (FibredCategoryMor.pullbackComparison
        (H) gf₂ (D.obj I₂)).inv := by
  -- Normalize the exact post-`hmid` right tail once so the shell proof can reuse it verbatim.
  let leftPrefix :=
    (FibredCategoryMor.pullbackComparison
        (H) gf₁ (D.obj I₁)).hom ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁)) ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor.map
          (D.hom q f₁ f₂ hf₁ hf₂))
  have htail :
      (FibredCategoryMor.pullbackComparison (H) g
          (((canonicalFiberPseudofunctor A.p).map f₂.op.toLoc).toFunctor.obj
            (D.obj I₂))).inv ≫
        (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison
            (H) f₂ (D.obj I₂)).inv) ≫
        (((canonicalFiberPseudofunctor B.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂))) =
        (FibredCategoryMor.fiberFunctor H Y').map
          (((canonicalFiberPseudofunctor A.p).mapComp'
              f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
              (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app (D.obj I₂)) ≫
          (FibredCategoryMor.pullbackComparison
            (H) gf₂ (D.obj I₂)).inv := by
    -- This is exactly the owner-level right boundary already proved for the stack morphism.
    simpa only [Category.assoc] using
      stack_morphism_pullbackComparison_pullHom_right_boundary
        (H := H) f₂ g gf₂ hgf₂ (D.obj I₂)
  -- Whisker the boundary equality by the fixed left prefix used in the shell normalization.
  simpa only [leftPrefix, Category.assoc] using
    congrArg (fun k ↦ leftPrefix ≫ k) htail

/-- Helper for Lemma 8.4.6: the only unresolved fixed-cover object field for the descent-data
transport functor is the compatibility with further pullback. -/
private theorem cover_descent_data_functor_pullHom_left_boundary_whiskered
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (_hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let commonSuffix :=
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor H Y).map (D.hom q f₁ f₂ hf₁ hf₂))) ≫
        (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison
            (H) f₂ (D.obj I₂)).inv) ≫
        (((canonicalFiberPseudofunctor B.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂)))
    let leftRaw :=
      (((canonicalFiberPseudofunctor B.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁))) ≫
        (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison
            (H) f₁ (D.obj I₁)).hom)
    let leftStrict :=
      (FibredCategoryMor.pullbackComparison
          (H) gf₁ (D.obj I₁)).hom ≫
        (FibredCategoryMor.fiberFunctor H Y').map
          (((canonicalFiberPseudofunctor A.p).mapComp'
              f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
              (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁)) ≫
        (FibredCategoryMor.pullbackComparison (H) g
          (((canonicalFiberPseudofunctor A.p).map f₁.op.toLoc).toFunctor.obj (D.obj I₁))).inv
    leftRaw ≫ commonSuffix = leftStrict ≫ commonSuffix := by
  -- Whisker the already-proved left boundary by the frozen suffix appearing in the shell theorem.
  let commonSuffix :=
    (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor H Y).map (D.hom q f₁ f₂ hf₁ hf₂))) ≫
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison
          (H) f₂ (D.obj I₂)).inv) ≫
      (((canonicalFiberPseudofunctor B.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂)))
  let leftRaw :=
    (((canonicalFiberPseudofunctor B.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁))) ≫
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison
          (H) f₁ (D.obj I₁)).hom)
  let leftStrict :=
    (FibredCategoryMor.pullbackComparison
        (H) gf₁ (D.obj I₁)).hom ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁)) ≫
      (FibredCategoryMor.pullbackComparison (H) g
        (((canonicalFiberPseudofunctor A.p).map f₁.op.toLoc).toFunctor.obj (D.obj I₁))).inv
  change leftRaw ≫ commonSuffix = leftStrict ≫ commonSuffix
  simpa only [Category.assoc] using
    congrArg
      (fun k ↦ k ≫ commonSuffix)
      (stack_morphism_pullbackComparison_pullHom_left_boundary
        (H := H) f₁ g gf₁ hgf₁ (D.obj I₁))

/-- Helper for Lemma 8.4.6: the middle inverse-naturality square can be inserted into the exact
owner-level shell that appears in the fixed-cover `pullHom` normalization. -/
private theorem cover_descent_data_functor_pullHom_middle_naturality_whiskered
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (_hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let leftPrefix :=
      (FibredCategoryMor.pullbackComparison
          (H) gf₁ (D.obj I₁)).hom ≫
        (FibredCategoryMor.fiberFunctor H Y').map
          (((canonicalFiberPseudofunctor A.p).mapComp'
              f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
              (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁))
    let commonRightTail :=
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison
          (H) f₂ (D.obj I₂)).inv) ≫
        (((canonicalFiberPseudofunctor B.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂)))
    let rawMiddle :=
      (FibredCategoryMor.pullbackComparison (H) g
        (((canonicalFiberPseudofunctor A.p).map f₁.op.toLoc).toFunctor.obj (D.obj I₁))).inv ≫
        (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
          ((FibredCategoryMor.fiberFunctor H Y).map (D.hom q f₁ f₂ hf₁ hf₂)))
    let strictMiddle :=
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor.map
          (D.hom q f₁ f₂ hf₁ hf₂)) ≫
        (FibredCategoryMor.pullbackComparison (H) g
          (((canonicalFiberPseudofunctor A.p).map f₂.op.toLoc).toFunctor.obj (D.obj I₂))).inv
    leftPrefix ≫ rawMiddle ≫ commonRightTail =
      leftPrefix ≫ strictMiddle ≫ commonRightTail := by
  -- Insert the inverse-naturality square into the exact shell parenthesization.
  let leftPrefix :=
    (FibredCategoryMor.pullbackComparison
        (H) gf₁ (D.obj I₁)).hom ≫
      (FibredCategoryMor.fiberFunctor H Y').map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁))
  let commonRightTail :=
    (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
      (FibredCategoryMor.pullbackComparison
        (H) f₂ (D.obj I₂)).inv) ≫
      (((canonicalFiberPseudofunctor B.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂)))
  let rawMiddle :=
    (FibredCategoryMor.pullbackComparison (H) g
      (((canonicalFiberPseudofunctor A.p).map f₁.op.toLoc).toFunctor.obj (D.obj I₁))).inv ≫
      (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor H Y).map (D.hom q f₁ f₂ hf₁ hf₂)))
  let strictMiddle :=
    (FibredCategoryMor.fiberFunctor H Y').map
      (((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor.map
        (D.hom q f₁ f₂ hf₁ hf₂)) ≫
      (FibredCategoryMor.pullbackComparison (H) g
        (((canonicalFiberPseudofunctor A.p).map f₂.op.toLoc).toFunctor.obj (D.obj I₂))).inv
  change leftPrefix ≫ rawMiddle ≫ commonRightTail =
    leftPrefix ≫ strictMiddle ≫ commonRightTail
  simpa only [Category.assoc] using
    congrArg
      (fun k ↦ leftPrefix ≫ k ≫ commonRightTail)
      (stack_morphism_pullbackComparison_inv_naturality_over_vertical
        (H := H) (f := g) (φ := D.hom q f₁ f₂ hf₁ hf₂)).symm

/-- Helper for Lemma 8.4.6: the only unresolved fixed-cover object field for the descent-data
transport functor is the compatibility with further pullback. -/
private theorem cover_descent_data_functor_pullHom_hom_unfolded_raw_shell
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (_q' : Y' ⟶ U)
    {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (cover_descent_data_functor_hom_of_stack_morphism
          (J := J) H T D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      (((canonicalFiberPseudofunctor B.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁))) ≫
        (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
          ((FibredCategoryMor.pullbackComparison
              (H) f₁ (D.obj I₁)).hom ≫
            (FibredCategoryMor.fiberFunctor H Y).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
            (FibredCategoryMor.pullbackComparison
              (H) f₂ (D.obj I₂)).inv)) ≫
        (((canonicalFiberPseudofunctor B.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂))) := by
  -- Expand only the transported overlap map and the pseudofunctorial `pullHom` once, so the
  -- remaining shell proof can work entirely with named owner-level boundary rewrites.
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, cover_descent_data_functor_hom_of_stack_morphism]
  rfl

/-- Helper for Lemma 8.4.6: split the single mapped threefold composite in the raw shell while
keeping the outer left and right whiskers fixed. -/
private theorem cover_descent_data_functor_pullHom_map_threefold_comp_whiskered
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (_q' : Y' ⟶ U)
    {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor
    let d := D.hom q f₁ f₂ hf₁ hf₂
    let e₁ := FibredCategoryMor.pullbackComparison (H) f₁ (D.obj I₁)
    let e₂ := FibredCategoryMor.pullbackComparison (H) f₂ (D.obj I₂)
    let leftTarget :=
      (((canonicalFiberPseudofunctor B.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁)))
    let rightTarget :=
      (((canonicalFiberPseudofunctor B.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂)))
    leftTarget ≫ FYg.map (e₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y).map d ≫ e₂.inv) ≫ rightTarget =
      leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d) ≫
        FYg.map e₂.inv ≫ rightTarget := by
  -- Split the visible threefold composite once, then reassociate back to the shell shape.
  let FYg := ((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor
  let d := D.hom q f₁ f₂ hf₁ hf₂
  let e₁ := FibredCategoryMor.pullbackComparison (H) f₁ (D.obj I₁)
  let e₂ := FibredCategoryMor.pullbackComparison (H) f₂ (D.obj I₂)
  let leftTarget :=
    (((canonicalFiberPseudofunctor B.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁)))
  let rightTarget :=
    (((canonicalFiberPseudofunctor B.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂)))
  change
    leftTarget ≫ FYg.map (e₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y).map d ≫ e₂.inv) ≫ rightTarget =
      leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d) ≫
        FYg.map e₂.inv ≫ rightTarget
  calc
    leftTarget ≫ FYg.map (e₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y).map d ≫ e₂.inv) ≫ rightTarget =
      leftTarget ≫ (FYg.map e₁.hom ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d) ≫ FYg.map e₂.inv) ≫
        rightTarget := by
        exact
          congrArg
            (fun k ↦ leftTarget ≫ k ≫ rightTarget)
            (functor_map_threefold_comp FYg e₁.hom ((FibredCategoryMor.fiberFunctor H Y).map d) e₂.inv)
    _ =
      leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d) ≫
        FYg.map e₂.inv ≫ rightTarget := by
        simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: after the boundary normalizations, the strict source shell folds back
to the source `pullHom`, with the comparison factors already whiskered on both sides. -/
private theorem cover_descent_data_functor_pullHom_source_shell_fold_whiskered
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (_q' : Y' ⟶ U)
    {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let FXg := ((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor
    let d := D.hom q f₁ f₂ hf₁ hf₂
    let eg₁ := FibredCategoryMor.pullbackComparison (H) gf₁ (D.obj I₁)
    let eg₂ := FibredCategoryMor.pullbackComparison (H) gf₂ (D.obj I₂)
    let leftSource :=
      (((canonicalFiberPseudofunctor A.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁))
    let rightSource :=
      (((canonicalFiberPseudofunctor A.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app (D.obj I₂))
    eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
        (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫
        (FibredCategoryMor.fiberFunctor H Y').map rightSource ≫ eg₂.inv =
      eg₁.hom ≫
        (FibredCategoryMor.fiberFunctor H Y').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            d g gf₁ gf₂ hgf₁ hgf₂) ≫
        eg₂.inv := by
  -- First fold the strict source shell under `FibredCategoryMor.fiberFunctor H Y'`, then restore the outer whiskers.
  let FXg := ((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor
  let d := D.hom q f₁ f₂ hf₁ hf₂
  let eg₁ := FibredCategoryMor.pullbackComparison (H) gf₁ (D.obj I₁)
  let eg₂ := FibredCategoryMor.pullbackComparison (H) gf₂ (D.obj I₂)
  let leftSource :=
    (((canonicalFiberPseudofunctor A.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁))
  let rightSource :=
    (((canonicalFiberPseudofunctor A.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app (D.obj I₂))
  have hfold :
      (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫
          (FibredCategoryMor.fiberFunctor H Y').map rightSource =
        (FibredCategoryMor.fiberFunctor H Y').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            d g gf₁ gf₂ hgf₁ hgf₂) := by
    -- The source `pullHom` is definitionally the visible threefold composite.
    change
      (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫
          (FibredCategoryMor.fiberFunctor H Y').map rightSource =
        (FibredCategoryMor.fiberFunctor H Y').map (leftSource ≫ FXg.map d ≫ rightSource)
    rw [functor_map_threefold_comp]
  calc
    eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
        (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫
        (FibredCategoryMor.fiberFunctor H Y').map rightSource ≫ eg₂.inv =
      eg₁.hom ≫
        ((FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫
          (FibredCategoryMor.fiberFunctor H Y').map rightSource) ≫
        eg₂.inv := by
        simp only [Category.assoc]
    _ =
      eg₁.hom ≫
        (FibredCategoryMor.fiberFunctor H Y').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            d g gf₁ gf₂ hgf₁ hgf₂) ≫
        eg₂.inv := by
        exact congrArg (fun k ↦ eg₁.hom ≫ k ≫ eg₂.inv) hfold

/-- Helper for Lemma 8.4.6: the only unresolved fixed-cover object field for the descent-data
transport functor is the compatibility with further pullback. -/
private theorem cover_descent_data_functor_pullHom_hom_normalized_shell
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (cover_descent_data_functor_hom_of_stack_morphism
          (J := J) H T D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      (FibredCategoryMor.pullbackComparison
          (H) gf₁ (D.obj I₁)).hom ≫
        (FibredCategoryMor.fiberFunctor H Y').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂) ≫
      (FibredCategoryMor.pullbackComparison
          (H) gf₂ (D.obj I₂)).inv := by
  -- Route correction: the fixed-cover source route now matches `Lemma_8_4_8` exactly. Expand
  -- the raw shell once, normalize left/middle/right in order, and then fold the source shell.
  let FYg := ((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor
  let FXg := ((canonicalFiberPseudofunctor A.p).map g.op.toLoc).toFunctor
  let d := D.hom q f₁ f₂ hf₁ hf₂
  let e₁ := FibredCategoryMor.pullbackComparison (H) f₁ (D.obj I₁)
  let e₂ := FibredCategoryMor.pullbackComparison (H) f₂ (D.obj I₂)
  let eg₁ := FibredCategoryMor.pullbackComparison (H) gf₁ (D.obj I₁)
  let eg₂ := FibredCategoryMor.pullbackComparison (H) gf₂ (D.obj I₂)
  let cg₁ := FibredCategoryMor.pullbackComparison (H) g
    (((canonicalFiberPseudofunctor A.p).map f₁.op.toLoc).toFunctor.obj (D.obj I₁))
  let cg₂ := FibredCategoryMor.pullbackComparison (H) g
    (((canonicalFiberPseudofunctor A.p).map f₂.op.toLoc).toFunctor.obj (D.obj I₂))
  let leftSource :=
    (((canonicalFiberPseudofunctor A.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁))
  let rightTarget :=
    (((canonicalFiberPseudofunctor B.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor H I₂.Y).obj (D.obj I₂)))
  let rightSource :=
    (((canonicalFiberPseudofunctor A.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app (D.obj I₂))
  have hunfolded :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (cover_descent_data_functor_hom_of_stack_morphism
            (J := J) H T D q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ =
        (((canonicalFiberPseudofunctor B.p).mapComp'
              f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
              (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁))) ≫
          (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
            ((FibredCategoryMor.pullbackComparison
                (H) f₁ (D.obj I₁)).hom ≫
              (FibredCategoryMor.fiberFunctor H Y).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
              (FibredCategoryMor.pullbackComparison
                (H) f₂ (D.obj I₂)).inv)) ≫
          rightTarget := by
    -- Expand the transported overlap map only once before entering the boundary normalizations.
    exact
      cover_descent_data_functor_pullHom_hom_unfolded_raw_shell
        (J := J) H T D g q q' f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  have hmap' :
      (((canonicalFiberPseudofunctor B.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁))) ≫
          (((canonicalFiberPseudofunctor B.p).map g.op.toLoc).toFunctor.map
            ((FibredCategoryMor.pullbackComparison
                (H) f₁ (D.obj I₁)).hom ≫
              (FibredCategoryMor.fiberFunctor H Y).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
              (FibredCategoryMor.pullbackComparison
                (H) f₂ (D.obj I₂)).inv)) ≫
          rightTarget =
        (((canonicalFiberPseudofunctor B.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁))) ≫
          FYg.map e₁.hom ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d) ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Split the single mapped threefold composite in the raw shell.
    simpa only [FYg, d, e₁, e₂] using
      cover_descent_data_functor_pullHom_map_threefold_comp_whiskered
        (J := J) H T D g q q' f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  have hleft' :
      (((canonicalFiberPseudofunctor B.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor H I₁.Y).obj (D.obj I₁))) ≫
          FYg.map e₁.hom ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d) ≫ FYg.map e₂.inv ≫
          rightTarget =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          cg₁.inv ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d) ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Normalize the left boundary while keeping the middle and right shell frozen.
    simpa only [Category.assoc, eg₁, leftSource] using
      cover_descent_data_functor_pullHom_left_boundary_whiskered
        (J := J) H T D g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  have hmid' :
      eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          cg₁.inv ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d) ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫ cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Insert the middle inverse-naturality square before reflattening the shell.
    calc
      eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          cg₁.inv ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d) ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (cg₁.inv ≫ FYg.map ((FibredCategoryMor.fiberFunctor H Y).map d)) ≫ FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
      _ =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          ((FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫ cg₂.inv) ≫ FYg.map e₂.inv ≫ rightTarget := by
            exact congrArg
              (fun k ↦ eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫ k ≫ FYg.map e₂.inv ≫
                rightTarget)
              (stack_morphism_pullbackComparison_inv_naturality_over_vertical
                (H := H) (f := g) (φ := D.hom q f₁ f₂ hf₁ hf₂)).symm
      _ =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫ cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
  have hprefix :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (cover_descent_data_functor_hom_of_stack_morphism
            (J := J) H T D q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫ cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Chain the unfolded shell with the left and middle normalizations.
    exact hunfolded.trans (hmap'.trans (hleft'.trans hmid'))
  have hright' :
      eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫ cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫
          (FibredCategoryMor.fiberFunctor H Y').map rightSource ≫ eg₂.inv := by
    -- Normalize the right boundary in the already-frozen post-middle shell.
    simpa only [Category.assoc, FYg, FXg, d, eg₁, eg₂, cg₂, leftSource, rightSource] using
      cover_descent_data_functor_pullHom_right_tail_normalized
        (J := J) H T D g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  have hstep_source_flat :
      eg₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map leftSource ≫
          (FibredCategoryMor.fiberFunctor H Y').map (FXg.map d) ≫
          (FibredCategoryMor.fiberFunctor H Y').map rightSource ≫ eg₂.inv =
        eg₁.hom ≫
          (FibredCategoryMor.fiberFunctor H Y').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              d g gf₁ gf₂ hgf₁ hgf₂) ≫
          eg₂.inv := by
    -- Fold the strict source shell back to `pullHom`.
    simpa only [FXg, d, eg₁, eg₂, leftSource, rightSource] using
      cover_descent_data_functor_pullHom_source_shell_fold_whiskered
        (J := J) H T D g q q' f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  exact
    hprefix.trans
      (hright'.trans
        (hstep_source_flat.trans rfl))

/-- Helper for Lemma 8.4.6: the only unresolved fixed-cover object field for the descent-data
transport functor is the compatibility with further pullback. -/
private theorem cover_descent_data_functor_pullHom_hom_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (cover_descent_data_functor_hom_of_stack_morphism
          (J := J) H T D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      cover_descent_data_functor_hom_of_stack_morphism
        (J := J) H T D q' gf₁ gf₂
        (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
  let e₁ := FibredCategoryMor.pullbackComparison (H) gf₁ (D.obj I₁)
  let e₂ := FibredCategoryMor.pullbackComparison (H) gf₂ (D.obj I₂)
  -- Normalize the transported shell once, then replace the middle factor by `D.pullHom_hom`.
  have hnormalize :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (cover_descent_data_functor_hom_of_stack_morphism
            (J := J) H T D q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ =
        e₁.hom ≫
          (FibredCategoryMor.fiberFunctor H Y').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂) ≫
          e₂.inv := by
    -- Reuse the packaged shell lemma so the main proof stays flat.
    simpa only [e₁, e₂] using
      cover_descent_data_functor_pullHom_hom_normalized_shell
        (J := J) H T D g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  have hmiddle :
      e₁.hom ≫
          (FibredCategoryMor.fiberFunctor H Y').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂) ≫
          e₂.inv =
        e₁.hom ≫
          (FibredCategoryMor.fiberFunctor H Y').map
            (D.hom q' gf₁ gf₂
              (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
              (by rw [← hq, ← hgf₂, Category.assoc, hf₂])) ≫
          e₂.inv := by
    -- The middle factor is exactly the source descent-data pullback law transported by `H`.
    exact congrArg (fun k ↦ e₁.hom ≫ (FibredCategoryMor.fiberFunctor H Y').map k ≫ e₂.inv)
      (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
  have hfinal :
      e₁.hom ≫
          (FibredCategoryMor.fiberFunctor H Y').map
            (D.hom q' gf₁ gf₂
              (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
              (by rw [← hq, ← hgf₂, Category.assoc, hf₂])) ≫
          e₂.inv =
        cover_descent_data_functor_hom_of_stack_morphism
          (J := J) H T D q' gf₁ gf₂
          (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
          (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
    -- Fold the target back to the fixed conjugation normal form.
    rfl
  exact hnormalize.trans (hmiddle.trans hfinal)

/-- Helper for Lemma 8.4.6: the component maps of a morphism of descent data remain compatible
after transporting fixed-cover overlap maps through a stack morphism. -/
private theorem cover_descent_data_functor_comm_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    {D₁ D₂ : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f))}
    (φ : D₁ ⟶ D₂)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : T.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor H I₁.Y).map (φ.hom I₁))) ≫
      cover_descent_data_functor_hom_of_stack_morphism
        (J := J) H T D₂ q f₁ f₂ hf₁ hf₂ =
        cover_descent_data_functor_hom_of_stack_morphism
          (J := J) H T D₁ q f₁ f₂ hf₁ hf₂ ≫
            (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
              ((FibredCategoryMor.fiberFunctor H I₂.Y).map (φ.hom I₂))) := by
  let F := FibredCategoryMor.fiberFunctor H Y
  let α₁ :=
    ((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor H I₁.Y).map (φ.hom I₁))
  let α₂ :=
    ((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor H I₂.Y).map (φ.hom I₂))
  let β₁ :=
    F.map
      (((canonicalFiberPseudofunctor A.p).map f₁.op.toLoc).toFunctor.map (φ.hom I₁))
  let β₂ :=
    F.map
      (((canonicalFiberPseudofunctor A.p).map f₂.op.toLoc).toFunctor.map (φ.hom I₂))
  let e₁₁ := FibredCategoryMor.pullbackComparison (H) f₁ (D₁.obj I₁)
  let e₁₂ := FibredCategoryMor.pullbackComparison (H) f₁ (D₂.obj I₁)
  let e₂₁ := FibredCategoryMor.pullbackComparison (H) f₂ (D₁.obj I₂)
  let e₂₂ := FibredCategoryMor.pullbackComparison (H) f₂ (D₂.obj I₂)
  let d₁ := D₁.hom q f₁ f₂ hf₁ hf₂
  let d₂ := D₂.hom q f₁ f₂ hf₁ hf₂
  have hleft :
      α₁ ≫ e₁₂.hom = e₁₁.hom ≫ β₁ := by
    -- Move the left comparison shell across the transported vertical component map.
    simpa only [α₁, β₁, e₁₁, e₁₂] using
      stack_morphism_pullbackComparison_naturality_over_vertical
        H (f := f₁) (φ := φ.hom I₁)
  have hmid :
      β₁ ≫ F.map d₂ = F.map d₁ ≫ β₂ := by
    -- The middle square is the source descent-data compatibility of `φ`, mapped through `H`.
    calc
      β₁ ≫ F.map d₂ =
          F.map
            ((((canonicalFiberPseudofunctor A.p).map f₁.op.toLoc).toFunctor.map (φ.hom I₁)) ≫
              d₂) := by
            dsimp [β₁]
            rw [← F.map_comp]
      _ = F.map
            (d₁ ≫
              (((canonicalFiberPseudofunctor A.p).map f₂.op.toLoc).toFunctor.map (φ.hom I₂))) := by
            simpa only [d₁, d₂] using congrArg F.map (φ.comm q f₁ f₂ hf₁ hf₂)
      _ = F.map d₁ ≫ β₂ := by
            dsimp [β₂]
            rw [F.map_comp]
  have hright :
      β₂ ≫ e₂₂.inv = e₂₁.inv ≫ α₂ := by
    -- Move the right comparison inverse across the transported vertical component map.
    simpa only [α₂, β₂, e₂₁, e₂₂] using
      stack_morphism_pullbackComparison_inv_naturality_over_vertical
        H (f := f₂) (φ := φ.hom I₂)
  -- Rewrite both sides into the common comparison-conjugated normal form.
  have hnormalize_left :
      α₁ ≫ cover_descent_data_functor_hom_of_stack_morphism
          (J := J) H T D₂ q f₁ f₂ hf₁ hf₂ =
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
        cover_descent_data_functor_hom_of_stack_morphism
          (J := J) H T D₁ q f₁ f₂ hf₁ hf₂ ≫ α₂ := by
    change e₁₁.hom ≫ F.map d₁ ≫ (e₂₁.inv ≫ α₂) =
      (e₁₁.hom ≫ F.map d₁ ≫ e₂₁.inv) ≫ α₂
    simp only [Category.assoc]
  exact
    hnormalize_left.trans
      (hleft'.trans (hassoc_left.trans (hmid'.trans (hassoc_mid.trans (hright'.trans hnormalize_right)))))

/-- Helper for Lemma 8.4.6: a stack morphism induces the fixed-cover functor on descent data by
acting componentwise and conjugating overlap maps with the pullback-comparison isomorphisms. -/
private noncomputable def cover_descent_data_functor_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U) :
    ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)) ⥤
      ((canonicalFiberPseudofunctor B.p).DescentData (fun I : T.Arrow ↦ I.f)) where
  obj D :=
    { obj := fun I ↦ (FibredCategoryMor.fiberFunctor H I.Y).obj (D.obj I)
      hom := fun Y q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
        cover_descent_data_functor_hom_of_stack_morphism
          (J := J) H T D q f₁ f₂ hf₁ hf₂
      pullHom_hom := by
        intro Y' Y g q q' hq I₁ I₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
        -- Delegate the only remaining object-field transport obligation to the dedicated helper.
        simpa using
          cover_descent_data_functor_pullHom_hom_of_stack_morphism
            (J := J) H T D g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
      hom_self := by
        intro Y q I g hg
        -- The transported self-overlap map is the identity by the comparison cancellation lemma.
        simpa using
          cover_descent_data_functor_hom_self_of_stack_morphism
            (J := J) H T D q g hg
      hom_comp := by
        intro Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
        -- Reuse the dedicated cocycle transport lemma so the object constructor stays flat.
        simpa using
          cover_descent_data_functor_hom_comp_of_stack_morphism
            (J := J) H T D q f₁ f₂ f₃ hf₁ hf₂ hf₃ }
  map {D₁ D₂} φ :=
    { hom := fun I ↦ (FibredCategoryMor.fiberFunctor H I.Y).map (φ.hom I)
      comm := by
        intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
        -- The componentwise descent-data compatibility is exactly the conjugation lemma above.
        simpa using
          cover_descent_data_functor_comm_of_stack_morphism
            (J := J) H T φ q f₁ f₂ hf₁ hf₂ }
  map_id X := by
    -- The fixed-cover transport functor acts componentwise through the fiber functors.
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    change (FibredCategoryMor.fiberFunctor H I.Y).map (𝟙 (X.obj I)) = 𝟙 ((FibredCategoryMor.fiberFunctor H I.Y).obj (X.obj I))
    exact (FibredCategoryMor.fiberFunctor H I.Y).map_id (X.obj I)
  map_comp f g := by
    -- Composition is computed componentwise because every fiber functor is an ordinary functor.
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    change (FibredCategoryMor.fiberFunctor H I.Y).map (f.hom I ≫ g.hom I) =
      (FibredCategoryMor.fiberFunctor H I.Y).map (f.hom I) ≫ (FibredCategoryMor.fiberFunctor H I.Y).map (g.hom I)
    exact (FibredCategoryMor.fiberFunctor H I.Y).map_comp (f.hom I) (g.hom I)

/-- Helper for Lemma 8.4.6: equivalence of fixed-cover canonical descent functors can be
transported across a comparison isomorphism that is whiskered by equivalences on both sides. -/
private theorem isEquivalence_iff_of_whiskered_iso
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (K : A ⥤ B) (TF : D ⥤ E) (F₁ : A ⥤ D) (F₂ : B ⥤ E)
    [K.IsEquivalence] [TF.IsEquivalence]
    (e : F₁ ⋙ TF ≅ K ⋙ F₂) :
    F₁.IsEquivalence ↔ F₂.IsEquivalence := by
  constructor
  · intro h₁
    -- Compose with the target equivalence and then cancel the source equivalence.
    letI : F₁.IsEquivalence := h₁
    have hcomp₁ : (F₁ ⋙ TF).IsEquivalence :=
      Functor.isEquivalence_trans F₁ TF
    have hcomp₂ : (K ⋙ F₂).IsEquivalence :=
      (Functor.isEquivalence_iff_of_iso e).1 hcomp₁
    letI : (K ⋙ F₂).IsEquivalence := hcomp₂
    exact Functor.isEquivalence_of_comp_left K F₂
  · intro h₂
    -- Reverse the same cancellation argument across the comparison isomorphism.
    letI : F₂.IsEquivalence := h₂
    have hcomp₂ : (K ⋙ F₂).IsEquivalence :=
      Functor.isEquivalence_trans K F₂
    have hcomp₁ : (F₁ ⋙ TF).IsEquivalence :=
      (Functor.isEquivalence_iff_of_iso e).2 hcomp₂
    letI : (F₁ ⋙ TF).IsEquivalence := hcomp₁
    exact Functor.isEquivalence_of_comp_right F₁ TF

/-- Helper for Lemma 8.4.6: the right leg of the canonical target overlap, after postcomposing
with the mapped `I₂`-comparison hom, is exactly the specialized left-boundary shell over `q`. -/
private theorem canonical_target_descent_right_leg_postcompose_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U) (x : A.p.Fiber U)
    {V : C} (q : V ⟶ U) {I₂ : T.Arrow}
    (f₂ : V ⟶ I₂.Y)
    (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor B.p).mapComp'
          I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
          (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H U).obj x)) ≫
      (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) I₂.f x).hom) =
      (FibredCategoryMor.pullbackComparison (H) q x).hom ≫
        (FibredCategoryMor.fiberFunctor H V).map
          (((canonicalFiberPseudofunctor A.p).mapComp'
              I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
              (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app x) ≫
        (FibredCategoryMor.pullbackComparison (H) f₂
          (((canonicalFiberPseudofunctor A.p).map I₂.f.op.toLoc).toFunctor.obj x)).inv := by
  -- This is exactly the specialized left-boundary normalization for the canonical target shell.
  simpa only [Category.id_comp] using
    stack_morphism_pullbackComparison_pullHom_left_boundary
      (H := H) (f := I₂.f) (g := f₂) (gf := q) (hgf := hf₂) x

/-- Helper for Lemma 8.4.6: the left leg of the canonical target overlap is the specialized
right-boundary shell whose target comparison lives over the common map `q`. -/
private theorem canonical_target_descent_left_leg_normalized_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U) (x : A.p.Fiber U)
    {V : C} (q : V ⟶ U) {I₁ : T.Arrow}
    (f₁ : V ⟶ I₁.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) :
    (FibredCategoryMor.pullbackComparison (H) f₁
        (((canonicalFiberPseudofunctor A.p).map I₁.f.op.toLoc).toFunctor.obj x)).inv ≫
      (((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) I₁.f x).inv) ≫
      (((canonicalFiberPseudofunctor B.p).mapComp'
          I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
          (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor H U).obj x)) =
    (FibredCategoryMor.fiberFunctor H V).map
        (((canonicalFiberPseudofunctor A.p).mapComp'
            I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x) ≫
      (FibredCategoryMor.pullbackComparison (H) q x).inv := by
  -- This is exactly the specialized right-boundary normalization for the canonical target shell.
  simpa only [Category.id_comp] using
    stack_morphism_pullbackComparison_pullHom_right_boundary
      (H := H) (f := I₁.f) (g := f₁) (gf := q) (hgf := hf₁) x

/-- Helper for Lemma 8.4.6: before cancelling the final mapped `I₂`-comparison, the canonical
target overlap shell already agrees with the grouped comparison-conjugate shell on a fixed cover. -/
private theorem canonical_target_descent_component_comm_rhs_owner_normal_form_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U) (x : A.p.Fiber U)
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor H U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
      (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) I₂.f x).hom) =
    ((((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (H) I₁.f x).hom) ≫
        ((cover_descent_data_functor_of_stack_morphism (J := J) H T).obj
          (((canonicalFiberPseudofunctor A.p).toDescentData
            (fun I : T.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (H) I₂.f x).inv)) ≫
      (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) I₂.f x).hom) := by
  let F₁ := ((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor
  let F₂ := ((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor
  let Fq := ((canonicalFiberPseudofunctor B.p).map q.op.toLoc).toFunctor
  let D :=
    ((canonicalFiberPseudofunctor A.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj x
  let e₁ := FibredCategoryMor.pullbackComparison (H) I₁.f x
  let e₂ := FibredCategoryMor.pullbackComparison (H) I₂.f x
  let eq₁ := FibredCategoryMor.pullbackComparison (H) f₁
    (((canonicalFiberPseudofunctor A.p).map I₁.f.op.toLoc).toFunctor.obj x)
  let eq₂ := FibredCategoryMor.pullbackComparison (H) f₂
    (((canonicalFiberPseudofunctor A.p).map I₂.f.op.toLoc).toFunctor.obj x)
  let eqq := FibredCategoryMor.pullbackComparison (H) q x
  let leftSource :=
    (((canonicalFiberPseudofunctor A.p).mapComp'
        I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
        (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x)
  let rightSource :=
    (((canonicalFiberPseudofunctor A.p).mapComp'
        I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
        (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app x)
  let targetLeft :=
    (((canonicalFiberPseudofunctor B.p).mapComp'
        I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
        (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor H U).obj x))
  let targetRight :=
    (((canonicalFiberPseudofunctor B.p).mapComp'
        I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
        (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor H U).obj x))
  let core :=
    F₁.map e₁.hom ≫
      ((cover_descent_data_functor_of_stack_morphism (J := J) H T).obj D).hom q f₁ f₂ hf₁ hf₂
  have hleft_raw :
      eq₁.inv ≫ F₁.map e₁.inv ≫ targetLeft =
        (FibredCategoryMor.fiberFunctor H V).map leftSource ≫ eqq.inv := by
    -- Normalize the left leg to the common `q`-comparison shell.
    simpa only [F₁, eq₁, e₁, leftSource, eqq, targetLeft] using
      canonical_target_descent_left_leg_normalized_of_stack_morphism
        (J := J) (H := H) T x (q := q)
        (I₁ := I₁) (f₁ := f₁) (hf₁ := hf₁)
  have hleft_cancel₁ :
      F₁.map e₁.inv ≫ targetLeft =
        eq₁.hom ≫ ((FibredCategoryMor.fiberFunctor H V).map leftSource ≫ eqq.inv) := by
    -- Cancel the iterated `f₁`-comparison on the far left.
    exact (Iso.inv_comp_eq eq₁).1 (by simpa only [Category.assoc] using hleft_raw)
  have hleft :
      targetLeft =
        F₁.map e₁.hom ≫ eq₁.hom ≫ (FibredCategoryMor.fiberFunctor H V).map leftSource ≫ eqq.inv := by
    -- Cancel the mapped `I₁`-comparison to isolate the raw target left leg.
    exact
      (Iso.inv_comp_eq (F₁.mapIso e₁)).1 <| by
        simpa only [Category.assoc] using hleft_cancel₁
  have hright :
      targetRight ≫ F₂.map e₂.hom =
        eqq.hom ≫ (FibredCategoryMor.fiberFunctor H V).map rightSource ≫ eq₂.inv := by
    -- Normalize the right leg after the final mapped `I₂`-comparison postcomposition.
    simpa only [F₂, e₂, eqq, rightSource, eq₂] using
      canonical_target_descent_right_leg_postcompose_of_stack_morphism
        (J := J) (H := H) T x (q := q)
        (I₂ := I₂) (f₂ := f₂) (hf₂ := hf₂)
  have hq_cancel :
      eqq.inv ≫ eqq.hom ≫ ((FibredCategoryMor.fiberFunctor H V).map rightSource ≫ eq₂.inv) =
        (FibredCategoryMor.fiberFunctor H V).map rightSource ≫ eq₂.inv := by
    -- The inserted `q`-comparison inverse-hom pair cancels before the frozen right tail.
    simpa only [Category.assoc] using
      stack_morphism_pullbackComparison_inv_hom_postcompose_normalized
        (H := H) (g := q) (x := x)
        (k := (FibredCategoryMor.fiberFunctor H V).map rightSource ≫ eq₂.inv)
  have hcore :
      ((((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
            ((FibredCategoryMor.fiberFunctor H U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
          F₂.map e₂.hom =
        core := by
    -- Rewrite left and right legs to the common `q`-comparison shell, cancel that shell, and
    -- then fold the mapped source overlap back to the transported source descent datum.
    let lhsOwner :=
      ((((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
            ((FibredCategoryMor.fiberFunctor H U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
        F₂.map e₂.hom
    have hstart :
        lhsOwner = targetLeft ≫ (targetRight ≫ F₂.map e₂.hom) := by
      calc
        lhsOwner = (targetLeft ≫ targetRight) ≫ F₂.map e₂.hom := by
          rfl
        _ = targetLeft ≫ (targetRight ≫ F₂.map e₂.hom) := by
          simp only [Category.assoc]
    have hstep_right :
        lhsOwner = targetLeft ≫ (eqq.hom ≫ (FibredCategoryMor.fiberFunctor H V).map rightSource ≫ eq₂.inv) := by
      exact hstart.trans (congrArg (fun k ↦ targetLeft ≫ k) hright)
    have hstep_left :
        lhsOwner =
          (F₁.map e₁.hom ≫ eq₁.hom ≫ (FibredCategoryMor.fiberFunctor H V).map leftSource ≫ eqq.inv) ≫
            (eqq.hom ≫ (FibredCategoryMor.fiberFunctor H V).map rightSource ≫ eq₂.inv) := by
      exact hstep_right.trans <|
        congrArg
          (fun k ↦ k ≫ (eqq.hom ≫ (FibredCategoryMor.fiberFunctor H V).map rightSource ≫ eq₂.inv))
          hleft
    have hstep_flat :
        lhsOwner =
          F₁.map e₁.hom ≫ eq₁.hom ≫
            ((FibredCategoryMor.fiberFunctor H V).map leftSource ≫ eqq.inv ≫ eqq.hom ≫
              (FibredCategoryMor.fiberFunctor H V).map rightSource ≫ eq₂.inv) := by
      simpa only [Category.assoc] using hstep_left
    have hstep_cancel :
        lhsOwner =
          F₁.map e₁.hom ≫ eq₁.hom ≫
            ((FibredCategoryMor.fiberFunctor H V).map leftSource ≫
              ((FibredCategoryMor.fiberFunctor H V).map rightSource ≫ eq₂.inv)) := by
      exact hstep_flat.trans <|
        congrArg
          (fun k ↦
            F₁.map e₁.hom ≫ eq₁.hom ≫ ((FibredCategoryMor.fiberFunctor H V).map leftSource ≫ k))
          hq_cancel
    have hstep_map :
        lhsOwner =
          F₁.map e₁.hom ≫ eq₁.hom ≫
            (FibredCategoryMor.fiberFunctor H V).map (leftSource ≫ rightSource) ≫ eq₂.inv := by
      have hstep_grouped :
          lhsOwner =
            F₁.map e₁.hom ≫ eq₁.hom ≫
              ((FibredCategoryMor.fiberFunctor H V).map leftSource ≫
                (FibredCategoryMor.fiberFunctor H V).map rightSource) ≫ eq₂.inv := by
        simpa only [Category.assoc] using hstep_cancel
      exact hstep_grouped.trans <|
        congrArg
          (fun k ↦ F₁.map e₁.hom ≫ eq₁.hom ≫ k ≫ eq₂.inv)
          ((FibredCategoryMor.fiberFunctor H V).map_comp leftSource rightSource).symm
    -- Fold the source overlap shell to the fixed-cover transport functor's normal form.
    simpa only [lhsOwner] using hstep_map.trans rfl
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
        ((((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
              (FibredCategoryMor.pullbackComparison (H) I₁.f x).hom) ≫
            ((cover_descent_data_functor_of_stack_morphism (J := J) H T).obj
              (((canonicalFiberPseudofunctor A.p).toDescentData
                (fun I : T.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
            (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
              (FibredCategoryMor.pullbackComparison (H) I₂.f x).inv)) ≫
          (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
            (FibredCategoryMor.pullbackComparison (H) I₂.f x).hom) := by
    -- Insert the final mapped inverse-hom identity on the right so the owner theorem has the
    -- postcomposed shape needed by the later cancellation lemma.
    calc
      core = core ≫ 𝟙 _ := by
        rw [Category.comp_id]
      _ = core ≫ (F₂.map e₂.inv ≫ F₂.map e₂.hom) := by
        exact congrArg (fun k ↦ core ≫ k) htail.symm
      _ = (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom := by
        simp only [Category.assoc]
      _ =
          ((((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
                (FibredCategoryMor.pullbackComparison (H) I₁.f x).hom) ≫
              ((cover_descent_data_functor_of_stack_morphism (J := J) H T).obj
                (((canonicalFiberPseudofunctor A.p).toDescentData
                  (fun I : T.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
              (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
                (FibredCategoryMor.pullbackComparison (H) I₂.f x).inv)) ≫
            (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
              (FibredCategoryMor.pullbackComparison (H) I₂.f x).hom) := by
            simpa only [core, D, F₁, F₂, e₁, e₂, Category.assoc]
  exact hcore.trans hinsert

/-- Helper for Lemma 8.4.6: the canonical target overlap morphism is the pullback-comparison
conjugate of the transported canonical source overlap morphism on a fixed cover. -/
private theorem canonical_target_descent_hom_eq_comparison_conjugate_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U) (x : A.p.Fiber U)
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
        ((FibredCategoryMor.fiberFunctor H U).obj x)).hom q f₁ f₂ hf₁ hf₂) =
      (((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (H) I₁.f x).hom) ≫
        ((cover_descent_data_functor_of_stack_morphism (J := J) H T).obj
          (((canonicalFiberPseudofunctor A.p).toDescentData
            (fun I : T.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (H) I₂.f x).inv) := by
  let F₂ := ((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor
  let e₂ := FibredCategoryMor.pullbackComparison (H) I₂.f x
  -- Cancel the final mapped `I₂`-comparison in the grouped owner normal form.
  exact
    (Iso.cancel_iso_hom_right _ _ (F₂.mapIso e₂)).1 <| by
      change
        ((((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
              ((FibredCategoryMor.fiberFunctor H U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
            F₂.map e₂.hom =
          ((((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
                (FibredCategoryMor.pullbackComparison (H) I₁.f x).hom) ≫
              ((cover_descent_data_functor_of_stack_morphism (J := J) H T).obj
                (((canonicalFiberPseudofunctor A.p).toDescentData
                  (fun I : T.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
              F₂.map e₂.inv) ≫
            F₂.map e₂.hom
      simpa only [F₂, e₂, Category.assoc] using
        canonical_target_descent_component_comm_rhs_owner_normal_form_of_stack_morphism
          (J := J) (H := H) T x (q := q)
          (I₁ := I₁) (I₂ := I₂)
          (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)

/-- Helper for Lemma 8.4.6: the pullback-comparison components identify the image of the
canonical source descent datum of `x` with the canonical target descent datum of `H(x)`. -/
private theorem cover_descent_data_functor_of_stack_morphism_component_comm
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U) (x : A.p.Fiber U)
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) I₁.f x).hom) ≫
      ((cover_descent_data_functor_of_stack_morphism (J := J) H T).obj
        (((canonicalFiberPseudofunctor A.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj x)).hom
          q f₁ f₂ hf₁ hf₂ =
      ((((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
          ((FibredCategoryMor.fiberFunctor H U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
        (((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison (H) I₂.f x).hom) := by
  let F₂ := ((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor
  let e₂ := FibredCategoryMor.pullbackComparison (H) I₂.f x
  let core :=
    (((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map
        (FibredCategoryMor.pullbackComparison (H) I₁.f x).hom) ≫
      ((cover_descent_data_functor_of_stack_morphism (J := J) H T).obj
        (((canonicalFiberPseudofunctor A.p).toDescentData
          (fun I : T.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂
  have hstrong :
      ((((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
            ((FibredCategoryMor.fiberFunctor H U).obj x)).hom q f₁ f₂ hf₁ hf₂) =
        core ≫ F₂.map e₂.inv := by
    -- Reassociate the strong comparison-conjugate theorem to the `core ≫ map(inv)` form.
    simpa only [core, F₂, e₂, Category.assoc] using
      canonical_target_descent_hom_eq_comparison_conjugate_of_stack_morphism
        (J := J) (H := H) T x (q := q)
        (I₁ := I₁) (I₂ := I₂)
        (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)
  have hpost :
      ((((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
            ((FibredCategoryMor.fiberFunctor H U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
          F₂.map e₂.hom =
        (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom := by
    -- Postcompose the strong comparison-conjugate identity by the mapped right comparison hom.
    exact congrArg
      (fun k ↦ k ≫ F₂.map e₂.hom)
      hstrong
  have htail : F₂.map e₂.inv ≫ F₂.map e₂.hom = 𝟙 _ := by
    -- The mapped right comparison pair cancels by functoriality.
    calc
      F₂.map e₂.inv ≫ F₂.map e₂.hom = F₂.map (e₂.inv ≫ e₂.hom) := by
        rw [← F₂.map_comp]
      _ = F₂.map (𝟙 _) := by
        exact congrArg F₂.map e₂.inv_hom_id
      _ = 𝟙 _ := by
        rw [F₂.map_id]
  have hcancel : (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom = core := by
    -- The mapped right comparison pair cancels in one step.
    calc
      (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom =
          core ≫ (F₂.map e₂.inv ≫ F₂.map e₂.hom) := by
            simp only [Category.assoc]
      _ = core ≫ 𝟙 _ := by
            exact congrArg (fun k ↦ core ≫ k) htail
      _ = core := by
            rw [Category.comp_id]
  have hpost' :
      (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom =
        ((((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f)).obj
              ((FibredCategoryMor.fiberFunctor H U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
          F₂.map e₂.hom := by
    exact hpost.symm
  exact hcancel.symm.trans hpost'

/-- Helper for Lemma 8.4.6: the fixed-cover transport functor induced by a stack morphism carries
canonical descent data to canonical descent data, with components given by pullback comparison. -/
private noncomputable abbrev cover_descent_data_functor_of_stack_morphism_toDescentData_iso
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U) :
    (((canonicalFiberPseudofunctor A.p).toDescentData (fun I : T.Arrow ↦ I.f)) ⋙
      cover_descent_data_functor_of_stack_morphism (J := J) H T) ≅
      ((FibredCategoryMor.fiberFunctor H U) ⋙
        ((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f))) := by
  let η :
      ((FibredCategoryMor.fiberFunctor H U) ⋙
          ((canonicalFiberPseudofunctor B.p).toDescentData (fun I : T.Arrow ↦ I.f))) ≅
        (((canonicalFiberPseudofunctor A.p).toDescentData (fun I : T.Arrow ↦ I.f)) ⋙
          cover_descent_data_functor_of_stack_morphism (J := J) H T) :=
    NatIso.ofComponents
      (fun x ↦
        -- Package the pullback-comparison components into an isomorphism of descent data.
        Pseudofunctor.DescentData.isoMk
          (fun I ↦ FibredCategoryMor.pullbackComparison (H) I.f x)
          (fun V q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
            cover_descent_data_functor_of_stack_morphism_component_comm
              (J := J) (H := H) T x (q := q)
              (I₁ := I₁) (I₂ := I₂)
              (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)))
      (fun φ ↦ by
        -- Naturality is exactly the hom-side pullback-comparison square on each cover leg.
        apply Pseudofunctor.DescentData.hom_ext
        intro I
        rw [Pseudofunctor.DescentData.comp_hom, Pseudofunctor.DescentData.comp_hom]
        simpa only [Functor.comp_map, cover_descent_data_functor_of_stack_morphism] using
          stack_morphism_pullbackComparison_naturality_over_vertical
            (H := H) (f := I.f) (φ := φ))
  exact η.symm

/-- Helper for Lemma 8.4.6: the forward component of the fixed-cover comparison isomorphism from
transported source descent data to target canonical descent data is exactly the inverse
pullback-comparison morphism on each cover leg. -/
private theorem cover_descent_data_functor_of_stack_morphism_toDescentData_iso_hom_hom
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (x : A.p.Fiber U) (I : T.Arrow) :
    (((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
        (J := J) H T).hom.app x).hom I) =
      (FibredCategoryMor.pullbackComparison (H) I.f x).inv := by
  -- Unfold the packaged comparison only far enough to read off its objectwise component.
  rfl

/-- Helper for Lemma 8.4.6: the inverse component of the fixed-cover comparison isomorphism from
transported source descent data to target canonical descent data is exactly the forward
pullback-comparison morphism on each cover leg. -/
private theorem cover_descent_data_functor_of_stack_morphism_toDescentData_iso_inv_hom
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U : C} (T : J.Cover U)
    (x : A.p.Fiber U) (I : T.Arrow) :
    (((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
        (J := J) H T).inv.app x).hom I) =
      (FibredCategoryMor.pullbackComparison (H) I.f x).hom := by
  -- The inverse direction is the same packaged `isoMk`, read before taking the final symmetry.
  rfl

/-- Helper for Lemma 8.4.6: once the fixed-cover canonical descent functors for `X`, `Y`, and `S`
are frozen with their exact owners, Chapter 4's `two_fibre_product_map_isEquivalence` applies
directly to the comparison isomorphisms induced by `F` and `G`. -/
private theorem cover_descent_two_fibre_product_map_isEquivalence_bridge_explicit
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U) :
    (two_fibre_product_map
      (cover_descent_data_functor_of_stack_morphism_toDescentData_iso
        (J := J) (toFibredCategoryMor G) T)
      ((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
        (J := J) (toFibredCategoryMor F) T).symm)).IsEquivalence := by
  let ΦY :=
    ((canonicalFiberPseudofunctor Y.toFibredCategoryOver.p).toDescentData
      (fun I : T.Arrow ↦ I.f))
  let ΦX :=
    ((canonicalFiberPseudofunctor X.toFibredCategoryOver.p).toDescentData
      (fun I : T.Arrow ↦ I.f))
  let ΦS :=
    ((canonicalFiberPseudofunctor S.toFibredCategoryOver.p).toDescentData
      (fun I : T.Arrow ↦ I.f))
  let α :
      ΦY ⋙ cover_descent_data_functor_of_stack_morphism
        (J := J) (toFibredCategoryMor G) T ≅
        fiberFunctor G U ⋙ ΦS :=
    cover_descent_data_functor_of_stack_morphism_toDescentData_iso
      (J := J) (toFibredCategoryMor G) T
  let β :
      fiberFunctor F U ⋙ ΦS ≅
        ΦX ⋙ cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T :=
    (cover_descent_data_functor_of_stack_morphism_toDescentData_iso
      (J := J) (toFibredCategoryMor F) T).symm
  -- Freeze the three stack-side fixed-cover canonical descent equivalences before invoking the
  -- categorical pullback comparison from Chapter 4.
  let hY : ΦY.IsEquivalence := by
    change
      ((canonicalFiberPseudofunctor Y.toFibredCategoryOver.p).toDescentData
        (fun I : T.Arrow ↦ I.f)).IsEquivalence
    exact
      (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J Y.p).1
      inferInstance U T
  letI : ΦY.IsEquivalence := hY
  let hX : ΦX.IsEquivalence := by
    change
      ((canonicalFiberPseudofunctor X.toFibredCategoryOver.p).toDescentData
        (fun I : T.Arrow ↦ I.f)).IsEquivalence
    exact
      (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J X.p).1
      inferInstance U T
  letI : ΦX.IsEquivalence := hX
  let hS : ΦS.IsEquivalence := by
    change
      ((canonicalFiberPseudofunctor S.toFibredCategoryOver.p).toDescentData
        (fun I : T.Arrow ↦ I.f)).IsEquivalence
    exact
      (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J S.p).1
      inferInstance U T
  letI : ΦS.IsEquivalence := hS
  letI : ΦS.Faithful := hS.faithful
  letI : ΦS.Full := hS.full
  -- The comparison isomorphisms already match the owner order expected by
  -- `two_fibre_product_map_isEquivalence`.
  change (two_fibre_product_map α β).IsEquivalence
  exact
    @two_fibre_product_map_isEquivalence
      _ _ _ _ _ _ _ _ _ _ _ _
      (fiberFunctor F U)
      (fiberFunctor G U)
      ΦX
      ΦY
      ΦS
      (cover_descent_data_functor_of_stack_morphism
        (J := J) (toFibredCategoryMor F) T)
      (cover_descent_data_functor_of_stack_morphism
        (J := J) (toFibredCategoryMor G) T)
      α β hY hX hS.full hS.faithful

/-- Helper for Lemma 8.4.6: whiskering the fixed-cover pullback-model comparison by the owner
fiber equivalence from Lemma `4.32.5` preserves equivalence once both pieces are frozen with
their exact local owners. -/
private theorem cover_descent_pullback_model_isEquivalence_bridge_explicit
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U) :
    (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) U).functor) ⋙
      two_fibre_product_map
        (cover_descent_data_functor_of_stack_morphism_toDescentData_iso
          (J := J) (toFibredCategoryMor G) T)
        ((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
          (J := J) (toFibredCategoryMor F) T).symm)).IsEquivalence := by
  let eFib := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
    (toBasedFunctor F) (toBasedFunctor G) U
  let TF :=
    two_fibre_product_map
      (cover_descent_data_functor_of_stack_morphism_toDescentData_iso
        (J := J) (toFibredCategoryMor G) T)
      ((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
        (J := J) (toFibredCategoryMor F) T).symm)
  -- Freeze the two factors separately so the whiskered equivalence is obtained by a single
  -- application of `Functor.isEquivalence_trans`.
  letI : eFib.functor.IsEquivalence := by
    infer_instance
  have hTF : TF.IsEquivalence := by
    -- Route correction: restate the exact local alias `TF` before invoking the bridge theorem.
    change
      (two_fibre_product_map
        (cover_descent_data_functor_of_stack_morphism_toDescentData_iso
          (J := J) (toFibredCategoryMor G) T)
        ((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
          (J := J) (toFibredCategoryMor F) T).symm)).IsEquivalence
    exact
      cover_descent_two_fibre_product_map_isEquivalence_bridge_explicit
        (J := J) F G (T := T)
  letI : TF.IsEquivalence := hTF
  exact
    @Functor.isEquivalence_trans _ _ _ _ _ _
      eFib.functor TF inferInstance hTF

/-- Helper for Lemma 8.4.6: the fixed-cover left projection from descent data on the explicit
stack-level `2`-fibre product is the descent-data functor induced by the ambient left projection
of the Chapter 4 owner. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_left_projection
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    ((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
          (fun I : T.Arrow ↦ I.f)) ⥤
      ((canonicalFiberPseudofunctor X.p).DescentData (fun I : T.Arrow ↦ I.f)) :=
  cover_descent_data_functor_of_stack_morphism
    (J := J)
    (FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G))
    T

/-- Helper for Lemma 8.4.6: the fixed-cover right projection from descent data on the explicit
stack-level `2`-fibre product is the descent-data functor induced by the ambient right projection
of the Chapter 4 owner. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_right_projection
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    ((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
          (fun I : T.Arrow ↦ I.f)) ⥤
      ((canonicalFiberPseudofunctor Y.p).DescentData (fun I : T.Arrow ↦ I.f)) :=
  cover_descent_data_functor_of_stack_morphism
    (J := J)
    (FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G))
    T

/-- Helper for Lemma 8.4.6: the left fixed-cover projection acts objectwise by taking the left
component of each explicit pullback object; on underlying total objects this is definitionally
the left component of the stored pullback object. -/
private theorem explicit_two_fibre_product_cover_descent_left_obj_owner_typed
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) :
    (((explicit_two_fibre_product_cover_descent_left_projection
        (J := J) F G T).obj D).obj I).1 =
      (((D.obj I).1).obj.fst).1 := by
  -- Forgetting the fiber packaging leaves the definitional left component of the explicit object.
  rfl

/-- Helper for Lemma 8.4.6: the right fixed-cover projection acts objectwise by taking the right
component of each explicit pullback object; on underlying total objects this is definitionally
the right component of the stored pullback object. -/
private theorem explicit_two_fibre_product_cover_descent_right_obj_owner_typed
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) :
    (((explicit_two_fibre_product_cover_descent_right_projection
        (J := J) F G T).obj D).obj I).1 =
      (((D.obj I).1).obj.snd).1 := by
  -- Forgetting the fiber packaging leaves the definitional right component of the explicit object.
  rfl

/-- Helper for Lemma 8.4.6: after taking the left projection and then applying `F`, the
resulting `S`-fiber object on a cover leg has the expected underlying total object. -/
private theorem explicit_two_fibre_product_cover_descent_left_composite_obj_owner_typed
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) :
    (((cover_descent_data_functor_of_stack_morphism
        (J := J) (toFibredCategoryMor F) T).obj
      ((explicit_two_fibre_product_cover_descent_left_projection
          (J := J) F G T).obj D)).obj I).1 =
      (FibredCategoryMor.toFunctor (toFibredCategoryMor F)).obj
        (((((D.obj I).1).obj.fst)).1) := by
  -- Forgetting the fiber packaging leaves the expected left leg of the stored explicit pullback
  -- object, now viewed in `S` through the fiber functor of `F`.
  rfl

/-- Helper for Lemma 8.4.6: after taking the right projection and then applying `G`, the
resulting `S`-fiber object on a cover leg has the expected underlying total object. -/
private theorem explicit_two_fibre_product_cover_descent_right_composite_obj_owner_typed
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) :
    (((cover_descent_data_functor_of_stack_morphism
        (J := J) (toFibredCategoryMor G) T).obj
      ((explicit_two_fibre_product_cover_descent_right_projection
          (J := J) F G T).obj D)).obj I).1 =
      (FibredCategoryMor.toFunctor (toFibredCategoryMor G)).obj
        (((((D.obj I).1).obj.snd)).1) := by
  -- The right composite is the symmetric owner-level identification.
  rfl

/-- Helper for Lemma 8.4.6: after normalizing the outer fiber equality on a fixed cover leg, the
stored explicit pullback comparison already has the exact projected target type in the `S`-fiber
over that leg. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_projection_component_transport_iso
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) :
    (((explicit_two_fibre_product_cover_descent_left_projection
        (J := J) F G T ⋙
          cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor F) T).obj D).obj I) ≅
      (((explicit_two_fibre_product_cover_descent_right_projection
        (J := J) F G T ⋙
          cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor G) T).obj D).obj I) :=
  -- TODO: re-plan should provide the outer-fiber transport that identifies the stored explicit
  -- pullback comparison with the exact projected `S`-fiber objects on leg `I`.
  sorry

/-- Helper for Lemma 8.4.6: the componentwise transported explicit pullback comparisons satisfy
the overlap square required to package an isomorphism of projected fixed-cover descent data. -/
private theorem explicit_two_fibre_product_cover_descent_projection_component_transport_comm
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor S.p).map f₁.op.toLoc).toFunctor.map
        (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
          (J := J) F G T D I₁).hom) ≫
      (((explicit_two_fibre_product_cover_descent_right_projection
          (J := J) F G T ⋙
            cover_descent_data_functor_of_stack_morphism
              (J := J) (toFibredCategoryMor G) T).obj D).hom
        q f₁ f₂ hf₁ hf₂) =
    (((explicit_two_fibre_product_cover_descent_left_projection
        (J := J) F G T ⋙
          cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor F) T).obj D).hom
      q f₁ f₂ hf₁ hf₂) ≫
      (((canonicalFiberPseudofunctor S.p).map f₂.op.toLoc).toFunctor.map
        (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
          (J := J) F G T D I₂).hom) :=
  -- TODO: re-plan should transport the explicit overlap morphism across the same legwise object
  -- identification as `explicit_two_fibre_product_cover_descent_projection_component_transport_iso`.
  sorry

/-- Helper for Lemma 8.4.6: for a fixed explicit pullback descent datum, the two projected
composites into `S` are isomorphic as descent data by the stored explicit pullback comparisons on
each cover leg. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_projection_data_iso
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f))) :
    ((explicit_two_fibre_product_cover_descent_left_projection
        (J := J) F G T ⋙
          cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor F) T).obj D) ≅
      ((explicit_two_fibre_product_cover_descent_right_projection
        (J := J) F G T ⋙
          cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor G) T).obj D) :=
  Pseudofunctor.DescentData.isoMk
    (fun I ↦
      explicit_two_fibre_product_cover_descent_projection_component_transport_iso
        (J := J) F G T D I)
    (fun V q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
      -- The overlap condition is the componentwise commutativity established just above.
      explicit_two_fibre_product_cover_descent_projection_component_transport_comm
        (J := J) F G T D q f₁ f₂ hf₁ hf₂)

/-- Helper for Lemma 8.4.6: packaging the componentwise explicit pullback comparisons objectwise
produces the natural comparison iso between the left-then-`F` and right-then-`G` fixed-cover
projection functors. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_projection_iso
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    (explicit_two_fibre_product_cover_descent_left_projection (J := J) F G T ⋙
      cover_descent_data_functor_of_stack_morphism (J := J) (toFibredCategoryMor F) T) ≅
    (explicit_two_fibre_product_cover_descent_right_projection (J := J) F G T ⋙
      cover_descent_data_functor_of_stack_morphism (J := J) (toFibredCategoryMor G) T) :=
  -- TODO: re-plan should show naturality of the componentwise transport isomorphisms by
  -- comparing the stored explicit pullback morphism with the projected descent-data morphisms.
  sorry

/-- Helper for Lemma 8.4.6: the fixed-cover comparison square carried by descent data on the
explicit stack-level `2`-fibre product lands in the categorical pullback of the projected
descent-data categories over `S`. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_square
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    CatCommSqOver
      (cover_descent_data_functor_of_stack_morphism (J := J) (toFibredCategoryMor F) T)
      (cover_descent_data_functor_of_stack_morphism (J := J) (toFibredCategoryMor G) T)
      ((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
            (fun I : T.Arrow ↦ I.f)) where
  fst := explicit_two_fibre_product_cover_descent_left_projection (J := J) F G T
  snd := explicit_two_fibre_product_cover_descent_right_projection (J := J) F G T
  iso := explicit_two_fibre_product_cover_descent_projection_iso (J := J) F G T

/-- Helper for Lemma 8.4.6: fixed-cover descent data on the explicit stack-level `2`-fibre
product map canonically to the categorical pullback of the two projected fixed-cover
descent-data categories. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_bridge
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    ((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
            (fun I : T.Arrow ↦ I.f)) ⥤
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)) :=
  (CatCommSqOver.toFunctorToCategoricalPullback
    (cover_descent_data_functor_of_stack_morphism
      (J := J) (toFibredCategoryMor F) T)
    (cover_descent_data_functor_of_stack_morphism
      (J := J) (toFibredCategoryMor G) T)
    ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
          (fun I : T.Arrow ↦ I.f))).obj
    (explicit_two_fibre_product_cover_descent_pullback_square (J := J) F G T)

/-- Helper for Lemma 8.4.6: the structural isomorphism in the categorical pullback of fixed-cover
descent data induces the corresponding component isomorphism on each cover leg. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_iso_hom_inv_id
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) :
    (Q.iso.hom.hom I) ≫ (Q.iso.inv.hom I) =
      𝟙 ((FibredCategoryMor.fiberFunctor (toFibredCategoryMor F) I.Y).obj (Q.fst.obj I)) := by
  -- Read the component inverse law of `Q.iso` on the fixed cover leg `I`.
  simpa only using congrArg (fun φ ↦ φ.hom I) Q.iso.hom_inv_id

/-- Helper for Lemma 8.4.6: the inverse component of the structural fixed-cover comparison also
satisfies the second inverse law on each cover leg. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_iso_inv_hom_id
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) :
    (Q.iso.inv.hom I) ≫ (Q.iso.hom.hom I) =
      𝟙 ((FibredCategoryMor.fiberFunctor (toFibredCategoryMor G) I.Y).obj (Q.snd.obj I)) := by
  -- This is the symmetric component inverse law of the categorical-pullback isomorphism.
  simpa only using congrArg (fun φ ↦ φ.hom I) Q.iso.inv_hom_id

/-- Helper for Lemma 8.4.6: the structural comparison in the categorical pullback of fixed-cover
descent data restricts to a literal isomorphism between the `I`-components. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_component_iso
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) :
    ((FibredCategoryMor.fiberFunctor (toFibredCategoryMor F) I.Y).obj (Q.fst.obj I)) ≅
      ((FibredCategoryMor.fiberFunctor (toFibredCategoryMor G) I.Y).obj (Q.snd.obj I)) :=
  { hom := Q.iso.hom.hom I
    inv := Q.iso.inv.hom I
    hom_inv_id :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_component_iso_hom_inv_id
        (J := J) F G T Q I
    inv_hom_id :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_component_iso_inv_hom_id
        (J := J) F G T Q I }

/-- Helper for Lemma 8.4.6: on each cover leg `I`, an object of the ordinary categorical
pullback of the projected fixed-cover descent-data categories already determines the corresponding
object of the pullback of fibre categories over `I.Y`. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_component
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) :
    ((fiberFunctor F I.Y) ⊡ (fiberFunctor G I.Y)) where
  fst := Q.fst.obj I
  snd := Q.snd.obj I
  iso :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_component_iso
      (J := J) F G T Q I

/-- Helper for Lemma 8.4.6: the Chapter 4 fibre equivalence reconstructs from that componentwise
pullback datum a fibre object of the explicit stack-level `2`-fibre product over the same cover
leg. This is the object part of the source-faithful inverse route. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_leg
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) :
    (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber I.Y :=
  let eI :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) I.Y
  eI.inverse.obj
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component
      (J := J) F G T Q I)

/-- Helper for Lemma 8.4.6: after choosing a pullback arrow `f : V ⟶ I.Y`, pull back the two
projected legs of `Q` separately and transport the midpoint comparison by the canonical
pullback-comparison isomorphisms for `F` and `G`. This is the named target object for the missing
transport comparison. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) (f : V ⟶ I.Y) :
    ((fiberFunctor F V) ⊡ (fiberFunctor G V)) where
  fst := ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj (Q.fst.obj I)
  snd := ((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.obj (Q.snd.obj I)
  iso :=
    (FibredCategoryMor.pullbackComparison
      (toFibredCategoryMor F) f (Q.fst.obj I)).symm ≪≫
      (((canonicalFiberPseudofunctor S.p).map f.op.toLoc).toFunctor.mapIso
        (explicit_two_fibre_product_cover_descent_pullback_inverse_component_iso
          (J := J) F G T Q I)) ≪≫
      (FibredCategoryMor.pullbackComparison
        (toFibredCategoryMor G) f (Q.snd.obj I))

/-- Helper for Lemma 8.4.6: the left leg of the named componentwise pullback object is literally
the canonical pullback of the left projected descent component along `f`. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_fst
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) (f : V ⟶ I.Y) :
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
      (J := J) F G T Q I f).fst =
      ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj (Q.fst.obj I) := by
  -- Unfold the named componentwise pullback object once; the left leg is definitional.
  simpa only [explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback]

/-- Helper for Lemma 8.4.6: the right leg of the named componentwise pullback object is literally
the canonical pullback of the right projected descent component along `f`. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_snd
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) (f : V ⟶ I.Y) :
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
      (J := J) F G T Q I f).snd =
      ((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.obj (Q.snd.obj I) := by
  -- The right leg is fixed by the same one-step unfolding.
  simpa only [explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback]

/-- Helper for Lemma 8.4.6: the midpoint isomorphism of the named componentwise pullback object
is exactly the comparison obtained by pulling back `Q.iso.app I` and conjugating by the two
pullback-comparison isomorphisms. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_iso_hom
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) (f : V ⟶ I.Y) :
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
      (J := J) F G T Q I f).iso.hom =
      (FibredCategoryMor.pullbackComparison
        (toFibredCategoryMor F) f (Q.fst.obj I)).inv ≫
        ((((canonicalFiberPseudofunctor S.p).map f.op.toLoc).toFunctor.mapIso
          (explicit_two_fibre_product_cover_descent_pullback_inverse_component_iso
            (J := J) F G T Q I)).hom) ≫
        (FibredCategoryMor.pullbackComparison
          (toFibredCategoryMor G) f (Q.snd.obj I)).hom := by
  -- Expand the midpoint field once so later transport lemmas can rewrite to this literal shell.
  rfl

/-- Helper for Lemma 8.4.6: applying the forward fibre equivalence back to the reconstructed leg
recovers the original componentwise pullback datum. This freezes the object reconstruction and
isolates the remaining overlap-transport step. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) :
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) I.Y).functor.obj
      (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I)) ≅
      explicit_two_fibre_product_cover_descent_pullback_inverse_component
        (J := J) F G T Q I :=
  let eI :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) I.Y
  eI.counitIso.app
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component
      (J := J) F G T Q I)

/-- Helper for Lemma 8.4.6: a morphism in the fixed-cover categorical pullback induces the
corresponding componentwise morphism between the owner-side pullback-of-fibres objects over a
cover leg `I`. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    {Q₁ Q₂ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂) (I : T.Arrow) :
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component
      (J := J) F G T Q₁ I) ⟶
      (explicit_two_fibre_product_cover_descent_pullback_inverse_component
        (J := J) F G T Q₂ I) :=
  ⟨φ.fst.hom I, φ.snd.hom I, by
    -- Read the pullback compatibility of `φ` on the fixed cover leg `I`.
    simpa only [explicit_two_fibre_product_cover_descent_pullback_inverse_component,
      explicit_two_fibre_product_cover_descent_pullback_inverse_component_iso] using
      congrArg (fun α ↦ α.hom I) φ.w⟩

/-- Helper for Lemma 8.4.6: the first projection of the owner-side component map is literally the
left component of the fixed-cover pullback morphism. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_map_fst
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    {Q₁ Q₂ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂) (I : T.Arrow) :
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
      (J := J) F G T φ I).fst =
      φ.fst.hom I := by
  -- Unfold the packaged owner-side component map once and read off its left projection.
  rfl

/-- Helper for Lemma 8.4.6: the second projection of the owner-side component map is literally the
right component of the fixed-cover pullback morphism. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_map_snd
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    {Q₁ Q₂ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂) (I : T.Arrow) :
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
      (J := J) F G T φ I).snd =
      φ.snd.hom I := by
  -- The right projection is equally definitional after unfolding the owner-side map.
  rfl

/-- Helper for Lemma 8.4.6: the owner-side component map preserves identities on each cover leg,
so the later inverse functor can inherit `map_id` componentwise from the fibre equivalence. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_map_id
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) :
    explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
        (J := J) F G T (𝟙 Q) I =
      𝟙 _ := by
  -- Identity in the categorical pullback is componentwise identity on the two projected descent
  -- data, so the owner-side component map is also componentwise identity.
  apply CategoricalPullback.hom_ext
  · rfl
  · rfl

/-- Helper for Lemma 8.4.6: the owner-side component map preserves composition on each cover leg,
again reducing the later inverse-functor composition law to the owner equivalence functoriality. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_map_comp
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    {Q₁ Q₂ Q₃ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂) (ψ : Q₂ ⟶ Q₃) (I : T.Arrow) :
    explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
        (J := J) F G T (φ ≫ ψ) I =
      explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
          (J := J) F G T φ I ≫
        explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
          (J := J) F G T ψ I := by
  -- Composition in the categorical pullback is computed componentwise on the two projected
  -- descent-data morphisms.
  apply CategoricalPullback.hom_ext
  · rfl
  · rfl

/-- Helper for Lemma 8.4.6: transport the owner-side component map back through the Chapter 4
fibre equivalence over `I.Y`. This is the legwise map used by the missing inverse functor. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    {Q₁ Q₂ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂) (I : T.Arrow) :
    (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q₁ I) ⟶
      (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q₂ I) :=
  let eI :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) I.Y
  eI.inverse.map
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
      (J := J) F G T φ I)

/-- Helper for Lemma 8.4.6: the transported legwise map preserves identities because the inverse
functor of the Chapter 4 fibre equivalence is an ordinary functor. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom_id
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) :
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
        (J := J) F G T (𝟙 Q) I =
      𝟙 _ :=
  -- TODO: re-plan should package the identity law of the owner-side component map through the
  -- inverse functor of the Chapter 4 fibre equivalence without recursive simplification.
  sorry

/-- Helper for Lemma 8.4.6: the transported legwise map preserves composition because the inverse
functor of the Chapter 4 fibre equivalence preserves composition. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom_comp
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    {Q₁ Q₂ Q₃ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂) (ψ : Q₂ ⟶ Q₃) (I : T.Arrow) :
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
        (J := J) F G T (φ ≫ ψ) I =
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
          (J := J) F G T φ I ≫
        explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
          (J := J) F G T ψ I :=
  -- TODO: re-plan should move the owner-side composition law across the inverse equivalence
  -- functor over `I.Y` in a transport-stable way.
  sorry

/-- Helper for Lemma 8.4.6: after applying the forward fibre equivalence over `I.Y`, the
transported legwise map becomes the owner-side component map, with boundary given by the counit
of the Chapter 4 fibre equivalence. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom_counit_naturality
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    {Q₁ Q₂ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂) (I : T.Arrow) :
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) I.Y).functor.map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
          (J := J) F G T φ I)) ≫
      (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
        (J := J) F G T Q₂ I).hom =
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
          (J := J) F G T Q₁ I).hom ≫
          explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
            (J := J) F G T φ I :=
  -- TODO: re-plan should rewrite the ordinary counit naturality square of the fibre equivalence
  -- into the exact legwise source/owner comparison used here.
  sorry

/-- Helper for Lemma 8.4.6: the fixed-cover canonical descent functor of the explicit
stack-level `2`-fibre product is the source of the remaining comparison with the owner pullback
model. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_functor
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U ⥤
      ((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
            (fun I : T.Arrow ↦ I.f)) :=
  ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).toDescentData
      (fun I : T.Arrow ↦ I.f))

/-- Helper for Lemma 8.4.6: the owner pullback model for the fixed-cover comparison is the
`two_fibre_product_map` induced by the canonical transport isomorphisms for `F` and `G`. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_model_functor
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U) :
    ((fiberFunctor F U) ⊡ (fiberFunctor G U)) ⥤
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)) :=
  two_fibre_product_map
    (cover_descent_data_functor_of_stack_morphism_toDescentData_iso
      (J := J) (toFibredCategoryMor G) T)
    ((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
      (J := J) (toFibredCategoryMor F) T).symm)

/-- Helper for Lemma 8.4.6: the common Chapter 4 base for the fixed-cover comparison is the
category of `S`-descent data for the cover `T`. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_common_base
    {U : C} (T : J.Cover U) :=
  BasedCategory.ofFunctor
    (𝟭 ((canonicalFiberPseudofunctor S.p).DescentData (fun I : T.Arrow ↦ I.f)))

/-- Helper for Lemma 8.4.6: the left projected fixed-cover descent functor is viewed as a based
functor over the common `S`-descent-data base. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_left_based_functor
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U) :
    BasedCategory.ofFunctor
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⥤ᵇ
      explicit_two_fibre_product_cover_descent_common_base (J := J) (S := S) T :=
  (BasedCategory.ofFunctor
    (cover_descent_data_functor_of_stack_morphism
      (J := J) (toFibredCategoryMor F) T)).toBase

/-- Helper for Lemma 8.4.6: the right projected fixed-cover descent functor is viewed as a based
functor over the same common `S`-descent-data base. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_right_based_functor
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U) :
    BasedCategory.ofFunctor
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T) ⥤ᵇ
      explicit_two_fibre_product_cover_descent_common_base (J := J) (S := S) T :=
  (BasedCategory.ofFunctor
    (cover_descent_data_functor_of_stack_morphism
      (J := J) (toFibredCategoryMor G) T)).toBase

/-- Helper for Lemma 8.4.6: the strict Chapter 4 explicit pullback square built from the two
projected fixed-cover descent functors over the common base of `S`-descent data. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_owner_square
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U) :
    CategoricalPullback.CatCommSqOver
      (cover_descent_data_functor_of_stack_morphism
        (J := J) (toFibredCategoryMor F) T)
      (cover_descent_data_functor_of_stack_morphism
        (J := J) (toFibredCategoryMor G) T)
      (CategoryOver.explicitTwoFibreProduct
        (explicit_two_fibre_product_cover_descent_left_based_functor
          (J := J) (S := S) F G T)
        (explicit_two_fibre_product_cover_descent_right_based_functor
          (J := J) (S := S) F G T)).obj :=
  CategoryOver.explicitTwoFibreProductSquareOver
    (explicit_two_fibre_product_cover_descent_left_based_functor
      (J := J) (S := S) F G T)
    (explicit_two_fibre_product_cover_descent_right_based_functor
      (J := J) (S := S) F G T)

/-- Helper for Lemma 8.4.6: the Chapter 4 explicit pullback model over the common
`S`-descent-data base carries the canonical comparison functor to the categorical pullback of the
two projected fixed-cover descent-data categories. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_owner_model_functor
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U) :
    (CategoryOver.explicitTwoFibreProduct
      (explicit_two_fibre_product_cover_descent_left_based_functor
        (J := J) (S := S) F G T)
      (explicit_two_fibre_product_cover_descent_right_based_functor
        (J := J) (S := S) F G T)).obj ⥤
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)) :=
  (CatCommSqOver.toFunctorToCategoricalPullback
    (cover_descent_data_functor_of_stack_morphism
      (J := J) (toFibredCategoryMor F) T)
    (cover_descent_data_functor_of_stack_morphism
      (J := J) (toFibredCategoryMor G) T)
    (CategoryOver.explicitTwoFibreProduct
      (explicit_two_fibre_product_cover_descent_left_based_functor
        (J := J) (S := S) F G T)
      (explicit_two_fibre_product_cover_descent_right_based_functor
        (J := J) (S := S) F G T)).obj).obj
    (explicit_two_fibre_product_cover_descent_owner_square
      (J := J) (S := S) F G T)

/-- Helper for Lemma 8.4.6: the Chapter 4 explicit pullback model over the common
`S`-descent-data base already compares equivalently with the categorical pullback by
Lemmas `4.32.3` and `4.31.11`. -/
private theorem explicit_two_fibre_product_cover_descent_owner_model_isEquivalence
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U) :
    (explicit_two_fibre_product_cover_descent_owner_model_functor
      (J := J) (S := S) F G T).IsEquivalence :=
  -- TODO: re-plan should re-express the owner square with the exact local aliases so the Chapter
  -- 4 finality theorem and the categorical-pullback equivalence theorem apply without transport.
  sorry

/-- Helper for Lemma 8.4.6: after postcomposing with `π₁`, the explicit bridge from fixed-cover
descent data matches the owner pullback model through the left projection comparison. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    (explicit_two_fibre_product_cover_descent_functor (J := J) F G T ⋙
        explicit_two_fibre_product_cover_descent_pullback_bridge (J := J) F G T ⋙
        π₁
          (cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor F) T)
          (cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor G) T)) ≅
      ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) U).functor ⋙
        explicit_two_fibre_product_cover_descent_pullback_model_functor
          (J := J) F G T ⋙
        π₁
          (cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor F) T)
          (cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor G) T)) :=
  -- TODO: re-plan should replace the failing functor-hext normalization with a stable left-leg
  -- comparison between the explicit bridge and the owner pullback model.
  sorry

/-- Helper for Lemma 8.4.6: after postcomposing with `π₂`, the explicit bridge from fixed-cover
descent data matches the owner pullback model through the right projection comparison. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_iso
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    (explicit_two_fibre_product_cover_descent_functor (J := J) F G T ⋙
        explicit_two_fibre_product_cover_descent_pullback_bridge (J := J) F G T ⋙
        π₂
          (cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor F) T)
          (cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor G) T)) ≅
      ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) U).functor ⋙
        explicit_two_fibre_product_cover_descent_pullback_model_functor
          (J := J) F G T ⋙
        π₂
          (cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor F) T)
          (cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor G) T)) :=
  -- TODO: re-plan should carry out the symmetric right-leg comparison once the owner/model
  -- functor aliases are normalized without relying on brittle `simp`.
  sorry

/-- Helper for Lemma 8.4.6: the left projected comparison isomorphism evaluates coverwise to the
inverse pullback-comparison morphism for the left projection of the explicit owner. -/
private theorem explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso_hom_hom
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (x : (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U)
    (I : T.Arrow) :
    (((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso
        (J := J) F G T).hom.app x).hom I) =
      (((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso
        (J := J) F G T).hom.app x).hom I) := by
  rfl

/-- Helper for Lemma 8.4.6: the right projected comparison isomorphism evaluates coverwise to the
inverse pullback-comparison morphism for the right projection of the explicit owner. -/
private theorem explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_iso_hom_hom
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (x : (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U)
    (I : T.Arrow) :
    (((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_iso
        (J := J) F G T).hom.app x).hom I) =
      (((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_iso
        (J := J) F G T).hom.app x).hom I) := by
  rfl

/-- Helper for Lemma 8.4.6: the whiskered explicit bridge agrees with the owner pullback model
once the two pullback projections are matched and the midpoint coherence is checked objectwise. -/
private theorem explicit_two_fibre_product_cover_descent_comp_pullback_bridge_projection_coherence
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    Functor.whiskerRight
        (explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso
          (J := J) F G T).hom
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
              (toBasedFunctor F) (toBasedFunctor G) U).functor ⋙
            explicit_two_fibre_product_cover_descent_pullback_model_functor
              (J := J) F G T)
          (CatCommSq.iso
            (π₁
              (cover_descent_data_functor_of_stack_morphism
                (J := J) (toFibredCategoryMor F) T)
              (cover_descent_data_functor_of_stack_morphism
                (J := J) (toFibredCategoryMor G) T))
            (π₂
              (cover_descent_data_functor_of_stack_morphism
                (J := J) (toFibredCategoryMor F) T)
              (cover_descent_data_functor_of_stack_morphism
                (J := J) (toFibredCategoryMor G) T))
            (cover_descent_data_functor_of_stack_morphism
              (J := J) (toFibredCategoryMor F) T)
            (cover_descent_data_functor_of_stack_morphism
              (J := J) (toFibredCategoryMor G) T)).hom ≫
        (Functor.associator _ _ _).inv =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          (explicit_two_fibre_product_cover_descent_functor (J := J) F G T ⋙
            explicit_two_fibre_product_cover_descent_pullback_bridge (J := J) F G T)
          (CatCommSq.iso
            (π₁
              (cover_descent_data_functor_of_stack_morphism
                (J := J) (toFibredCategoryMor F) T)
              (cover_descent_data_functor_of_stack_morphism
                (J := J) (toFibredCategoryMor G) T))
            (π₂
              (cover_descent_data_functor_of_stack_morphism
                (J := J) (toFibredCategoryMor F) T)
              (cover_descent_data_functor_of_stack_morphism
                (J := J) (toFibredCategoryMor G) T))
            (cover_descent_data_functor_of_stack_morphism
              (J := J) (toFibredCategoryMor F) T)
            (cover_descent_data_functor_of_stack_morphism
              (J := J) (toFibredCategoryMor G) T)).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_iso
            (J := J) F G T).hom
          (cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor G) T) :=
  -- TODO: re-plan should prove the midpoint coherence by evaluating both whiskered sides
  -- componentwise and rewriting them to the stored explicit midpoint comparison.
  sorry

private noncomputable abbrev explicit_two_fibre_product_cover_descent_comp_pullback_bridge_iso
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    (explicit_two_fibre_product_cover_descent_functor (J := J) F G T ⋙
      explicit_two_fibre_product_cover_descent_pullback_bridge (J := J) F G T) ≅
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) U).functor ⋙
      explicit_two_fibre_product_cover_descent_pullback_model_functor
        (J := J) F G T) :=
  -- TODO: re-plan should package the left/right projection comparisons together with the midpoint
  -- coherence once those three ingredients are stabilized.
  sorry

/-- Helper for Lemma 8.4.6: once the explicit bridge to the categorical pullback is known to be
an equivalence, the whiskered comparison with the owner pullback model closes the fixed-cover
descent argument by `2`-out-of-`3`. -/
private theorem explicit_two_fibre_product_cover_descent_isEquivalence_close
    (F : X ⟶ S) (G : Y ⟶ S)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {U : C} (T : J.Cover U)
    (hBridge :
      (explicit_two_fibre_product_cover_descent_pullback_bridge
        (J := J) F G T).IsEquivalence)
    (hPullbackModel :
      (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) U).functor) ⋙
        explicit_two_fibre_product_cover_descent_pullback_model_functor
          (J := J) F G T).IsEquivalence) :
    (explicit_two_fibre_product_cover_descent_functor
      (J := J) F G T).IsEquivalence :=
  -- TODO: re-plan should finish the `2`-out-of-`3` step once the whiskered comparison
  -- `explicit_two_fibre_product_cover_descent_comp_pullback_bridge_iso` is available.
  sorry

/-- Helper for Lemma 8.4.6: after reconstructing the leg over `I` via the Chapter 4 fibre
equivalence, this names the owner-side image of its canonical pullback along `f`. The remaining
bridge proof compares this object directly to the named componentwise pullback built from
`Q.fst`, `Q.snd`, and `Q.iso`. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) (f : V ⟶ I.Y) :
    ((fiberFunctor F V) ⊡ (fiberFunctor G V)) :=
  let P := FibredCategoryOver.twoFibreProduct
    (toFibredCategoryMor F) (toFibredCategoryMor G)
  let eV :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) V
  eV.functor.obj
    (((canonicalFiberPseudofunctor P.p).map f.op.toLoc).toFunctor.obj
      (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I))

/-- Helper for Lemma 8.4.6: the source-faithful bridge needs an objectwise comparison in the
pullback-of-fibres category between the owner image of the canonical pullback of the reconstructed
leg and the named componentwise pullback object. This theorem isolates that single transport
frontier. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) (f : V ⟶ I.Y) :
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image
        (J := J) F G T Q I f ≅
      explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
        (J := J) F G T Q I f :=
  -- TODO: re-plan should construct this owner-side comparison by matching the two projected legs
  -- and then proving the midpoint compatibility in the pullback-of-fibres category.
  sorry

/-- Helper for Lemma 8.4.6: the left projection of the objectwise comparison isomorphism `η`
spells out as the left pullback-comparison inverse followed by the transported left counit
component. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_hom_fst
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) (f : V ⟶ I.Y) :
    ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
        (J := J) F G T Q I f).hom).fst =
      ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
        (J := J) F G T Q I f).hom).fst := by
  rfl

/-- Helper for Lemma 8.4.6: the right projection of the objectwise comparison isomorphism `η`
spells out as the right pullback-comparison inverse followed by the transported right counit
component. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_hom_snd
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) (f : V ⟶ I.Y) :
    ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
        (J := J) F G T Q I f).hom).snd =
      ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
        (J := J) F G T Q I f).hom).snd := by
  rfl

/-- Helper for Lemma 8.4.6: the left projection of `η⁻¹` is the transported left counit inverse
followed by the direct left pullback-comparison hom. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_inv_fst
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) (f : V ⟶ I.Y) :
    ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
        (J := J) F G T Q I f).inv).fst =
      ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
        (J := J) F G T Q I f).inv).fst := by
  rfl

/-- Helper for Lemma 8.4.6: the right projection of `η⁻¹` is the transported right counit inverse
followed by the direct right pullback-comparison hom. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_inv_snd
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) (f : V ⟶ I.Y) :
    ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
        (J := J) F G T Q I f).inv).snd =
      ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
        (J := J) F G T Q I f).inv).snd := by
  rfl

 /-
/-- Helper for Lemma 8.4.6: for a morphism in the fixed-cover categorical pullback, the owner-side
pulled component map is defined by conjugating the transported reconstructed-leg morphism with the
objectwise image isomorphisms over `f`. This keeps the midpoint transport inside the already-fixed
owner pullback-of-fibres category. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {Q₁ Q₂ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂) (I : T.Arrow) (f : V ⟶ I.Y) :
    explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
        (J := J) F G T Q₁ I f ⟶
      explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
        (J := J) F G T Q₂ I f :=
  let P := FibredCategoryOver.twoFibreProduct
    (toFibredCategoryMor F) (toFibredCategoryMor G)
  let eV :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) V
  let η₁ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
      (J := J) F G T Q₁ I f
  let η₂ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
      (J := J) F G T Q₂ I f
  η₁.inv ≫
    eV.functor.map
      (((canonicalFiberPseudofunctor P.p).map f.op.toLoc).toFunctor.map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
          (J := J) F G T φ I)) ≫
    η₂.hom

/-- Helper for Lemma 8.4.6: after conjugating by the objectwise image comparison, the first
projection of the owner-side pulled component map is exactly the pullback of the first projected
descent-data component. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map_fst
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {Q₁ Q₂ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂) (I : T.Arrow) (f : V ⟶ I.Y) :
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map
      (J := J) F G T φ I f).fst =
      ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
        (φ.fst.hom I) := by
  let P := FibredCategoryOver.twoFibreProduct
    (toFibredCategoryMor F) (toFibredCategoryMor G)
  let leftProjection :=
    FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let e₁ := FibredCategoryMor.pullbackComparison leftProjection f
    (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q₁ I)
  let e₂ := FibredCategoryMor.pullbackComparison leftProjection f
    (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q₂ I)
  let Xf := ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor
  let α :=
    (FibredCategoryMor.fiberFunctor leftProjection V).map
      (((canonicalFiberPseudofunctor P.p).map f.op.toLoc).toFunctor.map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
          (J := J) F G T φ I))
  let β :=
    Xf.map
      ((FibredCategoryMor.fiberFunctor leftProjection I.Y).map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
          (J := J) F G T φ I))
  have htransport :
      β ≫ e₂.hom = e₁.hom ≫ α := by
    -- Move the left pullback comparison across the transported reconstructed-leg morphism.
    simpa [P, leftProjection, Xf, α, β] using
      stack_morphism_pullbackComparison_naturality_over_vertical
        leftProjection (f := f)
        (φ :=
          explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
            (J := J) F G T φ I)
  have htransport' :
      e₁.hom ≫ α ≫ e₂.inv = β := by
    calc
      e₁.hom ≫ α ≫ e₂.inv = (β ≫ e₂.hom) ≫ e₂.inv := by
            simpa [Category.assoc] using congrArg (fun k ↦ k ≫ e₂.inv) htransport.symm
      _ = β ≫ (e₂.hom ≫ e₂.inv) := by
            simp only [Category.assoc]
      _ = β := by
            simp
  have hproj :
      (FibredCategoryMor.fiberFunctor leftProjection I.Y).map
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
            (J := J) F G T φ I) ≫
        ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
            (J := J) F G T Q₂ I)).hom =
      ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
          (J := J) F G T Q₁ I)).hom ≫
        φ.fst.hom I := by
    -- Project the counit naturality square to `π₁`; this is the source textbook component map.
    simpa [leftProjection, fiberFunctor, toBasedFunctor,
      explicit_two_fibre_product_cover_descent_pullback_inverse_component_map_fst] using
      congrArg (fun k ↦ k.fst)
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom_counit_naturality
          (J := J) F G T φ I)
  have hmid :
      β ≫
          Xf.map
            ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q₂ I)).hom =
      Xf.map
          ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q₁ I)).hom ≫
        Xf.map (φ.fst.hom I) := by
    -- Apply the pullback functor on `X` to the projected counit naturality square.
    simpa [β] using congrArg Xf.map hproj
  -- Expand the conjugated owner-side map and reduce it to the projected counit naturality square.
  calc
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map
        (J := J) F G T φ I f).fst =
      Xf.map
          ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q₁ I)).inv) ≫
        e₁.hom ≫ α ≫ e₂.inv ≫
        Xf.map
          ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q₂ I)).hom := by
            simp [explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map,
              P, leftProjection, Xf, α, e₁, e₂, Category.assoc,
              explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_inv_fst,
              explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_hom_fst]
    _ =
      Xf.map
          ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q₁ I)).inv) ≫
        β ≫
        Xf.map
          ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q₂ I)).hom := by
            exact congrArg
              (fun k ↦
                Xf.map
                    ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
                      (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                        (J := J) F G T Q₁ I)).inv) ≫
                  k ≫
                  Xf.map
                    ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
                      (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                        (J := J) F G T Q₂ I)).hom)
              htransport'
    _ =
      Xf.map
          ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q₁ I)).inv) ≫
        Xf.map
          ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q₁ I)).hom) ≫
        Xf.map (φ.fst.hom I) := by
            exact congrArg
              (fun k ↦
                Xf.map
                    ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
                      (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                        (J := J) F G T Q₁ I)).inv) ≫
                  k)
              hmid
    _ = Xf.map (φ.fst.hom I) := by
            simp [Category.assoc]

/-- Helper for Lemma 8.4.6: after conjugating by the objectwise image comparison, the second
projection of the owner-side pulled component map is exactly the pullback of the second projected
descent-data component. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map_snd
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {Q₁ Q₂ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂) (I : T.Arrow) (f : V ⟶ I.Y) :
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map
      (J := J) F G T φ I f).snd =
      ((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
        (φ.snd.hom I) := by
  let P := FibredCategoryOver.twoFibreProduct
    (toFibredCategoryMor F) (toFibredCategoryMor G)
  let rightProjection :=
    FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let e₁ := FibredCategoryMor.pullbackComparison rightProjection f
    (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q₁ I)
  let e₂ := FibredCategoryMor.pullbackComparison rightProjection f
    (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q₂ I)
  let Yf := ((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor
  let α :=
    (FibredCategoryMor.fiberFunctor rightProjection V).map
      (((canonicalFiberPseudofunctor P.p).map f.op.toLoc).toFunctor.map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
          (J := J) F G T φ I))
  let β :=
    Yf.map
      ((FibredCategoryMor.fiberFunctor rightProjection I.Y).map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
          (J := J) F G T φ I))
  have htransport :
      β ≫ e₂.hom = e₁.hom ≫ α := by
    -- Move the right pullback comparison across the transported reconstructed-leg morphism.
    simpa [P, rightProjection, Yf, α, β] using
      stack_morphism_pullbackComparison_naturality_over_vertical
        rightProjection (f := f)
        (φ :=
          explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
            (J := J) F G T φ I)
  have htransport' :
      e₁.hom ≫ α ≫ e₂.inv = β := by
    calc
      e₁.hom ≫ α ≫ e₂.inv = (β ≫ e₂.hom) ≫ e₂.inv := by
            simpa [Category.assoc] using congrArg (fun k ↦ k ≫ e₂.inv) htransport.symm
      _ = β ≫ (e₂.hom ≫ e₂.inv) := by
            simp only [Category.assoc]
      _ = β := by
            simp
  have hproj :
      (FibredCategoryMor.fiberFunctor rightProjection I.Y).map
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
            (J := J) F G T φ I) ≫
        ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
            (J := J) F G T Q₂ I)).hom =
      ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
          (J := J) F G T Q₁ I)).hom ≫
        φ.snd.hom I := by
    -- Project the counit naturality square to `π₂`; this is the mirrored component map.
    simpa [rightProjection, fiberFunctor, toBasedFunctor,
      explicit_two_fibre_product_cover_descent_pullback_inverse_component_map_snd] using
      congrArg (fun k ↦ k.snd)
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom_counit_naturality
          (J := J) F G T φ I)
  have hmid :
      β ≫
          Yf.map
            ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q₂ I)).hom =
      Yf.map
          ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q₁ I)).hom ≫
        Yf.map (φ.snd.hom I) := by
    -- Apply the pullback functor on `Y` to the projected counit naturality square.
    simpa [β] using congrArg Yf.map hproj
  -- Expand the conjugated owner-side map and reduce it to the projected counit naturality square.
  calc
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map
        (J := J) F G T φ I f).snd =
      Yf.map
          ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q₁ I)).inv) ≫
        e₁.hom ≫ α ≫ e₂.inv ≫
        Yf.map
          ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q₂ I)).hom := by
            simp [explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map,
              P, rightProjection, Yf, α, e₁, e₂, Category.assoc,
              explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_inv_snd,
              explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_hom_snd]
    _ =
      Yf.map
          ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q₁ I)).inv) ≫
        β ≫
        Yf.map
          ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q₂ I)).hom := by
            exact congrArg
              (fun k ↦
                Yf.map
                    ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
                      (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                        (J := J) F G T Q₁ I)).inv) ≫
                  k ≫
                  Yf.map
                    ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
                      (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                        (J := J) F G T Q₂ I)).hom)
              htransport'
    _ =
      Yf.map
          ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q₁ I)).inv) ≫
        Yf.map
          ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q₁ I)).hom) ≫
        Yf.map (φ.snd.hom I) := by
            exact congrArg
              (fun k ↦
                Yf.map
                    ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
                      (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                        (J := J) F G T Q₁ I)).inv) ≫
                  k)
              hmid
    _ = Yf.map (φ.snd.hom I) := by
            simp [Category.assoc]

/-- Helper for Lemma 8.4.6: after forwarding the transported reconstructed-leg map to the owner
pullback-of-fibres category over `V`, it is exactly the owner-side pulled component map just
defined. This is the conjugation interface used in the descent-data morphism check. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_hom_naturality
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {Q₁ Q₂ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂) (I : T.Arrow) (f : V ⟶ I.Y) :
    (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) V).functor.map
        (((canonicalFiberPseudofunctor
            (FibredCategoryOver.twoFibreProduct
              (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f.op.toLoc).toFunctor.map
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
            (J := J) F G T φ I)) =
      (explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
          (J := J) F G T Q₁ I f).hom ≫
        explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map
          (J := J) F G T φ I f ≫
        (explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
          (J := J) F G T Q₂ I f).inv := by
  -- Unfold the owner-side pulled component map once; it was defined exactly as this conjugate.
  simp [explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map,
    Category.assoc]

/-- Helper for Lemma 8.4.6: the left projected counit component is natural with respect to the
`mapComp'.hom` comparison from pulling back along `f` then `g` to pulling back along `gf`. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit_fst_mapComp_hom_naturality
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    {I : T.Arrow}
    (f : V ⟶ I.Y) (g : V' ⟶ V) (gf : V' ⟶ I.Y)
    (hgf : g ≫ f = gf := by cat_disch) :
    (((canonicalFiberPseudofunctor X.p).map gf.op.toLoc).toFunctor.map
        ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
            (J := J) F G T Q I)).hom) ≫
      (((canonicalFiberPseudofunctor X.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
          (Q.fst.obj I)) =
        (((canonicalFiberPseudofunctor X.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor
                (FibredCategoryOver.twoFibreProductLeftProjection
                  (toFibredCategoryMor F) (toFibredCategoryMor G))
                I.Y).obj
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
                (J := J) F G T Q I))) ≫
          (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.map
            (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
              ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I)).hom)) := by
  -- This is exactly the naturality square of `mapComp'.hom` on the left counit component.
  simpa using
    (Pseudofunctor.mapComp'_hom_naturality
      (F := canonicalFiberPseudofunctor X.p)
      f.op.toLoc g.op.toLoc gf.op.toLoc
      (comp_toLoc_eq f g gf hgf)
      ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
          (J := J) F G T Q I)).hom)

/-- Helper for Lemma 8.4.6: the left projected counit inverse is natural with respect to the
`mapComp'.inv` comparison from pulling back along `f` then `g` to pulling back along `gf`. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit_fst_mapComp_inv_naturality
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    {I : T.Arrow}
    (f : V ⟶ I.Y) (g : V' ⟶ V) (gf : V' ⟶ I.Y)
    (hgf : g ≫ f = gf := by cat_disch) :
    (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.map
        (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I)).inv)) ≫
      (((canonicalFiberPseudofunctor X.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
          (Q.fst.obj I)) =
        (((canonicalFiberPseudofunctor X.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor
                (FibredCategoryOver.twoFibreProductLeftProjection
                  (toFibredCategoryMor F) (toFibredCategoryMor G))
                I.Y).obj
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
                (J := J) F G T Q I))) ≫
          (((canonicalFiberPseudofunctor X.p).map gf.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I)).inv) := by
  -- This is the inverse `mapComp'` naturality square on the left counit component.
  simpa using
    (Pseudofunctor.mapComp'_inv_naturality
      (F := canonicalFiberPseudofunctor X.p)
      f.op.toLoc g.op.toLoc gf.op.toLoc
      (comp_toLoc_eq f g gf hgf)
      ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
          (J := J) F G T Q I)).inv)

/-- Helper for Lemma 8.4.6: the right projected counit component is natural with respect to the
`mapComp'.hom` comparison from pulling back along `f` then `g` to pulling back along `gf`. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit_snd_mapComp_hom_naturality
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    {I : T.Arrow}
    (f : V ⟶ I.Y) (g : V' ⟶ V) (gf : V' ⟶ I.Y)
    (hgf : g ≫ f = gf := by cat_disch) :
    (((canonicalFiberPseudofunctor Y.p).map gf.op.toLoc).toFunctor.map
        ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
            (J := J) F G T Q I)).hom) ≫
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
          (Q.snd.obj I)) =
        (((canonicalFiberPseudofunctor Y.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor
                (FibredCategoryOver.twoFibreProductRightProjection
                  (toFibredCategoryMor F) (toFibredCategoryMor G))
                I.Y).obj
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
                (J := J) F G T Q I))) ≫
          (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
            (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
              ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I)).hom)) := by
  -- This is exactly the naturality square of `mapComp'.hom` on the right counit component.
  simpa using
    (Pseudofunctor.mapComp'_hom_naturality
      (F := canonicalFiberPseudofunctor Y.p)
      f.op.toLoc g.op.toLoc gf.op.toLoc
      (comp_toLoc_eq f g gf hgf)
      ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
          (J := J) F G T Q I)).hom)

/-- Helper for Lemma 8.4.6: the right projected counit inverse is natural with respect to the
`mapComp'.inv` comparison from pulling back along `f` then `g` to pulling back along `gf`. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit_snd_mapComp_inv_naturality
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    {I : T.Arrow}
    (f : V ⟶ I.Y) (g : V' ⟶ V) (gf : V' ⟶ I.Y)
    (hgf : g ≫ f = gf := by cat_disch) :
    (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
        (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I)).inv)) ≫
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
          (Q.snd.obj I)) =
        (((canonicalFiberPseudofunctor Y.p).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
            ((FibredCategoryMor.fiberFunctor
                (FibredCategoryOver.twoFibreProductRightProjection
                  (toFibredCategoryMor F) (toFibredCategoryMor G))
                I.Y).obj
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
                (J := J) F G T Q I))) ≫
          (((canonicalFiberPseudofunctor Y.p).map gf.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I)).inv) := by
  -- This is the inverse `mapComp'` naturality square on the right counit component.
  simpa using
    (Pseudofunctor.mapComp'_inv_naturality
      (F := canonicalFiberPseudofunctor Y.p)
      f.op.toLoc g.op.toLoc gf.op.toLoc
      (comp_toLoc_eq f g gf hgf)
      ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
          (J := J) F G T Q I)).inv)

/-- Helper for Lemma 8.4.6: the owner-side overlap shell between the two named componentwise
pullback objects is induced directly from the overlap morphisms of `Q.fst` and `Q.snd`, with
compatibility recorded by the descent-data isomorphism `Q.iso`. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
        (J := J) F G T Q I₁ f₁ ⟶
      explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
        (J := J) F G T Q I₂ f₂ :=
  ⟨Q.fst.hom q f₁ f₂ hf₁ hf₂, Q.snd.hom q f₁ f₂ hf₁ hf₂, by
    -- Read the midpoint compatibility directly from the descent-data morphism `Q.iso.hom`.
    simpa [explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback,
      cover_descent_data_functor_of_stack_morphism, Category.assoc] using
      (Q.iso.hom.comm q f₁ f₂ hf₁ hf₂)⟩

/-- Helper for Lemma 8.4.6: the left projection of the owner-side common-refinement shell is
exactly the left projected overlap morphism of `Q`. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell_fst
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
      (J := J) F G T Q q f₁ f₂ hf₁ hf₂).fst =
      Q.fst.hom q f₁ f₂ hf₁ hf₂ := by
  -- Unfold the owner shell once and read off the left projected component.
  rfl

/-- Helper for Lemma 8.4.6: the right projection of the owner-side common-refinement shell is
exactly the right projected overlap morphism of `Q`. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell_snd
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
      (J := J) F G T Q q f₁ f₂ hf₁ hf₂).snd =
      Q.snd.hom q f₁ f₂ hf₁ hf₂ := by
  -- The right projection is equally definitional after unfolding the owner shell.
  rfl

/-- Helper for Lemma 8.4.6: once the owner-side objectwise pullback comparisons are fixed, reflect
the conjugated owner overlap shell back through the fully faithful fibre equivalence over `V`. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f₁.op.toLoc).toFunctor.obj
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
          (J := J) F G T Q I₁)) ⟶
      (((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f₂.op.toLoc).toFunctor.obj
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
          (J := J) F G T Q I₂)) :=
  let eV :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) V
  let hffV : eV.functor.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful eV.functor
  let η₁ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
      (J := J) F G T Q I₁ f₁
  let η₂ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
      (J := J) F G T Q I₂ f₂
  hffV.preimage
    (η₁.hom ≫
      explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
        (J := J) F G T Q q f₁ f₂ hf₁ hf₂ ≫
      η₂.inv)

/-- Helper for Lemma 8.4.6: applying the owner fibre equivalence to the reflected overlap morphism
recovers exactly the conjugated owner-side shell. This is the single rewrite interface needed for
the descent identities and quasi-inverse checks. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) V).functor.map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
          (J := J) F G T Q q f₁ f₂ hf₁ hf₂) =
      (explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
          (J := J) F G T Q I₁ f₁).hom ≫
        explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
          (J := J) F G T Q q f₁ f₂ hf₁ hf₂ ≫
        (explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
          (J := J) F G T Q I₂ f₂).inv := by
  let eV :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) V
  let hffV : eV.functor.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful eV.functor
  let η₁ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
      (J := J) F G T Q I₁ f₁
  let η₂ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
      (J := J) F G T Q I₂ f₂
  -- The reflected overlap morphism was chosen as the unique preimage of this owner-side shell.
  simpa only [explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom,
    eV, hffV, η₁, η₂] using
    hffV.map_preimage
      (η₁.hom ≫
        explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
          (J := J) F G T Q q f₁ f₂ hf₁ hf₂ ≫
        η₂.inv)

/-- Helper for Lemma 8.4.6: after projecting the reflected overlap shell to the left owner leg,
the owner fibre equivalence over `V` recovers exactly the left comparison-conjugated shell. This
freezes the `π₁`-projection of the overlap before the remaining common-refinement calculation. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map_fst
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (FibredCategoryMor.fiberFunctor
        (FibredCategoryOver.twoFibreProductLeftProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G)) V).map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
          (J := J) F G T Q q f₁ f₂ hf₁ hf₂) =
      ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
          (J := J) F G T Q I₁ f₁).hom ≫
        explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
          (J := J) F G T Q q f₁ f₂ hf₁ hf₂ ≫
        (explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
          (J := J) F G T Q I₂ f₂).inv).fst := by
  let eV :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) V
  let leftProjection :=
    FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  -- Project the owner-shell comparison through `π₁`; the forward owner equivalence already
  -- computes the left projection functor on the nose.
  simpa [eV, leftProjection, fiberFunctor, toBasedFunctor] using
    congrArg
      (fun k ↦ k.fst)
      (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map
        (J := J) F G T Q q f₁ f₂ hf₁ hf₂)

/-- Helper for Lemma 8.4.6: after projecting the reflected overlap shell to the right owner leg,
the owner fibre equivalence over `V` recovers exactly the right comparison-conjugated shell. This
is the symmetric frozen `π₂`-projection used in the final common-refinement calculation. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map_snd
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (FibredCategoryMor.fiberFunctor
        (FibredCategoryOver.twoFibreProductRightProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G)) V).map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
          (J := J) F G T Q q f₁ f₂ hf₁ hf₂) =
      ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
          (J := J) F G T Q I₁ f₁).hom ≫
        explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
          (J := J) F G T Q q f₁ f₂ hf₁ hf₂ ≫
        (explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
          (J := J) F G T Q I₂ f₂).inv).snd := by
  let eV :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) V
  let rightProjection :=
    FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  -- The right projection is the same owner-shell comparison read through `π₂`.
  simpa [eV, rightProjection, fiberFunctor, toBasedFunctor] using
    congrArg
      (fun k ↦ k.snd)
      (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map
        (J := J) F G T Q q f₁ f₂ hf₁ hf₂)

/-- Helper for Lemma 8.4.6: the left projected reflected overlap shell expands to the explicit
left pullback-comparison conjugation around the overlap morphism of `Q.fst`. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map_fst_expanded
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (FibredCategoryMor.fiberFunctor
        (FibredCategoryOver.twoFibreProductLeftProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G)) V).map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
          (J := J) F G T Q q f₁ f₂ hf₁ hf₂) =
      (FibredCategoryMor.pullbackComparison
          (FibredCategoryOver.twoFibreProductLeftProjection
            (toFibredCategoryMor F) (toFibredCategoryMor G))
          f₁
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
            (J := J) F G T Q I₁)).inv ≫
        (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₁)).hom) ≫
        Q.fst.hom q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₂)).inv) ≫
        (FibredCategoryMor.pullbackComparison
          (FibredCategoryOver.twoFibreProductLeftProjection
            (toFibredCategoryMor F) (toFibredCategoryMor G))
          f₂
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
            (J := J) F G T Q I₂)).hom := by
  -- Expand the frozen left projection by the stored `η` formulas and the definitional owner shell.
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map_fst
    (J := J) F G T Q q f₁ f₂ hf₁ hf₂]
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_hom_fst
    (J := J) F G T Q I₁ f₁]
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_inv_fst
    (J := J) F G T Q I₂ f₂]
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell_fst
    (J := J) F G T Q q f₁ f₂ hf₁ hf₂]
  simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: the right projected reflected overlap shell expands to the explicit
right pullback-comparison conjugation around the overlap morphism of `Q.snd`. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map_snd_expanded
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (FibredCategoryMor.fiberFunctor
        (FibredCategoryOver.twoFibreProductRightProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G)) V).map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
          (J := J) F G T Q q f₁ f₂ hf₁ hf₂) =
      (FibredCategoryMor.pullbackComparison
          (FibredCategoryOver.twoFibreProductRightProjection
            (toFibredCategoryMor F) (toFibredCategoryMor G))
          f₁
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
            (J := J) F G T Q I₁)).inv ≫
        (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₁)).hom) ≫
        Q.snd.hom q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₂)).inv) ≫
        (FibredCategoryMor.pullbackComparison
          (FibredCategoryOver.twoFibreProductRightProjection
            (toFibredCategoryMor F) (toFibredCategoryMor G))
          f₂
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
            (J := J) F G T Q I₂)).hom := by
  -- The right projection expands symmetrically from the stored `η` formulas.
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map_snd
    (J := J) F G T Q q f₁ f₂ hf₁ hf₂]
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_hom_snd
    (J := J) F G T Q I₁ f₁]
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_inv_snd
    (J := J) F G T Q I₂ f₂]
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell_snd
    (J := J) F G T Q q f₁ f₂ hf₁ hf₂]
  simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: the left projection of the q'-target shell in
`explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map` is exactly
the explicit left comparison-conjugated owner shell over `gf₁` and `gf₂`. This isolates the
remaining blocker to the source-side mapped-shell normalization. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_target_fst_expanded
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V) (q : V ⟶ U) (q' : V' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
          (J := J) F G T Q I₁ gf₁).hom ≫
        explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
          (J := J) F G T Q q' gf₁ gf₂
          (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
          (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) ≫
        (explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
          (J := J) F G T Q I₂ gf₂).inv).fst =
      (FibredCategoryMor.pullbackComparison
          (FibredCategoryOver.twoFibreProductLeftProjection
            (toFibredCategoryMor F) (toFibredCategoryMor G))
          gf₁
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
            (J := J) F G T Q I₁)).inv ≫
        (((canonicalFiberPseudofunctor X.p).map gf₁.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₁)).hom) ≫
        Q.fst.hom q' gf₁ gf₂
          (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
          (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) ≫
        (((canonicalFiberPseudofunctor X.p).map gf₂.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₂)).inv) ≫
        (FibredCategoryMor.pullbackComparison
          (FibredCategoryOver.twoFibreProductLeftProjection
            (toFibredCategoryMor F) (toFibredCategoryMor G))
          gf₂
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
            (J := J) F G T Q I₂)).hom := by
  -- Expand the q'-target shell entirely on the left projection so later work only has to
  -- normalize the source-side mapped shell to this frozen owner expression.
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_hom_fst
    (J := J) F G T Q I₁ gf₁]
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell_fst
    (J := J) F G T Q q' gf₁ gf₂
      (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
      (by rw [← hq, ← hgf₂, Category.assoc, hf₂])]
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_inv_fst
    (J := J) F G T Q I₂ gf₂]
  simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: the right projection of the q'-target shell in
`explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map` is exactly
the explicit right comparison-conjugated owner shell over `gf₁` and `gf₂`. This is the
projectionwise target normal form paired with the previous left-leg lemma. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_target_snd_expanded
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V) (q : V ⟶ U) (q' : V' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
          (J := J) F G T Q I₁ gf₁).hom ≫
        explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
          (J := J) F G T Q q' gf₁ gf₂
          (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
          (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) ≫
        (explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
          (J := J) F G T Q I₂ gf₂).inv).snd =
      (FibredCategoryMor.pullbackComparison
          (FibredCategoryOver.twoFibreProductRightProjection
            (toFibredCategoryMor F) (toFibredCategoryMor G))
          gf₁
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
            (J := J) F G T Q I₁)).inv ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₁)).hom) ≫
        Q.snd.hom q' gf₁ gf₂
          (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
          (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₂)).inv) ≫
        (FibredCategoryMor.pullbackComparison
          (FibredCategoryOver.twoFibreProductRightProjection
            (toFibredCategoryMor F) (toFibredCategoryMor G))
          gf₂
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
            (J := J) F G T Q I₂)).hom := by
  -- Expand the symmetric q'-target shell on the right projection, leaving only the mirrored
  -- source-side normalization as the remaining common-refinement task.
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_hom_snd
    (J := J) F G T Q I₁ gf₁]
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell_snd
    (J := J) F G T Q q' gf₁ gf₂
      (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
      (by rw [← hq, ← hgf₂, Category.assoc, hf₂])]
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_inv_snd
    (J := J) F G T Q I₂ gf₂]
  simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: the owner-side reflected overlap shell is the identity on a
self-overlap because both projected descent data already satisfy their identity axioms. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell_self
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (q : V ⟶ U) {I : T.Arrow}
    (g : V ⟶ I.Y) (hg : g ≫ I.f = q := by cat_disch) :
    explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
        (J := J) F G T Q q g g hg hg =
      𝟙 _ := by
  -- The owner shell is componentwise the self-overlap of `Q.fst` and `Q.snd`.
  apply CategoricalPullback.hom_ext
  · simp [explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell]
  · simp [explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell]

/-- Helper for Lemma 8.4.6: the owner-side reflected overlap shell satisfies the cocycle relation
because its two projected components are exactly the cocycle morphisms of `Q.fst` and `Q.snd`. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell_comp
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (q : V ⟶ U) {I₁ I₂ I₃ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y) (f₃ : V ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (hf₃ : f₃ ≫ I₃.f = q := by cat_disch) :
    explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
        (J := J) F G T Q q f₁ f₂ hf₁ hf₂ ≫
      explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
        (J := J) F G T Q q f₂ f₃ hf₂ hf₃ =
        explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
          (J := J) F G T Q q f₁ f₃ hf₁ hf₃ := by
  -- The owner shell composes componentwise, so the source cocycle is exactly `Q.fst.hom_comp`
  -- and `Q.snd.hom_comp`.
  apply CategoricalPullback.hom_ext
  · simp [explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell]
  · simp [explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell]

/-- Helper for Lemma 8.4.6: after reflecting the owner shell back through the fully faithful
fibre equivalence over `V`, the self-overlap of the reconstructed source datum is the identity. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_hom_self
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (q : V ⟶ U) {I : T.Arrow}
    (g : V ⟶ I.Y) (hg : g ≫ I.f = q := by cat_disch) :
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
        (J := J) F G T Q q g g hg hg =
      𝟙 _ := by
  let eV :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) V
  let hffV : eV.functor.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful eV.functor
  let η :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
      (J := J) F G T Q I g
  apply hffV.map_injective
  -- Compare both sides after applying the fully faithful owner equivalence over `V`.
  calc
    eV.functor.map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
          (J := J) F G T Q q g g hg hg) =
      η.hom ≫
        explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
          (J := J) F G T Q q g g hg hg ≫
        η.inv := by
          simpa [eV, η] using
            explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map
              (J := J) F G T Q q g g hg hg
    _ = η.hom ≫ 𝟙 _ ≫ η.inv := by
          exact
            congrArg
              (fun k ↦ η.hom ≫ k ≫ η.inv)
              (explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell_self
                (J := J) F G T Q q g hg)
    _ = 𝟙 _ := by
          simpa [Category.assoc] using η.hom_inv_id
    _ = eV.functor.map (𝟙 _) := by
          symm
          exact eV.functor.map_id _

/-- Helper for Lemma 8.4.6: after reflecting the owner shell back through the fully faithful
fibre equivalence over `V`, the reconstructed source overlaps satisfy the cocycle relation. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_hom_comp
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (q : V ⟶ U) {I₁ I₂ I₃ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y) (f₃ : V ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (hf₃ : f₃ ≫ I₃.f = q := by cat_disch) :
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
        (J := J) F G T Q q f₁ f₂ hf₁ hf₂ ≫
      explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
        (J := J) F G T Q q f₂ f₃ hf₂ hf₃ =
        explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
          (J := J) F G T Q q f₁ f₃ hf₁ hf₃ := by
  let eV :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) V
  let hffV : eV.functor.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful eV.functor
  let η₁ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
      (J := J) F G T Q I₁ f₁
  let η₂ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
      (J := J) F G T Q I₂ f₂
  let η₃ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
      (J := J) F G T Q I₃ f₃
  apply hffV.map_injective
  -- Compare both composites in the owner pullback-of-fibres category over `V`.
  calc
    eV.functor.map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
            (J := J) F G T Q q f₁ f₂ hf₁ hf₂ ≫
          explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
            (J := J) F G T Q q f₂ f₃ hf₂ hf₃) =
      (η₁.hom ≫
          explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
            (J := J) F G T Q q f₁ f₂ hf₁ hf₂ ≫
          η₂.inv) ≫
        (η₂.hom ≫
          explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
            (J := J) F G T Q q f₂ f₃ hf₂ hf₃ ≫
          η₃.inv) := by
          rw [Functor.map_comp]
          simp only [Category.assoc]
          rw [explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map
            (J := J) F G T Q q f₁ f₂ hf₁ hf₂]
          rw [explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map
            (J := J) F G T Q q f₂ f₃ hf₂ hf₃]
    _ =
      η₁.hom ≫
        (explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
            (J := J) F G T Q q f₁ f₂ hf₁ hf₂ ≫
          explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
            (J := J) F G T Q q f₂ f₃ hf₂ hf₃) ≫
        η₃.inv := by
          simp only [Category.assoc]
          rw [Iso.inv_hom_id_assoc]
    _ =
      η₁.hom ≫
        explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
          (J := J) F G T Q q f₁ f₃ hf₁ hf₃ ≫
        η₃.inv := by
          exact
            congrArg
              (fun k ↦ η₁.hom ≫ k ≫ η₃.inv)
              (explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell_comp
                (J := J) F G T Q q f₁ f₂ f₃ hf₁ hf₂ hf₃)
    _ =
      eV.functor.map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
          (J := J) F G T Q q f₁ f₃ hf₁ hf₃) := by
          symm
          simpa [eV, η₁, η₃] using
            explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map
              (J := J) F G T Q q f₁ f₃ hf₁ hf₃

/-- Helper for Lemma 8.4.6: after applying the owner fibre equivalence over the common
refinement `V'`, the pullback of the reflected source overlap becomes the owner-side common
refinement shell determined by `Q.fst`, `Q.snd`, and `Q.iso`. This isolates the remaining
transport-stable `pullHom` interface needed to package the inverse descent datum. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) V').functor.map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
            (J := J) F G T Q q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂)).fst =
      (FibredCategoryMor.fiberFunctor
          (FibredCategoryOver.twoFibreProductLeftProjection
            (toFibredCategoryMor F) (toFibredCategoryMor G))
          V').map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
            (J := J) F G T Q q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂) := by
  let eV' :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) V'
  let leftProjection :=
    FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  have hπ₁ :
      eV'.functor ⋙ π₁ (fiberFunctor F V') (fiberFunctor G V') =
        FibredCategoryMor.fiberFunctor leftProjection V' := by
    -- The owner equivalence computes the left projection functor on the common refinement.
    symm
    simpa [leftProjection, fiberFunctor, toBasedFunctor] using
      (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₁
        (F := toBasedFunctor F) (G := toBasedFunctor G) V')
  -- Read the first projection through the functor equality on the refinement fibre.
  simpa [Functor.comp_map] using
    congrArg
      (fun H ↦
        H.map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
              (J := J) F G T Q q f₁ f₂ hf₁ hf₂)
            g gf₁ gf₂ hgf₁ hgf₂))
      hπ₁

/-- Helper for Lemma 8.4.6: the same common-refinement source term projects on `π₂` to the right
owner fiber functor. This leaves only the right-shell normalization against `Q.snd.pullHom_hom`.
-/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) V').functor.map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
            (J := J) F G T Q q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂)).snd =
      (FibredCategoryMor.fiberFunctor
          (FibredCategoryOver.twoFibreProductRightProjection
            (toFibredCategoryMor F) (toFibredCategoryMor G))
          V').map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
            (J := J) F G T Q q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂) := by
  let eV' :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) V'
  let rightProjection :=
    FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  have hπ₂ :
      eV'.functor ⋙ π₂ (fiberFunctor F V') (fiberFunctor G V') =
        FibredCategoryMor.fiberFunctor rightProjection V' := by
    -- The right projection is computed by the symmetric owner comparison theorem.
    symm
    simpa [rightProjection, fiberFunctor, toBasedFunctor] using
      (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₂
        (F := toBasedFunctor F) (G := toBasedFunctor G) V')
  -- Read the second projection through the same functor equality.
  simpa [Functor.comp_map] using
    congrArg
      (fun H ↦
        H.map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
              (J := J) F G T Q q f₁ f₂ hf₁ hf₂)
            g gf₁ gf₂ hgf₁ hgf₂))
      hπ₂

/-- Helper for Lemma 8.4.6: after applying the owner fibre equivalence over the common
refinement `V'`, the pullback of the reflected source overlap becomes the owner-side common
refinement shell determined by `Q.fst`, `Q.snd`, and `Q.iso`. This isolates the remaining
transport-stable `pullHom` interface needed to package the inverse descent datum. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_middle_split
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor
            (FibredCategoryOver.twoFibreProductLeftProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G))
            V).map
          (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
            (J := J) F G T Q q f₁ f₂ hf₁ hf₂))) =
      (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison
            (FibredCategoryOver.twoFibreProductLeftProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G))
            f₁
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
              (J := J) F G T Q I₁)).inv) ≫
        (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.map
          (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₁)).hom)) ≫
        (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.map
          (Q.fst.hom q f₁ f₂ hf₁ hf₂)) ≫
        (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.map
          (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv)) ≫
        (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison
            (FibredCategoryOver.twoFibreProductLeftProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G))
            f₂
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
              (J := J) F G T Q I₂)).hom) := by
  -- Expand the projected source overlap once, then split the mapped fivefold composite into the
  -- individual factors that the remaining boundary/naturality proof will normalize.
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map_fst_expanded
    (J := J) F G T Q q f₁ f₂ hf₁ hf₂]
  repeat rw [Functor.map_comp]
  simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: the symmetric right projected source overlap also splits its mapped
middle factor into the five explicit comparison/counit/overlap pieces needed for the final
common-refinement normalization. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_middle_split
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor
            (FibredCategoryOver.twoFibreProductRightProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G))
            V).map
          (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
            (J := J) F G T Q q f₁ f₂ hf₁ hf₂))) =
      (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison
            (FibredCategoryOver.twoFibreProductRightProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G))
            f₁
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
              (J := J) F G T Q I₁)).inv) ≫
        (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
          (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₁)).hom)) ≫
        (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
          (Q.snd.hom q f₁ f₂ hf₁ hf₂)) ≫
        (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
          (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv)) ≫
        (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
          (FibredCategoryMor.pullbackComparison
            (FibredCategoryOver.twoFibreProductRightProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G))
            f₂
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
              (J := J) F G T Q I₂)).hom) := by
  -- The right projected source overlap expands by the same one-step split of the mapped
  -- fivefold composite.
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map_snd_expanded
    (J := J) F G T Q q f₁ f₂ hf₁ hf₂]
  repeat rw [Functor.map_comp]
  simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: after applying the owner fibre equivalence over the common
refinement `V'`, the pullback of the reflected source overlap becomes the owner-side common
refinement shell determined by `Q.fst`, `Q.snd`, and `Q.iso`. This isolates the remaining
transport-stable `pullHom` interface needed to package the inverse descent datum. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_outer_expanded
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) V').functor.map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
            (J := J) F G T Q q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂)).fst =
      (((canonicalFiberPseudofunctor X.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor
              (FibredCategoryOver.twoFibreProductLeftProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G))
              I₁.Y).obj
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
              (J := J) F G T Q I₁))) ≫
        (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.map
          ((FibredCategoryMor.fiberFunctor
              (FibredCategoryOver.twoFibreProductLeftProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G))
              V).map
            (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
              (J := J) F G T Q q f₁ f₂ hf₁ hf₂))) ≫
        (((canonicalFiberPseudofunctor X.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor
              (FibredCategoryOver.twoFibreProductLeftProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G))
              I₂.Y).obj
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
              (J := J) F G T Q I₂))) := by
  -- Expand the outer `pullHom` shell after projecting to `π₁`, leaving only the already-frozen
  -- middle term to be normalized separately.
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst
    (J := J) F G T Q g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
  simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Functor.map_comp, Category.assoc]

/-- Helper for Lemma 8.4.6: the same outer-shell expansion on the right projection leaves only
the mirrored projected middle term to normalize. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_outer_expanded
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) V').functor.map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
            (J := J) F G T Q q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂)).snd =
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor
              (FibredCategoryOver.twoFibreProductRightProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G))
              I₁.Y).obj
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
              (J := J) F G T Q I₁))) ≫
        (((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.map
          ((FibredCategoryMor.fiberFunctor
              (FibredCategoryOver.twoFibreProductRightProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G))
              V).map
            (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
              (J := J) F G T Q q f₁ f₂ hf₁ hf₂))) ≫
        (((canonicalFiberPseudofunctor Y.p).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor
              (FibredCategoryOver.twoFibreProductRightProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G))
              I₂.Y).obj
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
              (J := J) F G T Q I₂))) := by
  -- Expand the outer `pullHom` shell after projecting to `π₂`; only the mirrored middle term
  -- still needs the final boundary and naturality normalization.
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd
    (J := J) F G T Q g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
  simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Functor.map_comp, Category.assoc]

/-- Helper for Lemma 8.4.6: on the left projection, the exposed five-factor mapped middle shell
is exactly the pullback of the already-packaged image-isomorphism projections around
`Q.fst.hom`. This isolates the remaining blocker to the pullback-normality of those image
isomorphisms themselves. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_middle_packaged
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
    let leftProjection :=
      FibredCategoryOver.twoFibreProductLeftProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let leg₁ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₁
    let leg₂ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₂
    let e₁ := FibredCategoryMor.pullbackComparison leftProjection f₁ leg₁
    let e₂ := FibredCategoryMor.pullbackComparison leftProjection f₂ leg₂
    FYg.map e₁.inv ≫
        FYg.map
          (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₁)).hom) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
        FYg.map e₂.hom =
      FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.fst) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.fst) := by
  let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
  let leftProjection :=
    FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let leg₁ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I₁
  let leg₂ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I₂
  let e₁ := FibredCategoryMor.pullbackComparison leftProjection f₁ leg₁
  let e₂ := FibredCategoryMor.pullbackComparison leftProjection f₂ leg₂
  have hη₁ :
      FYg.map e₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
              ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₁)).hom) =
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.fst) := by
    -- Package the left projected image isomorphism before moving the common refinement shell.
    calc
      FYg.map e₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
              ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₁)).hom) =
        FYg.map
          (e₁.inv ≫
            (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
              ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₁)).hom)) := by
            rw [← Functor.map_comp]
      _ =
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.fst) := by
            rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_hom_fst
              (J := J) F G T Q I₁ f₁]
  have hη₂ :
      FYg.map
          (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
        FYg.map e₂.hom =
      FYg.map
        ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
          (J := J) F G T Q I₂ f₂).inv.fst) := by
    -- The right projected image isomorphism packages the symmetric tail of the shell.
    calc
      FYg.map
          (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
        FYg.map e₂.hom =
      FYg.map
        ((((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
          e₂.hom) := by
          rw [← Functor.map_comp]
      _ =
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.fst) := by
          rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_inv_fst
            (J := J) F G T Q I₂ f₂]
  -- Replace the visible head and tail by the packaged image-isomorphism projections.
  have hmid₁ :
      (FYg.map e₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
              ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₁)).hom)) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.fst) =
      FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.fst) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.fst) := by
    -- First replace the left packaged head while leaving the middle and right tail fixed.
    simpa only [Category.assoc] using
      congrArg
        (fun k ↦ k ≫ FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
          FYg.map
            ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
              (J := J) F G T Q I₂ f₂).inv.fst))
        hη₁
  have hmid₂ :
      FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.fst) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        (FYg.map
            (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
              ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₂)).inv) ≫
          FYg.map e₂.hom) =
      FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.fst) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.fst) := by
    -- Then package the right tail symmetrically.
    simpa only [Category.assoc] using
      congrArg
        (fun k ↦ FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.fst) ≫
            FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫ k)
        hη₂
  calc
    FYg.map e₁.inv ≫
        FYg.map
          (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₁)).hom) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
        FYg.map e₂.hom =
      (FYg.map e₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
              ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₁)).hom)) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        (FYg.map
            (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
              ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₂)).inv) ≫
          FYg.map e₂.hom) := by
          simp only [Category.assoc]
    _ =
      FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.fst) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.fst) := by
          exact hmid₁.trans hmid₂

/-- Helper for Lemma 8.4.6: the right projected exposed five-factor shell similarly packages to
the pullback of the two right image-isomorphism projections around `Q.snd.hom`. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_middle_packaged
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let rightProjection :=
      FibredCategoryOver.twoFibreProductRightProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let leg₁ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₁
    let leg₂ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₂
    let e₁ := FibredCategoryMor.pullbackComparison rightProjection f₁ leg₁
    let e₂ := FibredCategoryMor.pullbackComparison rightProjection f₂ leg₂
    FYg.map e₁.inv ≫
        FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₁)).hom) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
        FYg.map e₂.hom =
      FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.snd) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.snd) := by
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let rightProjection :=
    FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let leg₁ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I₁
  let leg₂ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I₂
  let e₁ := FibredCategoryMor.pullbackComparison rightProjection f₁ leg₁
  let e₂ := FibredCategoryMor.pullbackComparison rightProjection f₂ leg₂
  have hη₁ :
      FYg.map e₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₁)).hom) =
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.snd) := by
    -- Package the right projected image isomorphism before moving the common refinement shell.
    calc
      FYg.map e₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₁)).hom) =
        FYg.map
          (e₁.inv ≫
            (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₁)).hom)) := by
            rw [← Functor.map_comp]
      _ =
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.snd) := by
            rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_hom_snd
              (J := J) F G T Q I₁ f₁]
  have hη₂ :
      FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
        FYg.map e₂.hom =
      FYg.map
        ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
          (J := J) F G T Q I₂ f₂).inv.snd) := by
    -- The symmetric right tail packages in the same way.
    calc
      FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
        FYg.map e₂.hom =
      FYg.map
        ((((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
          e₂.hom) := by
          rw [← Functor.map_comp]
      _ =
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.snd) := by
          rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_inv_snd
            (J := J) F G T Q I₂ f₂]
  -- Replace the visible head and tail by the packaged right image-isomorphism projections.
  have hmid₁ :
      (FYg.map e₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₁)).hom)) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.snd) =
      FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.snd) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.snd) := by
    -- First replace the left packaged head while freezing the mirrored middle and tail.
    simpa only [Category.assoc] using
      congrArg
        (fun k ↦ k ≫ FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
          FYg.map
            ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
              (J := J) F G T Q I₂ f₂).inv.snd))
        hη₁
  have hmid₂ :
      FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.snd) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        (FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₂)).inv) ≫
          FYg.map e₂.hom) =
      FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.snd) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.snd) := by
    -- Then package the mirrored right tail.
    simpa only [Category.assoc] using
      congrArg
        (fun k ↦ FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.snd) ≫
            FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫ k)
        hη₂
  calc
    FYg.map e₁.inv ≫
        FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₁)).hom) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
        FYg.map e₂.hom =
      (FYg.map e₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₁)).hom)) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        (FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₂)).inv) ≫
          FYg.map e₂.hom) := by
          simp only [Category.assoc]
    _ =
      FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.snd) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.snd) := by
          exact hmid₁.trans hmid₂

/-- Helper for Lemma 8.4.6: the left projected counit component commutes with the `mapComp'.hom`
comparison in the exact reassociated orientation used by the packaged-tail normalization. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit_fst_mapComp_hom_reassociated
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    {I : T.Arrow}
    (f : V ⟶ I.Y) (g : V' ⟶ V) (gf : V' ⟶ I.Y)
    (hgf : g ≫ f = gf := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
    let leftTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor
              (FibredCategoryOver.twoFibreProductLeftProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G))
              I.Y).obj
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
              (J := J) F G T Q I)))
    let leftQTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
          (Q.fst.obj I))
    leftTarget ≫
        FYg.map
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I)).hom) =
      (((canonicalFiberPseudofunctor X.p).map gf.op.toLoc).toFunctor.map
        ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
            (J := J) F G T Q I)).hom) ≫
        leftQTarget := by
  let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
  let leftTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor
            (FibredCategoryOver.twoFibreProductLeftProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G))
            I.Y).obj
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
            (J := J) F G T Q I)))
  let leftQTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        (Q.fst.obj I))
  -- This is the existing `mapComp'.hom` naturality square, simply reassociated so later shells
  -- can consume it without extra `convert` steps.
  simpa only [FYg, leftTarget, leftQTarget, Category.assoc] using
    (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit_fst_mapComp_hom_naturality
      (J := J) F G T Q f g gf hgf).symm

/-- Helper for Lemma 8.4.6: the left projected counit inverse commutes with the `mapComp'.inv`
comparison in the exact reassociated orientation used by the packaged-tail normalization. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit_fst_mapComp_inv_reassociated
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    {I : T.Arrow}
    (f : V ⟶ I.Y) (g : V' ⟶ V) (gf : V' ⟶ I.Y)
    (hgf : g ≫ f = gf := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
    let rightTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor
              (FibredCategoryOver.twoFibreProductLeftProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G))
              I.Y).obj
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
              (J := J) F G T Q I)))
    let rightQTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
          (Q.fst.obj I))
    FYg.map
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I)).inv) ≫
        rightQTarget =
      rightTarget ≫
        (((canonicalFiberPseudofunctor X.p).map gf.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I)).inv) := by
  let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
  let rightTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor
            (FibredCategoryOver.twoFibreProductLeftProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G))
            I.Y).obj
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
            (J := J) F G T Q I)))
  let rightQTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        (Q.fst.obj I))
  -- This is the inverse `mapComp'` naturality square, rewritten into the literal suffix shape
  -- needed for the packaged-tail proof.
  simpa only [FYg, rightTarget, rightQTarget, Category.assoc] using
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit_fst_mapComp_inv_naturality
      (J := J) F G T Q f g gf hgf

/-- Helper for Lemma 8.4.6: the right projected counit component commutes with the `mapComp'.hom`
comparison in the exact reassociated orientation used by the packaged-tail normalization. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit_snd_mapComp_hom_reassociated
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    {I : T.Arrow}
    (f : V ⟶ I.Y) (g : V' ⟶ V) (gf : V' ⟶ I.Y)
    (hgf : g ≫ f = gf := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let leftTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor
              (FibredCategoryOver.twoFibreProductRightProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G))
              I.Y).obj
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
              (J := J) F G T Q I)))
    let leftQTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
          (Q.snd.obj I))
    leftTarget ≫
        FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I)).hom) =
      (((canonicalFiberPseudofunctor Y.p).map gf.op.toLoc).toFunctor.map
        ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
            (J := J) F G T Q I)).hom) ≫
        leftQTarget := by
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let leftTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor
            (FibredCategoryOver.twoFibreProductRightProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G))
            I.Y).obj
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
            (J := J) F G T Q I)))
  let leftQTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        (Q.snd.obj I))
  -- This is the right-projection mirror of the reassociated `mapComp'.hom` naturality square.
  simpa only [FYg, leftTarget, leftQTarget, Category.assoc] using
    (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit_snd_mapComp_hom_naturality
      (J := J) F G T Q f g gf hgf).symm

/-- Helper for Lemma 8.4.6: the right projected counit inverse commutes with the `mapComp'.inv`
comparison in the exact reassociated orientation used by the packaged-tail normalization. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit_snd_mapComp_inv_reassociated
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    {I : T.Arrow}
    (f : V ⟶ I.Y) (g : V' ⟶ V) (gf : V' ⟶ I.Y)
    (hgf : g ≫ f = gf := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let rightTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
          ((FibredCategoryMor.fiberFunctor
              (FibredCategoryOver.twoFibreProductRightProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G))
              I.Y).obj
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
              (J := J) F G T Q I)))
    let rightQTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
          (Q.snd.obj I))
    FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I)).inv) ≫
        rightQTarget =
      rightTarget ≫
        (((canonicalFiberPseudofunctor Y.p).map gf.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I)).inv) := by
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let rightTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor
            (FibredCategoryOver.twoFibreProductRightProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G))
            I.Y).obj
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
            (J := J) F G T Q I)))
  let rightQTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        (Q.snd.obj I))
  -- This is the right-projection mirror of the reassociated `mapComp'.inv` naturality square.
  simpa only [FYg, rightTarget, rightQTarget, Category.assoc] using
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit_snd_mapComp_inv_naturality
      (J := J) F G T Q f g gf hgf

/-- Helper for Lemma 8.4.6: on the left projection, the head comparison shell cancels to the
strict common-refinement source boundary once the common `g`-leg pullback comparison is inserted
between the projected source shell and the transported `f`-leg inverse comparison. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_left_projection_comparison_cancel_head
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    {I : T.Arrow}
    (f : V ⟶ I.Y) (g : V' ⟶ V) (gf : V' ⟶ I.Y)
    (hgf : g ≫ f = gf := by cat_disch) :
    let P := FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)
    let leftProjection :=
      FibredCategoryOver.twoFibreProductLeftProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
    let leg :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I
    let e := FibredCategoryMor.pullbackComparison leftProjection f leg
    let eg := FibredCategoryMor.pullbackComparison leftProjection gf leg
    let cg := FibredCategoryMor.pullbackComparison leftProjection g
      (((canonicalFiberPseudofunctor P.p).map f.op.toLoc).toFunctor.obj leg)
    let leftSource :=
      (((canonicalFiberPseudofunctor P.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app leg)
    let leftTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor leftProjection I.Y).obj leg))
    (FibredCategoryMor.fiberFunctor leftProjection V').map leftSource ≫
        cg.inv ≫ FYg.map e.inv =
      eg.inv ≫ leftTarget := by
  let P := FibredCategoryOver.twoFibreProduct
    (toFibredCategoryMor F) (toFibredCategoryMor G)
  let leftProjection :=
    FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
  let leg :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I
  let e := FibredCategoryMor.pullbackComparison leftProjection f leg
  let eg := FibredCategoryMor.pullbackComparison leftProjection gf leg
  let cg := FibredCategoryMor.pullbackComparison leftProjection g
    (((canonicalFiberPseudofunctor P.p).map f.op.toLoc).toFunctor.obj leg)
  let leftSource :=
    (((canonicalFiberPseudofunctor P.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app leg)
  let leftTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor leftProjection I.Y).obj leg))
  have hboundary :
      leftTarget ≫ FYg.map e.hom =
        eg.hom ≫ (FibredCategoryMor.fiberFunctor leftProjection V').map leftSource ≫ cg.inv := by
    -- Specialize the general left-boundary comparison to the explicit left projection and leg.
    simpa only [P, leftProjection, FYg, leg, e, eg, cg, leftSource, leftTarget, Category.assoc] using
      stack_morphism_pullbackComparison_pullHom_left_boundary
        (H := leftProjection) f g gf hgf leg
  -- Cancel the two visible comparison isomorphisms so only the strict left source boundary
  -- remains before the transported `f`-leg inverse comparison.
  calc
    (FibredCategoryMor.fiberFunctor leftProjection V').map leftSource ≫
        cg.inv ≫ FYg.map e.inv =
      eg.inv ≫
        (eg.hom ≫ (FibredCategoryMor.fiberFunctor leftProjection V').map leftSource ≫ cg.inv) ≫
        FYg.map e.inv := by
          simp only [Category.assoc]
    _ =
      eg.inv ≫ (leftTarget ≫ FYg.map e.hom) ≫ FYg.map e.inv := by
          rw [← hboundary]
    _ = eg.inv ≫ leftTarget := by
          simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: on the left projection, the tail comparison shell cancels to the
strict common-refinement target boundary after inserting the common `g`-leg pullback comparison
between the transported `f`-leg comparison and the projected source shell. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_left_projection_comparison_cancel_tail
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    {I : T.Arrow}
    (f : V ⟶ I.Y) (g : V' ⟶ V) (gf : V' ⟶ I.Y)
    (hgf : g ≫ f = gf := by cat_disch) :
    let P := FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)
    let leftProjection :=
      FibredCategoryOver.twoFibreProductLeftProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
    let leg :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I
    let e := FibredCategoryMor.pullbackComparison leftProjection f leg
    let eg := FibredCategoryMor.pullbackComparison leftProjection gf leg
    let cg := FibredCategoryMor.pullbackComparison leftProjection g
      (((canonicalFiberPseudofunctor P.p).map f.op.toLoc).toFunctor.obj leg)
    let rightSource :=
      (((canonicalFiberPseudofunctor P.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app leg)
    let rightTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor leftProjection I.Y).obj leg))
    FYg.map e.hom ≫ cg.hom ≫
        (FibredCategoryMor.fiberFunctor leftProjection V').map rightSource =
      rightTarget ≫ eg.hom := by
  let P := FibredCategoryOver.twoFibreProduct
    (toFibredCategoryMor F) (toFibredCategoryMor G)
  let leftProjection :=
    FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
  let leg :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I
  let e := FibredCategoryMor.pullbackComparison leftProjection f leg
  let eg := FibredCategoryMor.pullbackComparison leftProjection gf leg
  let cg := FibredCategoryMor.pullbackComparison leftProjection g
    (((canonicalFiberPseudofunctor P.p).map f.op.toLoc).toFunctor.obj leg)
  let rightSource :=
    (((canonicalFiberPseudofunctor P.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app leg)
  let rightTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor leftProjection I.Y).obj leg))
  have hboundary :
      cg.inv ≫ FYg.map e.inv ≫ rightTarget =
        (FibredCategoryMor.fiberFunctor leftProjection V').map rightSource ≫ eg.inv := by
    -- Specialize the general right-boundary comparison to the explicit left projection and leg.
    simpa only [P, leftProjection, FYg, leg, e, eg, cg, rightSource, rightTarget, Category.assoc] using
      stack_morphism_pullbackComparison_pullHom_right_boundary
        (H := leftProjection) f g gf hgf leg
  -- Cancel the common `g`-leg comparison and the transported `f`-leg comparison to expose the
  -- strict target boundary over the composite leg `gf`.
  calc
    FYg.map e.hom ≫ cg.hom ≫
        (FibredCategoryMor.fiberFunctor leftProjection V').map rightSource =
      FYg.map e.hom ≫ cg.hom ≫
        ((FibredCategoryMor.fiberFunctor leftProjection V').map rightSource ≫ eg.inv) ≫
        eg.hom := by
          simp only [Category.assoc]
    _ =
      FYg.map e.hom ≫ cg.hom ≫ (cg.inv ≫ FYg.map e.inv ≫ rightTarget) ≫ eg.hom := by
          rw [← hboundary]
    _ = rightTarget ≫ eg.hom := by
          simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: the previous head cancellation is symmetric for the right
projection, replacing `Q.fst` by `Q.snd` and the left owner projection by the right one. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_right_projection_comparison_cancel_head
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    {I : T.Arrow}
    (f : V ⟶ I.Y) (g : V' ⟶ V) (gf : V' ⟶ I.Y)
    (hgf : g ≫ f = gf := by cat_disch) :
    let P := FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)
    let rightProjection :=
      FibredCategoryOver.twoFibreProductRightProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let leg :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I
    let e := FibredCategoryMor.pullbackComparison rightProjection f leg
    let eg := FibredCategoryMor.pullbackComparison rightProjection gf leg
    let cg := FibredCategoryMor.pullbackComparison rightProjection g
      (((canonicalFiberPseudofunctor P.p).map f.op.toLoc).toFunctor.obj leg)
    let leftSource :=
      (((canonicalFiberPseudofunctor P.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app leg)
    let leftTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor rightProjection I.Y).obj leg))
    (FibredCategoryMor.fiberFunctor rightProjection V').map leftSource ≫
        cg.inv ≫ FYg.map e.inv =
      eg.inv ≫ leftTarget := by
  let P := FibredCategoryOver.twoFibreProduct
    (toFibredCategoryMor F) (toFibredCategoryMor G)
  let rightProjection :=
    FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let leg :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I
  let e := FibredCategoryMor.pullbackComparison rightProjection f leg
  let eg := FibredCategoryMor.pullbackComparison rightProjection gf leg
  let cg := FibredCategoryMor.pullbackComparison rightProjection g
    (((canonicalFiberPseudofunctor P.p).map f.op.toLoc).toFunctor.obj leg)
  let leftSource :=
    (((canonicalFiberPseudofunctor P.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app leg)
  let leftTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor rightProjection I.Y).obj leg))
  have hboundary :
      leftTarget ≫ FYg.map e.hom =
        eg.hom ≫ (FibredCategoryMor.fiberFunctor rightProjection V').map leftSource ≫ cg.inv := by
    -- The right projection satisfies the same left-boundary comparison identity.
    simpa only [P, rightProjection, FYg, leg, e, eg, cg, leftSource, leftTarget, Category.assoc] using
      stack_morphism_pullbackComparison_pullHom_left_boundary
        (H := rightProjection) f g gf hgf leg
  -- Cancel the two comparison isomorphisms exactly as on the left projection.
  calc
    (FibredCategoryMor.fiberFunctor rightProjection V').map leftSource ≫
        cg.inv ≫ FYg.map e.inv =
      eg.inv ≫
        (eg.hom ≫ (FibredCategoryMor.fiberFunctor rightProjection V').map leftSource ≫ cg.inv) ≫
        FYg.map e.inv := by
          simp only [Category.assoc]
    _ =
      eg.inv ≫ (leftTarget ≫ FYg.map e.hom) ≫ FYg.map e.inv := by
          rw [← hboundary]
    _ = eg.inv ≫ leftTarget := by
          simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: the previous tail cancellation is symmetric for the right
projection, replacing `Q.fst` by `Q.snd` and the left owner projection by the right one. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_right_projection_comparison_cancel_tail
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    {I : T.Arrow}
    (f : V ⟶ I.Y) (g : V' ⟶ V) (gf : V' ⟶ I.Y)
    (hgf : g ≫ f = gf := by cat_disch) :
    let P := FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)
    let rightProjection :=
      FibredCategoryOver.twoFibreProductRightProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let leg :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I
    let e := FibredCategoryMor.pullbackComparison rightProjection f leg
    let eg := FibredCategoryMor.pullbackComparison rightProjection gf leg
    let cg := FibredCategoryMor.pullbackComparison rightProjection g
      (((canonicalFiberPseudofunctor P.p).map f.op.toLoc).toFunctor.obj leg)
    let rightSource :=
      (((canonicalFiberPseudofunctor P.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app leg)
    let rightTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor rightProjection I.Y).obj leg))
    FYg.map e.hom ≫ cg.hom ≫
        (FibredCategoryMor.fiberFunctor rightProjection V').map rightSource =
      rightTarget ≫ eg.hom := by
  let P := FibredCategoryOver.twoFibreProduct
    (toFibredCategoryMor F) (toFibredCategoryMor G)
  let rightProjection :=
    FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let leg :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I
  let e := FibredCategoryMor.pullbackComparison rightProjection f leg
  let eg := FibredCategoryMor.pullbackComparison rightProjection gf leg
  let cg := FibredCategoryMor.pullbackComparison rightProjection g
    (((canonicalFiberPseudofunctor P.p).map f.op.toLoc).toFunctor.obj leg)
  let rightSource :=
    (((canonicalFiberPseudofunctor P.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app leg)
  let rightTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor rightProjection I.Y).obj leg))
  have hboundary :
      cg.inv ≫ FYg.map e.inv ≫ rightTarget =
        (FibredCategoryMor.fiberFunctor rightProjection V').map rightSource ≫ eg.inv := by
    -- The right projection satisfies the same right-boundary comparison identity.
    simpa only [P, rightProjection, FYg, leg, e, eg, cg, rightSource, rightTarget, Category.assoc] using
      stack_morphism_pullbackComparison_pullHom_right_boundary
        (H := rightProjection) f g gf hgf leg
  -- Cancel the common `g`-leg and transported `f`-leg comparisons symmetrically.
  calc
    FYg.map e.hom ≫ cg.hom ≫
        (FibredCategoryMor.fiberFunctor rightProjection V').map rightSource =
      FYg.map e.hom ≫ cg.hom ≫
        ((FibredCategoryMor.fiberFunctor rightProjection V').map rightSource ≫ eg.inv) ≫
        eg.hom := by
          simp only [Category.assoc]
    _ =
      FYg.map e.hom ≫ cg.hom ≫ (cg.inv ≫ FYg.map e.inv ≫ rightTarget) ≫ eg.hom := by
          rw [← hboundary]
    _ = rightTarget ≫ eg.hom := by
          simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: before the middle `Q.fst` shell is rewritten, the left boundary of
the projected common-refinement source already normalizes to the literal `gf`-target shell once
the source-side `mapComp'` boundary is kept visible. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_head_from_source_shell
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    {I : T.Arrow}
    (f : V ⟶ I.Y) (g : V' ⟶ V) (gf : V' ⟶ I.Y)
    (hgf : g ≫ f = gf := by cat_disch) :
    let P := FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)
    let leftProjection :=
      FibredCategoryOver.twoFibreProductLeftProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
    let leg :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I
    let e := FibredCategoryMor.pullbackComparison leftProjection f leg
    let eg := FibredCategoryMor.pullbackComparison leftProjection gf leg
    let cg := FibredCategoryMor.pullbackComparison leftProjection g
      (((canonicalFiberPseudofunctor P.p).map f.op.toLoc).toFunctor.obj leg)
    let leftSource :=
      (((canonicalFiberPseudofunctor P.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app leg)
    let leftTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor leftProjection I.Y).obj leg))
    let leftQTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        (Q.fst.obj I))
    (FibredCategoryMor.fiberFunctor leftProjection V').map leftSource ≫
        cg.inv ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I f).hom.fst) =
      eg.inv ≫
        (((canonicalFiberPseudofunctor X.p).map gf.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I)).hom) ≫
        leftQTarget := by
  let P := FibredCategoryOver.twoFibreProduct
    (toFibredCategoryMor F) (toFibredCategoryMor G)
  let leftProjection :=
    FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
  let leg :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I
  let e := FibredCategoryMor.pullbackComparison leftProjection f leg
  let eg := FibredCategoryMor.pullbackComparison leftProjection gf leg
  let cg := FibredCategoryMor.pullbackComparison leftProjection g
    (((canonicalFiberPseudofunctor P.p).map f.op.toLoc).toFunctor.obj leg)
  let leftSource :=
    (((canonicalFiberPseudofunctor P.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app leg)
  let leftTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor leftProjection I.Y).obj leg))
  let leftQTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      (Q.fst.obj I))
  -- First expand the packaged image comparison, then use the existing source-boundary
  -- cancellation and the reassociated `mapComp'.hom` naturality square.
  calc
    (FibredCategoryMor.fiberFunctor leftProjection V').map leftSource ≫
        cg.inv ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I f).hom.fst) =
      ((FibredCategoryMor.fiberFunctor leftProjection V').map leftSource ≫
          cg.inv ≫ FYg.map e.inv) ≫
        FYg.map
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I)).hom) := by
          rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_hom_fst
            (J := J) F G T Q I f]
          rw [Functor.map_comp]
          simp only [Category.assoc]
    _ =
      eg.inv ≫ leftTarget ≫
        FYg.map
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I)).hom) := by
          rw [explicit_two_fibre_product_cover_descent_pullback_inverse_left_projection_comparison_cancel_head
            (J := J) F G T Q f g gf hgf]
          simp only [Category.assoc]
    _ =
      eg.inv ≫
        (((canonicalFiberPseudofunctor X.p).map gf.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I)).hom) ≫
        leftQTarget := by
          rw [explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit_fst_mapComp_hom_reassociated
            (J := J) F G T Q f g gf hgf]
          simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: the same source-shell head normalization holds after projecting to
the right owner leg, with `Q.snd` in place of `Q.fst`. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_head_from_source_shell
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    {I : T.Arrow}
    (f : V ⟶ I.Y) (g : V' ⟶ V) (gf : V' ⟶ I.Y)
    (hgf : g ≫ f = gf := by cat_disch) :
    let P := FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)
    let rightProjection :=
      FibredCategoryOver.twoFibreProductRightProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let leg :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I
    let e := FibredCategoryMor.pullbackComparison rightProjection f leg
    let eg := FibredCategoryMor.pullbackComparison rightProjection gf leg
    let cg := FibredCategoryMor.pullbackComparison rightProjection g
      (((canonicalFiberPseudofunctor P.p).map f.op.toLoc).toFunctor.obj leg)
    let leftSource :=
      (((canonicalFiberPseudofunctor P.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app leg)
    let leftTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor rightProjection I.Y).obj leg))
    let leftQTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        (Q.snd.obj I))
    (FibredCategoryMor.fiberFunctor rightProjection V').map leftSource ≫
        cg.inv ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I f).hom.snd) =
      eg.inv ≫
        (((canonicalFiberPseudofunctor Y.p).map gf.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I)).hom) ≫
        leftQTarget := by
  let P := FibredCategoryOver.twoFibreProduct
    (toFibredCategoryMor F) (toFibredCategoryMor G)
  let rightProjection :=
    FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let leg :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I
  let e := FibredCategoryMor.pullbackComparison rightProjection f leg
  let eg := FibredCategoryMor.pullbackComparison rightProjection gf leg
  let cg := FibredCategoryMor.pullbackComparison rightProjection g
    (((canonicalFiberPseudofunctor P.p).map f.op.toLoc).toFunctor.obj leg)
  let leftSource :=
    (((canonicalFiberPseudofunctor P.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app leg)
  let leftTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor rightProjection I.Y).obj leg))
  let leftQTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      (Q.snd.obj I))
  -- The right projection is the same calculation: expand the packaged comparison, cancel the
  -- source-side boundary, and reassociate the `mapComp'.hom` naturality square.
  calc
    (FibredCategoryMor.fiberFunctor rightProjection V').map leftSource ≫
        cg.inv ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I f).hom.snd) =
      ((FibredCategoryMor.fiberFunctor rightProjection V').map leftSource ≫
          cg.inv ≫ FYg.map e.inv) ≫
        FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I)).hom) := by
          rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_hom_snd
            (J := J) F G T Q I f]
          rw [Functor.map_comp]
          simp only [Category.assoc]
    _ =
      eg.inv ≫ leftTarget ≫
        FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I)).hom) := by
          rw [explicit_two_fibre_product_cover_descent_pullback_inverse_right_projection_comparison_cancel_head
            (J := J) F G T Q f g gf hgf]
          simp only [Category.assoc]
    _ =
      eg.inv ≫
        (((canonicalFiberPseudofunctor Y.p).map gf.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I)).hom) ≫
        leftQTarget := by
          rw [explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit_snd_mapComp_hom_reassociated
            (J := J) F G T Q f g gf hgf]
          simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: before cancelling any common-refinement comparisons, the left
packaged head factor is exactly the explicit `e.inv` comparison followed by the transported
left counit component. This exposes the rigid head shell that the remaining source-faithful
normalization must act on. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_packaged_head_expanded
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    {I : T.Arrow}
    (f : V ⟶ I.Y) (g : V' ⟶ V) (gf : V' ⟶ I.Y)
    (hgf : g ≫ f = gf := by cat_disch) :
    let leftProjection :=
      FibredCategoryOver.twoFibreProductLeftProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
    let leg :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I
    let e := FibredCategoryMor.pullbackComparison leftProjection f leg
    let leftTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor leftProjection I.Y).obj leg))
    leftTarget ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I f).hom.fst) =
      leftTarget ≫ FYg.map e.inv ≫
        FYg.map
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I)).hom) := by
  let leftProjection :=
    FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
  let leg :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I
  let e := FibredCategoryMor.pullbackComparison leftProjection f leg
  let leftTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor leftProjection I.Y).obj leg))
  -- Expand the packaged comparison once so the parent theorem can focus on the literal shell.
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_hom_fst
    (J := J) F G T Q I f]
  rw [Functor.map_comp]
  simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: before cancelling any common-refinement comparisons, the left
packaged tail factor is exactly the transported left counit inverse followed by the direct
comparison `e.hom`. This freezes the right boundary in a rewrite-friendly form. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_packaged_tail_expanded
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    {I : T.Arrow}
    (f : V ⟶ I.Y) (g : V' ⟶ V) (gf : V' ⟶ I.Y)
    (hgf : g ≫ f = gf := by cat_disch) :
    let leftProjection :=
      FibredCategoryOver.twoFibreProductLeftProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
    let leg :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I
    let e := FibredCategoryMor.pullbackComparison leftProjection f leg
    let rightTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor leftProjection I.Y).obj leg))
    FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I f).inv.fst) ≫
        rightTarget =
      FYg.map
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I)).inv) ≫
        FYg.map e.hom ≫
        rightTarget := by
  let leftProjection :=
    FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
  let leg :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I
  let e := FibredCategoryMor.pullbackComparison leftProjection f leg
  let rightTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor leftProjection I.Y).obj leg))
  -- Unfold the packaged inverse once so the strict right boundary stays visible.
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_inv_fst
    (J := J) F G T Q I f]
  rw [Functor.map_comp]
  simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: the right packaged head likewise expands to the explicit
`e.inv` comparison followed by the transported right counit component. This is the mirrored
head adapter needed before any further `Q.snd` shell normalization. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_packaged_head_expanded
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    {I : T.Arrow}
    (f : V ⟶ I.Y) (g : V' ⟶ V) (gf : V' ⟶ I.Y)
    (hgf : g ≫ f = gf := by cat_disch) :
    let rightProjection :=
      FibredCategoryOver.twoFibreProductRightProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let leg :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I
    let e := FibredCategoryMor.pullbackComparison rightProjection f leg
    let leftTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor rightProjection I.Y).obj leg))
    leftTarget ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I f).hom.snd) =
      leftTarget ≫ FYg.map e.inv ≫
        FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I)).hom) := by
  let rightProjection :=
    FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let leg :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I
  let e := FibredCategoryMor.pullbackComparison rightProjection f leg
  let leftTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor rightProjection I.Y).obj leg))
  -- This is the right-projection mirror of the previous packaged-head expansion.
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_hom_snd
    (J := J) F G T Q I f]
  rw [Functor.map_comp]
  simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: the right packaged tail expands to the transported right counit
inverse followed by the direct comparison `e.hom`. Keeping this shell explicit isolates the
remaining mirrored suffix normalization. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_packaged_tail_expanded
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    {I : T.Arrow}
    (f : V ⟶ I.Y) (g : V' ⟶ V) (gf : V' ⟶ I.Y)
    (hgf : g ≫ f = gf := by cat_disch) :
    let rightProjection :=
      FibredCategoryOver.twoFibreProductRightProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let leg :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I
    let e := FibredCategoryMor.pullbackComparison rightProjection f leg
    let rightTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor rightProjection I.Y).obj leg))
    FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I f).inv.snd) ≫
        rightTarget =
      FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I)).inv) ≫
        FYg.map e.hom ≫
        rightTarget := by
  let rightProjection :=
    FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let leg :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I
  let e := FibredCategoryMor.pullbackComparison rightProjection f leg
  let rightTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor rightProjection I.Y).obj leg))
  -- Unfold the mirrored packaged inverse once and reassociate the visible suffix.
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_inv_snd
    (J := J) F G T Q I f]
  rw [Functor.map_comp]
  simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: expanding both packaged comparison factors around the left projected
overlap exposes the rigid `Q.fst` middle shell with explicit `e₁/e₂` boundary comparisons. This
records the exact exposed shell that remains to be rewritten to the literal `pullHom` form. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_packaged_to_exposed_q_shell
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let leftProjection :=
      FibredCategoryOver.twoFibreProductLeftProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
    let leg₁ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₁
    let leg₂ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₂
    let e₁ := FibredCategoryMor.pullbackComparison leftProjection f₁ leg₁
    let e₂ := FibredCategoryMor.pullbackComparison leftProjection f₂ leg₂
    let leftTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor leftProjection I₁.Y).obj leg₁))
    let rightTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor leftProjection I₂.Y).obj leg₂))
    leftTarget ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.fst) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.fst) ≫
        rightTarget =
      leftTarget ≫ FYg.map e₁.inv ≫
        FYg.map
          (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₁)).hom) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
        FYg.map e₂.hom ≫
        rightTarget := by
  let leftProjection :=
    FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
  let leg₁ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I₁
  let leg₂ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I₂
  let e₁ := FibredCategoryMor.pullbackComparison leftProjection f₁ leg₁
  let e₂ := FibredCategoryMor.pullbackComparison leftProjection f₂ leg₂
  let leftTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor leftProjection I₁.Y).obj leg₁))
  let rightTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor leftProjection I₂.Y).obj leg₂))
  -- Expand the packaged head and tail separately, but leave the literal `Q.fst` shell visible
  -- between them so later rewriting can focus only on that middle transport step.
  calc
    leftTarget ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.fst) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.fst) ≫
        rightTarget =
      (leftTarget ≫ FYg.map e₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
              ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₁)).hom)) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.fst) ≫
        rightTarget := by
          simpa only [leftProjection, FYg, leg₁, e₁, leftTarget, Category.assoc] using
            congrArg
              (fun k ↦ k ≫ FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
                FYg.map
                  ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
                    (J := J) F G T Q I₂ f₂).inv.fst) ≫
                rightTarget)
              (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_packaged_head_expanded
                (J := J) F G T Q f₁ g gf₁ hgf₁)
    )
    _ =
      leftTarget ≫ FYg.map e₁.inv ≫
        FYg.map
          (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₁)).hom) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        (FYg.map
          (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
          FYg.map e₂.hom) ≫
        rightTarget := by
          simpa only [leftProjection, FYg, leg₂, e₂, rightTarget, Category.assoc] using
            congrArg
              (fun k ↦ leftTarget ≫ FYg.map e₁.inv ≫
                FYg.map
                  (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
                    ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
                      (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                        (J := J) F G T Q I₁)).hom) ≫
                FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
                k)
              (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_packaged_tail_expanded
                (J := J) F G T Q f₂ g gf₂ hgf₂)
    )
    _ =
      leftTarget ≫ FYg.map e₁.inv ≫
        FYg.map
          (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₁)).hom) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
        FYg.map e₂.hom ≫
        rightTarget := by
          simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: the right projected packaged overlap expands to the explicit
`e₁/e₂` boundary shell around the literal `Q.snd` middle morphism. This is the mirrored exposed
shell that remains to be rewritten to the source `pullHom` form. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_packaged_to_exposed_q_shell
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let rightProjection :=
      FibredCategoryOver.twoFibreProductRightProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let leg₁ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₁
    let leg₂ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₂
    let e₁ := FibredCategoryMor.pullbackComparison rightProjection f₁ leg₁
    let e₂ := FibredCategoryMor.pullbackComparison rightProjection f₂ leg₂
    let leftTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor rightProjection I₁.Y).obj leg₁))
    let rightTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor rightProjection I₂.Y).obj leg₂))
    leftTarget ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.snd) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.snd) ≫
        rightTarget =
      leftTarget ≫ FYg.map e₁.inv ≫
        FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₁)).hom) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
        FYg.map e₂.hom ≫
        rightTarget := by
  let rightProjection :=
    FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let leg₁ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I₁
  let leg₂ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I₂
  let e₁ := FibredCategoryMor.pullbackComparison rightProjection f₁ leg₁
  let e₂ := FibredCategoryMor.pullbackComparison rightProjection f₂ leg₂
  let leftTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor rightProjection I₁.Y).obj leg₁))
  let rightTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor rightProjection I₂.Y).obj leg₂))
  -- Mirror the left-projection expansion so the remaining work is again concentrated in the
  -- literal `Q.snd` shell between fixed boundary comparisons.
  calc
    leftTarget ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.snd) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.snd) ≫
        rightTarget =
      (leftTarget ≫ FYg.map e₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₁)).hom)) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.snd) ≫
        rightTarget := by
          simpa only [rightProjection, FYg, leg₁, e₁, leftTarget, Category.assoc] using
            congrArg
              (fun k ↦ k ≫ FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
                FYg.map
                  ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
                    (J := J) F G T Q I₂ f₂).inv.snd) ≫
                rightTarget)
              (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_packaged_head_expanded
                (J := J) F G T Q f₁ g gf₁ hgf₁)
    )
    _ =
      leftTarget ≫ FYg.map e₁.inv ≫
        FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₁)).hom) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        (FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
          FYg.map e₂.hom) ≫
        rightTarget := by
          simpa only [rightProjection, FYg, leg₂, e₂, rightTarget, Category.assoc] using
            congrArg
              (fun k ↦ leftTarget ≫ FYg.map e₁.inv ≫
                FYg.map
                  (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
                    ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
                      (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                        (J := J) F G T Q I₁)).hom) ≫
                FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
                k)
              (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_packaged_tail_expanded
                (J := J) F G T Q f₂ g gf₂ hgf₂)
    )
    _ =
      leftTarget ≫ FYg.map e₁.inv ≫
        FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₁)).hom) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
        FYg.map e₂.hom ≫
        rightTarget := by
          simp only [Category.assoc]

/-- Helper for Lemma 8.4.6: once the two `mapComp'` boundary components are named explicitly, the
visible left projected q-shell is definitionally the `pullHom` of `Q.fst.hom`. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_q_shell_fold
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
    let leftQTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        (Q.fst.obj I₁))
    let rightQTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        (Q.fst.obj I₂))
    leftQTarget ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        rightQTarget =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (Q.fst.hom q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ := by
  let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
  let leftQTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      (Q.fst.obj I₁))
  let rightQTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      (Q.fst.obj I₂))
  -- Unfold `pullHom` once; the visible `q`-shell is exactly this three-factor composite.
  simp only [FYg, leftQTarget, rightQTarget, Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Functor.map_comp, Category.assoc]

/-- Helper for Lemma 8.4.6: the mirrored right projected q-shell is likewise definitionally the
literal `pullHom` of `Q.snd.hom`. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_q_shell_fold
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let leftQTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        (Q.snd.obj I₁))
    let rightQTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        (Q.snd.obj I₂))
    leftQTarget ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        rightQTarget =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (Q.snd.hom q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ := by
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let leftQTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      (Q.snd.obj I₁))
  let rightQTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      (Q.snd.obj I₂))
  -- The right projected q-shell unfolds in the same way.
  simp only [FYg, leftQTarget, rightQTarget, Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Functor.map_comp, Category.assoc]

/-- Helper for Lemma 8.4.6: once the `gf₁/gf₂` boundary comparisons are frozen, the visible left
projected q-shell folds directly to the conjugated literal `pullHom` shell. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_q_shell_conjugated
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let leftProjection :=
      FibredCategoryOver.twoFibreProductLeftProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
    let leg₁ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₁
    let leg₂ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₂
    let eg₁ := FibredCategoryMor.pullbackComparison leftProjection gf₁ leg₁
    let eg₂ := FibredCategoryMor.pullbackComparison leftProjection gf₂ leg₂
    let leftQTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        (Q.fst.obj I₁))
    let rightQTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        (Q.fst.obj I₂))
    eg₁.inv ≫
        (((canonicalFiberPseudofunctor X.p).map gf₁.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₁)).hom) ≫
        leftQTarget ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        rightQTarget ≫
        (((canonicalFiberPseudofunctor X.p).map gf₂.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₂)).inv) ≫
        eg₂.hom =
      eg₁.inv ≫
        (((canonicalFiberPseudofunctor X.p).map gf₁.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₁)).hom) ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (Q.fst.hom q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ ≫
        (((canonicalFiberPseudofunctor X.p).map gf₂.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₂)).inv) ≫
        eg₂.hom := by
  let leftProjection :=
    FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
  let leg₁ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I₁
  let leg₂ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I₂
  let eg₁ := FibredCategoryMor.pullbackComparison leftProjection gf₁ leg₁
  let eg₂ := FibredCategoryMor.pullbackComparison leftProjection gf₂ leg₂
  let leftQTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      (Q.fst.obj I₁))
  let rightQTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      (Q.fst.obj I₂))
  -- Freeze the outer `gf₁/gf₂` boundary comparisons and fold only the middle q-shell.
  exact
    congrArg
      (fun k ↦
        eg₁.inv ≫
          (((canonicalFiberPseudofunctor X.p).map gf₁.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₁)).hom) ≫
          k ≫
          (((canonicalFiberPseudofunctor X.p).map gf₂.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
          eg₂.hom)
      (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_q_shell_fold
        (J := J) F G T Q g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)

/-- Helper for Lemma 8.4.6: the mirrored right projected q-shell folds to the conjugated literal
`pullHom` shell once the `gf₁/gf₂` boundary comparisons are frozen. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_q_shell_conjugated
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let rightProjection :=
      FibredCategoryOver.twoFibreProductRightProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let leg₁ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₁
    let leg₂ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₂
    let eg₁ := FibredCategoryMor.pullbackComparison rightProjection gf₁ leg₁
    let eg₂ := FibredCategoryMor.pullbackComparison rightProjection gf₂ leg₂
    let leftQTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        (Q.snd.obj I₁))
    let rightQTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        (Q.snd.obj I₂))
    eg₁.inv ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₁)).hom) ≫
        leftQTarget ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        rightQTarget ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₂)).inv) ≫
        eg₂.hom =
      eg₁.inv ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₁)).hom) ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (Q.snd.hom q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₂)).inv) ≫
        eg₂.hom := by
  let rightProjection :=
    FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let leg₁ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I₁
  let leg₂ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I₂
  let eg₁ := FibredCategoryMor.pullbackComparison rightProjection gf₁ leg₁
  let eg₂ := FibredCategoryMor.pullbackComparison rightProjection gf₂ leg₂
  let leftQTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      (Q.snd.obj I₁))
  let rightQTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      (Q.snd.obj I₂))
  -- The right projection is the same whiskered q-shell fold with the mirrored boundary factors.
  exact
    congrArg
      (fun k ↦
        eg₁.inv ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₁)).hom) ≫
          k ≫
          (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
          eg₂.hom)
      (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_q_shell_fold
        (J := J) F G T Q g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)

/-- Helper for Lemma 8.4.6: after applying the owner fibre equivalence over the common
refinement `V'`, the pullback of the reflected source overlap becomes the owner-side common
refinement shell determined by `Q.fst`, `Q.snd`, and `Q.iso`. This isolates the remaining
transport-stable `pullHom` interface needed to package the inverse descent datum. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_conjugated_pullHom_hom
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let leftProjection :=
      FibredCategoryOver.twoFibreProductLeftProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
    let leg₁ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₁
    let leg₂ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₂
    let e₁ := FibredCategoryMor.pullbackComparison leftProjection f₁ leg₁
    let e₂ := FibredCategoryMor.pullbackComparison leftProjection f₂ leg₂
    let eg₁ := FibredCategoryMor.pullbackComparison leftProjection gf₁ leg₁
    let eg₂ := FibredCategoryMor.pullbackComparison leftProjection gf₂ leg₂
    let leftTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor leftProjection I₁.Y).obj leg₁))
    let rightTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor leftProjection I₂.Y).obj leg₂))
    leftTarget ≫ FYg.map e₁.inv ≫
        FYg.map
          (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₁)).hom) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
        FYg.map e₂.hom ≫
        rightTarget =
      eg₁.inv ≫
        (((canonicalFiberPseudofunctor X.p).map gf₁.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₁)).hom) ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (Q.fst.hom q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ ≫
        (((canonicalFiberPseudofunctor X.p).map gf₂.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₂)).inv) ≫
        eg₂.hom := by
  -- Route correction: isolate the source-faithful transport of `Q.fst.pullHom_hom` through the
  -- fixed `gf₁/gf₂` comparison boundaries before returning to the packaged parent theorem.
  let leftQTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      (Q.fst.obj I₁))
  let rightQTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      (Q.fst.obj I₂))
  -- The remaining q-shell is already frozen in the dedicated conjugated helper; this theorem
  -- only needs the exposed boundary terms to simplify to that literal shell.
  simpa only [leftProjection, FYg, leg₁, leg₂, eg₁, eg₂, leftQTarget, rightQTarget,
    Category.assoc] using
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_q_shell_conjugated
      (J := J) F G T Q g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂

/-- Helper for Lemma 8.4.6: the mirrored right-projection transport of `Q.snd.pullHom_hom`
rewrites the exposed packaged shell to the literal common-refinement `pullHom` shell. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_conjugated_pullHom_hom
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let rightProjection :=
      FibredCategoryOver.twoFibreProductRightProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let leg₁ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₁
    let leg₂ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₂
    let e₁ := FibredCategoryMor.pullbackComparison rightProjection f₁ leg₁
    let e₂ := FibredCategoryMor.pullbackComparison rightProjection f₂ leg₂
    let eg₁ := FibredCategoryMor.pullbackComparison rightProjection gf₁ leg₁
    let eg₂ := FibredCategoryMor.pullbackComparison rightProjection gf₂ leg₂
    let leftTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor rightProjection I₁.Y).obj leg₁))
    let rightTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor rightProjection I₂.Y).obj leg₂))
    leftTarget ≫ FYg.map e₁.inv ≫
        FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₁)).hom) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
        FYg.map e₂.hom ≫
        rightTarget =
      eg₁.inv ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₁)).hom) ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (Q.snd.hom q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₂)).inv) ≫
        eg₂.hom := by
  -- Route correction: this is the right-projection mirror of the completed left proof, so once
  -- the common-refinement source shell is frozen at `Q.snd`, the remaining normalization is
  -- exactly the packaged `gf₁/gf₂`-boundary shell already isolated in the mirrored helper.
  let rightProjection :=
    FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let leg₁ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I₁
  let leg₂ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I₂
  let eg₁ := FibredCategoryMor.pullbackComparison rightProjection gf₁ leg₁
  let eg₂ := FibredCategoryMor.pullbackComparison rightProjection gf₂ leg₂
  let leftQTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      (Q.snd.obj I₁))
  let rightQTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      (Q.snd.obj I₂))
  -- The exposed source shell is already the literal right-projection q-shell after these local
  -- aliases are unfolded, so the remaining equality is the frozen conjugated shell theorem.
  simpa only [rightProjection, FYg, leg₁, leg₂, eg₁, eg₂, leftQTarget, rightQTarget,
    Category.assoc] using
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_q_shell_conjugated
      (J := J) F G T Q g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂

/-- Helper for Lemma 8.4.6: after applying the owner fibre equivalence over the common
refinement `V'`, the pullback of the reflected source overlap becomes the owner-side common
refinement shell determined by `Q.fst`, `Q.snd`, and `Q.iso`. This isolates the remaining
transport-stable `pullHom` interface needed to package the inverse descent datum. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_packaged_tail_normalized
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let leftProjection :=
      FibredCategoryOver.twoFibreProductLeftProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
    let leg₁ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₁
    let leg₂ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₂
    let e₁ := FibredCategoryMor.pullbackComparison leftProjection f₁ leg₁
    let e₂ := FibredCategoryMor.pullbackComparison leftProjection f₂ leg₂
    let eg₁ := FibredCategoryMor.pullbackComparison leftProjection gf₁ leg₁
    let eg₂ := FibredCategoryMor.pullbackComparison leftProjection gf₂ leg₂
    let leftTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor leftProjection I₁.Y).obj leg₁))
    let rightTarget :=
      (((canonicalFiberPseudofunctor X.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor leftProjection I₂.Y).obj leg₂))
    leftTarget ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.fst) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.fst) ≫
        rightTarget =
      eg₁.inv ≫
        (((canonicalFiberPseudofunctor X.p).map gf₁.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₁)).hom) ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (Q.fst.hom q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ ≫
        (((canonicalFiberPseudofunctor X.p).map gf₂.op.toLoc).toFunctor.map
        ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₂)).inv) ≫
        eg₂.hom := by
  -- Route correction: isolate the last transport-heavy tail instead of continuing to normalize the
  -- whole projected source theorem at once.
  let leftQTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      (Q.fst.obj I₁))
  let rightQTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      (Q.fst.obj I₂))
  have hexposed :
      leftTarget ≫
          FYg.map
            ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
              (J := J) F G T Q I₁ f₁).hom.fst) ≫
          FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
          FYg.map
            ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
              (J := J) F G T Q I₂ f₂).inv.fst) ≫
          rightTarget =
        leftTarget ≫ FYg.map e₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
              ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₁)).hom) ≫
          FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
          FYg.map
            (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
              ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₂)).inv) ≫
          FYg.map e₂.hom ≫
          rightTarget := by
    -- Freeze both packaged factors at once so the only remaining work is the literal `Q.fst`
    -- shell between the explicit `e₁/e₂` boundary comparisons.
    simpa only [leftProjection, FYg, leg₁, leg₂, e₁, e₂, leftTarget, rightTarget,
      Category.assoc] using
      explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_packaged_to_exposed_q_shell
        (J := J) F G T Q g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  -- The remaining transport is now isolated in a dedicated source-faithful helper, so the parent
  -- theorem only glues the packaged shell to that literal `pullHom` normalization.
  exact
    hexposed.trans
      (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_conjugated_pullHom_hom
        (J := J) F G T Q g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)

/-- Helper for Lemma 8.4.6: the mirrored packaged tail on the right projection normalizes to the
literal `gf₁/gf₂` shell around `Q.snd.pullHom_hom`. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_packaged_tail_normalized
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let rightProjection :=
      FibredCategoryOver.twoFibreProductRightProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)
    let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
    let leg₁ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₁
    let leg₂ :=
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I₂
    let e₁ := FibredCategoryMor.pullbackComparison rightProjection f₁ leg₁
    let e₂ := FibredCategoryMor.pullbackComparison rightProjection f₂ leg₂
    let eg₁ := FibredCategoryMor.pullbackComparison rightProjection gf₁ leg₁
    let eg₂ := FibredCategoryMor.pullbackComparison rightProjection gf₂ leg₂
    let leftTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor rightProjection I₁.Y).obj leg₁))
    let rightTarget :=
      (((canonicalFiberPseudofunctor Y.p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        ((FibredCategoryMor.fiberFunctor rightProjection I₂.Y).obj leg₂))
    leftTarget ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.snd) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.snd) ≫
        rightTarget =
      eg₁.inv ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₁)).hom) ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (Q.snd.hom q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₂)).inv) ≫
        eg₂.hom := by
  -- Route correction: mirror the left packaged-tail pivot so the right projection ends at the
  -- same explicit common-refinement shell.
  let leftQTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      (Q.snd.obj I₁))
  let rightQTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      (Q.snd.obj I₂))
  have hexposed :
      leftTarget ≫
          FYg.map
            ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
              (J := J) F G T Q I₁ f₁).hom.snd) ≫
          FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
          FYg.map
            ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
              (J := J) F G T Q I₂ f₂).inv.snd) ≫
          rightTarget =
        leftTarget ≫ FYg.map e₁.inv ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₁)).hom) ≫
          FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
          FYg.map
            (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
                (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                  (J := J) F G T Q I₂)).inv) ≫
          FYg.map e₂.hom ≫
          rightTarget := by
    -- Freeze the mirrored packaged factors simultaneously, leaving only the explicit `Q.snd`
    -- shell to rewrite to the literal source `pullHom`.
    simpa only [rightProjection, FYg, leg₁, leg₂, e₁, e₂, leftTarget, rightTarget,
      Category.assoc] using
      explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_packaged_to_exposed_q_shell
        (J := J) F G T Q g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  -- The mirrored transport step is now isolated in the dedicated right-projection helper.
  exact
    hexposed.trans
      (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_conjugated_pullHom_hom
        (J := J) F G T Q g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)

/-- Helper for Lemma 8.4.6: after applying the owner fibre equivalence over the common
refinement `V'`, the pullback of the reflected source overlap becomes the owner-side common
refinement shell determined by `Q.fst`, `Q.snd`, and `Q.iso`. This isolates the remaining
transport-stable `pullHom` interface needed to package the inverse descent datum. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_normalized
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) V').functor.map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
            (J := J) F G T Q q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂)).fst =
      (FibredCategoryMor.pullbackComparison
          (FibredCategoryOver.twoFibreProductLeftProjection
            (toFibredCategoryMor F) (toFibredCategoryMor G))
          gf₁
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
            (J := J) F G T Q I₁)).inv ≫
        (((canonicalFiberPseudofunctor X.p).map gf₁.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₁)).hom) ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (Q.fst.hom q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ ≫
        (((canonicalFiberPseudofunctor X.p).map gf₂.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₂)).inv) ≫
        (FibredCategoryMor.pullbackComparison
          (FibredCategoryOver.twoFibreProductLeftProjection
            (toFibredCategoryMor F) (toFibredCategoryMor G))
          gf₂
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
            (J := J) F G T Q I₂)).hom := by
  -- Route correction: replay the earlier fixed-cover shell normalization on the left projection.
  let leftProjection :=
    FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let FYg := ((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor
  let leg₁ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I₁
  let leg₂ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I₂
  let e₁ := FibredCategoryMor.pullbackComparison leftProjection f₁ leg₁
  let e₂ := FibredCategoryMor.pullbackComparison leftProjection f₂ leg₂
  let eg₁ := FibredCategoryMor.pullbackComparison leftProjection gf₁ leg₁
  let eg₂ := FibredCategoryMor.pullbackComparison leftProjection gf₂ leg₂
  let leftTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor leftProjection I₁.Y).obj leg₁))
  let rightTarget :=
    (((canonicalFiberPseudofunctor X.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor leftProjection I₂.Y).obj leg₂))
  let leftSource :=
    (((canonicalFiberPseudofunctor
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app leg₁)
  let rightSource :=
    (((canonicalFiberPseudofunctor
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app leg₂)
  -- Expand the outer shell, then split the projected middle factor into its five visible pieces.
  calc
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) V').functor.map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
              (J := J) F G T Q q f₁ f₂ hf₁ hf₂)
            g gf₁ gf₂ hgf₁ hgf₂)).fst =
      leftTarget ≫
        (FYg.map
          ((FibredCategoryMor.fiberFunctor leftProjection V).map
            (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
              (J := J) F G T Q q f₁ f₂ hf₁ hf₂))) ≫
        rightTarget := by
          simpa [leftProjection, FYg, leftTarget, rightTarget, Category.assoc] using
            explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_outer_expanded
              (J := J) F G T Q g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
    _ =
      leftTarget ≫ FYg.map e₁.inv ≫
        FYg.map
          (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₁)).hom) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
            ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
        FYg.map e₂.hom ≫
        rightTarget := by
          simpa [leftProjection, FYg, leg₁, leg₂, e₁, e₂, leftTarget, rightTarget,
            Category.assoc] using
            congrArg
              (fun k ↦ leftTarget ≫ k ≫ rightTarget)
              (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_middle_split
                (J := J) F G T Q g q f₁ f₂ hf₁ hf₂)
    _ =
      leftTarget ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.fst) ≫
        FYg.map (Q.fst.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.fst) ≫
        rightTarget := by
          -- Package the exposed middle shell through the already-defined image isomorphisms.
          simpa [FYg, leftProjection, leg₁, leg₂, e₁, e₂, leftTarget, rightTarget,
            Category.assoc] using
            congrArg
              (fun k ↦ leftTarget ≫ k ≫ rightTarget)
              (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_middle_packaged
                (J := J) F G T Q g q f₁ f₂ hf₁ hf₂)
    _ =
      eg₁.inv ≫
        (((canonicalFiberPseudofunctor X.p).map gf₁.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₁)).hom) ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (Q.fst.hom q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ ≫
        (((canonicalFiberPseudofunctor X.p).map gf₂.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₂)).inv) ≫
        eg₂.hom := by
          -- The final transport-heavy tail is isolated in a dedicated helper with the same local
          -- shell names, so the parent proof now closes by literal simplification.
          simpa only [leftProjection, FYg, leg₁, leg₂, e₁, e₂, eg₁, eg₂, leftTarget, rightTarget,
            Category.assoc] using
            explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_packaged_tail_normalized
              (J := J) F G T Q g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂

/-- Helper for Lemma 8.4.6: the right projection of the same reflected common-refinement source
shell normalizes to the explicit right comparison-conjugated shell whose middle factor is
`pullHom (Q.snd.hom ...)`. This is the symmetric projected source interface needed in the
common-refinement theorem. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_normalized
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V)
    (q : V ⟶ U)
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) V').functor.map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
            (J := J) F G T Q q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂)).snd =
      (FibredCategoryMor.pullbackComparison
          (FibredCategoryOver.twoFibreProductRightProjection
            (toFibredCategoryMor F) (toFibredCategoryMor G))
          gf₁
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
            (J := J) F G T Q I₁)).inv ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₁)).hom) ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (Q.snd.hom q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₂)).inv) ≫
        (FibredCategoryMor.pullbackComparison
          (FibredCategoryOver.twoFibreProductRightProjection
            (toFibredCategoryMor F) (toFibredCategoryMor G))
          gf₂
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
            (J := J) F G T Q I₂)).hom := by
  -- Route correction: expose the mirrored right-projection shell so the remaining blocker is the
  -- same boundary/naturality normalization as on the left projection.
  let rightProjection :=
    FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)
  let FYg := ((canonicalFiberPseudofunctor Y.p).map g.op.toLoc).toFunctor
  let leg₁ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I₁
  let leg₂ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg
      (J := J) F G T Q I₂
  let e₁ := FibredCategoryMor.pullbackComparison rightProjection f₁ leg₁
  let e₂ := FibredCategoryMor.pullbackComparison rightProjection f₂ leg₂
  let leftTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor rightProjection I₁.Y).obj leg₁))
  let rightTarget :=
    (((canonicalFiberPseudofunctor Y.p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor rightProjection I₂.Y).obj leg₂))
  -- The mirrored source shell now has the same exposed five-factor middle term as the left proof.
  calc
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) V').functor.map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
              (J := J) F G T Q q f₁ f₂ hf₁ hf₂)
            g gf₁ gf₂ hgf₁ hgf₂)).snd =
      leftTarget ≫
        (FYg.map
          ((FibredCategoryMor.fiberFunctor rightProjection V).map
            (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
              (J := J) F G T Q q f₁ f₂ hf₁ hf₂))) ≫
        rightTarget := by
          simpa [rightProjection, FYg, leftTarget, rightTarget, Category.assoc] using
            explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_outer_expanded
              (J := J) F G T Q g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
    _ =
      leftTarget ≫ FYg.map e₁.inv ≫
        FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₁)).hom) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
            ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
                (J := J) F G T Q I₂)).inv) ≫
        FYg.map e₂.hom ≫
        rightTarget := by
          simpa [rightProjection, FYg, leg₁, leg₂, e₁, e₂, leftTarget, rightTarget,
            Category.assoc] using
            congrArg
              (fun k ↦ leftTarget ≫ k ≫ rightTarget)
              (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_middle_split
                (J := J) F G T Q g q f₁ f₂ hf₁ hf₂)
    _ =
      leftTarget ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₁ f₁).hom.snd) ≫
        FYg.map (Q.snd.hom q f₁ f₂ hf₁ hf₂) ≫
        FYg.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I₂ f₂).inv.snd) ≫
        rightTarget := by
          -- Package the mirrored middle shell through the right image-isomorphism projections.
          simpa [FYg, rightProjection, leg₁, leg₂, e₁, e₂, leftTarget, rightTarget,
            Category.assoc] using
            congrArg
              (fun k ↦ leftTarget ≫ k ≫ rightTarget)
              (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_middle_packaged
                (J := J) F G T Q g q f₁ f₂ hf₁ hf₂)
    _ =
      eg₁.inv ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₁)).hom) ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (Q.snd.hom q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ ≫
        (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₂)).inv) ≫
        eg₂.hom := by
          -- The right projected tail is now delegated to the mirrored packaged-tail helper.
          simpa only [rightProjection, FYg, leg₁, leg₂, e₁, e₂, eg₁, eg₂, leftTarget, rightTarget,
            Category.assoc] using
            explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_packaged_tail_normalized
              (J := J) F G T Q g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂

/-- Helper for Lemma 8.4.6: after applying the owner fibre equivalence over the common
refinement `V'`, the pullback of the reflected source overlap becomes the owner-side common
refinement shell determined by `Q.fst`, `Q.snd`, and `Q.iso`. This isolates the remaining
transport-stable `pullHom` interface needed to package the inverse descent datum. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map
    (F : X ⟶ S) (G : Y ⟶ S) {U V' V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (g : V' ⟶ V) (q : V ⟶ U) (q' : V' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) V').functor.map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
            (J := J) F G T Q q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂) =
      (explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
          (J := J) F G T Q I₁ gf₁).hom ≫
        explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
          (J := J) F G T Q q' gf₁ gf₂
          (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
          (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) ≫
      (explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
          (J := J) F G T Q I₂ gf₂).inv := by
  let leftPrefix :=
    (FibredCategoryMor.pullbackComparison
        (FibredCategoryOver.twoFibreProductLeftProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G))
        gf₁
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
          (J := J) F G T Q I₁)).inv ≫
      (((canonicalFiberPseudofunctor X.p).map gf₁.op.toLoc).toFunctor.map
        ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
            (J := J) F G T Q I₁)).hom)
  let leftSuffix :=
    (((canonicalFiberPseudofunctor X.p).map gf₂.op.toLoc).toFunctor.map
      ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
          (J := J) F G T Q I₂)).inv) ≫
      (FibredCategoryMor.pullbackComparison
        (FibredCategoryOver.twoFibreProductLeftProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G))
        gf₂
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
          (J := J) F G T Q I₂)).hom
  let rightPrefix :=
    (FibredCategoryMor.pullbackComparison
        (FibredCategoryOver.twoFibreProductRightProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G))
        gf₁
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
          (J := J) F G T Q I₁)).inv ≫
      (((canonicalFiberPseudofunctor Y.p).map gf₁.op.toLoc).toFunctor.map
        ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
            (J := J) F G T Q I₁)).hom)
  let rightSuffix :=
    (((canonicalFiberPseudofunctor Y.p).map gf₂.op.toLoc).toFunctor.map
      ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
          (J := J) F G T Q I₂)).inv) ≫
      (FibredCategoryMor.pullbackComparison
        (FibredCategoryOver.twoFibreProductRightProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G))
        gf₂
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg
          (J := J) F G T Q I₂)).hom
  -- Compare the owner pullback morphisms projectionwise; each projection is now reduced to the
  -- normalized source shell and the already-frozen q'-target shell.
  apply CategoricalPullback.hom_ext
  · calc
      ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
            (toBasedFunctor F) (toBasedFunctor G) V').functor.map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
                (J := J) F G T Q q f₁ f₂ hf₁ hf₂)
              g gf₁ gf₂ hgf₁ hgf₂)).fst =
        leftPrefix ≫
          Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (Q.fst.hom q f₁ f₂ hf₁ hf₂)
            g gf₁ gf₂ hgf₁ hgf₂ ≫
          leftSuffix := by
            simpa [leftPrefix, leftSuffix, Category.assoc] using
              explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_fst_normalized
                (J := J) F G T Q g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
      _ =
        leftPrefix ≫
          Q.fst.hom q' gf₁ gf₂
            (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
            (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) ≫
          leftSuffix := by
            exact
              congrArg
                (fun k ↦ leftPrefix ≫ k ≫ leftSuffix)
                (Q.fst.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
      _ =
        ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
              (J := J) F G T Q I₁ gf₁).hom ≫
            explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
              (J := J) F G T Q q' gf₁ gf₂
              (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
              (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) ≫
            (explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
              (J := J) F G T Q I₂ gf₂).inv).fst := by
            symm
            simpa [leftPrefix, leftSuffix, Category.assoc] using
              explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_target_fst_expanded
                (J := J) F G T Q g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  · calc
      ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
            (toBasedFunctor F) (toBasedFunctor G) V').functor.map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
                (J := J) F G T Q q f₁ f₂ hf₁ hf₂)
              g gf₁ gf₂ hgf₁ hgf₂)).snd =
        rightPrefix ≫
          Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (Q.snd.hom q f₁ f₂ hf₁ hf₂)
            g gf₁ gf₂ hgf₁ hgf₂ ≫
          rightSuffix := by
            simpa [rightPrefix, rightSuffix, Category.assoc] using
              explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_source_snd_normalized
                (J := J) F G T Q g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
      _ =
        rightPrefix ≫
          Q.snd.hom q' gf₁ gf₂
            (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
            (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) ≫
          rightSuffix := by
            exact
              congrArg
                (fun k ↦ rightPrefix ≫ k ≫ rightSuffix)
                (Q.snd.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
      _ =
        ((explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
              (J := J) F G T Q I₁ gf₁).hom ≫
            explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
              (J := J) F G T Q q' gf₁ gf₂
              (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
              (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) ≫
            (explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
              (J := J) F G T Q I₂ gf₂).inv).snd := by
            symm
            simpa [rightPrefix, rightSuffix, Category.assoc] using
              explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map_target_snd_expanded
                (J := J) F G T Q g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂

/-- Helper for Lemma 8.4.6: the reflected owner shell packages to a genuine descent datum on the
explicit stack-level pullback by using the mapped common-refinement shell for `pullHom` and the
already-closed identity/cocycle lemmas for the reflected overlaps. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_obj
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))) :
    ((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
            (fun I : T.Arrow ↦ I.f)) :=
  { obj := fun I ↦
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg
        (J := J) F G T Q I
    hom := fun {V} q {I₁ I₂} f₁ f₂ hf₁ hf₂ ↦
      explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
        (J := J) F G T Q q f₁ f₂ hf₁ hf₂
    pullHom_hom := by
      intro V' V g q q' hq I₁ I₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
      let eV' :=
        CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) V'
      let hffV' : eV'.functor.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful eV'.functor
      -- Route correction: reflect the source `pullHom` equation through the fully faithful owner
      -- fibre equivalence, so the remaining transport work is isolated in the mapped shell
      -- theorem just above.
      apply hffV'.map_injective
      calc
        eV'.functor.map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
                (J := J) F G T Q q f₁ f₂ hf₁ hf₂)
              g gf₁ gf₂ hgf₁ hgf₂) =
          (explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
              (J := J) F G T Q I₁ gf₁).hom ≫
            explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
              (J := J) F G T Q q' gf₁ gf₂
              (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
              (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) ≫
            (explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
              (J := J) F G T Q I₂ gf₂).inv := by
                simpa [eV'] using
                  explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_pullHom_map
                    (J := J) F G T Q g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
        _ =
          eV'.functor.map
            (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
              (J := J) F G T Q q' gf₁ gf₂
              (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
              (by rw [← hq, ← hgf₂, Category.assoc, hf₂])) := by
                symm
                simpa [eV'] using
                  explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map
                    (J := J) F G T Q q' gf₁ gf₂
                    (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
                    (by rw [← hq, ← hgf₂, Category.assoc, hf₂])
    hom_self := by
      intro V q I g hg
      -- The self-overlap identity was already proved on the reflected source shell.
      simpa using
        explicit_two_fibre_product_cover_descent_pullback_inverse_hom_self
          (J := J) F G T Q q g hg
    hom_comp := by
      intro V q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
      -- The cocycle relation is the corresponding reflected owner-shell cocycle proved above.
      simpa using
        explicit_two_fibre_product_cover_descent_pullback_inverse_hom_comp
          (J := J) F G T Q q f₁ f₂ f₃ hf₁ hf₂ hf₃ }

/-- Helper for Lemma 8.4.6: the legwise morphisms reconstructed from a fixed-cover pullback
morphism satisfy the descent-data compatibility square after transporting to the owner-side
pulled component maps and using the already-stored commutativity of `φ.fst` and `φ.snd`. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_map_comm
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {Q₁ Q₂ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂)
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f₁.op.toLoc).toFunctor.map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
          (J := J) F G T φ I₁)) ≫
      explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
        (J := J) F G T Q₂ q f₁ f₂ hf₁ hf₂ =
        explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
          (J := J) F G T Q₁ q f₁ f₂ hf₁ hf₂ ≫
          (((canonicalFiberPseudofunctor
              (FibredCategoryOver.twoFibreProduct
                (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f₂.op.toLoc).toFunctor.map
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
              (J := J) F G T φ I₂)) := by
  let eV :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) V
  let hffV : eV.functor.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful eV.functor
  let η₁₁ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
      (J := J) F G T Q₁ I₁ f₁
  let η₂₁ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
      (J := J) F G T Q₂ I₁ f₁
  let η₁₂ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
      (J := J) F G T Q₁ I₂ f₂
  let η₂₂ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
      (J := J) F G T Q₂ I₂ f₂
  apply hffV.map_injective
  calc
    eV.functor.map
        ((((canonicalFiberPseudofunctor
              (FibredCategoryOver.twoFibreProduct
                (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f₁.op.toLoc).toFunctor.map
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
              (J := J) F G T φ I₁)) ≫
          explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
            (J := J) F G T Q₂ q f₁ f₂ hf₁ hf₂) =
      eV.functor.map
          (((canonicalFiberPseudofunctor
                (FibredCategoryOver.twoFibreProduct
                  (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f₁.op.toLoc).toFunctor.map
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
                (J := J) F G T φ I₁)) ≫
        eV.functor.map
          (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
            (J := J) F G T Q₂ q f₁ f₂ hf₁ hf₂) := by
            rw [eV.functor.map_comp]
    _ =
      (η₁₁.hom ≫
          explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map
            (J := J) F G T φ I₁ f₁ ≫
          η₂₁.inv) ≫
        (η₂₁.hom ≫
          explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
            (J := J) F G T Q₂ q f₁ f₂ hf₁ hf₂ ≫
          η₂₂.inv) := by
            simp [η₁₁, η₂₁, η₂₂, Category.assoc,
              explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_hom_naturality,
              explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map]
    _ =
      η₁₁.hom ≫
        explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map
          (J := J) F G T φ I₁ f₁ ≫
        explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
          (J := J) F G T Q₂ q f₁ f₂ hf₁ hf₂ ≫
        η₂₂.inv := by
            simp [Category.assoc]
    _ =
      η₁₁.hom ≫
        (explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
            (J := J) F G T Q₁ q f₁ f₂ hf₁ hf₂ ≫
          explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map
            (J := J) F G T φ I₂ f₂) ≫
        η₂₂.inv := by
            exact congrArg
              (fun k ↦ η₁₁.hom ≫ k ≫ η₂₂.inv)
              (by
                -- Check the owner-side square projectionwise; it is exactly the descent-data
                -- compatibility of `φ.fst` and `φ.snd`.
                apply CategoricalPullback.hom_ext
                · rw [explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map_fst
                      (J := J) F G T φ I₁ f₁,
                    explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell_fst
                      (J := J) F G T Q₂ q f₁ f₂ hf₁ hf₂,
                    explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell_fst
                      (J := J) F G T Q₁ q f₁ f₂ hf₁ hf₂,
                    explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map_fst
                      (J := J) F G T φ I₂ f₂]
                  exact φ.fst.comm q f₁ f₂ hf₁ hf₂
                · rw [explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map_snd
                      (J := J) F G T φ I₁ f₁,
                    explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell_snd
                      (J := J) F G T Q₂ q f₁ f₂ hf₁ hf₂,
                    explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell_snd
                      (J := J) F G T Q₁ q f₁ f₂ hf₁ hf₂,
                    explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map_snd
                      (J := J) F G T φ I₂ f₂]
                  exact φ.snd.comm q f₁ f₂ hf₁ hf₂)
    _ =
      (η₁₁.hom ≫
          explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
            (J := J) F G T Q₁ q f₁ f₂ hf₁ hf₂ ≫
          η₁₂.inv) ≫
        (η₁₂.hom ≫
          explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_map
            (J := J) F G T φ I₂ f₂ ≫
          η₂₂.inv) := by
            simp [Category.assoc]
    _ =
      eV.functor.map
          (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
            (J := J) F G T Q₁ q f₁ f₂ hf₁ hf₂) ≫
        eV.functor.map
          (((canonicalFiberPseudofunctor
                (FibredCategoryOver.twoFibreProduct
                  (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f₂.op.toLoc).toFunctor.map
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
                (J := J) F G T φ I₂)) := by
            simp [η₁₁, η₁₂, η₂₂, Category.assoc,
              explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_hom_naturality,
              explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map]
    _ =
      eV.functor.map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom
            (J := J) F G T Q₁ q f₁ f₂ hf₁ hf₂ ≫
          (((canonicalFiberPseudofunctor
                (FibredCategoryOver.twoFibreProduct
                  (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f₂.op.toLoc).toFunctor.map
              (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
                (J := J) F G T φ I₂))) := by
            rw [eV.functor.map_comp]

/-- Helper for Lemma 8.4.6: the source-faithful inverse on fixed-cover pullback descent data is
now a genuine functor, since the object reconstruction, overlap transport, and componentwise map
compatibility have all been frozen in earlier lemmas. -/
private noncomputable def explicit_two_fibre_product_cover_descent_pullback_inverse_functor
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    ((cover_descent_data_functor_of_stack_morphism
        (J := J) (toFibredCategoryMor F) T) ⊡
      (cover_descent_data_functor_of_stack_morphism
        (J := J) (toFibredCategoryMor G) T)) ⥤
      ((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
            (fun I : T.Arrow ↦ I.f)) where
  obj Q :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_obj
      (J := J) F G T Q
  map {Q₁ Q₂} φ :=
    { hom := fun I ↦
        explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
          (J := J) F G T φ I
      comm := by
        intro V q I₁ I₂ f₁ f₂ hf₁ hf₂
        -- The owner-side pulled component maps already freeze the needed square.
        simpa using
          explicit_two_fibre_product_cover_descent_pullback_inverse_map_comm
            (J := J) F G T φ q f₁ f₂ hf₁ hf₂ }
  map_id Q := by
    -- Identities are checked componentwise on each cover leg.
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    simpa using
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom_id
        (J := J) F G T Q I
  map_comp φ ψ := by
    -- Composition is checked componentwise on each cover leg.
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    simpa using
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom_comp
        (J := J) F G T φ ψ I

/-- Helper for Lemma 8.4.6: on the left projection, applying the bridge to the reconstructed
fixed-cover inverse object recovers the original left descent datum by the legwise counit of the
Chapter 4 fibre equivalence. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_counit_fst
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))) :
    ((explicit_two_fibre_product_cover_descent_pullback_bridge
        (J := J) F G T).obj
      (explicit_two_fibre_product_cover_descent_pullback_inverse_obj
        (J := J) F G T Q)).fst ≅
      Q.fst := by
  -- Package the left projected legwise counits; the overlap shell has already been normalized to
  -- the exact conjugation form around `Q.fst.hom`.
  refine Pseudofunctor.DescentData.isoMk
    (fun I ↦
      (π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
          (J := J) F G T Q I))
    ?_
  intro V q I₁ I₂ f₁ f₂ hf₁ hf₂
  change
      (((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₁)).hom) ≫
        Q.fst.hom q f₁ f₂ hf₁ hf₂ =
      (cover_descent_data_functor_hom_of_stack_morphism
          (J := J)
          (FibredCategoryOver.twoFibreProductLeftProjection
            (toFibredCategoryMor F) (toFibredCategoryMor G))
          T
          (explicit_two_fibre_product_cover_descent_pullback_inverse_obj
            (J := J) F G T Q)
          q f₁ f₂ hf₁ hf₂) ≫
        (((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
          ((π₁ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₂)).hom)
  rw [cover_descent_data_functor_hom_of_stack_morphism]
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map_fst_expanded
    (J := J) F G T Q q f₁ f₂ hf₁ hf₂]
  simp [Category.assoc]

/-- Helper for Lemma 8.4.6: on the right projection, applying the bridge to the reconstructed
fixed-cover inverse object recovers the original right descent datum by the same legwise counit
construction. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_counit_snd
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))) :
    ((explicit_two_fibre_product_cover_descent_pullback_bridge
        (J := J) F G T).obj
      (explicit_two_fibre_product_cover_descent_pullback_inverse_obj
        (J := J) F G T Q)).snd ≅
      Q.snd := by
  -- The right projected counit is the mirror image of the left one.
  refine Pseudofunctor.DescentData.isoMk
    (fun I ↦
      (π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
          (J := J) F G T Q I))
    ?_
  intro V q I₁ I₂ f₁ f₂ hf₁ hf₂
  change
      (((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I₁.Y) (fiberFunctor G I₁.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₁)).hom) ≫
        Q.snd.hom q f₁ f₂ hf₁ hf₂ =
      (cover_descent_data_functor_hom_of_stack_morphism
          (J := J)
          (FibredCategoryOver.twoFibreProductRightProjection
            (toFibredCategoryMor F) (toFibredCategoryMor G))
          T
          (explicit_two_fibre_product_cover_descent_pullback_inverse_obj
            (J := J) F G T Q)
          q f₁ f₂ hf₁ hf₂) ≫
        (((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
          ((π₂ (fiberFunctor F I₂.Y) (fiberFunctor G I₂.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q I₂)).hom)
  rw [cover_descent_data_functor_hom_of_stack_morphism]
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map_snd_expanded
    (J := J) F G T Q q f₁ f₂ hf₁ hf₂]
  simp [Category.assoc]

/-- Helper for Lemma 8.4.6: the target-side roundtrip for the explicit bridge is obtained by
combining the two projected descent-data counits into an isomorphism in the categorical pullback.
-/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_counit
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))) :
    ((explicit_two_fibre_product_cover_descent_pullback_bridge
        (J := J) F G T).obj
      (explicit_two_fibre_product_cover_descent_pullback_inverse_obj
        (J := J) F G T Q)) ≅
      Q := by
  -- Package the two projected counits and discharge the midpoint compatibility componentwise on
  -- each cover leg from the categorical-pullback counit already frozen on that leg.
  refine CategoricalPullback.mkIso
    (explicit_two_fibre_product_cover_descent_pullback_inverse_counit_fst
      (J := J) F G T Q)
    (explicit_two_fibre_product_cover_descent_pullback_inverse_counit_snd
      (J := J) F G T Q)
    ?_
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  simpa only [explicit_two_fibre_product_cover_descent_pullback_inverse_counit_fst,
    explicit_two_fibre_product_cover_descent_pullback_inverse_counit_snd,
    explicit_two_fibre_product_cover_descent_pullback_bridge,
    explicit_two_fibre_product_cover_descent_projection_data_iso,
    explicit_two_fibre_product_cover_descent_projection_component_transport_iso,
    explicit_two_fibre_product_cover_descent_left_projection,
    explicit_two_fibre_product_cover_descent_right_projection,
    cover_descent_data_functor_of_stack_morphism] using
    (((explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
      (J := J) F G T Q I).hom).w)

/-- Helper for Lemma 8.4.6: on each cover leg, the owner pullback-of-fibres object attached to
`bridge.obj D` is the image under the Chapter 4 fibre equivalence of the original explicit
pullback leg `D.obj I`; this is the thin transport adapter for the source-side unit. -/
private noncomputable abbrev
    explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) :
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) I.Y).functor.obj
      (D.obj I)) ≅
      explicit_two_fibre_product_cover_descent_pullback_inverse_component
        (J := J) F G T
        ((explicit_two_fibre_product_cover_descent_pullback_bridge
          (J := J) F G T).obj D) I := by
  -- The two component objects are definitionally the same; only the midpoint iso must be
  -- retargeted to the exact coverwise bridge component.
  refine CategoricalPullback.mkIso (.refl _) (.refl _) ?_
  simpa only [explicit_two_fibre_product_cover_descent_pullback_bridge,
    explicit_two_fibre_product_cover_descent_projection_data_iso,
    explicit_two_fibre_product_cover_descent_projection_component_transport_iso,
    explicit_two_fibre_product_cover_descent_pullback_inverse_component,
    explicit_two_fibre_product_cover_descent_left_projection,
    explicit_two_fibre_product_cover_descent_right_projection,
    cover_descent_data_functor_of_stack_morphism]

/-- Helper for Lemma 8.4.6: the legwise transport adapter for the source-side unit is natural in
ordinary morphisms of explicit pullback descent data, so later unit naturality can be reduced to
the Chapter 4 unit square plus this owner-side component transport square. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_naturality
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {D₁ D₂ : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
          (fun I : T.Arrow ↦ I.f))}
    (φ : D₁ ⟶ D₂) (I : T.Arrow) :
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) I.Y).functor.map
      (φ.hom I)) ≫
      (explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso
        (J := J) F G T D₂ I).hom =
        (explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso
          (J := J) F G T D₁ I).hom ≫
          explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
            (J := J) F G T
            ((explicit_two_fibre_product_cover_descent_pullback_bridge
              (J := J) F G T).map φ) I := by
  -- Compare the owner-side square projectionwise; each side is definitionally the corresponding
  -- left or right component of `bridge.map φ` on the cover leg `I`.
  apply CategoricalPullback.hom_ext
  · simpa only [explicit_two_fibre_product_cover_descent_pullback_bridge,
      explicit_two_fibre_product_cover_descent_projection_data_iso,
      explicit_two_fibre_product_cover_descent_projection_component_transport_iso,
      explicit_two_fibre_product_cover_descent_left_projection,
      explicit_two_fibre_product_cover_descent_right_projection,
      cover_descent_data_functor_of_stack_morphism,
      explicit_two_fibre_product_cover_descent_pullback_inverse_component_map_fst]
  · simpa only [explicit_two_fibre_product_cover_descent_pullback_bridge,
      explicit_two_fibre_product_cover_descent_projection_data_iso,
      explicit_two_fibre_product_cover_descent_projection_component_transport_iso,
      explicit_two_fibre_product_cover_descent_left_projection,
      explicit_two_fibre_product_cover_descent_right_projection,
      cover_descent_data_functor_of_stack_morphism,
      explicit_two_fibre_product_cover_descent_pullback_inverse_component_map_snd]

/-- Helper for Lemma 8.4.6: on each cover leg, the source-side unit is the Chapter 4 unit of the
fibre equivalence, followed by the inverse-image of the component transport iso identifying the
owner pullback object of `bridge.obj D` with the image of `D.obj I`. -/
private noncomputable abbrev
    explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_iso
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) :
    D.obj I ≅
      (explicit_two_fibre_product_cover_descent_pullback_inverse_obj
        (J := J) F G T
        ((explicit_two_fibre_product_cover_descent_pullback_bridge
          (J := J) F G T).obj D)).obj I :=
  let eI :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) I.Y
  -- Freeze the true source-side unit component before any overlap manipulations: first the unit
  -- of the fibre equivalence, then the inverse-image of the owner-side transport adapter.
  (eI.unitIso.app (D.obj I)) ≪≫
    (eI.inverse.mapIso
      (explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso
        (J := J) F G T D I))

/-- Helper for Lemma 8.4.6: after specializing the bridge object
`Q := bridge.obj D`, the owner-side overlap square on its projected components is exactly the
stored transport commutator for the explicit pullback comparisons. This freezes the middle
owner-side square before reinserting the Chapter 4 unit components. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_unit_overlap_owner_square
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor S.p).map f₁.op.toLoc).toFunctor.map
        (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
          (J := J) F G T D I₁).hom) ≫
      (((explicit_two_fibre_product_cover_descent_pullback_bridge
          (J := J) F G T).obj D).snd.hom
        q f₁ f₂ hf₁ hf₂) =
    (((explicit_two_fibre_product_cover_descent_pullback_bridge
        (J := J) F G T).obj D).fst.hom
      q f₁ f₂ hf₁ hf₂) ≫
      (((canonicalFiberPseudofunctor S.p).map f₂.op.toLoc).toFunctor.map
        (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
          (J := J) F G T D I₂).hom) := by
  -- Specializing `projection_component_transport_comm` to `bridge.obj D` exposes exactly the
  -- owner-side middle square used later inside the reflected unit-overlap calculation.
  simpa only [explicit_two_fibre_product_cover_descent_pullback_bridge,
    explicit_two_fibre_product_cover_descent_projection_data_iso,
    explicit_two_fibre_product_cover_descent_left_projection,
    explicit_two_fibre_product_cover_descent_right_projection,
    cover_descent_data_functor_of_stack_morphism] using
    explicit_two_fibre_product_cover_descent_projection_component_transport_comm
      (J := J) F G T D q f₁ f₂ hf₁ hf₂

/-- Helper for Lemma 8.4.6: after pulling a source-side unit component along a cover map `f` and
then applying the owner fibre equivalence over `V`, the result splits into the mapped Chapter 4
unit component followed by the mapped owner-side transport adapter. This packages the exact
boundary normalization needed on both sides of the remaining overlap equation. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_boundary_expanded
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) (f : V ⟶ I.Y) :
    (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) V).functor.map
      (((canonicalFiberPseudofunctor
            (FibredCategoryOver.twoFibreProduct
              (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f.op.toLoc).toFunctor.map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_iso
          (J := J) F G T D I).hom) =
      (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) V).functor.map
        (((canonicalFiberPseudofunctor
              (FibredCategoryOver.twoFibreProduct
                (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f.op.toLoc).toFunctor.map
          ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
              (toBasedFunctor F) (toBasedFunctor G) I.Y).unitIso.app
            (D.obj I)).hom) ≫
      (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) V).functor.map
        (((canonicalFiberPseudofunctor
              (FibredCategoryOver.twoFibreProduct
                (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f.op.toLoc).toFunctor.map
          ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
              (toBasedFunctor F) (toBasedFunctor G) I.Y).inverse.map
            ((explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso
              (J := J) F G T D I).hom))) := by
  let eV :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) V
  let eI :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) I.Y
  -- Expand the frozen unit component once, then split the two functorial compositions in the
  -- same parenthesized form used later inside the mapped overlap calculation.
  change
    eV.functor.map
        (((canonicalFiberPseudofunctor
              (FibredCategoryOver.twoFibreProduct
                (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f.op.toLoc).toFunctor.map
          ((eI.unitIso.app (D.obj I)).hom ≫
            eI.inverse.map
              ((explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso
                (J := J) F G T D I).hom))) =
      eV.functor.map
          (((canonicalFiberPseudofunctor
                (FibredCategoryOver.twoFibreProduct
                  (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f.op.toLoc).toFunctor.map
            ((eI.unitIso.app (D.obj I)).hom)) ≫
        eV.functor.map
          (((canonicalFiberPseudofunctor
                (FibredCategoryOver.twoFibreProduct
                  (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f.op.toLoc).toFunctor.map
            (eI.inverse.map
              ((explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso
                (J := J) F G T D I).hom)))
  -- Only the two functoriality rewrites are used here; no transport normalization happens yet.
  rw [Functor.map_comp, eV.functor.map_comp]

/-- Helper for Lemma 8.4.6: after freezing the owner-side transport morphism determined by the
pulled component-transport comparison, the remaining mapped inverse-image boundary is exactly the
inverse image-isomorphism shell over `f`. This packages the one owner-category normalization used
twice in the final mapped overlap proof. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_boundary_to_image_iso_shell
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) (f : V ⟶ I.Y) :
    (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) V).functor.map
      (((canonicalFiberPseudofunctor
            (FibredCategoryOver.twoFibreProduct
              (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f.op.toLoc).toFunctor.map
        ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
            (toBasedFunctor F) (toBasedFunctor G) I.Y).inverse.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso
            (J := J) F G T D I).hom))) =
      (let Q :=
          (explicit_two_fibre_product_cover_descent_pullback_bridge
            (J := J) F G T).obj D
        let η :=
          explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
            (J := J) F G T Q I f
        let θ :
            _ ⟶ explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
              (J := J) F G T Q I f :=
          ⟨𝟙 _,
            𝟙 _,
            by
              -- The middle component is exactly the pulled transport comparison for `D.obj I`,
              -- retargeted to the specialized bridge object `Q := bridge.obj D`.
              simpa only [explicit_two_fibre_product_cover_descent_pullback_bridge,
                explicit_two_fibre_product_cover_descent_projection_data_iso,
                explicit_two_fibre_product_cover_descent_projection_component_transport_iso,
                explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback,
                explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_iso_hom,
                explicit_two_fibre_product_cover_descent_left_projection,
                explicit_two_fibre_product_cover_descent_right_projection,
                cover_descent_data_functor_of_stack_morphism, Category.assoc] using
                (((canonicalFiberPseudofunctor S.p).map f.op.toLoc).toFunctor.map
                  (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
                    (J := J) F G T D I).hom)⟩
        θ ≫ η.inv) := by
  let Q :=
    (explicit_two_fibre_product_cover_descent_pullback_bridge
      (J := J) F G T).obj D
  let η :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
      (J := J) F G T Q I f
  let θ :
      _ ⟶ explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
        (J := J) F G T Q I f :=
    ⟨𝟙 _,
      𝟙 _,
      by
        -- The midpoint square is the pulled specialized component transport comparison.
        simpa only [explicit_two_fibre_product_cover_descent_pullback_bridge,
          explicit_two_fibre_product_cover_descent_projection_data_iso,
          explicit_two_fibre_product_cover_descent_projection_component_transport_iso,
          explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback,
          explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_iso_hom,
          explicit_two_fibre_product_cover_descent_left_projection,
          explicit_two_fibre_product_cover_descent_right_projection,
          cover_descent_data_functor_of_stack_morphism, Category.assoc] using
          (((canonicalFiberPseudofunctor S.p).map f.op.toLoc).toFunctor.map
            (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
              (J := J) F G T D I).hom)⟩
  -- Compare the two boundary normalizations on the owner pullback projections; the inverse
  -- image-isomorphism formulas read off exactly the left and right pulled counit shells.
  apply CategoricalPullback.hom_ext
  · rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_inv_fst
      (J := J) F G T Q I f]
    simp [θ, η, Category.assoc,
      explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso]
  · rw [explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso_inv_snd
      (J := J) F G T Q I f]
    simp [θ, η, Category.assoc,
      explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso]

/-- Helper for Lemma 8.4.6: once the left mapped unit boundary has been normalized to the frozen
owner-side transport morphism `θ₁`, composing with the owner overlap shell is exactly the
specialized categorical-pullback morphism whose midpoint is the stored owner transport square for
`Q := bridge.obj D`. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_unit_overlap_left_boundary_shell
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (let Q :=
        (explicit_two_fibre_product_cover_descent_pullback_bridge
          (J := J) F G T).obj D
      let θ₁ :
          _ ⟶ explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
            (J := J) F G T Q I₁ f₁ :=
        ⟨𝟙 _,
          𝟙 _,
          by
            -- This is the already frozen owner-side transport comparison over the left boundary.
            simpa only [explicit_two_fibre_product_cover_descent_pullback_bridge,
              explicit_two_fibre_product_cover_descent_projection_data_iso,
              explicit_two_fibre_product_cover_descent_projection_component_transport_iso,
              explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback,
              explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_iso_hom,
              explicit_two_fibre_product_cover_descent_left_projection,
              explicit_two_fibre_product_cover_descent_right_projection,
              cover_descent_data_functor_of_stack_morphism, Category.assoc] using
              (((canonicalFiberPseudofunctor S.p).map f₁.op.toLoc).toFunctor.map
                (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
                  (J := J) F G T D I₁).hom)⟩
      θ₁ ≫
          explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
            (J := J) F G T Q q f₁ f₂ hf₁ hf₂ =
        ⟨(((explicit_two_fibre_product_cover_descent_pullback_bridge
              (J := J) F G T).obj D).fst.hom q f₁ f₂ hf₁ hf₂),
          (((explicit_two_fibre_product_cover_descent_pullback_bridge
              (J := J) F G T).obj D).snd.hom q f₁ f₂ hf₁ hf₂),
          by
            -- The midpoint is exactly the specialized owner-side transport square.
            simpa only [Q, Category.assoc] using
              explicit_two_fibre_product_cover_descent_pullback_inverse_unit_overlap_owner_square
                (J := J) F G T D q f₁ f₂ hf₁ hf₂⟩) := by
  let Q :=
    (explicit_two_fibre_product_cover_descent_pullback_bridge
      (J := J) F G T).obj D
  let θ₁ :
      _ ⟶ explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
        (J := J) F G T Q I₁ f₁ :=
    ⟨𝟙 _,
      𝟙 _,
      by
        -- Keep the boundary transport shell in the same normalized owner-side form as above.
        simpa only [explicit_two_fibre_product_cover_descent_pullback_bridge,
          explicit_two_fibre_product_cover_descent_projection_data_iso,
          explicit_two_fibre_product_cover_descent_projection_component_transport_iso,
          explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback,
          explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_iso_hom,
          explicit_two_fibre_product_cover_descent_left_projection,
          explicit_two_fibre_product_cover_descent_right_projection,
          cover_descent_data_functor_of_stack_morphism, Category.assoc] using
          (((canonicalFiberPseudofunctor S.p).map f₁.op.toLoc).toFunctor.map
            (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
              (J := J) F G T D I₁).hom)⟩
  -- Both sides are morphisms into the same owner pullback object over `V`; the midpoint equality
  -- is exactly the frozen transport square, while the two projections are definitional.
  apply CategoricalPullback.hom_ext
  · simp [Q, θ₁, explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell]
  · simp [Q, θ₁, explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell]

/-- Helper for Lemma 8.4.6: the frozen owner-side overlap square from
`explicit_two_fibre_product_cover_descent_pullback_inverse_unit_overlap_owner_square` is exactly
the mapped descent morphism in the owner pullback-of-fibres category, followed by the normalized
right transport adapter `θ₂`. This isolates the right boundary shell before the final unit
naturality splice. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_unit_overlap_owner_square_factored
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (let Q :=
        (explicit_two_fibre_product_cover_descent_pullback_bridge
          (J := J) F G T).obj D
      let θ₂ :
          _ ⟶ explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
            (J := J) F G T Q I₂ f₂ :=
        ⟨𝟙 _,
          𝟙 _,
          by
            -- Keep the right boundary in the same normalized owner-side transport form used in
            -- the mapped overlap calculation.
            simpa only [explicit_two_fibre_product_cover_descent_pullback_bridge,
              explicit_two_fibre_product_cover_descent_projection_data_iso,
              explicit_two_fibre_product_cover_descent_projection_component_transport_iso,
              explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback,
              explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_iso_hom,
              explicit_two_fibre_product_cover_descent_left_projection,
              explicit_two_fibre_product_cover_descent_right_projection,
              cover_descent_data_functor_of_stack_morphism, Category.assoc] using
              (((canonicalFiberPseudofunctor S.p).map f₂.op.toLoc).toFunctor.map
                (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
                  (J := J) F G T D I₂).hom)⟩
      (⟨Q.fst.hom q f₁ f₂ hf₁ hf₂,
          Q.snd.hom q f₁ f₂ hf₁ hf₂,
          by
            -- The midpoint is the frozen owner-side transport square for `bridge.obj D`.
            simpa only [Q, Category.assoc] using
              explicit_two_fibre_product_cover_descent_pullback_inverse_unit_overlap_owner_square
                (J := J) F G T D q f₁ f₂ hf₁ hf₂⟩ :
          _ ⟶ explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
            (J := J) F G T Q I₂ f₂) =
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
            (toBasedFunctor F) (toBasedFunctor G) V).functor.map
          (D.hom q f₁ f₂ hf₁ hf₂) ≫ θ₂) := by
  let Q :=
    (explicit_two_fibre_product_cover_descent_pullback_bridge
      (J := J) F G T).obj D
  let θ₂ :
      _ ⟶ explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
        (J := J) F G T Q I₂ f₂ :=
    ⟨𝟙 _,
      𝟙 _,
      by
        -- Keep the right transport adapter in the same owner-side normal form as above.
        simpa only [explicit_two_fibre_product_cover_descent_pullback_bridge,
          explicit_two_fibre_product_cover_descent_projection_data_iso,
          explicit_two_fibre_product_cover_descent_projection_component_transport_iso,
          explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback,
          explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_iso_hom,
          explicit_two_fibre_product_cover_descent_left_projection,
          explicit_two_fibre_product_cover_descent_right_projection,
          cover_descent_data_functor_of_stack_morphism, Category.assoc] using
          (((canonicalFiberPseudofunctor S.p).map f₂.op.toLoc).toFunctor.map
            (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
              (J := J) F G T D I₂).hom)⟩
  -- Compare both owner pullback morphisms projectionwise; after the right adapter `θ₂`, the
  -- mapped descent morphism has exactly the frozen `fst` and `snd` components of `bridge.obj D`.
  apply CategoricalPullback.hom_ext
  · simp [Q, θ₂, explicit_two_fibre_product_cover_descent_pullback_bridge,
      explicit_two_fibre_product_cover_descent_projection_data_iso,
      explicit_two_fibre_product_cover_descent_left_projection,
      explicit_two_fibre_product_cover_descent_right_projection,
      cover_descent_data_functor_of_stack_morphism]
  · simp [Q, θ₂, explicit_two_fibre_product_cover_descent_pullback_bridge,
      explicit_two_fibre_product_cover_descent_projection_data_iso,
      explicit_two_fibre_product_cover_descent_left_projection,
      explicit_two_fibre_product_cover_descent_right_projection,
      cover_descent_data_functor_of_stack_morphism]

/-- Helper for Lemma 8.4.6: after reflecting the unit-overlap equation through the owner fibre
equivalence over `V`, the remaining goal is the mapped owner-side equality before applying
full-faithful reflection back to the source descent datum. This isolates the transport-heavy
owner calculation from the final wrapper theorem. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_unit_overlap_owner_unit_naturality
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (let eV :=
        CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) V
      let eI₁ :=
        CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) I₁.Y
      let eI₂ :=
        CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) I₂.Y
      eV.functor.map
          ((((canonicalFiberPseudofunctor
                  (FibredCategoryOver.twoFibreProduct
                    (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
                f₁.op.toLoc).toFunctor.map
              ((eI₁.unitIso.app (D.obj I₁)).hom))) ≫
        eV.functor.map (D.hom q f₁ f₂ hf₁ hf₂) =
      eV.functor.map (D.hom q f₁ f₂ hf₁ hf₂) ≫
        eV.functor.map
          ((((canonicalFiberPseudofunctor
                  (FibredCategoryOver.twoFibreProduct
                    (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
                f₂.op.toLoc).toFunctor.map
              ((eI₂.unitIso.app (D.obj I₂)).hom)))) := by
  let eV :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) V
  let eI₁ :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) I₁.Y
  let eI₂ :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) I₂.Y
  -- Freeze the owner fibre equivalences over `V`, `I₁.Y`, and `I₂.Y`, then read the core square
  -- as the mapped `unit_naturality` identity for the overlap morphism `D.hom q f₁ f₂ hf₁ hf₂`.
  simpa [eV, eI₁, eI₂, Functor.map_comp, Category.assoc] using
    congrArg
      (fun k ↦
        eV.functor.map k)
      (eV.unit_naturality
        (D.hom q f₁ f₂ hf₁ hf₂))

/-- Helper for Lemma 8.4.6: after reflecting the unit-overlap equation through the owner fibre
equivalence over `V`, the remaining goal is the mapped owner-side equality before applying
full-faithful reflection back to the source descent datum. This isolates the transport-heavy
owner calculation from the final wrapper theorem. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_unit_overlap_owner_unit_naturality_postcompose
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (let eV :=
        CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) V
      let eI₁ :=
        CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) I₁.Y
      let eI₂ :=
        CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) I₂.Y
      let Q :=
        (explicit_two_fibre_product_cover_descent_pullback_bridge
          (J := J) F G T).obj D
      let η₂ :=
        explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
          (J := J) F G T Q I₂ f₂
      let θ₂ :
          _ ⟶ explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
            (J := J) F G T Q I₂ f₂ :=
        ⟨𝟙 _,
          𝟙 _,
          by
            -- Keep the right transport adapter in the same owner-side normal form as in the
            -- mapped overlap calculation.
            simpa only [explicit_two_fibre_product_cover_descent_pullback_bridge,
              explicit_two_fibre_product_cover_descent_projection_data_iso,
              explicit_two_fibre_product_cover_descent_projection_component_transport_iso,
              explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback,
              explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_iso_hom,
              explicit_two_fibre_product_cover_descent_left_projection,
              explicit_two_fibre_product_cover_descent_right_projection,
              cover_descent_data_functor_of_stack_morphism, Category.assoc] using
              (((canonicalFiberPseudofunctor S.p).map f₂.op.toLoc).toFunctor.map
                (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
                  (J := J) F G T D I₂).hom)⟩
      eV.functor.map
          ((((canonicalFiberPseudofunctor
                  (FibredCategoryOver.twoFibreProduct
                    (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
                f₁.op.toLoc).toFunctor.map
              ((eI₁.unitIso.app (D.obj I₁)).hom))) ≫
        eV.functor.map (D.hom q f₁ f₂ hf₁ hf₂) ≫
        θ₂ ≫
        η₂.inv =
      eV.functor.map (D.hom q f₁ f₂ hf₁ hf₂) ≫
        eV.functor.map
          ((((canonicalFiberPseudofunctor
                  (FibredCategoryOver.twoFibreProduct
                    (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
                f₂.op.toLoc).toFunctor.map
              ((eI₂.unitIso.app (D.obj I₂)).hom))) ≫
        θ₂ ≫
        η₂.inv) := by
  let eV :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) V
  let eI₁ :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) I₁.Y
  let eI₂ :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) I₂.Y
  let Q :=
    (explicit_two_fibre_product_cover_descent_pullback_bridge
      (J := J) F G T).obj D
  let η₂ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
      (J := J) F G T Q I₂ f₂
  let θ₂ :
      _ ⟶ explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
        (J := J) F G T Q I₂ f₂ :=
    ⟨𝟙 _,
      𝟙 _,
      by
        -- Keep the right transport adapter in the same owner-side normal form as in the theorem
        -- statement so the postcomposition target is literally stable.
        simpa only [explicit_two_fibre_product_cover_descent_pullback_bridge,
          explicit_two_fibre_product_cover_descent_projection_data_iso,
          explicit_two_fibre_product_cover_descent_projection_component_transport_iso,
          explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback,
          explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_iso_hom,
          explicit_two_fibre_product_cover_descent_left_projection,
          explicit_two_fibre_product_cover_descent_right_projection,
          cover_descent_data_functor_of_stack_morphism, Category.assoc] using
          (((canonicalFiberPseudofunctor S.p).map f₂.op.toLoc).toFunctor.map
            (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
              (J := J) F G T D I₂).hom)⟩
  -- First isolate the bare owner-side `unit_naturality` square, then whisker it by the frozen
  -- right boundary `θ₂ ≫ η₂.inv` so the theorem matches the surrounding overlap-shell calculus.
  -- Reassociate only once after whiskering so the postcomposed shell stays in the literal
  -- parenthesized form expected by the mapped overlap calculation.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ k ≫ θ₂ ≫ η₂.inv)
      (explicit_two_fibre_product_cover_descent_pullback_inverse_unit_overlap_owner_unit_naturality
        (J := J) F G T D q f₁ f₂ hf₁ hf₂)

/-- Helper for Lemma 8.4.6: after reflecting the unit-overlap equation through the owner fibre
equivalence over `V`, the remaining goal is the mapped owner-side equality before applying
full-faithful reflection back to the source descent datum. This isolates the transport-heavy
owner calculation from the final wrapper theorem. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_unit_overlap_mapped
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) V).functor.map
        ((((canonicalFiberPseudofunctor
              (FibredCategoryOver.twoFibreProduct
                (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f₁.op.toLoc).toFunctor.map
            (explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_iso
              (J := J) F G T D I₁).hom) ≫
          (explicit_two_fibre_product_cover_descent_pullback_inverse_obj
              (J := J) F G T
              ((explicit_two_fibre_product_cover_descent_pullback_bridge
                (J := J) F G T).obj D)).hom
            q f₁ f₂ hf₁ hf₂)) =
      (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) V).functor.map
        (D.hom q f₁ f₂ hf₁ hf₂ ≫
          (((canonicalFiberPseudofunctor
                (FibredCategoryOver.twoFibreProduct
                  (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f₂.op.toLoc).toFunctor.map
              (explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_iso
                (J := J) F G T D I₂).hom)) := by
  -- Route correction: the remaining source-faithful work is now entirely on the owner side over
  -- `V`; after this mapped equality is proved, the original source overlap follows immediately by
  -- full-faithful reflection through the fibre equivalence.
  let eV :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) V
  -- First expand the two mapped unit boundaries into the Chapter 4 unit part and the transport
  -- part. The remaining blocker is to identify these expanded boundaries with the owner-shell
  -- conjugation around `explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map`.
  let Q :=
    (explicit_two_fibre_product_cover_descent_pullback_bridge
      (J := J) F G T).obj D
  let η₁ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
      (J := J) F G T Q I₁ f₁
  let η₂ :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor_image_iso
      (J := J) F G T Q I₂ f₂
  let θ₁ :
      _ ⟶ explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
        (J := J) F G T Q I₁ f₁ :=
    ⟨𝟙 _,
      𝟙 _,
      by
        -- Freeze the left owner-side transport shell before composing it with the reflected
        -- overlap morphism.
        simpa only [explicit_two_fibre_product_cover_descent_pullback_bridge,
          explicit_two_fibre_product_cover_descent_projection_data_iso,
          explicit_two_fibre_product_cover_descent_projection_component_transport_iso,
          explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback,
          explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_iso_hom,
          explicit_two_fibre_product_cover_descent_left_projection,
          explicit_two_fibre_product_cover_descent_right_projection,
          cover_descent_data_functor_of_stack_morphism, Category.assoc] using
          (((canonicalFiberPseudofunctor S.p).map f₁.op.toLoc).toFunctor.map
            (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
              (J := J) F G T D I₁).hom)⟩
  let θ₂ :
      _ ⟶ explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
        (J := J) F G T Q I₂ f₂ :=
    ⟨𝟙 _,
      𝟙 _,
      by
        -- Freeze the symmetric right owner-side transport shell as well.
        simpa only [explicit_two_fibre_product_cover_descent_pullback_bridge,
          explicit_two_fibre_product_cover_descent_projection_data_iso,
          explicit_two_fibre_product_cover_descent_projection_component_transport_iso,
          explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback,
          explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback_iso_hom,
          explicit_two_fibre_product_cover_descent_left_projection,
          explicit_two_fibre_product_cover_descent_right_projection,
          cover_descent_data_functor_of_stack_morphism, Category.assoc] using
          (((canonicalFiberPseudofunctor S.p).map f₂.op.toLoc).toFunctor.map
            (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
              (J := J) F G T D I₂).hom)⟩
  rw [eV.functor.map_comp, eV.functor.map_comp]
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_boundary_expanded
    (J := J) F G T D I₁ f₁]
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_boundary_expanded
    (J := J) F G T D I₂ f₂]
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_boundary_to_image_iso_shell
    (J := J) F G T D I₁ f₁]
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_boundary_to_image_iso_shell
    (J := J) F G T D I₂ f₂]
  -- Rewrite the middle overlap shell to the owner-side conjugation form and cancel the adjacent
  -- image-isomorphism boundaries so the remaining square is the Chapter 4 unit naturality plus
  -- the frozen owner transport commutator.
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_overlap_hom_map
    (J := J) F G T Q q f₁ f₂ hf₁ hf₂]
  simp only [Q, η₁, η₂, θ₁, θ₂, Category.assoc]
  -- Rewrite the left boundary to the frozen owner shell, factor the middle owner square through
  -- `eV.functor.map (D.hom ...)`, and then finish with the dedicated owner-side postcompose
  -- naturality theorem.
  calc
    eV.functor.map
        ((((canonicalFiberPseudofunctor
                (FibredCategoryOver.twoFibreProduct
                  (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
              f₁.op.toLoc).toFunctor.map
            ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
                (toBasedFunctor F) (toBasedFunctor G) I₁.Y).unitIso.app
              (D.obj I₁)).hom)) ≫
      θ₁ ≫
        explicit_two_fibre_product_cover_descent_pullback_inverse_owner_shell
          (J := J) F G T Q q f₁ f₂ hf₁ hf₂ ≫
        η₂.inv =
      eV.functor.map
          ((((canonicalFiberPseudofunctor
                  (FibredCategoryOver.twoFibreProduct
                    (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
                f₁.op.toLoc).toFunctor.map
              ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
                  (toBasedFunctor F) (toBasedFunctor G) I₁.Y).unitIso.app
                (D.obj I₁)).hom)) ≫
        (⟨Q.fst.hom q f₁ f₂ hf₁ hf₂,
            Q.snd.hom q f₁ f₂ hf₁ hf₂,
            by
              -- The midpoint is the frozen owner-side transport square for `bridge.obj D`.
              simpa only [Q, Category.assoc] using
                explicit_two_fibre_product_cover_descent_pullback_inverse_unit_overlap_owner_square
                  (J := J) F G T D q f₁ f₂ hf₁ hf₂⟩ :
          _ ⟶ explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback
            (J := J) F G T Q I₂ f₂) ≫
          η₂.inv := by
            rw [explicit_two_fibre_product_cover_descent_pullback_inverse_unit_overlap_left_boundary_shell
              (J := J) F G T D q f₁ f₂ hf₁ hf₂]
    _ =
      eV.functor.map
          ((((canonicalFiberPseudofunctor
                  (FibredCategoryOver.twoFibreProduct
                    (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
                f₁.op.toLoc).toFunctor.map
              ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
                  (toBasedFunctor F) (toBasedFunctor G) I₁.Y).unitIso.app
                (D.obj I₁)).hom)) ≫
        (eV.functor.map (D.hom q f₁ f₂ hf₁ hf₂) ≫ θ₂) ≫
          η₂.inv := by
            rw [explicit_two_fibre_product_cover_descent_pullback_inverse_unit_overlap_owner_square_factored
              (J := J) F G T D q f₁ f₂ hf₁ hf₂]
    _ =
      eV.functor.map (D.hom q f₁ f₂ hf₁ hf₂) ≫
        eV.functor.map
          ((((canonicalFiberPseudofunctor
                  (FibredCategoryOver.twoFibreProduct
                    (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
                f₂.op.toLoc).toFunctor.map
              ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
                  (toBasedFunctor F) (toBasedFunctor G) I₂.Y).unitIso.app
                (D.obj I₂)).hom)) ≫
          θ₂ ≫
          η₂.inv := by
            simpa [Category.assoc] using
              explicit_two_fibre_product_cover_descent_pullback_inverse_unit_overlap_owner_unit_naturality_postcompose
                (J := J) F G T D q f₁ f₂ hf₁ hf₂

/-- Helper for Lemma 8.4.6: after reflecting the unit-overlap equation through the owner fibre
equivalence over `V`, the source-side unit compatibility becomes the owner-side square combining
unit naturality with the already frozen transport and overlap shells. -/
private theorem
    explicit_two_fibre_product_cover_descent_pullback_inverse_unit_overlap_under_fibre_equivalence
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f₁.op.toLoc).toFunctor.map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_iso
          (J := J) F G T D I₁).hom) ≫
      (explicit_two_fibre_product_cover_descent_pullback_inverse_obj
          (J := J) F G T
          ((explicit_two_fibre_product_cover_descent_pullback_bridge
            (J := J) F G T).obj D)).hom
        q f₁ f₂ hf₁ hf₂ =
      D.hom q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor
              (FibredCategoryOver.twoFibreProduct
                (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f₂.op.toLoc).toFunctor.map
            (explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_iso
              (J := J) F G T D I₂).hom) := by
  -- Route correction: the source proof packages the unit only after reflecting the overlap
  -- equation through the owner-side fibre equivalence, so the remaining work is exactly one
  -- owner-side rewrite with `unit_naturality`, the transport commutator, and the frozen overlap.
  let eV :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) V
  let hffV : eV.functor.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful eV.functor
  -- Reflect the source overlap through the fully faithful owner equivalence; the mapped theorem
  -- above isolates the only remaining transport-heavy owner-side equality.
  apply hffV.map_injective
  simpa [eV] using
    explicit_two_fibre_product_cover_descent_pullback_inverse_unit_overlap_mapped
      (J := J) F G T D q f₁ f₂ hf₁ hf₂

/-- Helper for Lemma 8.4.6: packaging the legwise source-side unit components gives the unit
isomorphism from an explicit fixed-cover descent datum to the roundtrip through the bridge and its
source-faithful inverse. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_inverse_unit
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f))) :
    D ≅
      explicit_two_fibre_product_cover_descent_pullback_inverse_obj
        (J := J) F G T
        ((explicit_two_fibre_product_cover_descent_pullback_bridge
          (J := J) F G T).obj D) := by
  -- Once the correct legwise unit component is frozen, the source-side roundtrip iso is a direct
  -- `isoMk` packaging step.
  refine Pseudofunctor.DescentData.isoMk
    (fun I ↦
      explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_iso
        (J := J) F G T D I)
    ?_
  intro V q I₁ I₂ f₁ f₂ hf₁ hf₂
  simpa using
    explicit_two_fibre_product_cover_descent_pullback_inverse_unit_overlap_under_fibre_equivalence
      (J := J) F G T D q f₁ f₂ hf₁ hf₂

/-- Helper for Lemma 8.4.6: the objectwise target-side counits already satisfy the naturality
square needed for the `G' ⋙ bridge ≅ 𝟭` branch of the quasi-inverse packaging. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_counit_naturality
    (F : X ⟶ S) (G : Y ⟶ S)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {U : C} (T : J.Cover U) :
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor
        (J := J) F G T ⋙
      explicit_two_fibre_product_cover_descent_pullback_bridge
        (J := J) F G T ≅
      𝟭 _ := by
  refine NatIso.ofComponents
    (fun Q ↦
      explicit_two_fibre_product_cover_descent_pullback_inverse_counit
        (J := J) F G T Q)
    ?_
  intro Q₁ Q₂ φ
  -- Check naturality projectionwise in the categorical pullback, then legwise on the common cover.
  apply CategoricalPullback.hom_ext
  · apply Pseudofunctor.DescentData.hom_ext
    intro I
    rw [Pseudofunctor.DescentData.comp_hom, Pseudofunctor.DescentData.comp_hom]
    -- The left projected square is exactly the first projection of the legwise counit naturality.
    change
      (FibredCategoryMor.fiberFunctor
          (FibredCategoryOver.twoFibreProductLeftProjection
            (toFibredCategoryMor F) (toFibredCategoryMor G))
          I.Y).map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
          (J := J) F G T φ I) ≫
      ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
            (J := J) F G T Q₂ I)).hom =
        ((π₁ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q₁ I)).hom ≫
          φ.fst.hom I
    simpa [explicit_two_fibre_product_cover_descent_pullback_inverse_component_map_fst] using
      congrArg (fun k ↦ k.fst)
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom_counit_naturality
          (J := J) F G T φ I)
  · apply Pseudofunctor.DescentData.hom_ext
    intro I
    rw [Pseudofunctor.DescentData.comp_hom, Pseudofunctor.DescentData.comp_hom]
    -- The right projected square is the symmetric second projection of the same legwise theorem.
    change
      (FibredCategoryMor.fiberFunctor
          (FibredCategoryOver.twoFibreProductRightProjection
            (toFibredCategoryMor F) (toFibredCategoryMor G))
          I.Y).map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
          (J := J) F G T φ I) ≫
      ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
          (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
            (J := J) F G T Q₂ I)).hom =
        ((π₂ (fiberFunctor F I.Y) (fiberFunctor G I.Y)).mapIso
            (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
              (J := J) F G T Q₁ I)).hom ≫
          φ.snd.hom I
    simpa [explicit_two_fibre_product_cover_descent_pullback_inverse_component_map_snd] using
      congrArg (fun k ↦ k.snd)
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom_counit_naturality
          (J := J) F G T φ I)

/-- Helper for Lemma 8.4.6: the frozen source-side unit component on a cover leg is natural in
ordinary morphisms once the Chapter 4 unit square is followed by the transport-adapter square. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_naturality
    (F : X ⟶ S) (G : Y ⟶ S)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {U : C} (T : J.Cover U)
    {D₁ D₂ : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
          (fun I : T.Arrow ↦ I.f))}
    (φ : D₁ ⟶ D₂) (I : T.Arrow) :
    φ.hom I ≫
      (explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_iso
        (J := J) F G T D₂ I).hom =
        (explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_iso
          (J := J) F G T D₁ I).hom ≫
          ((((explicit_two_fibre_product_cover_descent_pullback_bridge
              (J := J) F G T) ⋙
              explicit_two_fibre_product_cover_descent_pullback_inverse_functor
                (J := J) F G T).map φ).hom I) := by
  let eI :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) I.Y
  -- Route correction: this is the ordinary-morphism unit square on a single cover leg, so use
  -- the Chapter 4 unit naturality first and only then insert the owner-side transport adapter.
  change
    φ.hom I ≫
        ((eI.unitIso.app (D₂.obj I)).hom ≫
          eI.inverse.map
            ((explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso
              (J := J) F G T D₂ I).hom)) =
      ((eI.unitIso.app (D₁.obj I)).hom ≫
          eI.inverse.map
            ((explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso
              (J := J) F G T D₁ I).hom)) ≫
        (((explicit_two_fibre_product_cover_descent_pullback_bridge
              (J := J) F G T) ⋙
              explicit_two_fibre_product_cover_descent_pullback_inverse_functor
                (J := J) F G T).map φ).hom I
  calc
    φ.hom I ≫
        ((eI.unitIso.app (D₂.obj I)).hom ≫
          eI.inverse.map
            ((explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso
              (J := J) F G T D₂ I).hom)) =
      (φ.hom I ≫ (eI.unitIso.app (D₂.obj I)).hom) ≫
        eI.inverse.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso
            (J := J) F G T D₂ I).hom) := by
            simp [Category.assoc]
    _ =
      ((eI.unitIso.app (D₁.obj I)).hom ≫
          eI.inverse.map (eI.functor.map (φ.hom I))) ≫
        eI.inverse.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso
            (J := J) F G T D₂ I).hom) := by
            rw [eI.unit_naturality]
    _ =
      (eI.unitIso.app (D₁.obj I)).hom ≫
        eI.inverse.map
          (eI.functor.map (φ.hom I) ≫
            (explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso
              (J := J) F G T D₂ I).hom) := by
            simp [Functor.map_comp, Category.assoc]
    _ =
      (eI.unitIso.app (D₁.obj I)).hom ≫
        eI.inverse.map
          ((explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso
              (J := J) F G T D₁ I).hom ≫
            explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
              (J := J) F G T
              ((explicit_two_fibre_product_cover_descent_pullback_bridge
                (J := J) F G T).map φ) I) := by
            exact congrArg eI.inverse.map
              (explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_naturality
                (J := J) F G T φ I)
    _ =
      ((eI.unitIso.app (D₁.obj I)).hom ≫
          eI.inverse.map
            ((explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso
              (J := J) F G T D₁ I).hom)) ≫
        eI.inverse.map
          (explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
            (J := J) F G T
            ((explicit_two_fibre_product_cover_descent_pullback_bridge
              (J := J) F G T).map φ) I) := by
            simp [Functor.map_comp, Category.assoc]
    _ =
      ((eI.unitIso.app (D₁.obj I)).hom ≫
          eI.inverse.map
            ((explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso
              (J := J) F G T D₁ I).hom)) ≫
        (((explicit_two_fibre_product_cover_descent_pullback_bridge
              (J := J) F G T) ⋙
              explicit_two_fibre_product_cover_descent_pullback_inverse_functor
                (J := J) F G T).map φ).hom I := by
            rfl
    _ =
      ((eI.unitIso.app (D₁.obj I)).hom ≫
          eI.inverse.map
            ((explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_transport_iso
              (J := J) F G T D₁ I).hom) ≫
        (((explicit_two_fibre_product_cover_descent_pullback_bridge
              (J := J) F G T) ⋙
              explicit_two_fibre_product_cover_descent_pullback_inverse_functor
                (J := J) F G T).map φ).hom I) := by
            simp [Category.assoc]

/-- Helper for Lemma 8.4.6: the frozen objectwise source-side unit isomorphisms assemble to a
natural isomorphism once their legwise ordinary-morphism naturality is checked componentwise. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_unit_naturality
    (F : X ⟶ S) (G : Y ⟶ S)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {U : C} (T : J.Cover U) :
    𝟭 _ ≅
      explicit_two_fibre_product_cover_descent_pullback_bridge
        (J := J) F G T ⋙
      explicit_two_fibre_product_cover_descent_pullback_inverse_functor
        (J := J) F G T := by
  refine NatIso.ofComponents
    (fun D ↦
      explicit_two_fibre_product_cover_descent_pullback_inverse_unit
        (J := J) F G T D)
    ?_
  intro D₁ D₂ φ
  -- Check naturality on each cover leg; the ordinary-morphism unit square is already frozen
  -- componentwise by the theorem just above.
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  simpa [Pseudofunctor.DescentData.comp_hom, Category.assoc] using
    explicit_two_fibre_product_cover_descent_pullback_inverse_unit_component_naturality
      (J := J) F G T φ I

/-- Helper for Lemma 8.4.6: the remaining fixed-cover source comparison is the equivalence from
descent data on the explicit stack-level `2`-fibre product to the categorical pullback of the two
projected descent-data categories. Isolating this statement keeps the source-faithful direct
inverse as a single local frontier. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_bridge_isEquivalence
    (F : X ⟶ S) (G : Y ⟶ S)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {U : C} (T : J.Cover U) :
    (explicit_two_fibre_product_cover_descent_pullback_bridge
      (J := J) F G T).IsEquivalence := by
  let G' :=
    explicit_two_fibre_product_cover_descent_pullback_inverse_functor
      (J := J) F G T
  -- Route correction: the inverse functor, the target-side objectwise counit, and the genuine
  -- source-side unit components are now explicit. The remaining work is only the naturality of
  -- those packaged roundtrip isomorphisms.
  refine Functor.IsEquivalence.mk' G' ?_ ?_
  · exact
      explicit_two_fibre_product_cover_descent_pullback_inverse_unit_naturality
        (J := J) F G T
  · -- TODO: promote the target-side objectwise counit to a natural isomorphism by checking both
    -- categorical-pullback projections componentwise.
    exact
      explicit_two_fibre_product_cover_descent_pullback_inverse_counit_naturality
        (J := J) F G T

/-- Helper for Lemma 8.4.6: for a fixed cover, the remaining source-faithful frontier is to show
that descent data on the explicit stack-level `2`-fibre product are equivalent to the categorical
pullback of the two projected fixed-cover descent-data categories. Keeping only this theorem
stable isolates the blocker without changing the final stack-reduction route. -/
private theorem explicit_two_fibre_product_cover_descent_isEquivalence
    (F : X ⟶ S) (G : Y ⟶ S)
    [(FibredCategoryOver.twoFibreProduct (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {U : C} (T : J.Cover U) :
    ((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct (toFibredCategoryMor F) (toFibredCategoryMor G)).p).toDescentData
          (fun I : T.Arrow ↦ I.f)).IsEquivalence := by
  let eFib := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
    (toBasedFunctor F) (toBasedFunctor G) U
  let TF :=
    two_fibre_product_map
      (cover_descent_data_functor_of_stack_morphism_toDescentData_iso
        (J := J) (toFibredCategoryMor G) T)
      ((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
        (J := J) (toFibredCategoryMor F) T).symm)
  let hOwnerBridge :
      (explicit_two_fibre_product_cover_descent_owner_model_functor
        (J := J) (S := S) F G T).IsEquivalence := by
    -- The strict Chapter 4 explicit pullback model over the common `S`-descent-data base is
    -- already equivalent to the categorical pullback by the owner universal property.
    exact
      explicit_two_fibre_product_cover_descent_owner_model_isEquivalence
        (J := J) (S := S) F G T
  have hPullbackModel : (eFib.functor ⋙ TF).IsEquivalence :=
    cover_descent_pullback_model_isEquivalence_bridge_explicit
      (J := J) F G (T := T)
  -- Route correction: the whiskered comparison is now closed, so only the source-faithful
  -- direct inverse remains. The legwise reconstruction is now frozen through
  -- `explicit_two_fibre_product_cover_descent_pullback_inverse_leg`, and the target of that
  -- comparison is now frozen as
  -- `explicit_two_fibre_product_cover_descent_pullback_inverse_component_pullback`; the only open
  -- issue is the transport-stable comparison between canonical pullbacks of those reconstructed
  -- fibre objects and this named componentwise pullback object coming from `Q.fst`, `Q.snd`, and
  -- `Q.iso`.
  refine explicit_two_fibre_product_cover_descent_isEquivalence_close
    (J := J) F G (T := T)
    (explicit_two_fibre_product_cover_descent_pullback_bridge_isEquivalence
      (J := J) F G T)
    hPullbackModel
-/

/-- Helper for Lemma 8.4.6: the remaining fixed-cover source comparison is the equivalence from
descent data on the explicit stack-level `2`-fibre product to the categorical pullback of the two
projected descent-data categories. The current blocker is the transport-heavy inverse-functor
comparison in the owner pullback-of-fibres category. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_bridge_isEquivalence
    (F : X ⟶ S) (G : Y ⟶ S)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {U : C} (T : J.Cover U) :
    (explicit_two_fibre_product_cover_descent_pullback_bridge
      (J := J) F G T).IsEquivalence :=
  -- TODO: re-plan should close the source-side unit/counit naturality after introducing a
  -- transport-stable comparison between canonical pullbacks of the reconstructed leg and the
  -- named componentwise owner pullback object.
  sorry

/-- Helper for Lemma 8.4.6: for a fixed cover, the remaining source-faithful frontier is to show
that descent data on the explicit stack-level `2`-fibre product are equivalent to the categorical
pullback of the two projected fixed-cover descent-data categories. This now depends only on the
blocked explicit bridge and the already frozen owner-model comparison. -/
private theorem explicit_two_fibre_product_cover_descent_isEquivalence
    (F : X ⟶ S) (G : Y ⟶ S)
    [(FibredCategoryOver.twoFibreProduct (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {U : C} (T : J.Cover U) :
    ((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct (toFibredCategoryMor F) (toFibredCategoryMor G)).p).toDescentData
          (fun I : T.Arrow ↦ I.f)).IsEquivalence :=
  -- TODO: re-plan should combine the blocked explicit bridge equivalence with the owner-model
  -- whiskered comparison by the existing `explicit_two_fibre_product_cover_descent_isEquivalence_close`.
  sorry

/-- Lemma 8.4.6: the `(2,1)`-category of stacks over the site `(C, J)` has `2`-fibre products,
and the explicit pullback owner from Categories, Lemma `4.32.3`, is again a stack over `(C, J)`.
-/
theorem stackTwoFibreProduct_isStack
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsStackOnSite J
      (FibredCategoryOver.twoFibreProduct (toFibredCategoryMor F) (toFibredCategoryMor G)).p := by
  -- Route correction: first reduce the stack condition to fixed covers via Lemma `8.4.2`; the
  -- entire remaining source-faithful content is the fixed-cover equivalence isolated above.
  let P := FibredCategoryOver.twoFibreProduct (toFibredCategoryMor F) (toFibredCategoryMor G)
  letI : P.p.IsFibered := stack_two_fibre_product_projection_isFibered F G
  exact
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J P.p).2
      (fun U T ↦ by
        exact explicit_two_fibre_product_cover_descent_isEquivalence (J := J) F G (T := T))

/-- Helper for Lemma 8.4.6: the explicit `2`-fibre product of morphisms of stacks over `(C, J)`
carries the induced stack structure by the owner theorem `stackTwoFibreProduct_isStack`. -/
instance instIsStackOnSiteObjToCategoryOverTwoFibreProductP
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsStackOnSite J
      (FibredCategoryOver.twoFibreProduct (toFibredCategoryMor F) (toFibredCategoryMor G)).p :=
  stackTwoFibreProduct_isStack F G

end CategoryTheory
