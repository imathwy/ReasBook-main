import Mathlib
import StacksProject_2024.Chap04.Definition_4_33_9
import StacksProject_2024.Chap04.Definition_4_32_1
import StacksProject_2024.Chap04.CanonicalFiberPseudofunctor

/-!
# Pullback-comparison naturality owner for Lemma 8.2.3

This support owner isolates the generic pullback-comparison construction and its fiberwise
naturality squares from the longer Hom-presheaf comparison proof in `Chap08.Lemma_8_2_3`.
Downstream files such as `Lemma_8_4_3` only need this geometric comparison block.
-/

open Opposite

universe u v uS vS

namespace CategoryTheory

open BasedFunctor

variable {C : Type u} [Category.{v} C]

attribute [local instance] FibredCategoryOver.isFibred

variable {X Y : FibredCategoryOver C}

/-- Helper for Lemma 8.2.3: a functor maps a threefold composite to the corresponding threefold
composite of mapped arrows. -/
theorem functor_map_threefold_comp
    {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    {W X Y Z : D} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    F.map (f ≫ g ≫ h) = F.map f ≫ F.map g ≫ F.map h := by
  -- Split the visible threefold composite into two binary functoriality steps.
  rw [Functor.map_comp, Functor.map_comp]

namespace FibredCategoryMor

/-- Helper for Lemma 8.2.3: mapping a strongly cartesian lift over `f` along a morphism of
fibred categories again yields a strongly cartesian lift over the same base arrow. -/
theorem map_stronglyCartesian_of_lift
    (F : X ⟶ Y) {a b : X.S} {U V : C} (f : V ⟶ U) (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian f φ) :
    Y.p.IsStronglyCartesian f (F.toHom.map φ) := by
  letI : X.p.IsHomLift f φ := hφ.toIsHomLift
  have hφ' : X.p.IsStronglyCartesian (X.p.map φ) φ := by
    -- Normalize the source lift to the projected base morphism before applying the owner API.
    subst_hom_lift X.p f φ
    simpa using hφ
  letI : Y.p.IsHomLift f (F.toHom.map φ) := by
    infer_instance
  have hY :
      Y.p.IsStronglyCartesian (Y.p.map (F.toHom.map φ)) (F.toHom.map φ) :=
    FibredCategoryMor.map_stronglyCartesian F φ hφ'
  -- Transport the target statement back to the original base arrow `f`.
  subst_hom_lift Y.p f (F.toHom.map φ)
  exact hY

/-- Helper for Lemma 8.2.3: a morphism of fibred categories admits the canonical comparison
isomorphism between pulling back after mapping and mapping after pulling back, together with the
postcomposition identity against the chosen target pullback arrow. -/
private theorem pullbackComparison_exists
    (F : X ⟶ Y) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    ∃ e :
      f ^*[canonicalPullbackChoice Y.p] ((F.toHom).fiberFunctor U).obj x ≅
        ((F.toHom).fiberFunctor V).obj (f ^*[canonicalPullbackChoice X.p] x),
      e.hom.1 ≫ F.toHom.map ((canonicalPullbackChoice X.p).map f x) =
        (canonicalPullbackChoice Y.p).map f (((F.toHom).fiberFunctor U).obj x) := by
  let hcX := canonicalPullbackChoice X.p
  let hcY := canonicalPullbackChoice Y.p
  let φ :
      (((F.toHom).fiberFunctor V).obj (f ^*[hcX] x)).1 ⟶
        (((F.toHom).fiberFunctor U).obj x).1 :=
    F.toHom.map (hcX.map f x)
  let ψ :
      (f ^*[hcY] (((F.toHom).fiberFunctor U).obj x)).1 ⟶
        (((F.toHom).fiberFunctor U).obj x).1 :=
    hcY.map f (((F.toHom).fiberFunctor U).obj x)
  have hφ : Y.p.IsStronglyCartesian f φ :=
    map_stronglyCartesian_of_lift F f (hcX.map f x) (hcX.isStronglyCartesian f x)
  have hψ : Y.p.IsStronglyCartesian f ψ :=
    hcY.isStronglyCartesian f (((F.toHom).fiberFunctor U).obj x)
  have hf : f = (Iso.refl V).hom ≫ f := by
    simp
  let e :
      (f ^*[hcY] (((F.toHom).fiberFunctor U).obj x)).1 ≅
        (((F.toHom).fiberFunctor V).obj (f ^*[hcX] x)).1 :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso Y.p hf φ ψ
  letI : Y.p.IsHomLift (𝟙 V) e.hom := by
    -- The hom component of the comparison iso lies over the identity of the pullback base.
    change Y.p.IsHomLift (Iso.refl V).hom e.hom
    exact Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift Y.p hf φ ψ
  letI : Y.p.IsHomLift (𝟙 V) e.inv := by
    -- The inverse component is vertical for the same reason.
    change Y.p.IsHomLift (Iso.refl V).inv e.inv
    exact Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift Y.p hf φ ψ
  let ehom :
      f ^*[hcY] ((F.toHom).fiberFunctor U).obj x ⟶
        ((F.toHom).fiberFunctor V).obj (f ^*[hcX] x) :=
    Functor.Fiber.homMk Y.p V e.hom
  let einv :
      ((F.toHom).fiberFunctor V).obj (f ^*[hcX] x) ⟶
        f ^*[hcY] ((F.toHom).fiberFunctor U).obj x :=
    Functor.Fiber.homMk Y.p V e.inv
  have hhom_inv : ehom ≫ einv = 𝟙 _ := by
    apply Functor.Fiber.hom_ext
    change e.hom ≫ e.inv = 𝟙 _
    exact e.hom_inv_id
  have hinv_hom : einv ≫ ehom = 𝟙 _ := by
    apply Functor.Fiber.hom_ext
    change e.inv ≫ e.hom = 𝟙 _
    exact e.inv_hom_id
  let eFiber :
      f ^*[hcY] ((F.toHom).fiberFunctor U).obj x ≅
        ((F.toHom).fiberFunctor V).obj (f ^*[hcX] x) :=
    { hom := ehom
      inv := einv
      hom_inv_id := hhom_inv
      inv_hom_id := hinv_hom }
  refine ⟨eFiber, ?_⟩
  change (Functor.IsStronglyCartesian.domainIsoOfBaseIso Y.p hf φ ψ).hom ≫ φ = ψ
  rw [Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
  exact Functor.IsStronglyCartesian.fac Y.p f φ hf ψ

/-- Helper for Lemma 8.2.3: the canonical comparison isomorphism in the fiber over the domain of
`f`, identifying the chosen pullback of `F(x)` with the image under `F` of the chosen pullback of
`x`. This is the core geometric object used by the source proof. -/
noncomputable def pullbackComparison
    (F : X ⟶ Y) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    f ^*[canonicalPullbackChoice Y.p] ((F.toHom).fiberFunctor U).obj x ≅
      ((F.toHom).fiberFunctor V).obj (f ^*[canonicalPullbackChoice X.p] x) :=
  Classical.choose (pullbackComparison_exists F f x)

/-- Helper for Lemma 8.2.3: the canonical pullback functor on fibers is characterized by the
factorization identity through the chosen strongly cartesian pullback arrow. -/
theorem canonical_pullbackFunctor_map_fac
    {S : Type*} [Category S] (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map φ)).1 ≫
        (canonicalPullbackChoice p).map f y =
      (canonicalPullbackChoice p).map f x ≫ φ.1 := by
  letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
  have hpull : p.IsStronglyCartesian f ((canonicalPullbackChoice p).map f x) :=
    (canonicalPullbackChoice p).isStronglyCartesian f x
  letI : p.IsHomLift f ((canonicalPullbackChoice p).map f x) := hpull.toIsHomLift
  letI : p.IsHomLift f ((canonicalPullbackChoice p).map f x ≫ φ.1) :=
    IsHomLift.comp_lift_id_right' p f ((canonicalPullbackChoice p).map f x) U φ.1
  letI : p.IsStronglyCartesian f ((canonicalPullbackChoice p).map f y) :=
    (canonicalPullbackChoice p).isStronglyCartesian f y
  -- Compare the chosen pullback arrow of `y` with the universal factorization induced by `φ`.
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

/-- Helper for Lemma 8.2.3: the hom part of the pullback-comparison isomorphism becomes the
chosen target pullback arrow after postcomposition with the image of the chosen source pullback
arrow. -/
theorem pullbackComparison_hom_postcompose
    (F : X ⟶ Y) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (pullbackComparison F f x).hom.1 ≫
        F.toHom.map ((canonicalPullbackChoice X.p).map f x) =
      (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj x) := by
  let hcX := canonicalPullbackChoice X.p
  let hcY := canonicalPullbackChoice Y.p
  let φ :
      (((F.toHom.fiberFunctor V).obj (f ^*[hcX] x)).1 ⟶
        ((F.toHom.fiberFunctor U).obj x).1) :=
    F.toHom.map (hcX.map f x)
  let ψ :
      (f ^*[hcY] ((F.toHom.fiberFunctor U).obj x)).1 ⟶
        ((F.toHom.fiberFunctor U).obj x).1 :=
    hcY.map f ((F.toHom.fiberFunctor U).obj x)
  have hφ : Y.p.IsStronglyCartesian f φ := by
    change Y.p.IsStronglyCartesian f (F.toHom.map (hcX.map f x))
    exact map_stronglyCartesian_of_lift F f (hcX.map f x) (hcX.isStronglyCartesian f x)
  have hψ : Y.p.IsStronglyCartesian f ψ := by
    change
      Y.p.IsStronglyCartesian f
        ((canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj x))
    exact hcY.isStronglyCartesian f ((F.toHom.fiberFunctor U).obj x)
  have hf : f = (Iso.refl V).hom ≫ f := by
    simp
  change (Classical.choose (pullbackComparison_exists F f x)).hom.1 ≫
      F.toHom.map ((canonicalPullbackChoice X.p).map f x) =
    (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj x)
  exact Classical.choose_spec (pullbackComparison_exists F f x)

/-- Helper for Lemma 8.2.3: postcomposing the inverse comparison morphism with the chosen target
pullback arrow recovers the image of the chosen source pullback arrow. -/
theorem pullbackComparison_inv_postcompose_owner
    (F : X ⟶ Y) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (pullbackComparison F f x).inv.1 ≫
        (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj x) =
      F.toHom.map ((canonicalPullbackChoice X.p).map f x) := by
  have hid :
      (pullbackComparison F f x).inv.1 ≫ (pullbackComparison F f x).hom.1 =
        𝟙 (((F.toHom.fiberFunctor V).obj (f ^*[canonicalPullbackChoice X.p] x)).1) := by
    exact congrArg (fun k ↦ k.1) (pullbackComparison F f x).inv_hom_id
  have hid_postcompose :
      ((pullbackComparison F f x).inv.1 ≫ (pullbackComparison F f x).hom.1) ≫
        F.toHom.map ((canonicalPullbackChoice X.p).map f x) =
      F.toHom.map ((canonicalPullbackChoice X.p).map f x) := by
    rw [hid]
    rw [Category.id_comp]
    rfl
  have hcompose :
      (pullbackComparison F f x).inv.1 ≫
          (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj x) =
        ((pullbackComparison F f x).inv.1 ≫ (pullbackComparison F f x).hom.1) ≫
          F.toHom.map ((canonicalPullbackChoice X.p).map f x) := by
    calc
      (pullbackComparison F f x).inv.1 ≫
          (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj x) =
        (pullbackComparison F f x).inv.1 ≫
          ((pullbackComparison F f x).hom.1 ≫
            F.toHom.map ((canonicalPullbackChoice X.p).map f x)) := by
          rw [(pullbackComparison_hom_postcompose F f x).symm]
          rfl
      _ =
        ((pullbackComparison F f x).inv.1 ≫ (pullbackComparison F f x).hom.1) ≫
          F.toHom.map ((canonicalPullbackChoice X.p).map f x) := by
          exact (Category.assoc _ _ _).symm
  exact Eq.trans hcompose hid_postcompose

/-- Helper for Lemma 8.2.3: composing in `C` and then passing to the locally discrete opposite is
the same as composing the corresponding `toLoc` arrows in the owner order used by `pullHom`. -/
theorem comp_toLoc_eq
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf) :
    f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc := by
  -- Translate the composite equality to `LocallyDiscrete Cᵒᵖ`.
  simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
    congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hgf)

/-- Helper for Lemma 8.2.3: the hom component of the flexible pullback-composition comparison for
the canonical fiber pseudofunctor satisfies the same factorization identity as the strict chosen
pullback-composition comparison. -/
theorem canonicalFiberPseudofunctor_mapComp'_hom_app_fac
    {S : Type*} [Category S] (p : S ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf)
    (x : p.Fiber D) :
    (((canonicalFiberPseudofunctor p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x).1 ≫
        (canonicalPullbackChoice p).map g
          (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj x) ≫
        (canonicalPullbackChoice p).map f x =
      (canonicalPullbackChoice p).map gf x := by
  -- Route correction: expose the generic `mapComp'` shell first, then reuse the chosen
  -- pullback-composition factorization instead of fighting the hidden equality transport.
  subst gf
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp] using
    (canonicalPullbackChoice p).pullbackCompComponentIso_fac f g x

/-- Helper for Lemma 8.2.3: the inverse component of the flexible pullback-composition comparison
for the canonical fiber pseudofunctor factors the composite pullback arrow through the iterated
chosen pullback arrows. -/
theorem canonicalFiberPseudofunctor_mapComp'_inv_app_fac
    {S : Type*} [Category S] (p : S ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf)
    (x : p.Fiber D) :
    (((canonicalFiberPseudofunctor p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app x).1 ≫
        (canonicalPullbackChoice p).map gf x =
      (canonicalPullbackChoice p).map g
          (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj x) ≫
        (canonicalPullbackChoice p).map f x := by
  -- Read the same chosen comparison component in the inverse factorization direction.
  subst gf
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp] using
    (canonicalPullbackChoice p).pullbackCompComponentIso_inv_fac f g x

/-- Helper for Lemma 8.2.3: mapping the source pullback factorization identity along a morphism of
fibred categories preserves the same factorization in the target total category. -/
private theorem map_canonical_pullbackFunctor_map_fac
    (F : X ⟶ Y) {U V : C} (f : V ⟶ U) {x y : X.p.Fiber U} (φ : x ⟶ y) :
    F.toHom.map ((canonicalPullbackChoice X.p).map f x) ≫ F.toHom.map φ.1 =
      F.toHom.map ((((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
        F.toHom.map ((canonicalPullbackChoice X.p).map f y) := by
  -- Apply `F` to the owner-level pullback factorization and normalize with functoriality.
  rw [← Functor.map_comp, ← Functor.map_comp]
  have hfac :
      ((canonicalPullbackChoice X.p).map f x) ≫ φ.1 =
        ((((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
          (canonicalPullbackChoice X.p).map f y := by
    exact
      (canonical_pullbackFunctor_map_fac (p := X.p) (f := f) (x := x) (y := y) (φ := φ)).symm
  exact congrArg (fun k ↦ F.toHom.map k) hfac

/-- Helper for Lemma 8.2.3: after postcomposing both candidate composites with the chosen target
pullback arrow on `F(y)`, the two owner-level composites agree. -/
private theorem pullbackComparison_hom_postcompose_eq
    (F : X ⟶ Y) {U V : C} (f : V ⟶ U) {x y : X.p.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
        ((F.toHom.fiberFunctor U).map φ))).1 ≫
        (pullbackComparison F f y).hom.1 ≫
        F.toHom.map ((canonicalPullbackChoice X.p).map f y) =
      ((pullbackComparison F f x).hom.1 ≫
          ((F.toHom.fiberFunctor V).map
            (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map φ)).1) ≫
        F.toHom.map ((canonicalPullbackChoice X.p).map f y) := by
  -- Compare the two candidates only after postcomposing with the common strongly cartesian
  -- target, which is the source-faithful uniqueness step.
  let lhs :=
    ((((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
        ((F.toHom.fiberFunctor U).map φ))).1 ≫
      (pullbackComparison F f y).hom.1 ≫
      F.toHom.map ((canonicalPullbackChoice X.p).map f y)
  let mid₁ :=
    ((((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
        ((F.toHom.fiberFunctor U).map φ))).1 ≫
      (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj y)
  let mid₂ :=
    (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj x) ≫
      ((F.toHom.fiberFunctor U).map φ).1
  let mid₃ :=
    ((pullbackComparison F f x).hom.1 ≫
        F.toHom.map ((canonicalPullbackChoice X.p).map f x)) ≫
      ((F.toHom.fiberFunctor U).map φ).1
  let mid₄ :=
    (pullbackComparison F f x).hom.1 ≫
      ((F.toHom.fiberFunctor V).map
        (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
      F.toHom.map ((canonicalPullbackChoice X.p).map f y)
  let rhs :=
    ((pullbackComparison F f x).hom.1 ≫
        ((F.toHom.fiberFunctor V).map
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map φ)).1) ≫
      F.toHom.map ((canonicalPullbackChoice X.p).map f y)
  have h₁ : lhs = mid₁ := by
    -- Rewrite the comparison isomorphism at `y` to the canonical target pullback arrow.
    change
      ((((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
          ((F.toHom.fiberFunctor U).map φ))).1 ≫
          (pullbackComparison F f y).hom.1 ≫
          F.toHom.map ((canonicalPullbackChoice X.p).map f y) =
        ((((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
            ((F.toHom.fiberFunctor U).map φ))).1 ≫
          (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj y)
    exact
      congrArg
        (fun k ↦
          ((((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
              ((F.toHom.fiberFunctor U).map φ))).1 ≫ k)
        (pullbackComparison_hom_postcompose F f y)
  have h₂ : mid₁ = mid₂ := by
    -- Pullback in the target fiber is already natural on the vertical morphism `F.map φ`.
    change
      ((((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
          ((F.toHom.fiberFunctor U).map φ))).1 ≫
          (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj y) =
        (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj x) ≫
          ((F.toHom.fiberFunctor U).map φ).1
    exact
      canonical_pullbackFunctor_map_fac
        (p := Y.p) (f := f) (φ := (F.toHom.fiberFunctor U).map φ)
  have h₃ : mid₂ = mid₃ := by
    -- Rewrite the target pullback arrow at `x` back through the comparison isomorphism.
    change
      (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj x) ≫
          ((F.toHom.fiberFunctor U).map φ).1 =
        (((pullbackComparison F f x).hom.1 ≫
            F.toHom.map ((canonicalPullbackChoice X.p).map f x)) ≫
          ((F.toHom.fiberFunctor U).map φ).1)
    exact
      (congrArg
        (fun k ↦ k ≫ ((F.toHom.fiberFunctor U).map φ).1)
        (pullbackComparison_hom_postcompose F f x)).symm
  have h₄ : mid₃ = mid₄ := by
    -- Map the source pullback factorization across `F` and then reassociate.
    calc
      (((pullbackComparison F f x).hom.1 ≫
          F.toHom.map ((canonicalPullbackChoice X.p).map f x)) ≫
        ((F.toHom.fiberFunctor U).map φ).1) =
          (pullbackComparison F f x).hom.1 ≫
            (F.toHom.map ((canonicalPullbackChoice X.p).map f x) ≫
              ((F.toHom.fiberFunctor U).map φ).1) := by
            rw [Category.assoc]
      _ =
          (pullbackComparison F f x).hom.1 ≫
            (F.toHom.map ((((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
              F.toHom.map ((canonicalPullbackChoice X.p).map f y)) := by
            exact
              congrArg
                (fun k ↦ (pullbackComparison F f x).hom.1 ≫ k)
                (map_canonical_pullbackFunctor_map_fac F f φ)
      _ =
          (pullbackComparison F f x).hom.1 ≫
            ((F.toHom.fiberFunctor V).map
              (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
            F.toHom.map ((canonicalPullbackChoice X.p).map f y) := by
            rfl
  have h₅ : mid₄ = rhs := by
    -- Reassociate the right-hand composite into the packaged naturality shape.
    change
      (pullbackComparison F f x).hom.1 ≫
          ((F.toHom.fiberFunctor V).map
            (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
          F.toHom.map ((canonicalPullbackChoice X.p).map f y) =
        ((pullbackComparison F f x).hom.1 ≫
            ((F.toHom.fiberFunctor V).map
              (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map φ)).1) ≫
          F.toHom.map ((canonicalPullbackChoice X.p).map f y)
    exact (Category.assoc _ _ _).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- Helper for Lemma 8.2.3: the pullback-comparison isomorphism intertwines pullback of vertical
morphisms with the image of the pulled-back morphism after forgetting to the total categories. -/
private theorem pullbackComparison_hom_naturality_over_vertical
    (F : X ⟶ Y) {U V : C} (f : V ⟶ U) {x y : X.p.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
        ((F.toHom.fiberFunctor U).map φ))).1 ≫
      (pullbackComparison F f y).hom.1 =
        (pullbackComparison F f x).hom.1 ≫
          ((F.toHom.fiberFunctor V).map
            (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map φ)).1 := by
  -- Compare the two ambient arrows after postcomposing with the common strongly cartesian target.
  let ex := pullbackComparison F f x
  let ey := pullbackComparison F f y
  let η :
      ((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.obj
          ((F.toHom.fiberFunctor U).obj x) ⟶
        ((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.obj
          ((F.toHom.fiberFunctor U).obj y) :=
    ((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
      ((F.toHom.fiberFunctor U).map φ)
  let θ :
      ((F.toHom.fiberFunctor V).obj
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x)) ⟶
        ((F.toHom.fiberFunctor V).obj
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y)) :=
    ((F.toHom.fiberFunctor V).map
      (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map φ))
  let φF :
      (((F.toHom.fiberFunctor V).obj (f ^*[canonicalPullbackChoice X.p] y)).1 ⟶
        (((F.toHom.fiberFunctor U).obj y).1)) :=
    F.toHom.map ((canonicalPullbackChoice X.p).map f y)
  have hφF : Y.p.IsStronglyCartesian f φF := by
    -- Transport the chosen source pullback lift across the morphism of fibred categories.
    change Y.p.IsStronglyCartesian f (F.toHom.map ((canonicalPullbackChoice X.p).map f y))
    exact
      map_stronglyCartesian_of_lift F f
        ((canonicalPullbackChoice X.p).map f y)
        ((canonicalPullbackChoice X.p).isStronglyCartesian f y)
  letI : Y.p.IsStronglyCartesian f φF := hφF
  letI : Y.p.IsHomLift (𝟙 V) η.1 := by
    exact η.2
  letI : Y.p.IsHomLift (𝟙 V) θ.1 := by
    exact θ.2
  letI : Y.p.IsHomLift (𝟙 V) ex.hom.1 := by
    exact ex.hom.2
  letI : Y.p.IsHomLift (𝟙 V) ey.hom.1 := by
    exact ey.hom.2
  letI : Y.p.IsHomLift (𝟙 V) (η.1 ≫ ey.hom.1) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
      (𝟙 V) η.1 η.2 V ey.hom.1 ey.hom.2
  letI : Y.p.IsHomLift (𝟙 V) (ex.hom.1 ≫ θ.1) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
      (𝟙 V) ex.hom.1 ex.hom.2 V θ.1 θ.2
  have hcomp :
      η.1 ≫ ey.hom.1 ≫ φF = (ex.hom.1 ≫ θ.1) ≫ φF := by
    simpa only [η, θ, φF, Category.assoc] using
      pullbackComparison_hom_postcompose_eq F f φ
  have hηey : Y.p.IsHomLift (𝟙 V) (η.1 ≫ ey.hom.1) := by infer_instance
  have hexθ : Y.p.IsHomLift (𝟙 V) (ex.hom.1 ≫ θ.1) := by infer_instance
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ Y.p _ _ _ _
      f φF inferInstance _ _ (𝟙 V) (η.1 ≫ ey.hom.1) (ex.hom.1 ≫ θ.1) hηey hexθ <| by
        rw [Category.assoc]
        exact hcomp

/-- Helper for Lemma 8.2.3: the pullback-comparison isomorphism is fiberwise natural on vertical
morphisms. This is the main comparison square from the source proof. -/
theorem pullbackComparison_naturality_over_vertical
    (F : X ⟶ Y) {U V : C} (f : V ⟶ U) {x y : X.p.Fiber U} (φ : x ⟶ y) :
    (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
        ((F.toHom.fiberFunctor U).map φ)) ≫
      (pullbackComparison F f y).hom =
        (pullbackComparison F f x).hom ≫
          (F.toHom.fiberFunctor V).map
            (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map φ) := by
  -- Reduce the fiber statement to the owner-level equality proved just above.
  apply Functor.Fiber.hom_ext
  exact pullbackComparison_hom_naturality_over_vertical F f φ

/-- Helper for Lemma 8.2.3: the inverse pullback-comparison isomorphism carries the source-faithful
vertical naturality square into the form needed by the final `pullHom` computation. -/
theorem pullbackComparison_inv_naturality_over_vertical
    (F : X ⟶ Y) {U V : C} (f : V ⟶ U) {x y : X.p.Fiber U} (φ : x ⟶ y) :
    (F.toHom.fiberFunctor V).map
        (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map φ) ≫
      (pullbackComparison F f y).inv =
        (pullbackComparison F f x).inv ≫
          (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
            ((F.toHom.fiberFunctor U).map φ)) := by
  -- Route correction: move the already proved hom-side square across the two comparison inverses.
  let ex := pullbackComparison F f x
  let ey := pullbackComparison F f y
  let η :=
    ((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
      ((F.toHom.fiberFunctor U).map φ)
  let θ :=
    (F.toHom.fiberFunctor V).map
      (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map φ)
  have hhom : η ≫ ey.hom = ex.hom ≫ θ := by
    simpa only [ex, ey, η, θ] using pullbackComparison_naturality_over_vertical F f φ
  symm
  apply (Iso.eq_comp_inv ey).2
  -- Precompose by `ex.inv` so the left comparison isomorphism cancels immediately.
  have hpre :
      ex.inv ≫
          ((((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
              ((F.toHom.fiberFunctor U).map φ)) ≫ ey.hom) =
        ex.inv ≫
          (ex.hom ≫
            (F.toHom.fiberFunctor V).map
              (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map φ)) := by
    exact congrArg (fun k ↦ ex.inv ≫ k) hhom
  simpa only [← Category.assoc, ex.inv_hom_id, Category.id_comp] using hpre

end FibredCategoryMor

end CategoryTheory
