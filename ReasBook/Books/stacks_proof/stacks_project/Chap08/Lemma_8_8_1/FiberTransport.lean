import StacksProject_2024.Chap08.Lemma_8_8_1.HomPresheafComparison
import StacksProject_2024.Chap08.Lemma_8_8_1.Precomposition
import Mathlib.Tactic.StacksAttribute

universe u v

namespace CategoryTheory

open Bicategory
open BasedFunctor
open FibredCategoryMor
open InducedCategory.Hom
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section

/-- Helper for Lemma 8.8.1: a based-functor isomorphism restricts to an isomorphism on each fiber
over `U`. Each component of the based natural isomorphism at the underlying object already lifts
`𝟙 U`, hence is a vertical morphism in the fiber, and the iso laws are inherited componentwise. -/
noncomputable def basedFiberFunctorIso
    {X Y : FibredCategoryOver C} {F G : X ⟶ Y}
    (e : FibredCategoryMor.toBasedFunctor F ≅ FibredCategoryMor.toBasedFunctor G)
    (U : C) (x : X.p.Fiber U) :
    ((FibredCategoryMor.fiberFunctor F U).obj x) ≅
      ((FibredCategoryMor.fiberFunctor G U).obj x) where
  hom := ⟨e.hom.toNatTrans.app x.1, e.hom.isHomLift x.2⟩
  inv := ⟨e.inv.toNatTrans.app x.1, e.inv.isHomLift x.2⟩
  hom_inv_id := by
    apply Functor.Fiber.hom_ext
    change e.hom.toNatTrans.app x.1 ≫ e.inv.toNatTrans.app x.1 = 𝟙 _
    have h := ((BasedNatTrans.forgetful X.toBasedCategory Y.toBasedCategory).mapIso e).hom_inv_id
    have h' := congrArg (fun t ↦ CategoryTheory.NatTrans.app t x.1) h
    simpa using h'
  inv_hom_id := by
    apply Functor.Fiber.hom_ext
    change e.inv.toNatTrans.app x.1 ≫ e.hom.toNatTrans.app x.1 = 𝟙 _
    have h := ((BasedNatTrans.forgetful X.toBasedCategory Y.toBasedCategory).mapIso e).inv_hom_id
    have h' := congrArg (fun t ↦ CategoryTheory.NatTrans.app t x.1) h
    simpa using h'

/-- Helper for Lemma 8.8.1: a compatible isomorphism
`G₁ ≫ stack_morphism_toFibredCategoryMor H ≅ G₂` restricts to an isomorphism on every fiber. -/
theorem comparison_iso_on_fiber
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    {G₁ : X ⟶ Y₁} {G₂ : X ⟶ Y₂} {H : Y₁ ⟶ Y₂}
    (α : G₁ ≫ stack_morphism_toFibredCategoryMor H ≅ G₂)
    (U : C) (x : X.p.Fiber U) :
    Nonempty (((FibredCategoryMor.fiberFunctor
      (G₁ ≫ stack_morphism_toFibredCategoryMor H) U).obj x) ≅
      ((FibredCategoryMor.fiberFunctor G₂ U).obj x)) :=
  -- Forget the owner isomorphism to the based-functor level via `basedFunctorIsoOfOwnerIso`,
  -- then restrict that based-functor iso to the fixed fiber over `U` at the object `x`.
  ⟨basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U x⟩

-- Package the presheaf transport induced by `mapIso` on each pullback functor: build the iso
-- objectwise via `Iso.homCongr` conjugation, then discharge the conjugation-naturality square
-- with the two `mapComp'` pullback-comparison naturality lemmas.
set_option backward.isDefEq.respectTransparency false in
/-- Helper for Lemma 8.8.1: the canonical (non-`choice`) Hom-presheaf transport isomorphism
induced by fiberwise isomorphisms `ex : x₁ ≅ x₂`, `ey : y₁ ≅ y₂` over a fixed `U`. Objectwise it
is the `Iso.homCongr` conjugation by the images of `ex`/`ey` under each pullback functor; the
naturality square is discharged by the two `mapComp'` pullback-comparison lemmas. -/
noncomputable def fiberHomPresheafIso
    {Y : FibredCategoryOver C} {U : C} {x₁ x₂ y₁ y₂ : Y.p.Fiber U}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) :
    ((canonicalFiberPseudofunctor Y.p).presheafHom x₁ y₁) ≅
      ((canonicalFiberPseudofunctor Y.p).presheafHom x₂ y₂) :=
  NatIso.ofComponents
    (fun W => Equiv.toIso
      (Iso.homCongr
        (((canonicalFiberPseudofunctor Y.p).map (.toLoc W.unop.hom.op)).toFunctor.mapIso ex)
        (((canonicalFiberPseudofunctor Y.p).map (.toLoc W.unop.hom.op)).toFunctor.mapIso ey)))
    (by
      rintro ⟨T₁⟩ ⟨T₂⟩ ⟨f⟩
      ext g
      dsimp [Pseudofunctor.presheafHom, Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Iso.homCongr]
      simp only [Category.assoc, Functor.map_comp]
      rw [Pseudofunctor.mapComp'_hom_naturality_assoc, Pseudofunctor.mapComp'_inv_naturality,
        Category.assoc])

/-- Helper for Lemma 8.8.1: fiberwise isomorphisms over a fixed `U` induce the corresponding
isomorphism of Hom presheaves on the slice site `J.over U`. This isolates the transport block
used later on a chosen common cover before any `W`-globalization is attempted. -/
theorem fiber_hom_presheaf_iso_exists_of_fiberIso
    {Y : FibredCategoryOver C}
    {U : C} {x₁ x₂ y₁ y₂ : Y.p.Fiber U}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) :
    Nonempty
      (((canonicalFiberPseudofunctor Y.p).presheafHom x₁ y₁) ≅
        ((canonicalFiberPseudofunctor Y.p).presheafHom x₂ y₂)) :=
  ⟨fiberHomPresheafIso ex ey⟩

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Lemma 8.8.1: the Hom-presheaf comparison map `fibredMorphismPresheafMap F` is
natural, objectwise on the slice site, under conjugation by the fiberwise transport isomorphisms
`fiberHomPresheafIso`. On the source side this is conjugation by `ex`, `ey`; on the target side by
their `F`-images. The proof unfolds both shells and feeds the two `pullbackComparison` vertical
naturality lemmas. -/
theorem fibredMorphismPresheafMap_natural_of_fiberIso_app
    {X Y : FibredCategoryOver C} (F : X ⟶ Y)
    {U : C} {x₁ x₂ y₁ y₂ : X.p.Fiber U} (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂)
    (W : (Over U)ᵒᵖ) (δ : ((canonicalFiberPseudofunctor X.p).presheafHom x₁ y₁).obj W) :
    (fibredMorphismPresheafMap F x₂ y₂).app W ((fiberHomPresheafIso (Y := X) ex ey).hom.app W δ) =
      (fiberHomPresheafIso (Y := Y) ((F.toHom.fiberFunctor U).mapIso ex)
          ((F.toHom.fiberFunctor U).mapIso ey)).hom.app W
        ((fibredMorphismPresheafMap F x₁ y₁).app W δ) := by
  -- Abbreviations matching the comparison-shell unfolding used by the `_comp_app` helper.
  -- Unfold the source-side transport `hom.app W` to the `Iso.homCongr` conjugation, then the outer
  -- `fibredMorphismPresheafMap … .app W` to its `pullbackComparison` shell.
  simp only [fiberHomPresheafIso, NatIso.ofComponents_hom_app, Equiv.toIso_hom,
    Iso.homCongr_apply, Functor.mapIso_inv, Functor.mapIso_hom]
  change
    (FibredCategoryMor.pullbackComparison F W.unop.hom x₂).hom ≫
        (F.toHom.fiberFunctor W.unop.left).map
          (((canonicalFiberPseudofunctor X.p).map (.toLoc W.unop.hom.op)).toFunctor.map ex.inv ≫
            δ ≫
            ((canonicalFiberPseudofunctor X.p).map (.toLoc W.unop.hom.op)).toFunctor.map ey.hom) ≫
          (FibredCategoryMor.pullbackComparison F W.unop.hom y₂).inv =
      ((canonicalFiberPseudofunctor Y.p).map (.toLoc W.unop.hom.op)).toFunctor.map
          ((F.toHom.fiberFunctor U).map ex.inv) ≫
        ((FibredCategoryMor.pullbackComparison F W.unop.hom x₁).hom ≫
            (F.toHom.fiberFunctor W.unop.left).map δ ≫
              (FibredCategoryMor.pullbackComparison F W.unop.hom y₁).inv) ≫
          ((canonicalFiberPseudofunctor Y.p).map (.toLoc W.unop.hom.op)).toFunctor.map
            ((F.toHom.fiberFunctor U).map ey.hom)
  -- The two vertical naturality squares for `pullbackComparison` (over `W.unop.hom`), applied to
  -- `ex.inv : x₂ ⟶ x₁` (hom side) and `ey.hom : y₁ ⟶ y₂` (inv side).
  have hx :
      ((canonicalFiberPseudofunctor Y.p).map (W.unop.hom).op.toLoc).toFunctor.map
            ((F.toHom.fiberFunctor U).map ex.inv) ≫
          (FibredCategoryMor.pullbackComparison F W.unop.hom x₁).hom =
        (FibredCategoryMor.pullbackComparison F W.unop.hom x₂).hom ≫
          (F.toHom.fiberFunctor W.unop.left).map
            (((canonicalFiberPseudofunctor X.p).map (W.unop.hom).op.toLoc).toFunctor.map ex.inv) :=
    FibredCategoryMor.pullbackComparison_naturality_over_vertical F W.unop.hom ex.inv
  have hy :
      (F.toHom.fiberFunctor W.unop.left).map
            (((canonicalFiberPseudofunctor X.p).map (W.unop.hom).op.toLoc).toFunctor.map ey.hom) ≫
          (FibredCategoryMor.pullbackComparison F W.unop.hom y₂).inv =
        (FibredCategoryMor.pullbackComparison F W.unop.hom y₁).inv ≫
          ((canonicalFiberPseudofunctor Y.p).map (W.unop.hom).op.toLoc).toFunctor.map
            ((F.toHom.fiberFunctor U).map ey.hom) :=
    FibredCategoryMor.pullbackComparison_inv_naturality_over_vertical F W.unop.hom ey.hom
  -- Transform the right-hand side into the left-hand side using the two naturality squares.
  -- Reassociate fully, expand the `F_V`-image of the source composite, then rewrite the leading
  -- `M^Y(F_U ex.inv) ≫ (pbc x₁).hom` block via `hx` and the trailing
  -- `(pbc y₁).inv ≫ M^Y(F_U ey.hom)` block via `← hy`.
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hx, ← hy]

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Lemma 8.8.1: the hom of the pullback-comparison isomorphism is natural under a
`2`-isomorphism `α : F ≅ F'` of owner morphisms. The comparison for `F'` is the comparison for
`F` conjugated by the `α`-induced fiberwise isomorphisms (pulled back to the slice object on the
source side). This is the `2`-cell analogue of `pullbackComparison_naturality_over_vertical`. -/
theorem pullbackComparison_hom_natural_of_ownerIso
    {X Y : FibredCategoryOver C} {F F' : X ⟶ Y} (α : F ≅ F')
    {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (FibredCategoryMor.pullbackComparison F' f x).hom.1 =
      (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
          (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U x).inv).1 ≫
        (FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
        (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) V
            (f ^*[canonicalPullbackChoice X.p] x)).hom.1 := by
  set θ := FibredCategoryMor.basedFunctorIsoOfOwnerIso α with hθ
  set e_x := basedFiberFunctorIso θ U x with hex
  set e_fx := basedFiberFunctorIso θ V (f ^*[canonicalPullbackChoice X.p] x) with hefx
  -- The common strongly cartesian witness OUT of the codomain `F'_V(f^*[X]x)`: image under `F'`
  -- of the chosen source pullback arrow.
  set φ' : (((F'.toHom.fiberFunctor V).obj (f ^*[canonicalPullbackChoice X.p] x)).1 ⟶
      ((F'.toHom.fiberFunctor U).obj x).1) :=
    F'.toHom.map ((canonicalPullbackChoice X.p).map f x) with hφ'
  have hφ'cart : Y.p.IsStronglyCartesian f φ' := by
    change Y.p.IsStronglyCartesian f (F'.toHom.map ((canonicalPullbackChoice X.p).map f x))
    exact FibredCategoryMor.map_stronglyCartesian_of_lift F' f
      ((canonicalPullbackChoice X.p).map f x)
      ((canonicalPullbackChoice X.p).isStronglyCartesian f x)
  letI : Y.p.IsStronglyCartesian f φ' := hφ'cart
  -- Both candidate comparison morphisms lift `𝟙 V`.
  letI hlL : Y.p.IsHomLift (𝟙 V) (FibredCategoryMor.pullbackComparison F' f x).hom.1 :=
    (FibredCategoryMor.pullbackComparison F' f x).hom.2
  letI hlR : Y.p.IsHomLift (𝟙 V)
      ((((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map e_x.inv).1 ≫
        (FibredCategoryMor.pullbackComparison F f x).hom.1 ≫ e_fx.hom.1) := by
    have h1 : Y.p.IsHomLift (𝟙 V)
        ((((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map e_x.inv).1) :=
      (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map e_x.inv).2
    have h2 : Y.p.IsHomLift (𝟙 V) (FibredCategoryMor.pullbackComparison F f x).hom.1 :=
      (FibredCategoryMor.pullbackComparison F f x).hom.2
    have h3 : Y.p.IsHomLift (𝟙 V) e_fx.hom.1 := e_fx.hom.2
    have h23 := @CategoryTheory.IsHomLift.comp_of_lift_id _ _ _ _ Y.p V _ _ _ _ _ h2 h3
    exact @CategoryTheory.IsHomLift.comp_of_lift_id _ _ _ _ Y.p V _ _ _ _ _ h1 h23
  -- It suffices to check both candidates agree after postcomposition with the cartesian `φ'`.
  refine Functor.IsStronglyCartesian.ext Y.p f φ' (𝟙 V) ?_
  -- Left candidate: `pullbackComparison_hom_postcompose` for `F'`.
  have hL :
      (FibredCategoryMor.pullbackComparison F' f x).hom.1 ≫ φ' =
        (canonicalPullbackChoice Y.p).map f ((F'.toHom.fiberFunctor U).obj x) :=
    FibredCategoryMor.pullbackComparison_hom_postcompose F' f x
  -- Right candidate: chase the conjugated composite through θ-naturality, the `F`-side
  -- `pullbackComparison_hom_postcompose`, and the target-fiber pullback functoriality, ending at
  -- the same chosen target pullback arrow.
  have hθnat :
      e_fx.hom.1 ≫ φ' =
        F.toHom.map ((canonicalPullbackChoice X.p).map f x) ≫ e_x.hom.1 := by
    -- `e_fx.hom.1 = θ.hom.app (f^*[X]x).1`, `e_x.hom.1 = θ.hom.app x.1`; this is the ordinary
    -- naturality of `θ.hom.toNatTrans` on the morphism `(canonicalPullbackChoice X.p).map f x`.
    have hnat := θ.hom.toNatTrans.naturality ((canonicalPullbackChoice X.p).map f x)
    -- `hnat : F.map g ≫ θ.app (cod g) = θ.app (dom g) ≫ F'.map g`.
    simp only [hex, hefx, basedFiberFunctorIso, hφ']
    exact hnat.symm
  have hFpost :
      (FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
          F.toHom.map ((canonicalPullbackChoice X.p).map f x) =
        (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj x) :=
    FibredCategoryMor.pullbackComparison_hom_postcompose F f x
  have hpullfac :
      (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map e_x.inv).1 ≫
          (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj x) =
        (canonicalPullbackChoice Y.p).map f ((F'.toHom.fiberFunctor U).obj x) ≫ e_x.inv.1 := by
    -- `e_x.inv : F'_U x ⟶ F_U x`; this is `canonical_pullbackFunctor_map_fac` for `p = Y.p`.
    have := FibredCategoryMor.canonical_pullbackFunctor_map_fac (p := Y.p) (f := f)
      (x := (F'.toHom.fiberFunctor U).obj x) (y := (F.toHom.fiberFunctor U).obj x) e_x.inv
    -- Domain of `e_x.inv` is `F'_U x`, codomain is `F_U x`.
    exact this
  have hinv : e_x.inv.1 ≫ e_x.hom.1 = 𝟙 _ :=
    congrArg (fun k => k.1) e_x.inv_hom_id
  -- Reduce the `ext` obligation `LHS ≫ φ' = RHS ≫ φ'` to the chosen target pullback arrow.
  rw [hL]
  calc
    (canonicalPullbackChoice Y.p).map f ((F'.toHom.fiberFunctor U).obj x)
        = (canonicalPullbackChoice Y.p).map f ((F'.toHom.fiberFunctor U).obj x) ≫
            (e_x.inv.1 ≫ e_x.hom.1) := by rw [hinv, Category.comp_id]
      _ = ((canonicalPullbackChoice Y.p).map f ((F'.toHom.fiberFunctor U).obj x) ≫ e_x.inv.1) ≫
            e_x.hom.1 := by rw [Category.assoc]
      _ = ((((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map e_x.inv).1 ≫
            (canonicalPullbackChoice Y.p).map f ((F.toHom.fiberFunctor U).obj x)) ≫ e_x.hom.1 := by
            rw [hpullfac]
      _ = (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map e_x.inv).1 ≫
            ((FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
              F.toHom.map ((canonicalPullbackChoice X.p).map f x)) ≫ e_x.hom.1 := by
            rw [hFpost, Category.assoc]
      _ = (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map e_x.inv).1 ≫
            (FibredCategoryMor.pullbackComparison F f x).hom.1 ≫
              (F.toHom.map ((canonicalPullbackChoice X.p).map f x) ≫ e_x.hom.1) := by
            simp only [Category.assoc]
      _ = (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map e_x.inv).1 ≫
            (FibredCategoryMor.pullbackComparison F f x).hom.1 ≫ e_fx.hom.1 ≫ φ' := by
            rw [hθnat]
      _ = ((((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map e_x.inv).1 ≫
            (FibredCategoryMor.pullbackComparison F f x).hom.1 ≫ e_fx.hom.1) ≫ φ' := by
            simp only [Category.assoc]

/-- Helper for Lemma 8.8.1: fiber-level form of `pullbackComparison_hom_natural_of_ownerIso`. -/
theorem pullbackComparison_hom_natural_of_ownerIso_fiber
    {X Y : FibredCategoryOver C} {F F' : X ⟶ Y} (α : F ≅ F')
    {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (FibredCategoryMor.pullbackComparison F' f x).hom =
      ((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
          (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U x).inv ≫
        (FibredCategoryMor.pullbackComparison F f x).hom ≫
        (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) V
            (f ^*[canonicalPullbackChoice X.p] x)).hom := by
  apply Functor.Fiber.hom_ext
  exact pullbackComparison_hom_natural_of_ownerIso α f x

/-- Helper for Lemma 8.8.1: the `α`-induced fiberwise isomorphisms are natural on vertical
morphisms over a fixed base object `V`. This is the restriction of the based natural isomorphism
`basedFunctorIsoOfOwnerIso α` to the fiber over `V`. -/
theorem basedFiberFunctorIso_naturality
    {X Y : FibredCategoryOver C} {F F' : X ⟶ Y} (α : F ≅ F')
    {V : C} {a b : X.p.Fiber V} (δ : a ⟶ b) :
    (FibredCategoryMor.fiberFunctor F V).map δ ≫
        (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) V b).hom =
      (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) V a).hom ≫
        (FibredCategoryMor.fiberFunctor F' V).map δ := by
  apply Functor.Fiber.hom_ext
  exact (FibredCategoryMor.basedFunctorIsoOfOwnerIso α).hom.toNatTrans.naturality δ.1

/-- Helper for Lemma 8.8.1: the fiber component of an owner iso at `z'` is determined by its
component at `z` and any fiber iso `c : z ≅ z'`, via the naturality of the underlying based
natural transformation. -/
theorem basedFiberFunctorIso_transport_of_fiberIso
    {X Y : FibredCategoryOver C} {F F' : X ⟶ Y} (γ : F ≅ F')
    {V : C} {z z' : X.p.Fiber V} (c : z ≅ z') :
    (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) V z').hom =
      (FibredCategoryMor.fiberFunctor F V).map c.inv ≫
        (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) V z).hom ≫
        (FibredCategoryMor.fiberFunctor F' V).map c.hom := by
  -- Naturality of the based natural transformation on `c.hom : z ⟶ z'`.
  have hnat :
      (FibredCategoryMor.fiberFunctor F V).map c.hom ≫
          (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) V z').hom =
        (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) V z).hom ≫
          (FibredCategoryMor.fiberFunctor F' V).map c.hom :=
    basedFiberFunctorIso_naturality γ (V := V) c.hom
  -- Solve for the component at `z'`.
  have hc : (FibredCategoryMor.fiberFunctor F V).map c.inv ≫
      (FibredCategoryMor.fiberFunctor F V).map c.hom = 𝟙 _ := by
    rw [← Functor.map_comp, c.inv_hom_id, Functor.map_id]
  calc
    (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) V z').hom
        = 𝟙 _ ≫ (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) V z').hom := by
          rw [Category.id_comp]
      _ = ((FibredCategoryMor.fiberFunctor F V).map c.inv ≫
            (FibredCategoryMor.fiberFunctor F V).map c.hom) ≫
            (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) V z').hom := by
          rw [hc]
      _ = (FibredCategoryMor.fiberFunctor F V).map c.inv ≫
            ((FibredCategoryMor.fiberFunctor F V).map c.hom ≫
              (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) V z').hom) := by
          rw [Category.assoc]
      _ = (FibredCategoryMor.fiberFunctor F V).map c.inv ≫
            ((basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) V z).hom ≫
              (FibredCategoryMor.fiberFunctor F' V).map c.hom) := by
          rw [hnat]

/-- Helper for Lemma 8.8.1: the canonical pullback of the fiber component of an owner iso at `x`
equals the `pullbackComparison`-conjugate of the component at the pulled-back object `f^* x`. This
is the bridge feeding `stack_cover_hom_ext` in the descent of a `2`-morphism. -/
theorem basedFiberFunctorIso_pullback_bridge
    {X Y : FibredCategoryOver C} {F F' : X ⟶ Y} (γ : F ≅ F')
    {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    ((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
        (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) U x).hom =
      (FibredCategoryMor.pullbackComparison F f x).hom ≫
        (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) V
            (f ^*[canonicalPullbackChoice X.p] x)).hom ≫
        (FibredCategoryMor.pullbackComparison F' f x).inv := by
  set M := ((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor with hM
  set e_x := basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) U x with hex
  set e_fx := basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso γ) V
    (f ^*[canonicalPullbackChoice X.p] x) with hefx
  -- The 2-cell naturality identity for `pullbackComparison`.
  have hR :
      (FibredCategoryMor.pullbackComparison F' f x).hom =
        M.map e_x.inv ≫ (FibredCategoryMor.pullbackComparison F f x).hom ≫ e_fx.hom :=
    pullbackComparison_hom_natural_of_ownerIso_fiber γ f x
  -- `key`: `M.map e_x.hom ≫ (pbc F' f x).hom = (pbc F f x).hom ≫ e_fx.hom`.
  have key :
      M.map e_x.hom ≫ (FibredCategoryMor.pullbackComparison F' f x).hom =
        (FibredCategoryMor.pullbackComparison F f x).hom ≫ e_fx.hom := by
    rw [hR]
    exact (M.mapIso e_x).hom_inv_id_assoc _
  -- Goal: `M.map e_x.hom = (pbc F f x).hom ≫ e_fx.hom ≫ (pbc F' f x).inv`.
  have hstep :
      M.map e_x.hom =
        ((FibredCategoryMor.pullbackComparison F f x).hom ≫ e_fx.hom) ≫
          (FibredCategoryMor.pullbackComparison F' f x).inv :=
    (Iso.eq_comp_inv (FibredCategoryMor.pullbackComparison F' f x)).2 key
  rw [hstep, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Lemma 8.8.1: the Hom-presheaf comparison map is natural, objectwise on the slice
site, under a `2`-isomorphism `α : F ≅ F'` of owner morphisms. The comparison for `F'` is the
comparison for `F` conjugated by the `α`-induced fiberwise transport. -/
theorem fibredMorphismPresheafMap_natural_of_ownerIso_app
    {X Y : FibredCategoryOver C} {F F' : X ⟶ Y} (α : F ≅ F')
    {U : C} (x y : X.p.Fiber U)
    (W : (Over U)ᵒᵖ) (δ : ((canonicalFiberPseudofunctor X.p).presheafHom x y).obj W) :
    (fibredMorphismPresheafMap F' x y).app W δ =
      (fiberHomPresheafIso (Y := Y)
          (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U x)
          (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U y)).hom.app W
        ((fibredMorphismPresheafMap F x y).app W δ) := by
  -- Unfold the source-side transport `hom.app W` to the conjugation, and the two outer
  -- comparison shells.
  simp only [fiberHomPresheafIso, NatIso.ofComponents_hom_app, Equiv.toIso_hom,
    Iso.homCongr_apply, Functor.mapIso_inv, Functor.mapIso_hom]
  change
    (FibredCategoryMor.pullbackComparison F' W.unop.hom x).hom ≫
        (F'.toHom.fiberFunctor W.unop.left).map δ ≫
        (FibredCategoryMor.pullbackComparison F' W.unop.hom y).inv =
      ((canonicalFiberPseudofunctor Y.p).map (.toLoc W.unop.hom.op)).toFunctor.map
          (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U x).inv ≫
        ((FibredCategoryMor.pullbackComparison F W.unop.hom x).hom ≫
            (F.toHom.fiberFunctor W.unop.left).map δ ≫
              (FibredCategoryMor.pullbackComparison F W.unop.hom y).inv) ≫
          ((canonicalFiberPseudofunctor Y.p).map (.toLoc W.unop.hom.op)).toFunctor.map
            (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U y).hom
  -- Expand `pbc F'` hom (at x) and inv (at y) through the `2`-cell naturality.
  rw [pullbackComparison_hom_natural_of_ownerIso_fiber α W.unop.hom x]
  -- Promote the hom-form `2`-cell identity to an isomorphism identity, then read off the inverse.
  have hisoY :
      FibredCategoryMor.pullbackComparison F' W.unop.hom y =
        (((canonicalFiberPseudofunctor Y.p).map (.toLoc W.unop.hom.op)).toFunctor.mapIso
            (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U y)).symm ≪≫
          FibredCategoryMor.pullbackComparison F W.unop.hom y ≪≫
          basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) W.unop.left
            (W.unop.hom ^*[canonicalPullbackChoice X.p] y) := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
    exact pullbackComparison_hom_natural_of_ownerIso_fiber α W.unop.hom y
  have hinv :
      (FibredCategoryMor.pullbackComparison F' W.unop.hom y).inv =
        (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) W.unop.left
            (W.unop.hom ^*[canonicalPullbackChoice X.p] y)).inv ≫
          (FibredCategoryMor.pullbackComparison F W.unop.hom y).inv ≫
          ((canonicalFiberPseudofunctor Y.p).map (.toLoc W.unop.hom.op)).toFunctor.map
            (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U y).hom := by
    rw [hisoY]
    simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, Category.assoc]
  rw [hinv]
  -- Collapse the middle `θ`-conjugation `e_fx.hom ≫ F'.map δ ≫ e_fy.inv = F.map δ`.
  have hmid :
      (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) W.unop.left
            (W.unop.hom ^*[canonicalPullbackChoice X.p] x)).hom ≫
          (F'.toHom.fiberFunctor W.unop.left).map δ ≫
          (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) W.unop.left
              (W.unop.hom ^*[canonicalPullbackChoice X.p] y)).inv =
        (F.toHom.fiberFunctor W.unop.left).map δ := by
    have hnat :
        (F.toHom.fiberFunctor W.unop.left).map δ ≫
            (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) W.unop.left
              (W.unop.hom ^*[canonicalPullbackChoice X.p] y)).hom =
          (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) W.unop.left
              (W.unop.hom ^*[canonicalPullbackChoice X.p] x)).hom ≫
            (F'.toHom.fiberFunctor W.unop.left).map δ :=
      basedFiberFunctorIso_naturality α (V := W.unop.left) δ
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  -- Reassociate and discharge the conjugation `e_fx.hom ≫ F'.map δ ≫ e_fy.inv = F.map δ`.
  simp only [Category.assoc, Functor.id_obj]
  rw [reassoc_of% hmid]
  rfl

/-- Helper for Lemma 8.8.1: local identifications
`((FibredCategoryMor.fiberFunctor G₁ U).obj xI) ≅ x` and
`((FibredCategoryMor.fiberFunctor G₁ U).obj yI) ≅ y`
transport the source Hom presheaf from the source-image pair to the restricted arbitrary-object
pair. This is the source-side half of the fixed-cover comparison transport. -/
noncomputable abbrev comparison_stackification_source_hom_presheaf_iso_of_local_models
    {X : FibredCategoryOver C} {Y₁ : StackOver J}
    {G₁ : X ⟶ Y₁}
    {U : C} {x y : Y₁.p.Fiber U} {xI yI : X.p.Fiber U}
    (hxI : ((FibredCategoryMor.fiberFunctor G₁ U).obj xI) ≅ x)
    (hyI : ((FibredCategoryMor.fiberFunctor G₁ U).obj yI) ≅ y) :
    ((canonicalFiberPseudofunctor Y₁.p).presheafHom
      ((FibredCategoryMor.fiberFunctor G₁ U).obj xI)
      ((FibredCategoryMor.fiberFunctor G₁ U).obj yI)) ≅
    ((canonicalFiberPseudofunctor Y₁.p).presheafHom x y) :=
  fiberHomPresheafIso (Y := Y₁.toFibredCategoryOver) hxI hyI

/-- Helper for Lemma 8.8.1: after applying `H`, the same local-model identifications transport the
target Hom presheaf from the source-image pair to the restricted arbitrary-object pair. This is
the codomain-side half of the fixed-cover comparison transport. -/
noncomputable abbrev comparison_stackification_target_hom_presheaf_iso_of_local_models
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    {G₁ : X ⟶ Y₁} (H : Y₁ ⟶ Y₂)
    {U : C} {x y : Y₁.p.Fiber U} {xI yI : X.p.Fiber U}
    (hxI : ((FibredCategoryMor.fiberFunctor G₁ U).obj xI) ≅ x)
    (hyI : ((FibredCategoryMor.fiberFunctor G₁ U).obj yI) ≅ y) :
    ((canonicalFiberPseudofunctor Y₂.p).presheafHom
      ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj
        ((FibredCategoryMor.fiberFunctor G₁ U).obj xI))
      ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj
        ((FibredCategoryMor.fiberFunctor G₁ U).obj yI))) ≅
    ((canonicalFiberPseudofunctor Y₂.p).presheafHom
      ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj x)
      ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).obj y)) :=
  fiberHomPresheafIso (Y := Y₂.toFibredCategoryOver)
    ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).mapIso hxI)
    ((FibredCategoryMor.fiberFunctor (stack_morphism_toFibredCategoryMor H) U).mapIso hyI)

/-- Helper for Lemma 8.8.1: a compatible owner isomorphism
`α : G₁ ≫ stack_morphism_toFibredCategoryMor H ≅ G₂` transports the target Hom presheaf on source-image objects
by conjugating with the induced fiberwise isomorphisms. This isolates the codomain transport from
the later `W`-argument. -/
noncomputable abbrev comparison_stackification_target_hom_presheaf_iso_of_ownerIso
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    {G₁ : X ⟶ Y₁} {G₂ : X ⟶ Y₂} {H : Y₁ ⟶ Y₂}
    (α : G₁ ≫ stack_morphism_toFibredCategoryMor H ≅ G₂)
    {U : C} (x y : X.p.Fiber U) :
    ((canonicalFiberPseudofunctor Y₂.p).presheafHom
      ((FibredCategoryMor.fiberFunctor
        (G₁ ≫ stack_morphism_toFibredCategoryMor H) U).obj x)
      ((FibredCategoryMor.fiberFunctor
        (G₁ ≫ stack_morphism_toFibredCategoryMor H) U).obj y)) ≅
    ((canonicalFiberPseudofunctor Y₂.p).presheafHom
      ((FibredCategoryMor.fiberFunctor G₂ U).obj x)
      ((FibredCategoryMor.fiberFunctor G₂ U).obj y)) :=
  fiberHomPresheafIso (Y := Y₂.toFibredCategoryOver)
    (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U x)
    (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U y)


/-- Helper for Lemma 8.8.1: the composite Hom-presheaf map attached to a compatible owner
isomorphism factors through the target-side conjugation isomorphism induced by that owner
isomorphism. This is the transport-stable normal form needed before applying `W.postcomp_iff`. -/
theorem comparison_stackification_composite_presheafMap_factor_of_ownerIso
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    {G₁ : X ⟶ Y₁} {G₂ : X ⟶ Y₂} {H : Y₁ ⟶ Y₂}
    (α : G₁ ≫ stack_morphism_toFibredCategoryMor H ≅ G₂)
    {U : C} (x y : X.p.Fiber U) :
    fibredMorphismPresheafMap (G₁ ≫ stack_morphism_toFibredCategoryMor H) x y =
        fibredMorphismPresheafMap G₂ x y ≫
        (comparison_stackification_target_hom_presheaf_iso_of_ownerIso
          (J := J) α x y).inv := by
  -- It suffices to prove the `.hom`-postcomposed form, which is the objectwise `2`-cell naturality
  -- of `fibredMorphismPresheafMap` under the owner isomorphism `α`.
  rw [Iso.eq_comp_inv]
  apply NatTrans.ext
  funext W
  apply funext
  intro δ
  -- Objectwise, this is exactly `fibredMorphismPresheafMap_natural_of_ownerIso_app α` (reversed).
  show (fibredMorphismPresheafMap (G₁ ≫ stack_morphism_toFibredCategoryMor H) x y ≫
      (comparison_stackification_target_hom_presheaf_iso_of_ownerIso (J := J) α x y).hom).app W δ
    = (fibredMorphismPresheafMap G₂ x y).app W δ
  simp only [NatTrans.comp_app, types_comp_apply]
  exact (fibredMorphismPresheafMap_natural_of_ownerIso_app α x y W δ).symm

/-- Helper for Lemma 8.8.1: the `W`-statement for the composite Hom-presheaf map is obtained by
transporting the stackification `W`-statement for `G₂` across the target-side owner isomorphism.
This is the missing owner-iso bridge from the actual stackification data of `G₂` to the direct
comparison triangle. -/
theorem comparison_stackification_composite_presheafMap_W_of_ownerIso
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (G₂ : X ⟶ Y₂)
    (hG₂ : FibredCategoryMor.IsStackification G₂)
    (H : Y₁ ⟶ Y₂)
    (α : G₁ ≫ stack_morphism_toFibredCategoryMor H ≅ G₂)
    {U : C} (x y : X.p.Fiber U) :
    (J.over U).W
      (fibredMorphismPresheafMap (G₁ ≫ stack_morphism_toFibredCategoryMor H) x y) := by
  have hfac :
      fibredMorphismPresheafMap (G₁ ≫ stack_morphism_toFibredCategoryMor H) x y =
        fibredMorphismPresheafMap G₂ x y ≫
          (comparison_stackification_target_hom_presheaf_iso_of_ownerIso
            (J := J) α x y).inv :=
    comparison_stackification_composite_presheafMap_factor_of_ownerIso
      (J := J) α x y
  have hIso :
      MorphismProperty.isomorphisms _
        ((comparison_stackification_target_hom_presheaf_iso_of_ownerIso
          (J := J) α x y).inv) := by
    infer_instance
  -- Rewrite to the factorized shape and transport the known `W`-statement for `G₂` across the
  -- postcomposition by the induced presheaf isomorphism.
  rw [hfac]
  exact
    (((GrothendieckTopology.W (J := J.over U) (A := Type _)).postcomp_iff
      (W' := MorphismProperty.isomorphisms _)
      (fibredMorphismPresheafMap G₂ x y)
      ((comparison_stackification_target_hom_presheaf_iso_of_ownerIso
        (J := J) α x y).inv)
      hIso).2
      (hG₂.morphismPresheafMap_W U x y))

/-- Helper for Lemma 8.8.1: any comparison morphism between two stackifications is locally
essentially surjective on objects. -/
theorem comparison_stack_morphism_locallyEssentiallySurjectiveOnObjects
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (G₂ : X ⟶ Y₂)
    (hG₂ : FibredCategoryMor.IsStackification G₂)
    (H : Y₁ ⟶ Y₂)
    (α : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂) :
    InducedCategory.Hom.LocallyEssentiallySurjectiveOnObjects J H := by
  let αOwner :
      G₁ ≫ stack_morphism_toFibredCategoryMor H ≅ G₂ :=
    comparison_stackification_ownerIsoOfPrecomposeIso (J := J) α
  intro U y
  -- Reuse the local models supplied by `G₂`, and transport them across the compatible
  -- comparison isomorphism from `H ∘ G₁` to `G₂`.
  rcases hG₂.locallyEssentiallySurjectiveOnObjects U y with ⟨S, hS⟩
  refine ⟨S, ?_⟩
  intro I
  rcases hS I with ⟨x, ⟨e₂⟩⟩
  rcases comparison_iso_on_fiber αOwner I.Y x with ⟨eα⟩
  refine ⟨(FibredCategoryMor.fiberFunctor G₁ I.Y).obj x, ?_⟩
  -- The chosen local source object maps under `H` to `G₂ x` up to the fiberwise comparison.
  simpa using ⟨eα ≪≫ e₂⟩

end

end CategoryTheory
