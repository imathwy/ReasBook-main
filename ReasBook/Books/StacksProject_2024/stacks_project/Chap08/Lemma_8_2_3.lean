import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_33_9
import StacksProject_2024.stacks_project.Chap04.Lemma_4_35_9
import StacksProject_2024.stacks_project.Chap08.Definition_8_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite

universe u v

namespace CategoryTheory

open Functor IsStronglyCartesian FibredCategoryMor

variable {C : Type u} [Category.{v} C]

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

/-- A morphism of fibred categories sends a strongly cartesian lift over `f` to a strongly
cartesian lift over the same base arrow `f`. -/
private theorem map_stronglyCartesian_of_lift
    (F : X ⟶ Y) {a b : X.S} {U V : C} (f : V ⟶ U) (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian f φ) :
    Y.p.IsStronglyCartesian f (F.toHom.map φ) := by
  letI : X.p.IsHomLift f φ := hφ.toIsHomLift
  have hφ' : X.p.IsStronglyCartesian (X.p.map φ) φ := by
    subst_hom_lift X.p f φ
    simpa using hφ
  letI : Y.p.IsHomLift f (F.toHom.map φ) := by
    infer_instance
  have hY :
      Y.p.IsStronglyCartesian (Y.p.map (F.toHom.map φ)) (F.toHom.map φ) :=
    map_stronglyCartesian F φ hφ'
  subst_hom_lift Y.p f (F.toHom.map φ)
  exact hY

/-- The canonical comparison isomorphism in the fiber over the domain of `f`,
`f^* F(x) ≅ F(f^* x)`. -/
noncomputable def FibredCategoryMor.pullbackComparison
    (F : X ⟶ Y) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    f ^*[canonicalPullbackChoice Y.p] ((F.toHom).fiberFunctor U).obj x ≅
      ((F.toHom).fiberFunctor V).obj (f ^*[canonicalPullbackChoice X.p] x) := by
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
    domainIsoOfBaseIso Y.p hf φ ψ
  letI : Y.p.IsHomLift (𝟙 V) e.hom := by
    change Y.p.IsHomLift (Iso.refl V).hom e.hom
    exact domainUniqueUpToIso_inv_isHomLift Y.p hf φ ψ
  letI : Y.p.IsHomLift (𝟙 V) e.inv := by
    change Y.p.IsHomLift (Iso.refl V).inv e.inv
    exact domainUniqueUpToIso_hom_isHomLift Y.p hf φ ψ
  refine
    { hom := Functor.Fiber.homMk Y.p V e.hom
      inv := Functor.Fiber.homMk Y.p V e.inv
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        change e.hom ≫ e.inv = 𝟙 _
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        change e.inv ≫ e.hom = 𝟙 _
        exact e.inv_hom_id }

/-- The component at `f : V ⟶ U` of the morphism on canonical Hom-presheaves induced by `F`. -/
private noncomputable def fibredMorphismPresheafMapApp
    (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U) (f : (Over U)ᵒᵖ) :
    ((canonicalFiberPseudofunctor X.p).presheafHom x y).obj f →
      ((canonicalFiberPseudofunctor Y.p).presheafHom
        (((F.toHom).fiberFunctor U).obj x)
        (((F.toHom).fiberFunctor U).obj y)).obj f :=
  fun φ ↦
    (pullbackComparison F f.unop.hom x).hom ≫
      ((F.toHom).fiberFunctor f.unop.left).map φ ≫
        (pullbackComparison F f.unop.hom y).inv

/-- The componentwise maps induced by `F` are natural in objects of the slice category `C/U`. -/
private theorem fibredMorphismPresheafMap_naturality
    (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U)
    {f g : (Over U)ᵒᵖ} (α : f ⟶ g) :
    ((canonicalFiberPseudofunctor X.p).presheafHom x y).map α ≫
      fibredMorphismPresheafMapApp F x y g =
      fibredMorphismPresheafMapApp F x y f ≫
        ((canonicalFiberPseudofunctor Y.p).presheafHom
          (((F.toHom).fiberFunctor U).obj x)
          (((F.toHom).fiberFunctor U).obj y)).map α := sorry

/-- Lemma 8.2.3: a `1`-morphism of fibred categories over `C` induces the canonical morphism of
presheaves `Mor_{S₁}(x, y) ⟶ Mor_{S₂}(F(x), F(y))` on the slice category `C/U`. The source and
target are stated using the canonical Hom-presheaves from Definition `8.2.2`. -/
noncomputable def FibredCategoryMor.fibredMorphismPresheafMap
    (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U) :
    (canonicalFiberPseudofunctor X.p).presheafHom x y ⟶
      (canonicalFiberPseudofunctor Y.p).presheafHom
        (((F.toHom).fiberFunctor U).obj x)
        (((F.toHom).fiberFunctor U).obj y) where
  app f := fibredMorphismPresheafMapApp F x y f
  naturality := fun {_ _} α ↦ fibredMorphismPresheafMap_naturality F x y α

/-- At the identity object of `C/U`, the canonical Hom-presheaf map induced by `F` agrees with
the usual map on fibre morphisms after transporting through the standard equivalences
`presheafHomObjHomEquiv`. -/
theorem FibredCategoryMor.fibredMorphismPresheafMap_app_id
    (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U) (φ : x ⟶ y) :
    (fibredMorphismPresheafMap F x y).app (op (Over.mk (𝟙 U)))
      ((canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv φ) =
        (canonicalFiberPseudofunctor Y.p).presheafHomObjHomEquiv
          (((F.toHom).fiberFunctor U).map φ) := by
  sorry

/-- If a `1`-morphism of fibred categories over `C` is fully faithful, then the
canonical morphism of Hom-presheaves from Lemma `8.2.3` is an isomorphism. -/
theorem FibredCategoryMor.fibredMorphismPresheafMap_isIso_of_fullyFaithful
    (F : X ⟶ Y) (hF : Nonempty F.toHom.FullyFaithful)
    {U : C} (x y : X.p.Fiber U) :
    IsIso (fibredMorphismPresheafMap F x y) := by
  sorry

end CategoryTheory
