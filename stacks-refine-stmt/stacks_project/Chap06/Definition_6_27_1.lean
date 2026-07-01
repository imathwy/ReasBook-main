import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap06.Definition_6_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace Opposite
open scoped AlgebraicGeometry

attribute [local instance] Classical.propDecidable

universe u v w

section

variable {X : TopCat.{u}}
variable {C : Type v} [CategoryTheory.Category C] [CategoryTheory.Limits.HasTerminal C]

/- Domain-style sampling for Definition 6.27.1:
- primary domain: skyscraper sheaves on topological spaces and pushforward of module sheaves along
  morphisms of ringed spaces;
- sampled owner declarations:
  `TopCat.skyscraperSheaf`,
  `TopCat.stalkSkyscraperSheafAdjunction`,
  `AlgebraicGeometry.RingedSpace.Hom.pushforward`,
  `SheafOfModules.pushforward`;
- owner abstraction: `skyscraperSheaf` on the sheaf side and
  `((pointInclusion x) _*).obj` on the module-sheaf side;
- source/core/bridge triage:
  `source-facing`: the point ringed space `({x}, \mathcal O_{X, x})`, its inclusion `i_x`, and the
    skyscraper module sheaf `i_{x, *} M`;
  `core/canonical`: `skyscraperSheaf` and `RingedSpace.Hom.pushforward`;
  `bridge/view`: the concrete realization of `({x}, \mathcal O_{X, x})` on `TopCat.of PUnit`.

Primitive data are only the point `x`, the value `A`, and the stalk module `M`. The one-point
space, its unique point, and the auxiliary skyscraper sheaf on that space are implementation
choices, not separate owners, so the file should use the canonical declarations directly instead of
introducing parallel aliases.
-/

/- Definition 6.27.1 (1)–(3): for a point `x : X` and a value `A`, the skyscraper sheaf at `x`
with value `A` is the canonical mathlib sheaf `skyscraperSheaf x A`. In the classical Stacks
Project cases, `A` may be a set, an abelian group, or another algebraic structure. -/
recall skyscraperSheaf

/-- A sheaf is a skyscraper sheaf if it is isomorphic to `skyscraperSheaf x A` for some point
`x` and some value `A`. -/
def IsSkyscraperSheaf (ℱ : TopCat.Sheaf C X) : Prop :=
  ∃ (x : X) (A : C), IsIsomorphic ℱ (skyscraperSheaf x A)

@[simp] theorem isSkyscraperSheaf_skyscraperSheaf (x : X) (A : C) :
    IsSkyscraperSheaf (skyscraperSheaf x A) :=
  ⟨x, A, ⟨Iso.refl _⟩⟩

end

namespace AlgebraicGeometry

section

variable {X : RingedSpace.{u}}

open CategoryTheory.Limits

private noncomputable def pointInclusionPresheafMap (x : X) :
    X.presheaf ⟶
      (ofHom (ContinuousMap.const (TopCat.of PUnit) x)) _*
        (skyscraperSheaf PUnit.unit (X.presheaf.stalk x)).obj :=
  ((stalkSkyscraperSheafAdjunction x).unit.app X.sheaf).hom ≫
    eqToHom (skyscraperPresheaf_eq_pushforward x (X.presheaf.stalk x))

/-- The one-point ringed space `({x}, \mathcal O_{X, x})`, modeled on `TopCat.of PUnit` with
structure sheaf the skyscraper sheaf at its unique point valued in `\mathcal O_{X, x}`. -/
noncomputable def pointRingedSpace (x : X) : RingedSpace :=
  let pointSheaf := skyscraperSheaf PUnit.unit (X.presheaf.stalk x)
  { carrier := TopCat.of PUnit
    presheaf := pointSheaf.obj
    IsSheaf := pointSheaf.property }

/-- Definition 6.27.1 (1): the canonical morphism of ringed spaces
`i_x : ({x}, \mathcal O_{X, x}) \to (X, \mathcal O_X)`. -/
noncomputable def pointInclusion (x : X) : pointRingedSpace x ⟶ X :=
  InducedCategory.homMk
    { base := ofHom (ContinuousMap.const (TopCat.of PUnit) x)
      c := pointInclusionPresheafMap x }

-- Proof sketch: unfold `pointInclusion`; the induced-category morphism was defined by the
-- constant base map together with the presheaf morphism `pointInclusionPresheafMap x`.
/-- Unfolding `pointInclusion` identifies its underlying morphism of presheafed spaces. -/
theorem pointInclusion_def (x : X) :
    (pointInclusion x).hom =
      { base := ofHom (ContinuousMap.const (TopCat.of PUnit) x)
        c := pointInclusionPresheafMap x } := sorry

-- Proof sketch: unfold `pointInclusion`; the induced-category morphism was defined with base map
-- `ContinuousMap.const (TopCat.of PUnit) x`, so the underlying continuous map is definitionally
-- that constant map.
/-- The underlying continuous map of `pointInclusion x` is the constant map to `x`. -/
@[simp] theorem pointInclusion_hom_base (x : X) :
    (pointInclusion x).hom.base = ofHom (ContinuousMap.const (TopCat.of PUnit) x) := sorry

-- Proof sketch: apply `pointInclusion_hom_base` and evaluate the resulting equality of continuous
-- maps at the unique point `PUnit.unit`.
/-- Evaluating `pointInclusion x` at the unique point of `({x}, \mathcal O_{X, x})` returns `x`. -/
@[simp] theorem pointInclusion_hom_base_apply (x : X) :
    (pointInclusion x).hom.base PUnit.unit = x := sorry

private theorem pointOpen_eq_top {U : Opens (TopCat.of PUnit)} (h : PUnit.unit ∈ U) :
    U = ⊤ := by
  ext y
  cases y
  simp [h]

private theorem pointOpen_eq_bot {U : Opens (TopCat.of PUnit)} (h : PUnit.unit ∉ U) :
    U = ⊥ := by
  ext y
  cases y
  constructor
  · intro hy
    exact (h hy).elim
  · intro hy
    exact False.elim hy

private noncomputable abbrev pointRingCatSheaf (x : X) :=
  RingedSpace.ringCatSheaf (pointRingedSpace x)

theorem pointRingedSpace_ringCatSheaf_obj_top (x : X) :
    (RingedSpace.ringCatSheaf (pointRingedSpace x)).obj.obj (op ⊤) =
      RingCat.of (X.presheaf.stalk x) := by
  let pointSheaf : Sheaf CommRingCat (TopCat.of PUnit) :=
    skyscraperSheaf PUnit.unit (X.presheaf.stalk x)
  change
    (forget₂ CommRingCat RingCat).obj
        (pointSheaf.obj.obj
          (op ⊤)) =
      RingCat.of (X.presheaf.stalk x)
  simp [pointSheaf, skyscraperSheaf, skyscraperPresheaf]
  rfl

private noncomputable def pointModulePresheafObj
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    (U : (Opens (TopCat.of PUnit))ᵒᵖ) →
    ModuleCat.{u} ((pointRingCatSheaf x).obj.obj U) :=
  fun U ↦ by
    by_cases hU : PUnit.unit ∈ unop U
    · have hU' : U = op ⊤ := by
        simpa using congrArg op (pointOpen_eq_top hU)
      subst hU'
      exact
        (ModuleCat.restrictScalars (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom).obj M
    · exact ⊤_ ModuleCat.{u} ((pointRingCatSheaf x).obj.obj U)

private noncomputable def pointModulePresheaf
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    PresheafOfModules.{u} (pointRingCatSheaf x).obj where
  obj := pointModulePresheafObj x M
  map {U V} i := by
    by_cases hV : PUnit.unit ∈ unop V
    · have hU : PUnit.unit ∈ unop U := i.unop.le hV
      have hU' : U = op ⊤ := by
        simpa using congrArg op (pointOpen_eq_top hU)
      have hV' : V = op ⊤ := by
        simpa using congrArg op (pointOpen_eq_top hV)
      subst hU'
      subst hV'
      have hi : i = 𝟙 (op ⊤) := Subsingleton.elim _ _
      exact
        (ModuleCat.restrictScalarsId'App
          ((pointRingCatSheaf x).obj.map i).hom
          (by
            subst hi
            exact congrArg RingCat.Hom.hom
              ((pointRingCatSheaf x).obj.map_id (op ⊤)))
          (pointModulePresheafObj x M (op ⊤))).inv
    · simpa [pointModulePresheafObj, hV] using
        (0 :
          pointModulePresheafObj x M U ⟶
            (ModuleCat.restrictScalars
              ((pointRingCatSheaf x).obj.map i).hom).obj
                (pointModulePresheafObj x M V))
  map_id := by
    intro U
    sorry
  map_comp := by
    intro U V W i j
    sorry

noncomputable def pointModuleSheaf
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    SheafOfModules.{u} (RingedSpace.ringCatSheaf (pointRingedSpace x)) where
  val := pointModulePresheaf x M
  isSheaf := by
    sorry

/-- The value of `pointModuleSheaf x M` on the top open is the module `M`, viewed through the
canonical identification of the top ring of `({x}, \mathcal O_{X, x})` with `\mathcal O_{X, x}`.
-/
noncomputable def pointModuleSheaf_objTopIso
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    (pointModuleSheaf x M).val.obj (op (⊤ : Opens (TopCat.of PUnit))) ≅
      (ModuleCat.restrictScalars
        (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom).obj M := by
  refine eqToIso ?_
  sorry

/-
On the one-point ringed space `({x}, \mathcal O_{X, x})`, a morphism into the point module sheaf
`pointModuleSheaf x M` is determined by its component on the top open.
-/
noncomputable def pointModuleSheaf_homEquivTop
    (x : X) (G : RingedSpace.Modules (pointRingedSpace x))
    (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    (G ⟶ pointModuleSheaf x M) ≃
      (G.val.obj (op (⊤ : Opens (TopCat.of PUnit))) ⟶ (pointModuleSheaf x M).val.obj (op ⊤)) where
  toFun f := f.val.app (op ⊤)
  invFun φ :=
    { val :=
        { app := fun U ↦ by
            by_cases hU : PUnit.unit ∈ unop U
            · have hU' : U = op ⊤ := by
                simpa using congrArg op (pointOpen_eq_top hU)
              subst hU'
              exact φ
            · exact 0
          naturality := by
            sorry } }
  left_inv f := by
    sorry
  right_inv φ := by
    sorry

/-- Definition 6.27.1 (2): for a point `x : X` and an `\mathcal O_{X, x}`-module `M`,
`skyscraperModuleSheaf x M` is the canonical pushforward `i_{x, *} M` along the inclusion
`i_x : ({x}, \mathcal O_{X, x}) \to (X, \mathcal O_X)`. -/
noncomputable def skyscraperModuleSheaf
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    SheafOfModules.{u} ((RingedSpace.ringCatSheaf X)) :=
  ((pointInclusion x) _*).obj (pointModuleSheaf x M)

/-- Definition 6.27.1 (3): an `\mathcal O_X`-module sheaf is a skyscraper module sheaf if it is
isomorphic to `i_{x, *} M` for some point `x : X` and some `\mathcal O_{X, x}`-module `M`. -/
def IsSkyscraperModuleSheaf
    (ℱ : SheafOfModules.{u} ((RingedSpace.ringCatSheaf X))) : Prop :=
  ∃ (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))),
    IsIsomorphic ℱ (skyscraperModuleSheaf x M)

/-- The canonical skyscraper module sheaf `i_{x, *} M` is a skyscraper module sheaf. -/
theorem isSkyscraperModuleSheaf_skyscraperModuleSheaf
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    IsSkyscraperModuleSheaf (skyscraperModuleSheaf x M) :=
  ⟨x, M, ⟨Iso.refl _⟩⟩

end

end AlgebraicGeometry
