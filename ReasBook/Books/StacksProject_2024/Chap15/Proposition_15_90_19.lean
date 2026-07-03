import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap15.PrincipalIdeal
import StacksProject_2024.Chap15.Theorem_15_90_18

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace FGModuleCat

section CommRing

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

private noncomputable def restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) ≃ₗ[S] S :=
  { __ := AddEquiv.refl S
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower R S ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

private noncomputable def extendScalarsTensorEquiv (M : FGModuleCat R) :
    ↑((ModuleCat.extendScalars (algebraMap R S)).obj M.obj) ≃ₗ[S] TensorProduct R S M.obj :=
  TensorProduct.AlgebraTensorModule.congr
    (restrictScalarsSelfEquiv R S)
    (LinearEquiv.refl R M.obj)

variable {R S}

/-- Extension of scalars on finitely generated modules, obtained by restricting
`ModuleCat.extendScalars` to the canonical owner `FGModuleCat`. -/
noncomputable abbrev extendScalars (f : R →+* S) : FGModuleCat R ⥤ FGModuleCat S :=
  let _ : Algebra R S := f.toAlgebra
  (ModuleCat.isFG S).lift
    ((ModuleCat.isFG R).ι ⋙ ModuleCat.extendScalars f)
    (fun M ↦
      (inferInstance : Module.Finite S (TensorProduct R S M.obj)).equiv
        (by
          simpa using (extendScalarsTensorEquiv R S M)))

omit [Algebra R S] in
@[simp] lemma extendScalars_obj_obj (f : R →+* S) (M : FGModuleCat R) :
    ((extendScalars f).obj M).obj = ((ModuleCat.extendScalars f).obj M.obj) :=
  rfl

omit [Algebra R S] in
@[simp] lemma extendScalars_map_hom (f : R →+* S) {M N : FGModuleCat R} (g : M ⟶ N) :
    ((extendScalars f).map g).hom = (ModuleCat.extendScalars f).map g.hom :=
  rfl

end CommRing

end FGModuleCat

section

variable {R : Type u} [CommRing R] (f : R)

local notation "RHat" => principalAdicCompletion f
local notation "RHatf" => Localization.Away (algebraMap R RHat f)
local notation "Rf" => Localization.Away f
local notation "completionFG" => FGModuleCat.extendScalars (algebraMap R RHat)
local notation "completionOverlapFG" => FGModuleCat.extendScalars (algebraMap RHat RHatf)
local notation "localizationFG" => FGModuleCat.extendScalars (algebraMap R Rf)
local notation "localizationOverlapFG" =>
  FGModuleCat.extendScalars (Localization.awayMap (algebraMap R RHat) f)
local notation "FGGlueCat" =>
  CategoricalPullback
    completionOverlapFG
    localizationOverlapFG

/- Domain-style sampling for 15.90.19:
- primary domain: single-element formal glueing for finitely generated module categories over
  `R`, `R^∧`, `(R^∧)_f`, and `R_f`;
- sampled owner declarations:
  `FGModuleCat`,
  `FGModuleCat.extendScalars`,
  `formalGlueingSingleFunctor`,
  `CategoricalPullback`;
- best owner abstraction:
  the pullback of the finitely generated change-of-rings functors
  `completionOverlapFG` and `localizationOverlapFG`, with
  `formalGlueingSingleFunctor RHat f` used only as the ambient comparison model;
- primitive data:
  the completion ring `RHat`, the localization square
  `R → RHat`, `R → Rf`, `RHat → RHatf`, `Rf → RHatf`, and the canonical owner
  `FGModuleCat.extendScalars` on each edge;
- derived API:
  the formal glueing functor `FGModuleCat R ⥤ FGGlueCat` and the equivalence statement below.

Source/core/bridge triage:
- `source-facing`: `principalAdicFormalGlueingFGFunctor` and
  `principalAdicFormalGlueingFGFunctor_isEquivalence`;
- `core/canonical`: `FGModuleCat`, `FGModuleCat.extendScalars`, and
  `formalGlueingSingleFunctor RHat f`;
- `bridge/view`: the ambient `ModuleCat` formal glueing object used to furnish the comparison
  isomorphism and finiteness witnesses for the pullback object below.
-/

-- Proof sketch: for `M : FGModuleCat R`, the first component of
-- `formalGlueingSingleFunctor RHat f` is extension of scalars
-- `M ⊗[R] R^∧`, and the second component is `M ⊗[R] R_f`. Finite generation is preserved
-- by scalar extension along both `R → R^∧` and `R → R_f`.
/-- The completion component of the single-element formal glueing datum attached to a finitely
generated `R`-module is finitely generated over `R^∧`. -/
theorem principalAdicFormalGlueingSingleFunctor_fst_finite
    (M : FGModuleCat R) :
    Module.Finite RHat (((formalGlueingSingleFunctor RHat f).obj M.obj).fst) := sorry

/-- The localization component of the single-element formal glueing datum attached to a finitely
generated `R`-module is finitely generated over `R_f`. -/
theorem principalAdicFormalGlueingSingleFunctor_snd_finite
    (M : FGModuleCat R) :
    Module.Finite Rf (((formalGlueingSingleFunctor RHat f).obj M.obj).snd) := sorry

/-- The formal glueing functor on finitely generated `R`-modules obtained by restricting the
single-element formal glueing functor for the `f`-adic completion to the pullback
`Mod^{fg}_{R^∧} ×_{Mod^{fg}_{(R^∧)_f}} Mod^{fg}_{R_f}`. -/
noncomputable abbrev principalAdicFormalGlueingFGFunctor :
    FGModuleCat R ⥤ FGGlueCat where
  obj M :=
    let X := (formalGlueingSingleFunctor RHat f).obj M.obj
    CategoricalPullback.mk
      ⟨X.fst, principalAdicFormalGlueingSingleFunctor_fst_finite f M⟩
      ⟨X.snd, principalAdicFormalGlueingSingleFunctor_snd_finite f M⟩
      ((ModuleCat.isFG RHatf).isoMk X.iso)
  map g :=
    let φ := (formalGlueingSingleFunctor RHat f).map g.hom
    CategoricalPullback.Hom.mk
      ((ModuleCat.isFG RHat).homMk φ.fst)
      ((ModuleCat.isFG Rf).homMk φ.snd)
      (by
        apply ObjectProperty.hom_ext
        simpa using φ.w)
  map_id M := by
    ext <;> simp
  map_comp g h := by
    ext <;> simp

-- Proof sketch: the completion map `R → R^∧` is flat for Noetherian `R` by
-- Lemma `10.97.2`, and the quotient map `R / fR → R^∧ / f R^∧` is bijective.
-- Theorem `15.90.18` therefore gives an equivalence for the ambient module categories. The source
-- and target finite-generation conditions are preserved and reflected by the completion and
-- localization functors, so the equivalence restricts to the pullback of the finitely generated
-- module categories.
/-- Proposition 15.90.19: if `R` is Noetherian and `R^∧` is the `f`-adic completion of `R`, then
the functor sending a finitely generated `R`-module `M` to its completion-localization glueing
datum `(M^∧, M_f, can)` defines an equivalence from `Mod^{fg}_R` to the fiber product of the
finitely generated module categories over `R^∧`, `(R^∧)_f`, and `R_f`. -/
theorem principalAdicFormalGlueingFGFunctor_isEquivalence [IsNoetherianRing R] :
    Functor.IsEquivalence (principalAdicFormalGlueingFGFunctor f) := sorry

end
