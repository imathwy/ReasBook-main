import Mathlib
import StacksProject_2024.Chap15.Definition_15_75_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Helper for Lemma 15.75.10: the fixed scalar-extension functor along `A → B`. -/
private abbrev ExtMod : ModuleCat.{u} A ⥤ ModuleCat.{u} B :=
  ModuleCat.extendScalars.{u, u, u} (algebraMap A B)

/-- Helper for Lemma 15.75.10: the degree-zero embedding into `D(A)`. -/
private abbrev single₀A : ModuleCat.{u} A ⥤ DerivedCategory (ModuleCat.{u} A) :=
  DerivedCategory.singleFunctor (ModuleCat.{u} A) (0 : ℤ)

/-- Helper for Lemma 15.75.10: the degree-zero embedding into `D(B)`. -/
private abbrev single₀B : ModuleCat.{u} B ⥤ DerivedCategory (ModuleCat.{u} B) :=
  DerivedCategory.singleFunctor (ModuleCat.{u} B) (0 : ℤ)

local notation "Ext" => ExtMod (A := A) (B := B)

/- Domain-style sampling for Lemma 15.75.10:
- primary domain: perfect modules viewed in degree `0` inside derived module categories and then
  transported across flat scalar extension;
- sampled owner declarations:
  `ModuleCat.IsPerfect`,
  `DerivedCategory.IsPerfect`,
  `CochainComplex.IsBoundedFiniteProjective`,
  `ModuleCat.extendScalars`;
- best owner abstraction: this file is a `bridge/view`; the source-facing module statement should
  keep `ModuleCat.IsPerfect` as the owner, but the proof should proceed by transporting the
  bounded finite-projective witness complex from Definition `15.75.1` through exact flat scalar
  extension;
- primitive vs. derived:
  primitive data are the flat map `A → B`, the module `M`, and a bounded finite-projective
  complex representing `M[0]`;
  the derived API needed here is the exact functor `Ext.mapDerivedCategory` on that witness,
  together with the degree-zero comparison for scalar extension;
- source/core/bridge triage:
  `source-facing`: perfectness is preserved by flat scalar extension for modules;
  `core/canonical`: `DerivedCategory.IsPerfect` and
    `CochainComplex.IsBoundedFiniteProjective`;
  `bridge/view`: exact scalar extension on complexes and the degree-zero comparison
    for `ModuleCat.extendScalars`. -/

-- Route correction: instead of importing the later derived-base-change theorem, transport the
-- bounded finite-projective witness from the definition of `ModuleCat.IsPerfect` through exact
-- flat scalar extension and then compare exact scalar extension on `M[0]` with `(M ⊗_A B)[0]`.

/-- Helper for Lemma 15.75.10: ordinary scalar extension is additive. -/
local instance extendScalars_additive :
    (ExtMod (A := A) (B := B)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).left_adjoint_additive

/-- Helper for Lemma 15.75.10: flat scalar extension preserves finite limits, so it acts exactly
on the derived category. -/
local instance extendScalars_preservesFiniteLimits [Module.Flat A B] :
    Limits.PreservesFiniteLimits (ExtMod (A := A) (B := B)) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr (show Module.Flat A B from inferInstance))

/-- Helper for Lemma 15.75.10: after restricting scalars, the regular `B`-module is canonically
itself. -/
private noncomputable abbrev restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ≃ₗ[B] B :=
  { __ := AddEquiv.refl B
    map_smul' := fun _ _ ↦ rfl }

/-- Helper for Lemma 15.75.10: the restricted scalar action on `B` still forms the expected
scalar tower over `A`. -/
private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower A B ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Lemma 15.75.10: scalar extension in `ModuleCat` is canonically the tensor-product
module. -/
private noncomputable def extendScalars_tensor_module_iso
    (M : ModuleCat A) :
    ((ExtMod (A := A) (B := B)).obj M) ≅ ModuleCat.of B (TensorProduct A B (M : Type u)) := by
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      restrictScalarsSelfEquiv
      (LinearEquiv.refl A (M : Type u))).toModuleIso

/-- Helper for Lemma 15.75.10: exact scalar extension carries `M[0]` to the degree-zero complex
of `M ⊗_A B`. -/
private noncomputable def extendScalars_single0_iso [Module.Flat A B]
    (M : ModuleCat A) :
    ((ExtMod (A := A) (B := B)).mapDerivedCategory.obj (single₀A.obj M)) ≅
      single₀B.obj ((Ext).obj M) :=
  ((ExtMod (A := A) (B := B)).mapDerivedCategory.mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app M)) ≪≫
    (ExtMod (A := A) (B := B)).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M) ≪≫
    DerivedCategory.Q.mapIso
      ((CategoryTheory.Functor.mapCochainComplexSingleFunctor Ext (0 : ℤ)).app M) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat B) (0 : ℤ)).app ((Ext).obj M)).symm

/-- Helper for Lemma 15.75.10: exact flat scalar extension carries a bounded finite-projective
complex of `A`-modules to a bounded finite-projective complex of `B`-modules. -/
private theorem isBoundedFiniteProjective_mapExtendScalars
    [Module.Flat A B] (L : CochainComplex (ModuleCat A) ℤ)
    [hL : CochainComplex.IsBoundedFiniteProjective L] :
    CochainComplex.IsBoundedFiniteProjective
      (((Ext).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) := by
  rcases hL.bounded with ⟨a, b, hGE, hLE⟩
  refine ⟨⟨a, b, ?_, ?_⟩, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff] at hGE ⊢
    intro i hi
    simpa [CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
      Functor.map_isZero Ext (hGE i hi)
  · rw [CochainComplex.isStrictlyLE_iff] at hLE ⊢
    intro i hi
    simpa [CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
      Functor.map_isZero Ext (hLE i hi)
  · intro i
    let e := extendScalars_tensor_module_iso (A := A) (B := B) (L.X i)
    letI : Module.Finite B (TensorProduct A B ((L.X i : ModuleCat A) : Type u)) :=
      Module.Finite.base_change (R := A) (A := B) (M := L.X i)
    exact Module.Finite.equiv e.toLinearEquiv.symm
  · intro i
    let e := extendScalars_tensor_module_iso (A := A) (B := B) (L.X i)
    letI : Module.Projective B (TensorProduct A B ((L.X i : ModuleCat A) : Type u)) :=
      Module.Projective.tensorProduct
    exact Module.Projective.of_equiv e.toLinearEquiv.symm

/-- Lemma 15.75.10: for a flat ring map `A → B`, the base change of a perfect `A`-module is a
perfect `B`-module. This is the module-level bridge/view of Lemma `15.75.9`. -/
@[stacks 066X]
theorem isPerfect_extendScalars
    (hflat : (algebraMap A B).Flat) (M : ModuleCat.{u} A) (hM : M.IsPerfect) :
    ((Ext).obj M).IsPerfect := by
  letI : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hflat
  rcases hM with ⟨L, e, hL⟩
  let Lbase : CochainComplex (ModuleCat B) ℤ :=
    ((Ext).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  have hLbase : CochainComplex.IsBoundedFiniteProjective Lbase := by
    -- Proof comment: exact flat scalar extension preserves the bounded support and finite
    -- projective terms of the chosen representative.
    simpa [Lbase] using
      (isBoundedFiniteProjective_mapExtendScalars (A := A) (B := B) L)
  refine ⟨Lbase, ?_, hLbase⟩
  -- Proof comment: apply exact scalar extension to the witness `M[0] ≅ Q.obj L`, then identify
  -- exact scalar extension of `M[0]` with `(M ⊗_A B)[0]`.
  exact
    (extendScalars_single0_iso (A := A) (B := B) M).symm ≪≫
      ((Ext).mapDerivedCategory.mapIso e) ≪≫
      ((Ext).mapDerivedCategoryFactors.app L)

end

end CategoryTheory
