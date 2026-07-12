import StacksProject_2024.Chap10.Lemma_10_76_1
import StacksProject_2024.Chap15.Lemma_15_31_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open ModuleCat
open MonoidalCategory
open AlgebraicTopology
open scoped TensorProduct

universe u

/-
Domain-style sampling for the base-change statement on the extended alternating Čech complex:
- primary domain: scalar extension of cochain complexes of modules, specialized to extended
  alternating Čech complexes;
- owner-level declarations inspected:
  `extendedAlternatingCechComplex`
  `extendedAlternatingCechComplex_iso_tensorObj`
  `ModuleCat.extendScalars`
  `ModuleCat.extendScalarsTensorLeftNatIso`
  `Functor.mapHomologicalComplex`
  `awayLocalizationFamilyMap`

Best owner abstraction:
- `source-facing`: the extended alternating Čech complex attached to a finite family and a module;
- `core/canonical`: scalar extension via
  `((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (up ℕ)).obj`;
- `bridge/view`: the comparison isomorphism type between the owner over `S` for the image family
  and the scalar extension of the ring specialization `extendedAlternatingCechComplex f R`.

Primitive data is only the family `f`, the algebra `R → S`, and the `R`-module `M`. Degreewise
tensor/localization comparison morphisms are implementation data and should stay in the owner files,
not as a parallel local bridge in this module-valued wrapper. The ring-level base-change
comparison should therefore be exposed as the owner-level companion declaration that the
module-valued comparison reuses.
-/

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {r : ℕ}
variable (f : Fin r → R)
variable (M : Type u) [AddCommGroup M] [Module R M]

local notation "fS" => fun i ↦ algebraMap R S (f i)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace TensorObjComparison

section

variable {R : Type u} [CommRing R]
variable {r : ℕ}
variable (f : Fin r → R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Helper for Lemma 15.29.3: the tensor description of the extended alternating Čech complex from
Lemma `15.29.2`, localized here so this file does not depend on the broken upstream module build. -/
private noncomputable def extendedAlternatingCechComplex_iso_tensorObj :
    extendedAlternatingCechComplex f M ≅
      (((tensorLeft (ModuleCat.of R M)).mapHomologicalComplex (up ℕ)).obj
        (extendedAlternatingCechComplex f R)) :=
  -- TODO: once the earlier owner theorem from `15.29.2` can be imported without rebuilding the
  -- broken dependency chain through `15.31.1`, replace this local placeholder by `simpa using`
  -- that theorem rather than reproving the tensor bridge here.
  sorry

end

end TensorObjComparison

private abbrev extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S :=
  ModuleCat.extendScalars (algebraMap R S)

private abbrev extendScalarsCpx :
    CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat S) ℕ :=
  (extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S).mapHomologicalComplex (up ℕ)

private noncomputable def restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) ≃ₗ[S] S :=
  { __ := AddEquiv.refl S
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower R S ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

private noncomputable def extendScalarsModuleIso
    (N : Type u) [AddCommGroup N] [Module R N] :
    (extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S).obj (ModuleCat.of R N) ≅
      ModuleCat.of S (S ⊗[R] N) := by
  simpa [extendScalarsFunctor, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      restrictScalarsSelfEquiv
      (LinearEquiv.refl R N)).toModuleIso

omit f in
private abbrev ringArrow (f : Fin r → R) :
    Arrow (ModuleCat R) :=
  Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap R f))

omit f in
private abbrev ringArrowBaseChange (f : Fin r → R) :
    Arrow (ModuleCat S) :=
  (extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S).mapArrow.obj (ringArrow f)

omit f in
private abbrev ringArrowS (f : Fin r → R) :
    Arrow (ModuleCat S) :=
  Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap S fun i ↦ algebraMap R S (f i)))

private abbrev extendScalarsCosimplicialFunctor :
    CosimplicialObject (ModuleCat R) ⥤ CosimplicialObject (ModuleCat S) :=
  (CategoryTheory.CosimplicialObject.whiskering (ModuleCat R) (ModuleCat S)).obj
    (extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S)

private noncomputable def extendScalarsRingIso :
    (extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S).obj (ModuleCat.of R R) ≅
      ModuleCat.of S S :=
  extendScalarsModuleIso R ≪≫
    (Algebra.TensorProduct.rid R S S).toLinearEquiv.toModuleIso

omit f in
private noncomputable abbrev extendScalarsAwayFamilyLinearEquiv (f : Fin r → R) :
    S ⊗[R] (∀ i : Fin r, Localization.Away (f i)) ≃ₗ[S]
      ∀ i : Fin r, Localization.Away ((algebraMap R S) (f i)) :=
  (Algebra.TensorProduct.piRight R S S fun i : Fin r ↦ Localization.Away (f i)).toLinearEquiv ≪≫ₗ
    LinearEquiv.piCongrRight fun i : Fin r ↦
      (IsLocalization.Away.tensorEquiv S (f i) (Localization.Away (f i))).toLinearEquiv

omit f in
private noncomputable def extendScalarsAwayFamilyIso
    (f : Fin r → R) :
    (extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S).obj
        (ModuleCat.of R (∀ i : Fin r, Localization.Away (f i))) ≅
      ModuleCat.of S (∀ i : Fin r, Localization.Away ((algebraMap R S) (f i))) :=
  extendScalarsModuleIso (∀ i : Fin r, Localization.Away (f i)) ≪≫
    (extendScalarsAwayFamilyLinearEquiv f).toModuleIso

omit f in
private theorem awayLocalizationFamilyMap_extendScalars (f : Fin r → R) :
    extendScalarsRingIso.inv ≫
        (extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S).map
          (ModuleCat.ofHom (awayLocalizationFamilyMap R f)) ≫
        (extendScalarsAwayFamilyIso f).hom =
      ModuleCat.ofHom (awayLocalizationFamilyMap S fun i ↦ algebraMap R S (f i)) := by
  sorry

omit f in
private noncomputable def ringArrowIso (f : Fin r → R) :
    (ringArrowBaseChange f : Arrow (ModuleCat S)) ≅ ringArrowS f :=
  Arrow.isoMk
    extendScalarsRingIso
    (extendScalarsAwayFamilyIso f)
    (by
      calc
        extendScalarsRingIso.hom ≫
            ModuleCat.ofHom (awayLocalizationFamilyMap S fun i ↦ algebraMap R S (f i)) =
          extendScalarsRingIso.hom ≫
              (extendScalarsRingIso.inv ≫
                (extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S).map
                  (ModuleCat.ofHom (awayLocalizationFamilyMap R f)) ≫
                (extendScalarsAwayFamilyIso f).hom) := by
            rw [awayLocalizationFamilyMap_extendScalars f]
        _ =
            (extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S).map
              (ModuleCat.ofHom (awayLocalizationFamilyMap R f)) ≫
            (extendScalarsAwayFamilyIso f).hom := by
            simp)

omit f in
private noncomputable abbrev extendScalarsCechConerveComponent
    (f : Fin r → R) (n : SimplexCategory) :
    ((ringArrowBaseChange f : Arrow (ModuleCat S)).cechConerve).obj n ≅
      (extendScalarsCosimplicialFunctor.obj ((ringArrow f : Arrow (ModuleCat R)).cechConerve)).obj n :=
  (HasColimit.isoOfNatIso
      (WidePushoutShape.diagramIsoWideSpan
        ((WidePushoutShape.wideSpan (ringArrow f).left
          (fun _ : Fin (n.len + 1) ↦ (ringArrow f).right)
          fun _ ↦ (ringArrow f).hom) ⋙
          (extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S)))).symm ≪≫
    (preservesColimitIso (extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S)
      (WidePushoutShape.wideSpan (ringArrow f).left
        (fun _ : Fin (n.len + 1) ↦ (ringArrow f).right)
        fun _ ↦ (ringArrow f).hom)).symm

omit f in
private noncomputable def extendScalarsCechConerveIso (f : Fin r → R) :
    (ringArrowBaseChange f : Arrow (ModuleCat S)).cechConerve ≅
      extendScalarsCosimplicialFunctor.obj ((ringArrow f : Arrow (ModuleCat R)).cechConerve) :=
  sorry

private theorem extendScalars_alternatingCofaceMapComplex :
    alternatingCofaceMapComplex (ModuleCat R) ⋙
        (extendScalarsCpx : CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat S) ℕ) =
      extendScalarsCosimplicialFunctor ⋙
        alternatingCofaceMapComplex (ModuleCat S) := by
  -- TODO: this should be the coface-map analogue of mathlib's
  -- `map_alternatingFaceMapComplex`. The current direct `Functor.ext` proof times out during
  -- definitional reduction of the composed functors, so the next pass should isolate the object
  -- equality and the degreewise differential equality into explicit rewrite lemmas first.
  sorry

omit f in
private noncomputable abbrev ordinaryRingIso (f : Fin r → R) :
    alternatingCechComplex (fun i ↦ algebraMap R S (f i)) S ≅
      (extendScalarsCpx : CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat S) ℕ).obj
        (alternatingCechComplex f R) :=
  (alternatingCofaceMapComplex (ModuleCat S)).mapIso
      (((CategoryTheory.CosimplicialObject.cechConerve :
          Arrow (ModuleCat.{u} S) ⥤ CosimplicialObject (ModuleCat.{u} S)).mapIso
        (ringArrowIso f).symm) ≪≫
        extendScalarsCechConerveIso f) ≪≫
    (eqToIso
      (Functor.congr_obj
        extendScalars_alternatingCofaceMapComplex
        ((ringArrow f).cechConerve))).symm

omit f in
private noncomputable def ringExtendedComponentIso (f : Fin r → R) (i : ℕ) :
    (extendedAlternatingCechComplex (fun i ↦ algebraMap R S (f i)) S).X i ≅
      ((extendScalarsCpx : CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat S) ℕ).obj
        (extendedAlternatingCechComplex f R)).X i :=
  match i with
  | 0 => by
      simpa [extendedAlternatingCechComplex] using
        extendScalarsRingIso.symm
  | n + 1 => by
      simpa [extendedAlternatingCechComplex] using
        (HomologicalComplex.eval (ModuleCat S) (up ℕ) n).mapIso
          (ordinaryRingIso f)

omit f in
private theorem ring_extendedAlternatingCechComplex_iso_extendScalars_hom_comm
    (f : Fin r → R) :
    ∀ i j,
      (ComplexShape.up ℕ).Rel i j →
        (ringExtendedComponentIso f i).hom ≫
            ((extendScalarsCpx : CochainComplex (ModuleCat R) ℕ ⥤
                CochainComplex (ModuleCat S) ℕ).obj
              (extendedAlternatingCechComplex f R)).d i j =
          (extendedAlternatingCechComplex (fun i ↦ algebraMap R S (f i)) S).d i j ≫
            (ringExtendedComponentIso f j).hom := by
  sorry

-- Proof sketch: the ring-valued extended alternating Čech complex admits a canonical base-change
-- comparison isomorphism. The module-valued comparison below factors through this owner-level
-- ring specialization together with the tensor-description bridge from `15.29.2`.
/-- The ring-valued base-change comparison for the extended alternating Čech complex. -/
noncomputable def ring_extendedAlternatingCechComplex_iso_extendScalars :
    extendedAlternatingCechComplex fS S ≅
      (extendScalarsCpx : CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat S) ℕ).obj
        (extendedAlternatingCechComplex f R) :=
  HomologicalComplex.Hom.isoOfComponents
    (ringExtendedComponentIso f)
    (ring_extendedAlternatingCechComplex_iso_extendScalars_hom_comm f)

private def tensorExtendScalars_mapHomologicalComplex_obj_iso
    (K : CochainComplex (ModuleCat R) ℕ) :
    ((Functor.mapHomologicalComplex
        (tensorLeft ((extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S).obj (ModuleCat.of R M)))
        (up ℕ) : CochainComplex (ModuleCat S) ℕ ⥤ CochainComplex (ModuleCat S) ℕ).obj
      ((extendScalarsCpx : CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat S) ℕ).obj
        K)) ≅
      ((Functor.mapHomologicalComplex
          ((extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S) ⋙
            tensorLeft
              ((extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S).obj (ModuleCat.of R M)))
          (up ℕ)).obj K) :=
  eqToIso rfl

private def extendScalarsTensor_mapHomologicalComplex_obj_iso
    (K : CochainComplex (ModuleCat R) ℕ) :
    ((Functor.mapHomologicalComplex
        (tensorLeft (ModuleCat.of R M) ⋙ (extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S))
        (up ℕ)).obj K) ≅
      ((extendScalarsCpx : CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat S) ℕ).obj
        (((tensorLeft (ModuleCat.of R M)).mapHomologicalComplex (up ℕ)).obj K)) :=
  eqToIso rfl

/-- Helper for Lemma 15.29.3: after base-changing a cochain complex, tensoring by the extended
module `S ⊗[R] M` agrees with first tensoring by `M` over `R` and then extending scalars. -/
private noncomputable def tensor_extendScalars_reassociation_iso
    (K : CochainComplex (ModuleCat R) ℕ) :
    ((Functor.mapHomologicalComplex
        (tensorLeft (ModuleCat.of S (S ⊗[R] M)))
        (up ℕ)).obj
      ((extendScalarsCpx : CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat S) ℕ).obj
        K)) ≅
      ((extendScalarsCpx : CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat S) ℕ).obj
        (((tensorLeft (ModuleCat.of R M)).mapHomologicalComplex (up ℕ)).obj K)) :=
  let tensorLeftIso :
      tensorLeft ((extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S).obj (ModuleCat.of R M)) ≅
        tensorLeft (ModuleCat.of S (S ⊗[R] M)) :=
    (tensoringLeft (ModuleCat S)).mapIso (extendScalarsModuleIso M)
  let tensorCommIso :
      tensorLeft (ModuleCat.of R M) ⋙ (extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S) ≅
        (extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S) ⋙
          tensorLeft ((extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S).obj (ModuleCat.of R M)) :=
    ModuleCat.extendScalarsTensorLeftNatIso (algebraMap R S) (ModuleCat.of R M)
  let tensorCommCpxIso :
      (Functor.mapHomologicalComplex
          ((extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S) ⋙
            tensorLeft
              ((extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S).obj (ModuleCat.of R M)))
          (ComplexShape.up ℕ)).obj K ≅
        (Functor.mapHomologicalComplex
          (tensorLeft (ModuleCat.of R M) ⋙ (extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S))
          (ComplexShape.up ℕ)).obj K :=
    ((NatIso.mapHomologicalComplex tensorCommIso (ComplexShape.up ℕ)).app K).symm
  -- First replace the tensor-left object by the canonical base-changed module.
  ((NatIso.mapHomologicalComplex tensorLeftIso (up ℕ)).app
      ((extendScalarsCpx : CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat S) ℕ).obj
        K)).symm ≪≫
    -- Then commute extension of scalars past tensoring before identifying the underlying object.
    (tensorExtendScalars_mapHomologicalComplex_obj_iso M K) ≪≫
    tensorCommCpxIso ≪≫
    (extendScalarsTensor_mapHomologicalComplex_obj_iso M K)

-- Proof sketch: base change identifies each term in the extended alternating Čech complex of `M`
-- with the corresponding term for `S ⊗[R] M` and the image family `algebraMap R S ∘ f` by
-- composing the owner-level ring base-change bridge with the tensor-description bridge.
/-- Lemma 15.29.3: for a ring map `R → S`, the extended alternating Čech complex over `S`
attached to `algebraMap R S ∘ f` and `S ⊗[R] M` is isomorphic to the scalar extension of the
extended alternating Čech complex over `R` attached to `f` and `M`. This file exposes the
canonical comparison isomorphism itself, rather than only an existential wrapper around it. -/
@[stacks 0G6I]
noncomputable def extendedAlternatingCechComplex_iso_extendScalars :
    extendedAlternatingCechComplex fS (S ⊗[R] M) ≅
      (extendScalarsCpx : CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat S) ℕ).obj
        (extendedAlternatingCechComplex f M) :=
  let ringCech : CochainComplex (ModuleCat R) ℕ := extendedAlternatingCechComplex f R
  let TensorS₀ : CochainComplex (ModuleCat S) ℕ ⥤ CochainComplex (ModuleCat S) ℕ :=
    ((tensorLeft (of S (S ⊗[R] M))).mapHomologicalComplex (up ℕ) :
      CochainComplex (ModuleCat S) ℕ ⥤ CochainComplex (ModuleCat S) ℕ)
  let tensorExtIso :
      extendedAlternatingCechComplex f M ≅
        (((tensorLeft (ModuleCat.of R M)).mapHomologicalComplex (up ℕ)).obj ringCech) :=
    TensorObjComparison.extendedAlternatingCechComplex_iso_tensorObj f M
  -- Route correction: keep the source proof's architecture explicit by composing
  -- tensor-description over `S`, ring-level base change, and then the tensor/base-change
  -- reassociation as one named bridge before returning to the module-valued owner over `R`.
  (TensorObjComparison.extendedAlternatingCechComplex_iso_tensorObj fS (S ⊗[R] M)) ≪≫
    (TensorS₀.mapIso (ring_extendedAlternatingCechComplex_iso_extendScalars f)) ≪≫
    (tensor_extendScalars_reassociation_iso (R := R) (S := S) (M := M) ringCech) ≪≫
    ((extendScalarsCpx : CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat S) ℕ).mapIso
      tensorExtIso).symm

end
