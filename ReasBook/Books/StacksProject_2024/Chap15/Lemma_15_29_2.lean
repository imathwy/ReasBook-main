import Mathlib.CategoryTheory.CommSq
import StacksProject_2024.Chap15.Lemma_15_29_1
import StacksProject_2024.Chap15.Lemma_15_31_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open ModuleCat
open MonoidalCategory
open AlgebraicTopology
open LocalizedModule
open Opposite
open scoped TensorProduct

/-
Domain-style sampling for the tensor description of the extended alternating Čech complex:
- owner abstractions inspected:
  `extendedAlternatingCechComplex`
  `alternatingCechComplex`
  `awayLocalizationFamilyMap`
  `CochainComplex.fromSingle₀AsComplex`
  `alternatingCofaceMapComplex`
  `Functor.mapHomologicalComplex`

Layer triage:
- `source-facing`: Lemma `15.29.2` identifies the module-valued extended alternating Čech complex
  with the result of tensoring the ring-valued extended alternating Čech complex by the module.
- `core/canonical`: degreewise tensoring of cochain complexes via
  `((tensorLeft (ModuleCat.of R M)).mapHomologicalComplex (ComplexShape.up ℕ)).obj`.
- `bridge/view`: the comparison theorem below between the existing module-valued owner from
  `15.29.1` and its ring specialization `extendedAlternatingCechComplex f R`.

Primitive data stays in the owner files: the localization-family map, the ordinary alternating
Čech complex, and the degree-zero augmentation. This file only exposes the tensor-description
bridge and does not introduce a parallel wrapper for that canonical tensor functor.
-/

section

variable {R : Type u} [CommRing R]
variable {r : ℕ}
variable (f : Fin r → R)
variable (M : Type u) [AddCommGroup M] [Module R M]

private abbrev tensorComplexFunctor :
    CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat R) ℕ :=
  (tensorLeft (of R M)).mapHomologicalComplex (up ℕ)

private abbrev ringArrow :
    Arrow (ModuleCat R) :=
  Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap R f))

private abbrev moduleArrow :
    Arrow (ModuleCat R) :=
  Arrow.mk (ofHom (awayLocalizationFamilyMap M f))

private abbrev tensorRingArrow :
    Arrow (ModuleCat R) :=
  (tensorLeft (of R M)).mapArrow.obj (ringArrow f)

private abbrev tensorCosimplicialFunctor :
    CosimplicialObject (ModuleCat R) ⥤ CosimplicialObject (ModuleCat R) :=
  (CosimplicialObject.whiskering (ModuleCat R) (ModuleCat R)).obj (tensorLeft (of R M))

private noncomputable abbrev codomainLinearEquiv :
    M ⊗[R] (∀ i : Fin r, Localization.Away (f i)) ≃ₗ[R]
      ∀ i : Fin r, LocalizedModule.Away (f i) M :=
  (TensorProduct.piRight R R M (fun i : Fin r ↦ Localization.Away (f i))) ≪≫ₗ
    LinearEquiv.piCongrRight fun i : Fin r ↦
      TensorProduct.comm R M (Localization.Away (f i)) ≪≫ₗ
        (LocalizedModule.equivTensorProduct (Submonoid.powers (f i)) M).symm.restrictScalars R

private theorem codomainLinearEquiv_tmul_one_apply (x : M) :
    (codomainLinearEquiv f M)
        (x ⊗ₜ[R] ConcreteCategory.hom (ModuleCat.ofHom (awayLocalizationFamilyMap R f)) 1) =
      ConcreteCategory.hom (moduleArrow f M).hom x := by
  sorry

private theorem awayLocalizationFamilyMap_tensor_comm :
    ((ρ_ (of R M)).symm).hom ≫
        (tensorLeft (of R M)).map (ModuleCat.ofHom (awayLocalizationFamilyMap R f)) ≫
        (codomainLinearEquiv f M).toModuleIso.hom =
      (moduleArrow f M).hom := by
  sorry

private theorem awayLocalizationFamilyMap_tensorSq :
    CommSq ((ρ_ (of R M)).symm).hom (moduleArrow f M).hom
      ((tensorLeft (of R M)).map (ModuleCat.ofHom (awayLocalizationFamilyMap R f)))
      (codomainLinearEquiv f M).toModuleIso.inv := by
  sorry

private noncomputable abbrev arrowIso :
    moduleArrow f M ≅ ((tensorLeft (of R M)).mapArrow.obj (ringArrow f)) :=
  Arrow.isoMk ((ρ_ (of R M)).symm) ((codomainLinearEquiv f M).toModuleIso.symm)
    (awayLocalizationFamilyMap_tensorSq f M).w

private noncomputable abbrev tensorCechConerveComponent (n : SimplexCategory) :
    (((tensorLeft (of R M)).mapArrow.obj (ringArrow f)).cechConerve).obj n ≅
      ((tensorCosimplicialFunctor M).obj ((ringArrow f).cechConerve)).obj n :=
  (HasColimit.isoOfNatIso
      (WidePushoutShape.diagramIsoWideSpan
        ((WidePushoutShape.wideSpan (ringArrow f).left
          (fun _ : Fin (n.len + 1) ↦ (ringArrow f).right)
          fun _ ↦ (ringArrow f).hom) ⋙ tensorLeft (of R M)))).symm ≪≫
    (preservesColimitIso (tensorLeft (of R M))
      (WidePushoutShape.wideSpan (ringArrow f).left
        (fun _ : Fin (n.len + 1) ↦ (ringArrow f).right)
        fun _ ↦ (ringArrow f).hom)).symm

private noncomputable abbrev tensorCechConerveIso :
    ((tensorLeft (of R M)).mapArrow.obj (ringArrow f)).cechConerve ≅
      (tensorCosimplicialFunctor M).obj ((ringArrow f).cechConerve) :=
  NatIso.ofComponents (tensorCechConerveComponent f M) (by
    sorry)

private noncomputable abbrev cechConerveIso :
    (moduleArrow f M).cechConerve ≅
      (tensorCosimplicialFunctor M).obj ((ringArrow f).cechConerve) :=
  (CategoryTheory.CosimplicialObject.cechConerve :
    Arrow (ModuleCat.{u} R) ⥤ CosimplicialObject (ModuleCat.{u} R)).mapIso (arrowIso f M) ≪≫
    tensorCechConerveIso f M

private theorem tensor_alternatingCofaceMapComplex (M : Type u) [AddCommGroup M] [Module R M] :
    alternatingCofaceMapComplex (ModuleCat R) ⋙
        (tensorLeft (of R M)).mapHomologicalComplex (up ℕ) =
      (tensorCosimplicialFunctor M) ⋙ alternatingCofaceMapComplex (ModuleCat R) := by
  sorry

private noncomputable abbrev ordinaryIso :
    alternatingCechComplex f M ≅
      (tensorComplexFunctor M).obj (alternatingCechComplex f R) :=
  (alternatingCofaceMapComplex (ModuleCat R)).mapIso (cechConerveIso f M) ≪≫
    (eqToIso
      (Functor.congr_obj
        (tensor_alternatingCofaceMapComplex M)
        (ringArrow f).cechConerve)).symm

-- Proof sketch: tensor the ring-valued Čech conerve termwise by `M`, use the standard
-- identification `M ⊗[R] R_{f_I} ≃ M_{f_I}` on each Čech term, and transport the degree-zero
-- tensor term to `M` via the monoidal unit isomorphism. This yields the canonical comparison
-- isomorphism between the module-valued owner from `15.29.1` and the tensor image of the
-- ring-valued owner from `15.31.1`.
/-- Lemma 15.29.2: the extended alternating Čech complex of an `R`-module `M` attached to a finite
family `f : Fin r → R` is canonically isomorphic to the complex obtained by tensoring the
ring-valued extended alternating Čech complex attached to `f` with `M`. -/
noncomputable def extendedAlternatingCechComplex_iso_tensorObj :
    extendedAlternatingCechComplex f M ≅
      ((tensorLeft (of R M)).mapHomologicalComplex (up ℕ)).obj
        (extendedAlternatingCechComplex f R) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun
      | 0 => (ρ_ (of R M)).symm
      | n + 1 =>
          (HomologicalComplex.eval (ModuleCat R) (up ℕ) n).mapIso
            (ordinaryIso f M))
    (by
      sorry)

end
