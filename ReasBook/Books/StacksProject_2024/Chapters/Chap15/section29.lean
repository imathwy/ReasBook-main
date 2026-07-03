import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.CategoryTheory.CommSq

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_29_1 (from Chap15) -/
noncomputable section

open CategoryTheory
open AlgebraicTopology

universe u v

/-
Domain-style sampling for the extended alternating Čech complex:
- owner abstraction: `extendedAlternatingCechComplex`
- same-domain declarations inspected:
  `awayLocalizationFamilyMap`
  `Arrow.augmentedCechConerve`
  `alternatingCofaceMapComplex`
  `CochainComplex.fromSingle₀AsComplex`

Layer triage:
- `source-facing`: the extended alternating Čech complex of a finite family `f` and an `R`-module
  `M`
- `core/canonical`: the ordinary alternating Čech complex obtained from the Čech conerve of the
  canonical localization-family map, then extended in degree `0` by
  `CochainComplex.fromSingle₀AsComplex`
- `bridge/view`: the degree-zero augmentation map from `M` into the ordinary alternating Čech
  complex

Primitive data is only the canonical localization-family map `awayLocalizationFamilyMap M f`.
The ordinary alternating Čech complex, its augmentation, and the extended complex are derived
from that owner construction; the finite-subset indexing, sign bookkeeping, and entrywise
differentials should therefore not remain primitive public data here.
-/

section

variable {R : Type u} [CommRing R]
variable {r : ℕ}

/-- The ordinary alternating Čech complex of `M` attached to the family `f`. -/
abbrev alternatingCechComplex (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] :
    CochainComplex (ModuleCat.{max u v} R) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat.{max u v} R)).obj
    ((Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).cechConerve)

/-- The degree-zero augmentation map from `M` to the ordinary alternating Čech complex. -/
abbrev alternatingCechComplexAugmentationMap (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] :
    ModuleCat.of R M ⟶ (alternatingCechComplex f M).X 0 :=
  (Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).augmentedCechConerve.hom.app
    (SimplexCategory.mk 0)

-- Proof sketch: the two degree-zero coface maps are induced by the same localization-family map,
-- so their alternating sum vanishes after precomposition with the augmentation map.
/-- The degree-zero augmentation map is a cocycle for the ordinary alternating Čech complex. -/
theorem alternatingCechComplexAugmentationMap_comp_d_zero_one
    (f : Fin r → R) (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    alternatingCechComplexAugmentationMap f M ≫ (alternatingCechComplex f M).d 0 1 = 0 := sorry

/-- The augmentation from `M` to the ordinary alternating Čech complex of `f`. -/
abbrev alternatingCechComplexAugmentation (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] :
    (CochainComplex.single₀ (ModuleCat.{max u v} R)).obj (ModuleCat.of R M) ⟶
      alternatingCechComplex f M :=
  (CochainComplex.fromSingle₀Equiv (alternatingCechComplex f M) (ModuleCat.of R M)).symm
    ⟨alternatingCechComplexAugmentationMap f M,
      alternatingCechComplexAugmentationMap_comp_d_zero_one f M⟩

/-- Lemma 15.29.1: the extended alternating Čech complex attached to a finite family
`f : Fin r → R` and an `R`-module `M`, obtained by adjoining the canonical degree-zero
augmentation to the ordinary alternating Čech complex. The ring-valued extended alternating Čech
complex is the special case `M = R`. -/
def extendedAlternatingCechComplex (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] :
    CochainComplex (ModuleCat.{max u v} R) ℕ :=
  CochainComplex.fromSingle₀AsComplex (alternatingCechComplex f M) (ModuleCat.of R M)
    (alternatingCechComplexAugmentation f M)

end

/-! ### Lemma_15_29_2 (from Chap15) -/
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

/-! ### Lemma_15_29_3 (from Chap15) -/
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
  ext s
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
private noncomputable abbrev extendScalarsCechConerveIso (f : Fin r → R) :
    (ringArrowBaseChange f : Arrow (ModuleCat S)).cechConerve ≅
      extendScalarsCosimplicialFunctor.obj ((ringArrow f : Arrow (ModuleCat R)).cechConerve) :=
  NatIso.ofComponents
    (extendScalarsCechConerveComponent f)
    (by
      intro n m α
      sorry)

private theorem extendScalars_alternatingCofaceMapComplex :
    alternatingCofaceMapComplex (ModuleCat R) ⋙
        (extendScalarsCpx : CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat S) ℕ) =
      extendScalarsCosimplicialFunctor ⋙
        alternatingCofaceMapComplex (ModuleCat S) := by
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
  intro i j hij
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

-- Proof sketch: base change identifies each term in the extended alternating Čech complex of `M`
-- with the corresponding term for `S ⊗[R] M` and the image family `algebraMap R S ∘ f` by
-- composing the owner-level ring base-change bridge with the tensor-description bridge.
/-- Lemma 15.29.3: for a ring map `R → S`, the extended alternating Čech complex over `S`
attached to `algebraMap R S ∘ f` and `S ⊗[R] M` is isomorphic to the scalar extension of the
extended alternating Čech complex over `R` attached to `f` and `M`. This file exposes the
canonical comparison isomorphism itself, rather than only an existential wrapper around it. -/
noncomputable def extendedAlternatingCechComplex_iso_extendScalars :
    extendedAlternatingCechComplex fS (S ⊗[R] M) ≅
      (extendScalarsCpx : CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat S) ℕ).obj
        (extendedAlternatingCechComplex f M) :=
  let ringCech : CochainComplex (ModuleCat R) ℕ := extendedAlternatingCechComplex f R
  let TensorS₀ : CochainComplex (ModuleCat S) ℕ ⥤ CochainComplex (ModuleCat S) ℕ :=
    ((tensorLeft (of S (S ⊗[R] M))).mapHomologicalComplex (up ℕ) :
      CochainComplex (ModuleCat S) ℕ ⥤ CochainComplex (ModuleCat S) ℕ)
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
          (ComplexShape.up ℕ)).obj ringCech ≅
        (Functor.mapHomologicalComplex
          (tensorLeft (ModuleCat.of R M) ⋙ (extendScalarsFunctor : ModuleCat R ⥤ ModuleCat S))
          (ComplexShape.up ℕ)).obj ringCech :=
    ((NatIso.mapHomologicalComplex tensorCommIso (ComplexShape.up ℕ)).app
      ringCech).symm
  let tensorExtIso :
      extendedAlternatingCechComplex f M ≅
        (((tensorLeft (ModuleCat.of R M)).mapHomologicalComplex (up ℕ)).obj ringCech) :=
    extendedAlternatingCechComplex_iso_tensorObj f M
  (extendedAlternatingCechComplex_iso_tensorObj fS (S ⊗[R] M)) ≪≫
    (TensorS₀.mapIso (ring_extendedAlternatingCechComplex_iso_extendScalars f)) ≪≫
    ((NatIso.mapHomologicalComplex tensorLeftIso (up ℕ)).app
      ((extendScalarsCpx : CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat S) ℕ).obj
        ringCech)).symm ≪≫
    (tensorExtendScalars_mapHomologicalComplex_obj_iso M ringCech) ≪≫
    tensorCommCpxIso ≪≫
    (extendScalarsTensor_mapHomologicalComplex_obj_iso M ringCech) ≪≫
    ((extendScalarsCpx : CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat S) ℕ).mapIso
      tensorExtIso).symm

end

/-! ### Lemma_15_29_4 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open HomologicalComplex
open ZeroObject
open LocalizedModule

noncomputable section

universe u v

/-
Domain-style sampling:
- primary domain: localization families and the extended alternating Čech complex of an
  `R`-module;
- sampled owner declarations:
  `awayLocalizationFamilyMap`,
  `extendedAlternatingCechComplex`,
  `CategoryTheory.cechConerveRetraction_comp_coaugmentation_homotopic_id`,
  `CategoryTheory.CosimplicialObject.alternatingCofaceMapComplex_map_isHomotopyEquivalence`;
- best owner abstraction: the source-facing statement here is the contractibility of the canonical
  owner `extendedAlternatingCechComplex f M` under the unit-at-one-index hypothesis, while the
  split-mono and Čech-conerve homotopy machinery remains derived bridge data from the Chapter 10
  and Chapter 14 owners.

Primitive data is only the canonical localization-family map `awayLocalizationFamilyMap M f`.
The retraction of that map and the resulting homotopy-equivalence-to-zero statement are derived
API and should not be repackaged as new owners.
-/

section

variable {R : Type u} [CommRing R]
variable {M : Type (max u v)} [AddCommGroup M] [Module R M]
variable {r : ℕ}

/-- Scalar multiplication by an element of the powers of a unit is an invertible endomorphism of
an `R`-module. -/
private theorem powers_endomorphism_isUnit_of_isUnit (x : R) (hx : IsUnit x)
    (s : Submonoid.powers x) :
    IsUnit ((algebraMap R (Module.End R M)) s) := sorry

private abbrev awayLocalizationFamilyMapSection (f : Fin r → R) (i : Fin r)
    [Fact (IsUnit (f i))] :
    ModuleCat.of R (∀ j : Fin r, LocalizedModule.Away (f j) M) ⟶ ModuleCat.of R M :=
  ModuleCat.ofHom <|
    (LocalizedModule.lift (Submonoid.powers (f i)) (LinearMap.id)
        (powers_endomorphism_isUnit_of_isUnit (f i) (Fact.out : IsUnit (f i)))).comp
      (LinearMap.proj i)

-- Proof sketch: project to the `i`th factor and apply the localization universal property with
-- `g = LinearMap.id`; because `f i` is a unit, the resulting lift is inverse to
-- `LocalizedModule.mkLinearMap`, so the canonical localization-family map admits a retraction.
/-- If one entry `f i` is a unit, the canonical localization-family map is split mono. -/
theorem awayLocalizationFamilyMap_isSplitMono_of_isUnit_at (f : Fin r → R) (i : Fin r)
    (hi : IsUnit (f i)) :
    IsSplitMono (ModuleCat.ofHom (awayLocalizationFamilyMap M f)) := by
  letI : Fact (IsUnit (f i)) := ⟨hi⟩
  refine IsSplitMono.mk' ?_
  refine ⟨awayLocalizationFamilyMapSection f i, ?_⟩
  refine ModuleCat.hom_ext ?_
  ext m
  simp [awayLocalizationFamilyMapSection, awayLocalizationFamilyMap]

-- Proof sketch: `awayLocalizationFamilyMap_isSplitMono_of_isUnit_at` gives a retraction of the
-- canonical localization-family map. Lemma `14.28.5` then identifies the Čech conerve of this
-- split monomorphism as a cosimplicial retract of the constant cosimplicial object, and the
-- associated alternating complex is therefore homotopy equivalent to the single-term zero
-- complex.
/-- The extended alternating Čech complex is contractible as soon as one of the localizing
entries is a unit. -/
theorem extendedAlternatingCechComplex_homotopyEquivalent_zero_of_isUnit_at
    (f : Fin r → R) (i : Fin r) (hi : IsUnit (f i)) :
    Nonempty
      (HomotopyEquiv (extendedAlternatingCechComplex f M) 0) := sorry

-- Proof sketch: choose an index `i` for which `f i` is a unit and apply the indexed contractibility
-- statement.
/-- Lemma 15.29.4: if one of the localizing elements in the finite family `f` is a unit, then the
extended alternating Čech complex of the `R`-module `M` is homotopy equivalent to the zero
cochain complex. -/
theorem extendedAlternatingCechComplex_homotopyEquivalent_zero_of_exists_isUnit
    (f : Fin r → R) (hunit : ∃ i : Fin r, IsUnit (f i)) :
    Nonempty
      (HomotopyEquiv (extendedAlternatingCechComplex f M) 0) := by
  rcases hunit with ⟨i, hi⟩
  exact extendedAlternatingCechComplex_homotopyEquivalent_zero_of_isUnit_at f i hi

end

/-! ### Lemma_15_29_5 (from Chap15) -/
noncomputable section

universe u v

open CategoryTheory.Limits

/-
Domain-style sampling:
- primary domain: homology of the extended alternating Čech complex of a finite family in a
  commutative ring;
- sampled owner declarations:
  `extendedAlternatingCechComplex`
  `extendedAlternatingCechComplex_homotopyEquivalent_zero_of_exists_isUnit`
  `extendedAlternatingCechComplex_homology_isZero_of_isKoszulRegularSequence`
  `Module.support`;
- best owner abstraction: the cohomology modules in this lemma are already canonically the
  homology objects `(extendedAlternatingCechComplex f M).homology q`, so no parallel local
  cohomology owner should be introduced here.

Primitive data is only the finite family `f`, the `R`-module `M`, and the canonical owner
`extendedAlternatingCechComplex f M`. The cohomology objects, their support, and the annihilation
properties are derived API of that owner.

Source/core/bridge triage:
- `source-facing`: the four cohomology consequences stated in Lemma 15.29.5;
- `core/canonical`: homology of the owner complex `(extendedAlternatingCechComplex f M).homology q`;
- `bridge/view`: support and annihilation reformulations of those homology objects.
-/

section

variable {R : Type u} [CommRing R]
variable {M : Type (max u v)} [AddCommGroup M] [Module R M]
variable {r : ℕ}

-- Proof sketch: the extended alternating Čech complex is concentrated in degrees `0, ..., r`, so
-- the homology object in degree `q` is zero once `q > r`.
/-- Lemma 15.29.5 (1): the extended alternating Čech cohomology vanishes in degrees above `r`,
which is the `q ∉ [0, r]` vanishing statement in the natural `ℕ`-indexed model of the complex. -/
theorem extendedAlternatingCechCohomology_isZero_of_gt
    {f : Fin r → R} {q : ℕ} (hq : r < q) :
    IsZero ((extendedAlternatingCechComplex f M).homology q) := sorry

-- Proof sketch: localize the extended alternating Čech complex at `f i`; by Lemma 15.29.3 this
-- localized complex is again an extended alternating Čech complex, and by Lemma 15.29.4 it is
-- contractible because `f i` becomes a unit. Hence the localized cohomology vanishes, which means
-- some positive power of `f i` kills the class `x`.
/-- Lemma 15.29.5 (2): every cohomology class in the extended alternating Čech complex is
annihilated by a positive power of each generator `f i`. -/
theorem exists_pow_smul_eq_zero_of_mem_extendedAlternatingCechCohomology
    {f : Fin r → R} (q : ℕ) (i : Fin r)
    (x : (extendedAlternatingCechComplex f M).homology q) :
    ∃ n : ℕ, 1 ≤ n ∧ f i ^ n • x = 0 := sorry

-- Proof sketch: by the previous clause, localizing the cohomology module at any `f i` gives zero.
-- The support criterion for localization then places the support inside the common zero locus of
-- the ideal generated by the family `f`.
/-- Lemma 15.29.5 (3): the support of the `q`th extended alternating Čech cohomology module is
contained in the closed subset `V(f₁, ..., fᵣ)`. -/
theorem support_extendedAlternatingCechCohomology_subset_zeroLocus
    {f : Fin r → R} (q : ℕ) :
    Module.support R ((extendedAlternatingCechComplex f M).homology q) ⊆
      PrimeSpectrum.zeroLocus (Ideal.span (Set.range f)) := sorry

-- Proof sketch: an element `a ∈ (f₁, ..., fᵣ)` acting invertibly on `M` also acts invertibly on
-- every term of the extended alternating Čech complex and hence on its cohomology. Clause (3)
-- shows that the support of the cohomology is contained in `V(a)`, so invertibility of `a`
-- forces the cohomology module to vanish.
/-- Lemma 15.29.5 (4): if some element of the ideal `(f₁, ..., fᵣ)` acts invertibly on `M`, then
every extended alternating Čech cohomology module vanishes. -/
theorem extendedAlternatingCechCohomology_isZero_of_exists_isUnit_span
    {f : Fin r → R} (q : ℕ)
    (hunit : ∃ a ∈ Ideal.span (Set.range f), IsUnit (algebraMap R (Module.End R M) a)) :
    IsZero ((extendedAlternatingCechComplex f M).homology q) := sorry

end

/-! ### Lemma_15_29_6 (from Chap15) -/
noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open RingTheory.Sequence
open ModuleCat
open ModuleCat.exteriorPower
open Set
open scoped KoszulComplex

/-
Domain-style sampling for the powered Koszul description of the extended alternating Čech complex:
- owner abstractions inspected:
  `extendedAlternatingCechComplex`
  `awayLocalizationFamilyMap`
  `koszulPowerStepLinearMap`
  `koszulPowerInverseSystem`
  `Functor.ofSequence`
  `K^•[n](f)`

Layer triage:
- `source-facing`: the realization of the extended alternating Čech complex of a finite family
  `f : Fin r → R` as a sequential colimit of the cohomologically reindexed powered Koszul stages,
  with the direct-system maps from the source proof
- `core/canonical`: the module-valued owner `extendedAlternatingCechComplex`, specialized here to
  `extendedAlternatingCechComplex f R`
  together with the powered Koszul owners `koszulPowerStepLinearMap` and
  `koszulPowerInverseSystem` from `15.92.15`
- `bridge/view`: the bounded cochain reindexing of the powered Koszul stages, and the source-facing
  direct-system maps on those stages used to compute the Čech colimit

Primitive data belongs to the owner construction from `15.31.1`: the canonical localization-family
map, its Čech conerve, and the degree-zero augmentation. The powered Koszul stages and their
diagonal transition map are already owned by `koszulPowerInverseSystem` and
`koszulPowerStepLinearMap`; this file only adds the source-facing cochain bridge needed for the
direct-limit computation.
-/

section

variable {R : Type u} [CommRing R]
variable {r : ℕ}
variable (f : Fin r → R)

private abbrev ringArrow : Arrow (ModuleCat R) :=
  Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap R f))

private noncomputable abbrev koszulPowerCochainStage (n : ℕ) :
    CochainComplex (ModuleCat R) ℕ :=
  (((K^•[n](f)).extend (embeddingUpIntLE (r : ℤ))).restriction embeddingUpNat)

private theorem koszulPowerCochainIndex_eq (p : ℕ) (hp : p ≤ r) :
    (embeddingUpIntLE (r : ℤ)).f (r - p) = (p : ℤ) := by
  dsimp [embeddingUpIntLE]
  omega

/-- The degree-`p` component of the direct-system map on the cohomologically reindexed powered
Koszul stages, obtained by applying exterior power functoriality to the canonical diagonal step
map. In basis coordinates, this is the complementary-product map from the Stacks proof. -/
private noncomputable def koszulPowerCochainStepComponent (n p : ℕ) :
    (koszulPowerCochainStage f n).X p ⟶ (koszulPowerCochainStage f (n + 1)).X p :=
  if hp : p ≤ r then
    let hq := koszulPowerCochainIndex_eq p hp
    ((((K^•[n](f)).extend (embeddingUpIntLE (r : ℤ))).restrictionXIso embeddingUpNat rfl).hom ≫
        (((K^•[n](f)).extendXIso (embeddingUpIntLE (r : ℤ)) hq).hom ≫
          (ModuleCat.exteriorPower.map (ModuleCat.ofHom (koszulPowerStepLinearMap f)) (r - p) ≫
            (((K^•[n + 1](f)).extendXIso (embeddingUpIntLE (r : ℤ)) hq).inv ≫
              (((K^•[n + 1](f)).extend (embeddingUpIntLE (r : ℤ))).restrictionXIso
                embeddingUpNat rfl).inv))))
  else
    0

private theorem koszulPowerCochainStep_comm (n p : ℕ) :
    koszulPowerCochainStepComponent f n p ≫
        (koszulPowerCochainStage f (n + 1)).d p (p + 1) =
      (koszulPowerCochainStage f n).d p (p + 1) ≫
        koszulPowerCochainStepComponent f n (p + 1) := by
  sorry

private theorem koszulComplement_card_eq (p : ℕ) (hp : p ≤ r) :
    p + (r - p) = Fintype.card (Fin r) := by
  simp
  omega

private noncomputable abbrev koszulExteriorBasis (p : ℕ) :
    Module.Basis (powersetCard (Fin r) p) R (⋀[R]^p (Fin r → R)) :=
  (Pi.basisFun R (Fin r)).exteriorPower p

private noncomputable def koszulPowerCochainStageXIso (n p : ℕ) (hp : p ≤ r) :
    (koszulPowerCochainStage f n).X p ≅ ModuleCat.of R (⋀[R]^(r - p) (Fin r → R)) :=
  (((K^•[n](f)).extend (embeddingUpIntLE (r : ℤ))).restrictionXIso embeddingUpNat rfl) ≪≫
    ((K^•[n](f)).extendXIso (embeddingUpIntLE (r : ℤ)) (koszulPowerCochainIndex_eq p hp))

private noncomputable def koszulPowerDegreeZeroLinearMap :
    ⋀[R]^r (Fin r → R) →ₗ[R] R :=
  (koszulExteriorBasis r).constr R (fun _ ↦ (1 : R))

private noncomputable def koszulComplementSubset (p : ℕ) (hp : p ≤ r)
    (s : powersetCard (Fin r) (r - p)) :
    powersetCard (Fin r) p :=
  powersetCard.compl (koszulComplement_card_eq p hp) s

private noncomputable abbrev cechConerveTerm (p : ℕ) : ModuleCat R :=
  (ringArrow f).cechConerve.obj (SimplexCategory.mk p)

private noncomputable def koszulCechBranchNumerator (n p : ℕ)
    (s : powersetCard (Fin r) p) (k : Fin p) : R :=
  Finset.prod (Finset.univ.erase k) fun l ↦ f (powersetCard.ofFinEmbEquiv.symm s l) ^ (n + 1)

private noncomputable def koszulCechBranchVector (n p : ℕ)
    (s : powersetCard (Fin r) p) (k : Fin p) :
    ∀ i : Fin r, Localization.Away (f i) :=
  fun i ↦
    dite (i = powersetCard.ofFinEmbEquiv.symm s k)
      (fun h ↦ h.rec <|
        LocalizedModule.mk (koszulCechBranchNumerator f n p s k)
          ⟨f (powersetCard.ofFinEmbEquiv.symm s k) ^ (n + 1), by
            refine ⟨n + 1, by simpa [h]⟩⟩)
      (fun _ ↦ 0)

private noncomputable abbrev cechConerveBranchHom (p : ℕ) (k : Fin (p + 1)) :
    ModuleCat.of R (∀ i : Fin r, Localization.Away (f i)) ⟶ cechConerveTerm f p :=
  show ModuleCat.of R (∀ i : Fin r, Localization.Away (f i)) ⟶
      widePushout (ModuleCat.of R R)
        (fun _ : Fin (p + 1) ↦ ModuleCat.of R (∀ i : Fin r, Localization.Away (f i)))
        (fun _ ↦ ModuleCat.ofHom (awayLocalizationFamilyMap R f)) from
    WidePushout.ι (fun _ : Fin (p + 1) ↦ ModuleCat.ofHom (awayLocalizationFamilyMap R f)) k

private noncomputable def koszulAlternatingBasisImage (n p : ℕ) (hp : p + 1 ≤ r)
    (s : powersetCard (Fin r) (r - (p + 1))) :
    cechConerveTerm f p :=
  let t := koszulComplementSubset (p + 1) hp s
  ∑ k : Fin (p + 1),
    (-1 : ℤ) ^ (k : ℕ) •
      (cechConerveBranchHom f p k).hom (koszulCechBranchVector f n (p + 1) t k)

private noncomputable def koszulAlternatingLinearMap (n p : ℕ) (hp : p + 1 ≤ r) :
    ⋀[R]^(r - (p + 1)) (Fin r → R) →ₗ[R] cechConerveTerm f p :=
  (koszulExteriorBasis (r - (p + 1))).constr R
    (koszulAlternatingBasisImage f n p hp)

private theorem extendedAlternatingCechComplex_X_zero :
    (extendedAlternatingCechComplex f R).X 0 = ModuleCat.of R R := by
  simp [extendedAlternatingCechComplex, alternatingCechComplexAugmentation,
    CochainComplex.fromSingle₀AsComplex]

private theorem extendedAlternatingCechComplex_X_succ (p : ℕ) :
    (extendedAlternatingCechComplex f R).X (p + 1) = cechConerveTerm f p := by
  change (extendedAlternatingCechComplex f R).X (p + 1) =
    (ringArrow f).cechConerve.obj (SimplexCategory.mk p)
  simp [extendedAlternatingCechComplex, alternatingCechComplexAugmentation,
    CochainComplex.fromSingle₀AsComplex]
  rfl

private noncomputable def koszulPowerToExtendedComponent (n p : ℕ) :
    (koszulPowerCochainStage f n).X p ⟶ (extendedAlternatingCechComplex f R).X p :=
  if hp : p ≤ r then
    match p with
    | 0 =>
        (koszulPowerCochainStageXIso f n 0 hp).hom ≫
          ModuleCat.ofHom koszulPowerDegreeZeroLinearMap ≫
            eqToHom (extendedAlternatingCechComplex_X_zero f).symm
    | q + 1 =>
        (koszulPowerCochainStageXIso f n (q + 1) hp).hom ≫
          ModuleCat.ofHom (koszulAlternatingLinearMap f n q hp) ≫
            eqToHom (extendedAlternatingCechComplex_X_succ f q).symm
  else
    0

private theorem koszulPowerToExtendedComponent_comm (n p : ℕ) :
    koszulPowerToExtendedComponent f n p ≫ (extendedAlternatingCechComplex f R).d p (p + 1) =
      (koszulPowerCochainStage f n).d p (p + 1) ≫ koszulPowerToExtendedComponent f n (p + 1) := by
  sorry

private noncomputable abbrev koszulPowerToExtendedMap (n : ℕ) :
    koszulPowerCochainStage f n ⟶ extendedAlternatingCechComplex f R :=
  { f := koszulPowerToExtendedComponent f n
    comm' := fun p q hpq ↦ by
      subst hpq
      simpa using koszulPowerToExtendedComponent_comm f n p }

/- The source-facing direct-system map
`K(f₁^(n+1), ..., fᵣ^(n+1)) ⟶ K(f₁^(n+2), ..., fᵣ^(n+2))`
between the cohomologically reindexed powered Koszul stages. On degree `p`, this is the
complementary-product map from the Stacks proof. -/
private noncomputable abbrev koszulPowerCochainStep (n : ℕ) :
    koszulPowerCochainStage f n ⟶ koszulPowerCochainStage f (n + 1) :=
  { f := koszulPowerCochainStepComponent f n
    comm' := fun p q hpq ↦ by
      subst hpq
      simpa using koszulPowerCochainStep_comm f n p }

private theorem koszulPowerToExtended_naturality (n : ℕ) :
    koszulPowerCochainStep f n ≫ koszulPowerToExtendedMap f (n + 1) =
      koszulPowerToExtendedMap f n := by
  sorry

/-- The sequential direct system of the cohomologically reindexed powered Koszul complexes
`K^•(f₁^(n+1), …, fᵣ^(n+1))`, with transition maps induced by the canonical diagonal step map on
the finite free module `Fin r → R`. This is the source-facing bridge object in Lemma `15.29.6`. -/
noncomputable def koszulPowerCochainSystem :
    ℕ ⥤ CochainComplex (ModuleCat R) ℕ :=
  Functor.ofSequence (koszulPowerCochainStep f)

-- Proof sketch: compute the degreewise colimit of `koszulPowerCochainSystem f`
-- direct-limit description of `Localization.Away (Finset.prod s.1 f)`. In the reindexed
-- cohomological grading, the differentials on the powered Koszul stages become the alternating
-- Čech coboundaries, so the colimit identifies with `extendedAlternatingCechComplex f`.
/-- The comparison cocone on the powered Koszul cochain system used to define the colimit map in
Lemma `15.29.6`. -/
private noncomputable abbrev koszulPowerCochainSystemCocone :
    Cocone (koszulPowerCochainSystem f) where
  pt := extendedAlternatingCechComplex f R
  ι := NatTrans.ofSequence
    (fun n ↦ koszulPowerToExtendedMap f n)
    (fun n ↦ by
      simpa [koszulPowerCochainSystem, Functor.ofSequence_map_homOfLE_succ] using
        koszulPowerToExtended_naturality f n)

/-- The comparison morphism from the colimit of the powered Koszul cochain system to the extended
alternating Čech complex. -/
private noncomputable abbrev colimit_koszulPowerCochainSystem_to_extendedAlternatingCechComplex :
    colimit (koszulPowerCochainSystem f) ⟶ extendedAlternatingCechComplex f R :=
  colimit.desc _ (koszulPowerCochainSystemCocone f)

/-- The comparison from the colimit of the powered Koszul cochain system to the extended
alternating Čech complex is an isomorphism. -/
private theorem colimit_koszulPowerCochainSystem_to_extendedAlternatingCechComplex_isIso :
    IsIso (colimit_koszulPowerCochainSystem_to_extendedAlternatingCechComplex f) := by
  sorry

/-- Lemma 15.29.6: the extended alternating Čech complex of a finite family `f : Fin r → R` is
canonically isomorphic to the colimit of the sequential cochain system of powered Koszul
complexes. -/
noncomputable def extendedAlternatingCechComplex_iso_colimit_koszulPowerCochainSystem
    :
    extendedAlternatingCechComplex f R ≅
      colimit (koszulPowerCochainSystem f) :=
  let _ := colimit_koszulPowerCochainSystem_to_extendedAlternatingCechComplex_isIso f
  (asIso (colimit_koszulPowerCochainSystem_to_extendedAlternatingCechComplex f)).symm

end
