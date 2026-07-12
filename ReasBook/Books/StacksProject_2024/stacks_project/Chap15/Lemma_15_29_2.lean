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
  -- Evaluate the product comparison coordinatewise and reduce each component to the standard
  -- localization/tensor description `M_(fᵢ) ≃ R_(fᵢ) ⊗[R] M`.
  ext i
  change (LocalizedModule.equivTensorProduct (Submonoid.powers (f i)) M).symm
      (Localization.mk (1 : R) (1 : Submonoid.powers (f i)) ⊗ₜ[R] x) =
    LocalizedModule.mk x (1 : Submonoid.powers (f i))
  simpa using
    (LocalizedModule.equivTensorProduct_symm_apply_tmul
      (S := Submonoid.powers (f i)) (M := M) x (1 : R) (1 : Submonoid.powers (f i)))

private theorem awayLocalizationFamilyMap_tensor_comm :
    ((ρ_ (of R M)).symm).hom ≫
        (tensorLeft (of R M)).map (ModuleCat.ofHom (awayLocalizationFamilyMap R f)) ≫
        (codomainLinearEquiv f M).toModuleIso.hom =
      (moduleArrow f M).hom := by
  -- On an element `x : M`, the source map tensors `x` with the degree-zero generator `1`, and the
  -- previous computation identifies the result with the module localization-family map.
  ext x i
  simpa using congrArg (fun y => y i) (codomainLinearEquiv_tmul_one_apply (f := f) (M := M) x)

private theorem awayLocalizationFamilyMap_tensorSq :
    CommSq ((ρ_ (of R M)).symm).hom (moduleArrow f M).hom
      ((tensorLeft (of R M)).map (ModuleCat.ofHom (awayLocalizationFamilyMap R f)))
      (codomainLinearEquiv f M).toModuleIso.inv := by
  -- Reassociate the arrow-level comparison and then cancel the codomain isomorphism on the right.
  refine CommSq.mk ?_
  exact
    (CategoryTheory.Iso.eq_comp_inv ((codomainLinearEquiv f M).toModuleIso)).2
      (awayLocalizationFamilyMap_tensor_comm (f := f) (M := M))

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

/-- Helper for Lemma 15.29.2: on the head leg of the wide pushout, the tensor/Čech comparison is
the functorial image of the original head map. -/
private theorem tensorCechConerveComponent_hom_head (n : SimplexCategory) :
    WidePushout.head (fun _ : Fin (n.len + 1) ↦ (tensorRingArrow f M).hom) ≫
        (tensorCechConerveComponent f M n).hom =
      (tensorLeft (of R M)).map
        (WidePushout.head (fun _ : Fin (n.len + 1) ↦ (ringArrow f).hom)) := by
  -- Proof comment: rewrite the comparison as the composite of the two colimit isomorphisms and
  -- then evaluate each one on the head coprojection.
  rw [Category.assoc]
  rw [HasColimit.isoOfNatIso_ι_hom_assoc]
  rw [ι_preservesColimitIso_hom]
  simp [tensorCechConerveComponent]

/-- Helper for Lemma 15.29.2: on each branch leg of the wide pushout, the tensor/Čech comparison
is the functorial image of the original branch coprojection. -/
private theorem tensorCechConerveComponent_hom_ι (n : SimplexCategory) (i : Fin (n.len + 1)) :
    WidePushout.ι (fun _ : Fin (n.len + 1) ↦ (tensorRingArrow f M).hom) i ≫
        (tensorCechConerveComponent f M n).hom =
      (tensorLeft (of R M)).map
        (WidePushout.ι (fun _ : Fin (n.len + 1) ↦ (ringArrow f).hom) i) := by
  -- Proof comment: the same transport computation as for the head leg applies to every branch.
  rw [Category.assoc]
  rw [HasColimit.isoOfNatIso_ι_hom_assoc]
  rw [ι_preservesColimitIso_hom]
  simp [tensorCechConerveComponent]

/-- Helper for Lemma 15.29.2: the stagewise tensor/Čech comparison is natural in the simplex. -/
private theorem tensorCechConerveComponent_hom_naturality
    {n n' : SimplexCategory} (α : n ⟶ n') :
    (((tensorLeft (of R M)).mapArrow.obj (ringArrow f)).cechConerve).map α ≫
        (tensorCechConerveComponent f M n').hom =
      (tensorCechConerveComponent f M n).hom ≫
        ((tensorCosimplicialFunctor M).obj ((ringArrow f).cechConerve)).map α := by
  -- Proof comment: both maps out of the source wide pushout are determined by their head and
  -- branch restrictions, and those restrictions are the same after rewriting the comparison legs.
  refine WidePushout.hom_ext _ _ _ (fun j ↦ ?_) ?_
  · calc
      WidePushout.ι (fun _ : Fin (n.len + 1) ↦ (tensorRingArrow f M).hom) j ≫
          (((tensorLeft (of R M)).mapArrow.obj (ringArrow f)).cechConerve).map α ≫
            (tensorCechConerveComponent f M n').hom =
        WidePushout.ι (fun _ : Fin (n'.len + 1) ↦ (tensorRingArrow f M).hom) (α.toOrderHom j) ≫
          (tensorCechConerveComponent f M n').hom := by
          simp [Category.assoc]
      _ =
        (tensorLeft (of R M)).map
          (WidePushout.ι (fun _ : Fin (n'.len + 1) ↦ (ringArrow f).hom) (α.toOrderHom j)) := by
          rw [tensorCechConerveComponent_hom_ι]
      _ =
        (tensorCechConerveComponent f M n).hom ≫
          ((tensorCosimplicialFunctor M).obj ((ringArrow f).cechConerve)).map α := by
          rw [tensorCechConerveComponent_hom_ι]
          simp [tensorCosimplicialFunctor, Category.assoc]
  · calc
      WidePushout.head (fun _ : Fin (n.len + 1) ↦ (tensorRingArrow f M).hom) ≫
          (((tensorLeft (of R M)).mapArrow.obj (ringArrow f)).cechConerve).map α ≫
            (tensorCechConerveComponent f M n').hom =
        WidePushout.head (fun _ : Fin (n'.len + 1) ↦ (tensorRingArrow f M).hom) ≫
          (tensorCechConerveComponent f M n').hom := by
          simp [tensorCosimplicialFunctor, Category.assoc]
      _ =
        (tensorLeft (of R M)).map
          (WidePushout.head (fun _ : Fin (n'.len + 1) ↦ (ringArrow f).hom)) := by
          rw [tensorCechConerveComponent_hom_head]
      _ =
        (tensorCechConerveComponent f M n).hom ≫
          ((tensorCosimplicialFunctor M).obj ((ringArrow f).cechConerve)).map α := by
          rw [tensorCechConerveComponent_hom_head]
          simp [tensorCosimplicialFunctor, Category.assoc]

private noncomputable abbrev tensorCechConerveIso :
    ((tensorLeft (of R M)).mapArrow.obj (ringArrow f)).cechConerve ≅
      (tensorCosimplicialFunctor M).obj ((ringArrow f).cechConerve) :=
  NatIso.ofComponents
    (tensorCechConerveComponent f M)
    (fun α ↦ tensorCechConerveComponent_hom_naturality (f := f) (M := M) α)

private noncomputable abbrev cechConerveIso :
    (moduleArrow f M).cechConerve ≅
      (tensorCosimplicialFunctor M).obj ((ringArrow f).cechConerve) :=
  (CategoryTheory.CosimplicialObject.cechConerve :
    Arrow (ModuleCat.{u} R) ⥤ CosimplicialObject (ModuleCat.{u} R)).mapIso (arrowIso f M) ≪≫
    tensorCechConerveIso f M

/-- Helper for Lemma 15.29.2: tensoring commutes with the differential of the alternating coface
complex, degree by degree. -/
private theorem tensor_alternatingCofaceMapComplex_objD
    (U : CosimplicialObject (ModuleCat R)) (n : ℕ) :
    (((tensorComplexFunctor M).obj
        ((alternatingCofaceMapComplex (ModuleCat R)).obj U)).d n (n + 1)) =
      (((alternatingCofaceMapComplex (ModuleCat R)).obj
          ((tensorCosimplicialFunctor M).obj U)).d n (n + 1)) := by
  -- Proof comment: both differentials are the same alternating sum of coface maps, with
  -- `tensorLeft` pushed through termwise by additivity.
  rw [show (((tensorComplexFunctor M).obj
        ((alternatingCofaceMapComplex (ModuleCat R)).obj U)).d n (n + 1)) =
      (tensorLeft (of R M)).map
        (AlgebraicTopology.AlternatingCofaceMapComplex.objD U n) by
      simp [tensorComplexFunctor, AlgebraicTopology.alternatingCofaceMapComplex,
        AlgebraicTopology.AlternatingCofaceMapComplex.obj,
        CategoryTheory.Functor.mapHomologicalComplex_obj_d]]
  rw [show (((alternatingCofaceMapComplex (ModuleCat R)).obj
        ((tensorCosimplicialFunctor M).obj U)).d n (n + 1)) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        ((tensorCosimplicialFunctor M).obj U) n by
      simp [AlgebraicTopology.alternatingCofaceMapComplex,
        AlgebraicTopology.AlternatingCofaceMapComplex.obj]]
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD, Functor.map_sum]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [Functor.map_zsmul]
  rfl

private theorem tensor_alternatingCofaceMapComplex (M : Type u) [AddCommGroup M] [Module R M] :
    alternatingCofaceMapComplex (ModuleCat R) ⋙
        (tensorLeft (of R M)).mapHomologicalComplex (up ℕ) =
      (tensorCosimplicialFunctor M) ⋙ alternatingCofaceMapComplex (ModuleCat R) := by
  -- Proof comment: follow mathlib's `map_alternatingFaceMapComplex` pattern, but in the cochain
  -- direction. The object part is degreewise identity on terms, and the differential comparison is
  -- the explicit tensor-through-alternating-sum lemma above.
  refine Functor.ext ?_ ?_
  · intro U
    refine HomologicalComplex.ext rfl ?_
    · rintro i j (rfl : i + 1 = j)
      simpa using tensor_alternatingCofaceMapComplex_objD (R := R) (M := M) U i
    · ext n
      rfl
  · intro U V α
    ext n
    simp [tensorCosimplicialFunctor]

private noncomputable abbrev ordinaryIso :
    alternatingCechComplex f M ≅
      (tensorComplexFunctor M).obj (alternatingCechComplex f R) :=
  (alternatingCofaceMapComplex (ModuleCat R)).mapIso (cechConerveIso f M) ≪≫
    (eqToIso
      (Functor.congr_obj
        (tensor_alternatingCofaceMapComplex M)
        (ringArrow f).cechConerve)).symm

/-- Helper for Lemma 15.29.2: the degreewise comparison between the extended module-valued Čech
complex and the tensor image of the ring-valued extended Čech complex. -/
private noncomputable def extendedAlternatingCechComplex_componentIso (i : ℕ) :
    (extendedAlternatingCechComplex f M).X i ≅
      (((tensorLeft (of R M)).mapHomologicalComplex (up ℕ)).obj
        (extendedAlternatingCechComplex f R)).X i :=
  match i with
  | 0 => by
      simpa [extendedAlternatingCechComplex] using
        (ρ_ (of R M)).symm
  | n + 1 => by
      simpa [extendedAlternatingCechComplex] using
        (HomologicalComplex.eval (ModuleCat R) (up ℕ) n).mapIso
          (ordinaryIso f M)

/-- Helper for Lemma 15.29.2: the degreewise comparison isomorphisms commute with the extended
alternating Čech differentials. -/
private theorem extendedAlternatingCechComplex_componentIso_hom_comm :
    ∀ i j,
      (ComplexShape.up ℕ).Rel i j →
        (extendedAlternatingCechComplex_componentIso (f := f) (M := M) i).hom ≫
            (((tensorLeft (of R M)).mapHomologicalComplex (up ℕ)).obj
              (extendedAlternatingCechComplex f R)).d i j =
          (extendedAlternatingCechComplex f M).d i j ≫
            (extendedAlternatingCechComplex_componentIso (f := f) (M := M) j).hom := by
  intro i j hij
  -- The extended complex has only two genuine boundary shapes: the augmentation `0 ⟶ 1`
  -- and the inherited differentials of the ordinary alternating Čech complex in positive degree.
  -- TODO: after rewriting the augmented differentials by `augment_d_zero_one` and
  -- `augment_d_succ_succ`, the remaining mismatch is the packaged transport hidden inside
  -- `extendedAlternatingCechComplex_componentIso`. The next plan should isolate exactly that
  -- transport as a standalone rewrite-compatible lemma.
  sorry

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
    (extendedAlternatingCechComplex_componentIso (f := f) (M := M))
    (extendedAlternatingCechComplex_componentIso_hom_comm (f := f) (M := M))

end
