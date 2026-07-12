import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Projective
import StacksProject_2024.Chap12.Lemma_12_24_11
import StacksProject_2024.Chap12.Lemma_12_25_1
import StacksProject_2024.Chap10.Lemma_10_71_1
import StacksProject_2024.Chap13.Lemma_13_15_5
import StacksProject_2024.Chap13.Lemma_13_19_3
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Lemma_15_59_3
import StacksProject_2024.Chap15.Lemma_15_59_14
import StacksProject_2024.Chap15.Lemma_15_59_15
import StacksProject_2024.Chap15.Lemma_15_67_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped DerivedTensorProduct

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {a b c d : ℤ}

local notation "DModB" => DerivedCategory (ModuleCat B)
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "HA" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "HB" => DerivedCategory.homologyFunctor (ModuleCat B)

/-- Helper for Lemma 15.67.10: the stable degree-zero embedding of `A`-modules into `D(A)`. -/
private abbrev single₀A : ModuleCat A ⥤ DModA :=
  DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/-- Helper for Lemma 15.67.10: the stable degree-zero embedding of `B`-modules into `D(B)`. -/
private abbrev single₀B : ModuleCat B ⥤ DModB :=
  DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ)

/-- Helper for Lemma 15.67.10: exact restriction of scalars on derived categories. -/
private abbrev restrictDerived : DModB ⥤ DModA :=
  Functor.mapDerivedCategory (ModuleCat.restrictScalars (algebraMap A B))

/-- Helper for Lemma 15.67.10: extend a chain-level free resolution to the cochain model used by
the source proof. -/
private abbrev resolutionView
    (P : ChainComplex (ModuleCat A) ℕ) : CochainComplex (ModuleCat A) ℤ :=
  P.extend ComplexShape.embeddingDownNat

/-- Helper for Lemma 15.67.10: the extended free-resolution model still represents `M[0]` in
`D(A)`. -/
private noncomputable def resolution_view_iso_single_zero
    (M : ModuleCat A)
    (P : ChainComplex (ModuleCat A) ℕ)
    (π : P ⟶ (ChainComplex.single₀ (ModuleCat A)).obj M)
    [ChainComplex.IsFreeResolution π] :
    DerivedCategory.Q.obj (resolutionView (A := A) P) ≅ (single₀A.obj M) := by
  let f :
      DerivedCategory.Q.obj (resolutionView (A := A) P) ⟶
        DerivedCategory.Q.obj
          (((ChainComplex.single₀ (ModuleCat A)).obj M).extend ComplexShape.embeddingDownNat) :=
    DerivedCategory.Q.map (HomologicalComplex.extendMap π ComplexShape.embeddingDownNat)
  have hf : IsIso f := by
    -- Proof comment: extending the augmentation by zero preserves the free-resolution
    -- quasi-isomorphism.
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let e :
      DerivedCategory.Q.obj (resolutionView (A := A) P) ≅
        DerivedCategory.Q.obj
          (((ChainComplex.single₀ (ModuleCat A)).obj M).extend ComplexShape.embeddingDownNat) :=
    asIso f
  -- Proof comment: rewrite the extended single complex back to the canonical derived object
  -- `M[0]`.
  exact
    e ≪≫
      (DerivedCategory.Q.mapIso
        (HomologicalComplex.extendSingleIso
          ComplexShape.embeddingDownNat M (0 : ℕ) (0 : ℤ) rfl)) ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app M).symm

/-- Helper for Lemma 15.67.10: restricting scalars from `B` to `A` commutes with homology on
derived categories of modules. -/
private noncomputable def restrictScalars_homology_iso
    (L : DModB) (i : ℤ) :
    (HA i).obj ((restrictDerived (A := A) (B := B)).obj L) ≅
      (ModuleCat.restrictScalars (algebraMap A B)).obj ((HB i).obj L) := by
  let K := DerivedCategory.Q.objPreimage L
  let FK := ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  let eB :
      (HB i).obj L ≅ K.homology i :=
    ((HB i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat B) i).app K
  -- Proof comment: pass to a chosen cochain model of `L`, compare strict homology before and
  -- after restriction, and then return to the derived-category homology objects.
  exact
    (HA i).mapIso
        ((((restrictDerived (A := A) (B := B)).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm) ≪≫
          ((ModuleCat.restrictScalars
            (algebraMap A B)).mapDerivedCategoryFactors.app K)) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat A) i).app FK ≪≫
      (K.sc i).mapHomologyIso (ModuleCat.restrictScalars (algebraMap A B)) ≪≫
      (ModuleCat.restrictScalars (algebraMap A B)).mapIso eB.symm

/-- Helper for Lemma 15.67.10: exact restriction of scalars commutes with derived tensor
products. -/
private noncomputable def restrict_scalars_derivedTensorProduct_iso
    (K L : DModB) :
    ((restrictDerived (A := A) (B := B)).obj (K ⊗[B]^L L)) ≅
      (((restrictDerived (A := A) (B := B)).obj K) ⊗[A]^L
        ((restrictDerived (A := A) (B := B)).obj L)) :=
  -- TODO: build the monoidal comparison for exact derived restriction of scalars and use it to
  -- transport `K ⊗[B]^L L` to the `A`-linear derived tensor product of the restricted factors.
  sorry

/-- Helper for Lemma 15.67.10: the tensor bicomplex whose total complex is the ordinary tensor
product complex. -/
private abbrev tensor_bicomplex
    (E N : CochainComplex (ModuleCat B) ℤ) :
    HomologicalComplex₂ (ModuleCat B) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((curriedTensor (ModuleCat B)).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj E).obj N

/-- Helper for Lemma 15.67.10: totalizing the tensor bicomplex recovers the ordinary tensor
product complex. -/
private noncomputable def tensor_bicomplex_total_iso_tensorObj
    (E N : CochainComplex (ModuleCat B) ℤ) :
    HomologicalComplex₂.total (tensor_bicomplex (B := B) E N) (ComplexShape.up ℤ) ≅
      HomologicalComplex.tensorObj E N := by
  -- Proof comment: both sides are the same tensor-totalization construction.
  exact Iso.refl _

/-- Helper for Lemma 15.67.10: if the left tensor factor is zero in degree `p`, then the
corresponding tensor-bicomplex term is zero. -/
private theorem tensor_bicomplex_term_isZero_of_left_isZero
    {E N : CochainComplex (ModuleCat B) ℤ} {p q : ℤ}
    (hEzero : IsZero (E.X p)) :
    IsZero (((tensor_bicomplex (B := B) E N).X p).X q) := by
  -- TODO: braid the tensor term to `tensorLeft (N.X q)` applied to the zero object `E.X p`,
  -- then use `Functor.map_isZero` to conclude.
  sorry

/-- Helper for Lemma 15.67.10: the source proof computes the right test tensor factor from a
chosen free `A`-resolution of `M`. -/
private noncomputable def tensor_resolution_model_right_factor_iso
    (L : DModB)
    (M : ModuleCat A)
    (P : ChainComplex (ModuleCat A) ℕ)
    (π : P ⟶ (ChainComplex.single₀ (ModuleCat A)).obj M)
    [ChainComplex.IsFreeResolution π] :
    let PB :=
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (resolutionView (A := A) P))
    let N_M := HomologicalComplex.tensorObj (DerivedCategory.Q.objPreimage L) PB
    ((restrictDerived (A := A) (B := B)).obj (DerivedCategory.Q.obj N_M)) ≅
      (((restrictDerived (A := A) (B := B)).obj L) ⊗[A]^L (single₀A.obj M)) :=
  -- TODO: restrict the strict tensor-resolution model, apply
  -- `restrictScalars_tensorObj_extendScalars_iso`, then compare the two strict factors with
  -- `Q.objObjPreimageIso` and `resolution_view_iso_single_zero`.
  sorry

/-- Helper for Lemma 15.67.10: the source proof computes the tested tensor object from the bounded
flat representative `E` and the free-resolution model of `L \otimes_A^{\mathbf L} M`. -/
private noncomputable def tensor_resolution_model_iso_over_base_test
    (K L : DModB)
    {E : CochainComplex (ModuleCat B) ℤ}
    (eE : K ≅ DerivedCategory.Q.obj E)
    (M : ModuleCat A)
    (P : ChainComplex (ModuleCat A) ℕ)
    (π : P ⟶ (ChainComplex.single₀ (ModuleCat A)).obj M)
    [ChainComplex.IsFreeResolution π] :
    let PB :=
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (resolutionView (A := A) P))
    let N_M := HomologicalComplex.tensorObj (DerivedCategory.Q.objPreimage L) PB
    (((restrictDerived (A := A) (B := B)).obj (K ⊗[B]^L L)) ⊗[A]^L (single₀A.obj M)) ≅
      ((restrictDerived (A := A) (B := B)).obj
        (DerivedCategory.Q.obj (HomologicalComplex.tensorObj E N_M))) :=
  -- TODO: follow the source proof literally: move restriction past the derived tensor product,
  -- reassociate, replace `K` by `Q.obj E`, replace the right test factor by the strict model
  -- from `tensor_resolution_model_right_factor_iso`, and then collapse back to `Q.obj (tensorObj
  -- E N_M)` using `Functor.Monoidal.μIso` and `derivedCategory_tensorObj_iso_derivedTensorProduct`.
  sorry

/-- Helper for Lemma 15.67.10: the strict tensor-resolution model for
`L \otimes_A^{\mathbf L} M` has homology only in degrees `[c, d]`. -/
private theorem test_resolution_model_homology_isZero_of_hasTorAmplitudeIn
    (L : DModB)
    (hL :
      HasTorAmplitudeIn
        (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L) c d)
    (M : ModuleCat A)
    (P : ChainComplex (ModuleCat A) ℕ)
    (π : P ⟶ (ChainComplex.single₀ (ModuleCat A)).obj M)
    [ChainComplex.IsFreeResolution π]
    (q : ℤ)
    (hq : q ∉ Set.Icc c d) :
    let PB :=
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (resolutionView (A := A) P))
    let N_M := HomologicalComplex.tensorObj (DerivedCategory.Q.objPreimage L) PB
    IsZero (N_M.homology q) := by
  -- TODO: transport `hL M q hq` across `tensor_resolution_model_right_factor_iso`, then use
  -- `restrictScalars_homology_iso` and `homologyFunctorFactors` to descend to the strict
  -- `B`-complex homology object and reflect zero with `isZero_of_restrictScalars_obj`.
  sorry

/-- Helper for Lemma 15.67.10: the first page-one terms of the tensor bicomplex vanish outside
the rectangle `[a, b] × [c, d]`. -/
private theorem tensor_bicomplex_page_one_isZero_outside_rectangle
    (E N : CochainComplex (ModuleCat B) ℤ)
    (hGE : E.IsStrictlyGE a)
    (hLE : E.IsStrictlyLE b)
    (hFlat : E.IsTermwiseFlat)
    (hN : ∀ q : ℤ, q ∉ Set.Icc c d → IsZero (N.homology q))
    (p q : ℤ)
    (hpq : (p, q) ∉ Set.Icc a b ×ˢ Set.Icc c d) :
    IsZero (firstDoubleComplexPageOne (tensor_bicomplex (B := B) E N) p q) := by
  -- TODO: outside the horizontal interval, kill the middle term of the short complex computing
  -- column homology using `tensor_bicomplex_term_isZero_of_left_isZero`; outside the vertical
  -- interval, use exact tensoring by the flat module `E.X p` and `(N.sc q).mapHomologyIso`.
  sorry

/-- Helper for Lemma 15.67.10: once the first page-one support is confined to the rectangle
`[a, b] × [c, d]`, the total tensor complex has homology only in degrees `[a + c, b + d]`. -/
private theorem tensor_bicomplex_total_homology_isZero_outside_sum_interval
    (E N : CochainComplex (ModuleCat B) ℤ)
    (hGE : E.IsStrictlyGE a)
    (hLE : E.IsStrictlyLE b)
    (hFlat : E.IsTermwiseFlat)
    (hN : ∀ q : ℤ, q ∉ Set.Icc c d → IsZero (N.homology q))
    (i : ℤ)
    (hi : i ∉ Set.Icc (a + c) (b + d)) :
    IsZero ((HomologicalComplex.tensorObj E N).homology i) := by
  -- TODO: choose an associated spectral sequence for `firstDoubleComplexFilteredComplex
  -- (tensor_bicomplex E N)`, confine its page-one support to
  -- `Finset.product (Finset.Icc a b) (Finset.Icc c d)`, and then apply
  -- `cohomology_isZero_of_not_mem_totalDegree_image_support`.
  sorry

/-- Lemma 15.67.10: if `K^•` has tor-amplitude in `[a, b]` over `B` and `L^•`, viewed as a
complex of `A`-modules by restriction of scalars, has tor-amplitude in `[c, d]`, then
`K^• \otimes_B^{\mathbf L} L^•`, viewed as a complex of `A`-modules, has tor-amplitude in
`[a + c, b + d]`. -/
@[stacks 0B66]
theorem hasTorAmplitudeIn_restrictScalars_derivedTensorProduct
    (K L : DModB)
    (hK : HasTorAmplitudeIn K a b)
    (hL :
      HasTorAmplitudeIn
        (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L) c d) :
    HasTorAmplitudeIn
      (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj
        (K ⊗[B]^L L))
      (a + c) (b + d) := by
  intro M i hi
  -- Proof comment: follow the source proof by testing against an arbitrary `A`-module `M`,
  -- resolving it freely, and replacing `K` by a bounded flat representative over `B`.
  obtain ⟨P, π, hπ⟩ := module_exists_free_resolution (R := A) (M := M)
  letI : ChainComplex.IsFreeResolution π := hπ
  obtain ⟨E, eE, hEGE, hELE, hEFlat⟩ :=
    (hasTorAmplitudeIn_iff_exists_flat_representative (R := B) K a b).1 hK
  let PB :=
    (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (resolutionView (A := A) P))
  let N_M : CochainComplex (ModuleCat B) ℤ :=
    HomologicalComplex.tensorObj (DerivedCategory.Q.objPreimage L) PB
  let eM := resolution_view_iso_single_zero (A := A) M P π
  let eHi := restrictScalars_homology_iso (A := A) (B := B) L i
  let _ := hEGE
  let _ := hELE
  let _ := hEFlat
  let _ := eE
  let _ := N_M
  let _ := eM
  let _ := eHi
  have hTensorModel :
      IsZero ((HomologicalComplex.tensorObj E N_M).homology i) :=
    tensor_bicomplex_total_homology_isZero_outside_sum_interval
      E N_M hEGE hELE hEFlat
      (fun q hq ↦
        test_resolution_model_homology_isZero_of_hasTorAmplitudeIn
          (A := A) (B := B) (c := c) (d := d) L hL M P π q hq)
      i hi
  let eTest :=
    tensor_resolution_model_iso_over_base_test
      (A := A) (B := B) K L (E := E) eE M P π
  have hRestrictedTensor :
      IsZero
        ((ModuleCat.restrictScalars (algebraMap A B)).obj
          ((HB i).obj (DerivedCategory.Q.obj (HomologicalComplex.tensorObj E N_M)))) := by
    -- Proof comment: compute the homology of the localized strict tensor model and then restrict
    -- scalars on the resulting `B`-module.
    have hRestrictedStrict :
        IsZero
          ((ModuleCat.restrictScalars (algebraMap A B)).obj
            ((HomologicalComplex.tensorObj E N_M).homology i)) :=
      (ModuleCat.restrictScalars (algebraMap A B)).map_isZero hTensorModel
    exact
      ((ModuleCat.restrictScalars (algebraMap A B)).mapIso
        ((DerivedCategory.homologyFunctorFactors (ModuleCat B) i).app
          (HomologicalComplex.tensorObj E N_M))).isZero_iff.2
        hRestrictedStrict
  have hModel :
      IsZero
        ((HA i).obj
          (((restrictDerived (A := A) (B := B)).obj
            (DerivedCategory.Q.obj (HomologicalComplex.tensorObj E N_M))))) := by
    -- Proof comment: restriction of scalars commutes with derived homology, so the vanishing of
    -- the restricted strict homology object returns to the derived-side test object.
    exact
      (restrictScalars_homology_iso (A := A) (B := B)
        (DerivedCategory.Q.obj (HomologicalComplex.tensorObj E N_M)) i).isZero_iff.2
        hRestrictedTensor
  -- Proof comment: transport the vanishing statement back across the chosen comparison from the
  -- tested derived tensor object to the strict tensor-resolution model.
  exact hModel.of_iso ((HA i).mapIso eTest)

end

end CategoryTheory
