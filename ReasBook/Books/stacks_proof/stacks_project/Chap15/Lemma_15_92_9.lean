import Mathlib
import StacksProject_2024.Chap10.Lemma_10_24_5
import StacksProject_2024.Chap15.Lemma_15_74_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open ModuleCat.MonoidalCategory
open scoped DerivedTensorProduct TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.DerivedCategory

section

variable {A : Type u} [CommRing A]

private abbrev DMod_ (A : Type u) [CommRing A] := DerivedCategory (ModuleCat.{u} A)
local notation "DMod" => DMod_ A
local notation "RHomPkg" => MonoidalClosed DMod
private abbrev Cpx_ (A : Type u) [CommRing A] := CochainComplex (ModuleCat.{u} A) ℤ
local notation "Cpx" => Cpx_ A
private abbrev KMod_ (A : Type u) [CommRing A] := HomotopyCategory (ModuleCat.{u} A) (up ℤ)
local notation "KMod" => KMod_ A
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
private noncomputable abbrev single₀_ (A : Type u) [CommRing A] :
    ModuleCat.{u} A ⥤ DMod_ A :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} A) (0 : ℤ) :
    ModuleCat.{u} A ⥤ DMod_ A)
local notation "single₀" => single₀_ A

/-- Helper for Lemma 15.92.9: the textbook localization-away object
`R\mathrm{Hom}_A(A_f, K)` used in this file. -/
private noncomputable abbrev localizationAwayT_core
    (H : RHomPkg) (f : A) (K : DMod) : DMod :=
  letI : Closed ((single₀).obj (ModuleCat.of A (Localization.Away f))) := H.closed _
  (ihom ((single₀).obj (ModuleCat.of A (Localization.Away f)))).obj K

local notation "localizationAwayT" => localizationAwayT_core

private abbrev singleZeroCpx (M : ModuleCat.{u} A) : Cpx :=
  (CochainComplex.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).obj M

local instance : MonoidalCategory KMod :=
  homotopyCategory_monoidalCategory

/-- Helper for Lemma 15.92.9: the quotient functor from cochain complexes to the derived category
carries its standard monoidal structure. -/
private noncomputable instance quotientFunctorMonoidal :
    (DerivedCategory.Q : Cpx ⥤ DMod).Monoidal := by
  -- Match the canonical owner used in the Chapter 15 derived-tensor API.
  change (((HomotopyCategory.quotient (ModuleCat.{u} A) (up ℤ)) ⋙ Qh)).Monoidal
  infer_instance

section Monoidal

local instance : MonoidalCategory DMod := inferInstance

private noncomputable abbrev localizationAwayTensorLinearEquiv
    (f g : A) :
    Localization.Away f ⊗[A] Localization.Away g ≃ₗ[A] Localization.Away (f * g) :=
  ((LocalizedModule.equivTensorProduct (Submonoid.powers f) (Localization.Away g)).symm.restrictScalars A) ≪≫ₗ
    awayMulLinearEquiv g f A ≪≫ₗ
      awayEqLinearEquiv A (mul_comm g f)

private noncomputable abbrev localizationAwayTensorModuleIso
    (f g : A) :
    ModuleCat.of A (Localization.Away f ⊗[A] Localization.Away g) ≅
      ModuleCat.of A (Localization.Away (f * g)) :=
  (localizationAwayTensorLinearEquiv f g).toModuleIso

/-- Helper for Lemma 15.92.9: postcomposing a descended tensor-totalization map can be checked on
each `(p,q)` summand. -/
@[reassoc]
private theorem iTensorObj_mapBifunctorDesc_assoc
    {K L : Cpx} (n : ℤ) {B C : ModuleCat A}
    (f : ∀ p q
      (_h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor (ModuleCat.{u} A)).obj (K.X p)).obj (L.X q) ⟶ B)
    (u : B ⟶ C) (p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫
        HomologicalComplex.mapBifunctorDesc
          (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat.{u} A))
          (c := ComplexShape.up ℤ) (A := B) (j := n) f ≫ u =
      f p q h ≫ u := by
  -- Cross the `tensorObj` abbreviation once, then postcompose the owner universal-property
  -- formula `ι_mapBifunctorDesc`.
  simpa only [HomologicalComplex.ιTensorObj] using
    congrArg (fun t ↦ t ≫ u)
      (HomologicalComplex.ι_mapBifunctorDesc
        (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat.{u} A))
        (c := ComplexShape.up ℤ) (A := B) (j := n) (f := f) p q h)

/-- Helper for Lemma 15.92.9: away from degree `0`, the single complex contributes a zero summand
to the tensor totalization. -/
private theorem tensor_single0_off_diagonal_isZero
    (E : Cpx) (N : ModuleCat A) (p q : ℤ) (hq : q ≠ 0) :
    CategoryTheory.Limits.IsZero (((curriedTensor (ModuleCat.{u} A)).obj (E.X p)).obj
      ((singleZeroCpx N).X q)) := by
  -- Apply `tensorLeft (E.X p)` to the zero object occurring in the single complex away from
  -- degree `0`.
  exact
    CategoryTheory.Functor.map_isZero ((curriedTensor (ModuleCat.{u} A)).obj (E.X p))
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) N q hq)

/-- Helper for Lemma 15.92.9: on the surviving degree-`0` summand, tensoring with the single
complex is exactly right tensoring by the underlying module. -/
private noncomputable def tensor_single0_diagonal_iso
    (E : Cpx) (N : ModuleCat A) (n : ℤ) :
    ((curriedTensor (ModuleCat.{u} A)).obj (E.X n)).obj
      ((singleZeroCpx N).X 0) ≅
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).X n := by
  -- The right-tensor complex is defined degreewise, so only the canonical identification of the
  -- degree-`0` term of the single complex with `N` remains.
  simpa using
    CategoryTheory.Functor.mapIso ((curriedTensor (ModuleCat.{u} A)).obj (E.X n))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) N)

/-- Helper for Lemma 15.92.9: the forward degreewise comparison keeps only the unique diagonal
summand of the tensor totalization. -/
private noncomputable def tensor_single0_component_hom
    (E : Cpx) (N : ModuleCat A) (n : ℤ) :
    (HomologicalComplex.tensorObj E (singleZeroCpx N)).X n ⟶
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := E)
    (K₂ := singleZeroCpx N)
    (F := curriedTensor (ModuleCat.{u} A))
    (c := ComplexShape.up ℤ)
    (A := (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n)
    (j := n)
    (fun p q h ↦ by
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h
        subst p
        exact (tensor_single0_diagonal_iso E N n).hom
      · exact 0)

/-- Helper for Lemma 15.92.9: on the surviving diagonal summand, the forward comparison is the
canonical degreewise tensor identification. -/
@[reassoc]
private theorem tensor_single0_component_hom_diag
    (E : Cpx) (N : ModuleCat A) (n : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n) :
    HomologicalComplex.ιTensorObj E (singleZeroCpx N) n 0 n h ≫
      tensor_single0_component_hom E N n =
        (tensor_single0_diagonal_iso E N n).hom := by
  let B :
      ModuleCat A :=
    (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n
  let f : ∀ p q
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor (ModuleCat.{u} A)).obj (E.X p)).obj ((singleZeroCpx N).X q) ⟶ B :=
    fun p q h' ↦ by
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h'
        subst p
        exact (tensor_single0_diagonal_iso E N n).hom
      · exact 0
  -- Evaluate the descended tensor map on the unique surviving `(n,0)` summand.
  simpa [tensor_single0_component_hom, B, f] using
    (iTensorObj_mapBifunctorDesc_assoc
      (K := E)
      (L := singleZeroCpx N)
      (n := n) (B := B) (C := B) f (𝟙 B) n 0 h)

/-- Helper for Lemma 15.92.9: away from the diagonal summand, the forward comparison vanishes. -/
@[reassoc]
private theorem tensor_single0_component_hom_off_diagonal
    (E : Cpx) (N : ModuleCat A) (n p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n)
    (hq : q ≠ 0) :
    HomologicalComplex.ιTensorObj E (singleZeroCpx N) p q n h ≫
      tensor_single0_component_hom E N n =
        0 := by
  let B :
      ModuleCat A :=
    (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n
  let f : ∀ p' q'
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p', q') = n),
      ((curriedTensor (ModuleCat.{u} A)).obj (E.X p')).obj ((singleZeroCpx N).X q') ⟶ B :=
    fun p' q' h' ↦ by
      by_cases hq' : q' = 0
      · subst hq'
        have hp' : p' = n := by simpa using h'
        subst p'
        exact (tensor_single0_diagonal_iso E N n).hom
      · exact 0
  -- Off the diagonal, the defining branch of the descended map is literally zero.
  simpa [tensor_single0_component_hom, B, f, hq] using
    (iTensorObj_mapBifunctorDesc_assoc
      (K := E)
      (L := singleZeroCpx N)
      (n := n) (B := B) (C := B) f (𝟙 B) p q h)

/-- Helper for Lemma 15.92.9: the inverse degreewise comparison reinserts the surviving diagonal
summand into the tensor totalization. -/
private noncomputable def tensor_single0_component_inv
    (E : Cpx) (N : ModuleCat A) (n : ℤ) :
    (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n ⟶
      (HomologicalComplex.tensorObj E (singleZeroCpx N)).X n :=
  (tensor_single0_diagonal_iso E N n).inv ≫
    HomologicalComplex.ιTensorObj E (singleZeroCpx N) n 0 n
      (by simp)

/-- Helper for Lemma 15.92.9: in each total degree, tensoring with a degree-zero single complex
collapses to the unique surviving diagonal summand. -/
private noncomputable def tensor_single0_component_iso
    (E : Cpx) (N : ModuleCat A) (n : ℤ) :
    (HomologicalComplex.tensorObj E (singleZeroCpx N)).X n ≅
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).X n :=
  { hom := tensor_single0_component_hom E N n
    inv := tensor_single0_component_inv E N n
    hom_inv_id := by
      -- Check the identity on the tensor totalization summandwise.
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h
        subst p
        change
          ((HomologicalComplex.ιTensorObj E (singleZeroCpx N) n 0 n h ≫
              tensor_single0_component_hom E N n) ≫
            tensor_single0_component_inv E N n) =
            HomologicalComplex.ιTensorObj E (singleZeroCpx N) n 0 n h ≫
              𝟙 ((HomologicalComplex.tensorObj E (singleZeroCpx N)).X n)
        simpa [tensor_single0_component_inv, Category.assoc] using
          congrArg (fun k ↦ k ≫ tensor_single0_component_inv E N n)
            (tensor_single0_component_hom_diag E N n h)
      · change
          ((HomologicalComplex.ιTensorObj E (singleZeroCpx N) p q n h ≫
              tensor_single0_component_hom E N n) ≫
            tensor_single0_component_inv E N n) =
            HomologicalComplex.ιTensorObj E (singleZeroCpx N) p q n h ≫
              𝟙 ((HomologicalComplex.tensorObj E (singleZeroCpx N)).X n)
        rw [tensor_single0_component_hom_off_diagonal E N n p q h hq]
        simp only [CategoryTheory.Limits.zero_comp, Category.comp_id]
        symm
        exact (tensor_single0_off_diagonal_isZero E N p q hq).eq_of_src _ _
    inv_hom_id := by
      let h0 : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n := by
        simp
      -- Rewrite the middle composite to the diagonal isomorphism and cancel it immediately.
      change
        ((tensor_single0_diagonal_iso E N n).inv ≫
            HomologicalComplex.ιTensorObj E (singleZeroCpx N) n 0 n h0) ≫
          tensor_single0_component_hom E N n =
            𝟙 ((((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E).X n)
      calc
        ((tensor_single0_diagonal_iso E N n).inv ≫
            HomologicalComplex.ιTensorObj E (singleZeroCpx N) n 0 n h0) ≫
          tensor_single0_component_hom E N n
            = (tensor_single0_diagonal_iso E N n).inv ≫
                (HomologicalComplex.ιTensorObj E (singleZeroCpx N) n 0 n h0 ≫
                  tensor_single0_component_hom E N n) := by
                    simp [Category.assoc]
        _ = (tensor_single0_diagonal_iso E N n).inv ≫
              (tensor_single0_diagonal_iso E N n).hom := by
                simpa using
                  congrArg (fun k ↦ (tensor_single0_diagonal_iso E N n).inv ≫ k)
                    (tensor_single0_component_hom_diag E N n h0)
        _ = 𝟙 _ := by simp }

/-- Helper for Lemma 15.92.9: the diagonal tensor comparison is natural in the differential of
the left cochain complex. -/
private theorem tensor_single0_diagonal_iso_hom_naturality
    (E : Cpx) (N : ModuleCat A) (i j : ℤ)
    (_hij : (ComplexShape.up ℤ).Rel i j) :
    (tensor_single0_diagonal_iso E N i).hom ≫
        (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E).d i j =
      (((curriedTensor (ModuleCat.{u} A)).map (E.d i j)).app ((singleZeroCpx N).X 0)) ≫
        (tensor_single0_diagonal_iso E N j).hom := by
  -- The degreewise comparison is obtained by applying the tensor functor to `singleObjXSelf`.
  simpa [tensor_single0_diagonal_iso, CategoryTheory.Functor.mapHomologicalComplex_obj_d,
    singleZeroCpx] using
    (((curriedTensor (ModuleCat.{u} A)).map (E.d i j)).naturality
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) N).hom)

/-- Helper for Lemma 15.92.9: the inverse diagonal tensor comparison satisfies the same
naturality square rewritten for the chain-level inverse map. -/
private theorem tensor_single0_diagonal_iso_inv_naturality
    (E : Cpx) (N : ModuleCat A) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (tensor_single0_diagonal_iso E N i).inv ≫
        (((curriedTensor (ModuleCat.{u} A)).map (E.d i j)).app ((singleZeroCpx N).X 0)) =
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E).d i j ≫
        (tensor_single0_diagonal_iso E N j).inv := by
  -- Cancel the target diagonal isomorphism and reuse the forward naturality square.
  apply (cancel_mono (tensor_single0_diagonal_iso E N j).hom).1
  simpa [Category.assoc] using
    calc
      (tensor_single0_diagonal_iso E N i).inv ≫
          (((curriedTensor (ModuleCat.{u} A)).map (E.d i j)).app ((singleZeroCpx N).X 0)) ≫
          (tensor_single0_diagonal_iso E N j).hom
        = (tensor_single0_diagonal_iso E N i).inv ≫
            ((tensor_single0_diagonal_iso E N i).hom ≫
              (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj E).d i j) := by
            rw [tensor_single0_diagonal_iso_hom_naturality E N i j hij]
      _ =
          (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E).d i j := by
            simp

/-- Helper for Lemma 15.92.9: the inverse degreewise tensor comparison already respects the
cochain differential. -/
private theorem tensor_single0_component_inv_comm
    (E : Cpx) (N : ModuleCat A) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    tensor_single0_component_inv E N i ≫
        (HomologicalComplex.tensorObj E (singleZeroCpx N)).d i j =
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E).d i j ≫
        tensor_single0_component_inv E N j := by
  have hj : j = i + 1 := by
    simpa [ComplexShape.up, eq_comm] using hij
  subst hj
  -- Expand the total differential into its horizontal and vertical pieces; the vertical part is
  -- zero because the degree-zero single complex has zero outgoing differential.
  simp only [tensor_single0_component_inv, Category.assoc,
    HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq
      (K₁ := E)
      (K₂ := singleZeroCpx N)
      (F := curriedTensor (ModuleCat.{u} A))
      (c := ComplexShape.up ℤ)
      (h := (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))
      (i₂ := 0)
      (j := i + 1)
      (h' := by simp)]
  rw [HomologicalComplex.mapBifunctor.d₂_eq
      (K₁ := E)
      (K₂ := singleZeroCpx N)
      (F := curriedTensor (ModuleCat.{u} A))
      (c := ComplexShape.up ℤ)
      (i₁ := i)
      (h := (show (ComplexShape.up ℤ).Rel 0 (0 + 1) by simp))
      (j := i + 1)
      (h' := by simp)]
  have hsingle : ((singleZeroCpx N).d 0 (0 + 1)) = 0 := rfl
  rw [hsingle, Functor.map_zero, CategoryTheory.Limits.zero_comp, smul_zero,
    CategoryTheory.Limits.comp_zero, add_zero]
  rw [show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, 0) = 1 by
      rfl, one_smul]
  rw [← Category.assoc]
  rw [tensor_single0_diagonal_iso_inv_naturality
      (E := E)
      (N := N)
      (i := i)
      (j := i + 1)
      (hij := (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))]
  simp [HomologicalComplex.ιTensorObj, Category.assoc]

/-- Helper for Lemma 15.92.9: tensoring a cochain complex with a degree-zero single complex is
canonically the same as tensoring on the right by the underlying module. -/
private noncomputable def tensor_single0_complex_iso
    (E : Cpx) (N : ModuleCat A) :
    HomologicalComplex.tensorObj E (singleZeroCpx N) ≅
      ((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ tensor_single0_component_iso E N n)
    (fun i j hij ↦ by
      -- Rewrite the inverse chain-map square into the forward orientation expected by
      -- `isoOfComponents`.
      apply (cancel_mono (tensor_single0_component_iso E N j).inv).1
      apply (cancel_epi (tensor_single0_component_iso E N i).inv).1
      simpa [Category.assoc] using
        (tensor_single0_component_inv_comm E N i j hij).symm)

/-- Helper for Lemma 15.92.9: right tensoring a degree-zero single complex stays degree-zero. -/
private noncomputable def singleZeroTensorRightComplexIso
    (M N : ModuleCat A) :
    ((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (singleZeroCpx M) ≅
      singleZeroCpx (ModuleCat.of A ((↑M) ⊗[A] ↑N)) :=
  -- The canonical `singleMapHomologicalComplex` owner already records that mapping a degree-zero
  -- single complex through `tensorRight N` is the degree-zero single complex of the tensor module.
  (HomologicalComplex.singleMapHomologicalComplex
    (CategoryTheory.MonoidalCategory.tensorRight N) (ComplexShape.up ℤ) (0 : ℤ)).app M

/-- Helper for Lemma 15.92.9: tensoring two degree-zero single cochain complexes is canonically
the degree-zero single complex of the tensor product module. -/
private noncomputable def singleZeroTensorComplexIso
    (M N : ModuleCat A) :
    HomologicalComplex.tensorObj (singleZeroCpx M) (singleZeroCpx N) ≅
      singleZeroCpx (ModuleCat.of A ((↑M) ⊗[A] ↑N)) := by
  -- Route correction: the literal equality route is too rigid, so we first compare
  -- `M[0] ⊗ N[0]` with right tensoring `M[0]` by `N`, and then use the canonical
  -- `singleMapHomologicalComplex` transport for `tensorRight N`.
  exact
    tensor_single0_complex_iso (singleZeroCpx M) N ≪≫
      singleZeroTensorRightComplexIso M N

private noncomputable def singleZeroDerivedTensorModuleIso
    (M N : ModuleCat A) :
    ((single₀).obj M ⊗[A]^L (single₀).obj N) ≅
      (single₀).obj (ModuleCat.of A ((↑M) ⊗[A] ↑N)) :=
  -- First pass from the derived tensor product to `Q` of the tensor complex, then replace that
  -- tensor complex by the degree-zero tensor-module complex through the chain-level bridge above.
  ((((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      (ModuleCat.of A ((↑M) ⊗[A] ↑N))).symm) ≪≫
    (DerivedCategory.Q.mapIso (singleZeroTensorComplexIso M N).symm) ≪≫
      (Functor.Monoidal.μIso (DerivedCategory.Q : Cpx ⥤ DMod) (singleZeroCpx M)
        (singleZeroCpx N)).symm ≪≫
        (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app M) ⊗ᵢ
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app N)) ≪≫
          derivedCategory_tensorObj_iso_derivedTensorProduct ((single₀).obj M)
            ((single₀).obj N)).symm

private noncomputable def localizationAwayTensorIso
    (f g : A) :
    ((single₀).obj (ModuleCat.of A (Localization.Away f)) ⊗[A]^L
      (single₀).obj (ModuleCat.of A (Localization.Away g))) ≅
      (single₀).obj (ModuleCat.of A (Localization.Away (f * g))) :=
  singleZeroDerivedTensorModuleIso
      (ModuleCat.of A (Localization.Away f))
      (ModuleCat.of A (Localization.Away g)) ≪≫
    (single₀).mapIso (localizationAwayTensorModuleIso f g)

/- Domain-style sampling for Lemma 15.92.9:
- primary domain: localization-away objects `T(K, f)` in the closed monoidal derived category
  `D(A)`;
- sampled owner declarations:
  `CategoryTheory.DerivedCategory.localizationAwayT`,
  `CategoryTheory.derivedInternalHomTensorIso`,
  `awayMulLinearEquiv`,
  `CategoryTheory.DerivedCategory.localizationAwayT_isDerivedLimit`,
  `CategoryTheory.derivedInternalHom_comp`;
- best owner abstraction: the chapter owner `localizationAwayT H f K` for the textbook object
  `T(K, f)`;
- primitive data: `H : RHomPkg`, `f g : A`, and `K : DMod`;
- derived API: the product-localization comparison below.

Layer triage:
- `source-facing`: `localizationAwayT_mul`;
- `core/canonical`: `localizationAwayT H f K` and the currying comparison
  `derivedInternalHomTensorIso`;
- `bridge/view`: the identification of iterated away localizations with localization away from
  `f * g`, concretely routed through the module-side owner `awayMulLinearEquiv` on
  `Localization.Away g` and then transported to degree-zero objects in `D(A)`, expressed as an
  object-level `Iso`. -/

-- Proof sketch: combine the tensor-Hom currying comparison from Lemma `15.74.1` with the
-- module-side owner `awayMulLinearEquiv` identifying iterated away localization with
-- localization away from `f * g`, transported to the degree-zero objects `A_f`, `A_g`, and
-- `A_{fg}` in `D(A)`.
/-- The canonical comparison morphism
`T(T(K, g), f) ⟶ T(K, fg)` obtained by currying together the two localization-away internal-Hom
owners and then identifying the degree-zero localized tensor factor with `A_{fg}[0]`. -/
private noncomputable def localizationAwayT_mul_hom
    (H : RHomPkg) (f g : A) (K : DMod) :
    localizationAwayT H f (localizationAwayT H g K) ⟶ localizationAwayT H (f * g) K :=
  (derivedInternalHomTensorIso H
      ((single₀).obj (ModuleCat.of A (Localization.Away f)))
      ((single₀).obj (ModuleCat.of A (Localization.Away g)))
      K).hom ≫
    derivedInternalHomMap H (localizationAwayTensorIso f g).inv (𝟙 K)

/-- Helper for Lemma 15.92.9: an isomorphism in the tensor source variable induces the expected
isomorphism on the derived internal Hom object. -/
private noncomputable def localizationAwayTensorInternalHomIso
    (H : RHomPkg) (f g : A) (K : DMod) :
    (letI := H
     (ihom (((single₀).obj (ModuleCat.of A (Localization.Away f))) ⊗[A]^L
       ((single₀).obj (ModuleCat.of A (Localization.Away g))))).obj K) ≅
      localizationAwayT H (f * g) K := by
  letI := H
  refine
    { hom := (MonoidalClosed.pre (localizationAwayTensorIso f g).inv).app K
      inv := (MonoidalClosed.pre (localizationAwayTensorIso f g).hom).app K
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · simpa using
      (congrArg (fun α ↦ α.app K)
        (MonoidalClosed.pre_map (localizationAwayTensorIso f g).hom
          (localizationAwayTensorIso f g).inv)).symm
  · simpa using
      (congrArg (fun α ↦ α.app K)
        (MonoidalClosed.pre_map (localizationAwayTensorIso f g).inv
          (localizationAwayTensorIso f g).hom)).symm

/-- Lemma 15.92.9: the textbook localization-away object satisfies
`T(T(K, g), f) ≃ T(K, fg)`. This is the owner-level form of the iterated derived internal-Hom
comparison for the degree-zero localization objects `A_f`, `A_g`, and `A_{fg}`. -/
@[stacks 0A6C]
noncomputable abbrev localizationAwayT_mul
    (H : RHomPkg) (f g : A) (K : DMod) :
    localizationAwayT H f (localizationAwayT H g K) ≅ localizationAwayT H (f * g) K := by
  letI := H
  exact
    (derivedInternalHomTensorIso H
      ((single₀).obj (ModuleCat.of A (Localization.Away f)))
      ((single₀).obj (ModuleCat.of A (Localization.Away g)))
      K) ≪≫
    localizationAwayTensorInternalHomIso H f g K

end Monoidal

end

end CategoryTheory.DerivedCategory
