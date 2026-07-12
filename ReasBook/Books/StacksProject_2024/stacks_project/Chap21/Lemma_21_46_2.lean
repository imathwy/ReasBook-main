import Mathlib.CategoryTheory.Abelian.NonPreadditive
import StacksProject_2024.Chap12.Definition_12_19_3
import StacksProject_2024.Chap13.Definition_13_8_1
import StacksProject_2024.Chap18.RingedSiteModuleCategory
import StacksProject_2024.Chap21.Definition_21_17_2
import StacksProject_2024.Chap21.Lemma_21_17_15

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [hAbelian : Abelian (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ M : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj M).Additive]
variable [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "single₀" => CochainComplex.singleFunctor Mod (0 : ℤ)

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)]

/- Domain-style sampling for Lemma 21.46.2:
- primary domain: cochain-level tor-amplitude and flatness on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.IsFlat`,
  `CochainComplex.minus`,
  `CochainComplex.singleFunctor`;
- best owner abstraction: the ambient owner category is `ringedSiteModuleCategory J 𝒪`, while the
  theorem itself remains source-facing because it is a truncation/cokernel statement about an
  actual cochain complex, not merely a derived-category predicate;
- primitive data: the complex `E`, bounded-above and termwise-flat hypotheses, and the exactness
  of `E ⊗ ℱ[0]` outside `[a, b]`;
- derived API: the flatness conclusion for the canonical cokernel `cokernel (E.dFrom (a - 1))`.

Source/core/bridge triage:
- `source-facing`: this lemma, which identifies the new degree-`a` term after truncation;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪`, `IsFlat 𝒪`, `CochainComplex.minus`, and the
  canonical degree-zero `ℤ`-indexed cochain owner `single₀`;
- `bridge/view`: none. The theorem is not an exact-interface wrapper around an existing owner
  theorem, so the refinement should keep the theorem and only delete the local duplicate wheel
  around the ambient module category. -/

-- Proof sketch: because `E` is bounded above with flat terms, Lemma `21.17.8` makes `E` K-flat,
-- so tensoring `E` with any `\mathcal O`-module computes derived tensoring with `Q(E)`. The
-- tor-amplitude hypothesis forces exactness in degree `a - 1` after tensoring with any module,
-- hence the tail ending in `cokernel(d^{a - 1})` is a flat resolution. Therefore `Tor₁` of this
-- cokernel with every module vanishes, and Lemma `21.17.15` yields flatness.
--
-- The sheafification hypotheses used by that proof route are implementation infrastructure rather
-- than mathematical inputs of the flatness criterion, so they do not appear in the theorem
-- statement.
omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: the degree `a - 1` lies outside the interval `[a, b]`. -/
private lemma sub_one_not_mem_Icc
    (a b : ℤ) :
    a - 1 ∉ Set.Icc a b := by
  -- The left endpoint of the interval is already too large for `a - 1`.
  intro h
  have hfalse : ¬ a ≤ a - 1 := by
    omega
  exact hfalse h.1

omit [MonoidalPreadditive Mod] hAbelian
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: postcompose the owner universal property
`HomologicalComplex.ι_mapBifunctorDesc` by a chosen morphism. -/
@[reassoc]
private theorem iTensorObj_mapBifunctorDesc_assoc
    (K L : CochainComplex Mod ℤ) (n : ℤ) {A B : Mod}
    (f : ∀ p q
      (_h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor Mod).obj (K.X p)).obj (L.X q) ⟶ A)
    (u : A ⟶ B) (p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫
        HomologicalComplex.mapBifunctorDesc
          f ≫ u =
      f p q h ≫ u := by
  simpa only [HomologicalComplex.ιTensorObj] using
    congrArg (fun t ↦ t ≫ u)
      (HomologicalComplex.ι_mapBifunctorDesc
        f p q h)

omit [MonoidalPreadditive Mod]
  [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
    CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]
  [(curriedTensor Mod).Additive]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: away from degree `0`, the degree-zero single complex contributes a
zero summand to the tensor totalization. -/
private theorem tensor_single0_off_diagonal_isZero
    (E : CochainComplex Mod ℤ) (ℱ : Mod) (p q : ℤ) (hq : q ≠ 0) :
    CategoryTheory.Limits.IsZero (((curriedTensor Mod).obj (E.X p)).obj
      (((single₀).obj ℱ).X q)) := by
  -- Apply left tensoring by `E.X p` to the zero object occurring in `ℱ[0]` away from degree `0`.
  exact
    CategoryTheory.Functor.map_isZero ((curriedTensor Mod).obj (E.X p))
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) ℱ q hq)

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: on the surviving degree-`0` summand, tensoring with `ℱ[0]`
identifies with right tensoring by `ℱ`. -/
private noncomputable def tensor_single0_diagonal_iso
    (E : CochainComplex Mod ℤ) (ℱ : Mod) (n : ℤ) :
    ((curriedTensor Mod).obj (E.X n)).obj (((single₀).obj ℱ).X 0) ≅
      (((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).X n := by
  -- The mapped complex is degreewise right tensoring, so only the degree-`0` identification in
  -- the single complex remains.
  simpa using
    CategoryTheory.Functor.mapIso ((curriedTensor Mod).obj (E.X n))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) ℱ)

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: the forward degreewise comparison keeps only the unique diagonal
summand of `E ⊗ ℱ[0]`. -/
private noncomputable def tensor_single0_component_hom
    (E : CochainComplex Mod ℤ) (ℱ : Mod) (n : ℤ) :
    (HomologicalComplex.tensorObj E ((single₀).obj ℱ)).X n ⟶
      (((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).X n :=
  HomologicalComplex.mapBifunctorDesc
    (fun p q h ↦ by
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h
        subst p
        exact (tensor_single0_diagonal_iso E ℱ n).hom
      · exact 0)

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [MonoidalPreadditive Mod]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: on the diagonal summand, the forward comparison is the expected
degreewise identification. -/
private theorem tensor_single0_component_hom_diag
    (E : CochainComplex Mod ℤ) (ℱ : Mod) (n : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n) :
    HomologicalComplex.ιTensorObj E ((single₀).obj ℱ) n 0 n h ≫
        tensor_single0_component_hom E ℱ n =
      (tensor_single0_diagonal_iso E ℱ n).hom := by
  let A : Mod :=
    (((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).X n
  let f : ∀ p q
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor Mod).obj (E.X p)).obj (((single₀).obj ℱ).X q) ⟶ A :=
    fun p q h' ↦ by
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h'
        subst p
        exact (tensor_single0_diagonal_iso E ℱ n).hom
      · exact 0
  -- Evaluate the descended tensor map on the unique surviving `(n, 0)` summand.
  simpa [tensor_single0_component_hom, A, f] using
    (iTensorObj_mapBifunctorDesc_assoc
      E ((single₀).obj ℱ) n f (𝟙 A) n 0 h)

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [MonoidalPreadditive Mod]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: off the diagonal, the forward comparison map is zero. -/
private theorem tensor_single0_component_hom_off_diagonal
    (E : CochainComplex Mod ℤ) (ℱ : Mod) (n p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n)
    (hq : q ≠ 0) :
    HomologicalComplex.ιTensorObj E ((single₀).obj ℱ) p q n h ≫
        tensor_single0_component_hom E ℱ n = 0 := by
  let A : Mod :=
    (((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).X n
  let f : ∀ p' q'
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p', q') = n),
      ((curriedTensor Mod).obj (E.X p')).obj (((single₀).obj ℱ).X q') ⟶ A :=
    fun p' q' h' ↦ by
      by_cases hq' : q' = 0
      · subst hq'
        have hp' : p' = n := by simpa using h'
        subst p'
        exact (tensor_single0_diagonal_iso E ℱ n).hom
      · exact 0
  -- Off the diagonal, the defining branch of the descended map is literally zero.
  simpa [tensor_single0_component_hom, A, f, hq] using
    (iTensorObj_mapBifunctorDesc_assoc
      E ((single₀).obj ℱ) n f (𝟙 A) p q h)

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: the inverse degreewise comparison reinserts the surviving diagonal
summand into the tensor totalization. -/
private noncomputable def tensor_single0_component_inv
    (E : CochainComplex Mod ℤ) (ℱ : Mod) (n : ℤ) :
    (((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).X n ⟶
      (HomologicalComplex.tensorObj E ((single₀).obj ℱ)).X n :=
  (tensor_single0_diagonal_iso E ℱ n).inv ≫
    HomologicalComplex.ιTensorObj E ((single₀).obj ℱ) n 0 n
      (by simp)

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: in each total degree, tensoring with the degree-zero single complex
`ℱ[0]` collapses to right tensoring by `ℱ`. -/
private noncomputable def tensor_single0_component_iso
    (E : CochainComplex Mod ℤ) (ℱ : Mod) (n : ℤ) :
    (HomologicalComplex.tensorObj E ((single₀).obj ℱ)).X n ≅
      (((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).X n :=
  { hom := tensor_single0_component_hom E ℱ n
    inv := tensor_single0_component_inv E ℱ n
    hom_inv_id := by
      -- Check the identity on the tensor totalization summandwise.
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h
        subst p
        change
          ((HomologicalComplex.ιTensorObj E ((single₀).obj ℱ) n 0 n h ≫
              tensor_single0_component_hom E ℱ n) ≫
            tensor_single0_component_inv E ℱ n) =
            HomologicalComplex.ιTensorObj E ((single₀).obj ℱ) n 0 n h ≫
              𝟙 ((HomologicalComplex.tensorObj E ((single₀).obj ℱ)).X n)
        simpa [tensor_single0_component_inv, Category.assoc] using
          congrArg (fun k ↦ k ≫ tensor_single0_component_inv E ℱ n)
            (tensor_single0_component_hom_diag E ℱ n h)
      · change
          ((HomologicalComplex.ιTensorObj E ((single₀).obj ℱ) p q n h ≫
              tensor_single0_component_hom E ℱ n) ≫
            tensor_single0_component_inv E ℱ n) =
            HomologicalComplex.ιTensorObj E ((single₀).obj ℱ) p q n h ≫
              𝟙 ((HomologicalComplex.tensorObj E ((single₀).obj ℱ)).X n)
        rw [tensor_single0_component_hom_off_diagonal E ℱ n p q h hq]
        simp only [CategoryTheory.Limits.zero_comp, Category.comp_id]
        symm
        exact (tensor_single0_off_diagonal_isZero E ℱ p q hq).eq_of_src _ _
    inv_hom_id := by
      let h0 : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n := by
        simp
      -- The inverse lands in the diagonal summand and cancels there immediately.
      change
        ((tensor_single0_diagonal_iso E ℱ n).inv ≫
            HomologicalComplex.ιTensorObj E ((single₀).obj ℱ) n 0 n h0) ≫
          tensor_single0_component_hom E ℱ n =
            𝟙 ((((tensorRight ℱ).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E).X n)
      calc
        ((tensor_single0_diagonal_iso E ℱ n).inv ≫
            HomologicalComplex.ιTensorObj E ((single₀).obj ℱ) n 0 n h0) ≫
          tensor_single0_component_hom E ℱ n
            = (tensor_single0_diagonal_iso E ℱ n).inv ≫
                (HomologicalComplex.ιTensorObj E ((single₀).obj ℱ) n 0 n h0 ≫
                  tensor_single0_component_hom E ℱ n) := by
                    simp [Category.assoc]
        _ = (tensor_single0_diagonal_iso E ℱ n).inv ≫
              (tensor_single0_diagonal_iso E ℱ n).hom := by
                simpa using
                  congrArg (fun k ↦ (tensor_single0_diagonal_iso E ℱ n).inv ≫ k)
                    (tensor_single0_component_hom_diag E ℱ n h0)
        _ = 𝟙 _ := by simp }

omit [MonoidalPreadditive Mod]
  [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
    CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]
  [∀ M : Mod, ((curriedTensor Mod).obj M).Additive]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: the diagonal comparison is natural in the differential of `E`. -/
private theorem tensor_single0_diagonal_iso_hom_naturality
    (E : CochainComplex Mod ℤ) (ℱ : Mod) (i j : ℤ)
    (_hij : (ComplexShape.up ℤ).Rel i j) :
    (tensor_single0_diagonal_iso E ℱ i).hom ≫
        (((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j =
      (((curriedTensor Mod).map (E.d i j)).app (((single₀).obj ℱ).X 0)) ≫
        (tensor_single0_diagonal_iso E ℱ j).hom := by
  -- Rewrite the diagonal comparison through `singleObjXSelf`.
  simpa [tensor_single0_diagonal_iso, CategoryTheory.Functor.mapHomologicalComplex_obj_d,
    CochainComplex.singleFunctor] using
    (((curriedTensor Mod).map (E.d i j)).naturality
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) ℱ).hom)

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [MonoidalPreadditive Mod]
  [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
    CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]
  [∀ M : Mod, ((curriedTensor Mod).obj M).Additive]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: the inverse diagonal comparison satisfies the same naturality
square rewritten for the inverse map. -/
private theorem tensor_single0_diagonal_iso_inv_naturality
    (E : CochainComplex Mod ℤ) (ℱ : Mod) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (tensor_single0_diagonal_iso E ℱ i).inv ≫
        (((curriedTensor Mod).map (E.d i j)).app (((single₀).obj ℱ).X 0)) =
      (((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j ≫
        (tensor_single0_diagonal_iso E ℱ j).inv := by
  -- Cancel the target diagonal isomorphism and reuse the forward square.
  apply (cancel_mono (tensor_single0_diagonal_iso E ℱ j).hom).1
  calc
    (tensor_single0_diagonal_iso E ℱ i).inv ≫
        (((curriedTensor Mod).map (E.d i j)).app (((single₀).obj ℱ).X 0)) ≫
        (tensor_single0_diagonal_iso E ℱ j).hom
      = (tensor_single0_diagonal_iso E ℱ i).inv ≫
          (tensor_single0_diagonal_iso E ℱ i).hom ≫
            (((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ (tensor_single0_diagonal_iso E ℱ i).inv ≫ k)
              (tensor_single0_diagonal_iso_hom_naturality E ℱ i j hij).symm
    _ = (((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j := by
      simpa [Category.assoc] using
        IsIso.inv_hom_id_assoc
          (tensor_single0_diagonal_iso E ℱ i).hom
          ((((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j)
    _ =
        ((((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j ≫
            (tensor_single0_diagonal_iso E ℱ j).inv) ≫
          (tensor_single0_diagonal_iso E ℱ j).hom := by
        simpa [Category.assoc] using
          (IsIso.hom_inv_id_assoc
            (tensor_single0_diagonal_iso E ℱ j).inv
            ((((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j)).symm

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [MonoidalPreadditive Mod]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: the inverse degreewise comparison already respects the cochain
differential. -/
private theorem tensor_single0_component_inv_comm
    (E : CochainComplex Mod ℤ) (ℱ : Mod) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    tensor_single0_component_inv E ℱ i ≫
        (HomologicalComplex.tensorObj E ((single₀).obj ℱ)).d i j =
      (((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j ≫
        tensor_single0_component_inv E ℱ j := by
  have hj : j = i + 1 := by
    simpa [ComplexShape.up, eq_comm] using hij
  subst hj
  -- Expand the total differential into its horizontal and vertical pieces; the vertical part is
  -- zero because the degree-zero single complex has zero outgoing differential.
  simp only [tensor_single0_component_inv, Category.assoc,
    HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq
      E ((single₀).obj ℱ) (curriedTensor Mod) (ComplexShape.up ℤ)
      (show (ComplexShape.up ℤ).Rel i (i + 1) by simp) 0 (i + 1) (by simp)]
  rw [HomologicalComplex.mapBifunctor.d₂_eq
      E ((single₀).obj ℱ) (curriedTensor Mod) (ComplexShape.up ℤ)
      i (show (ComplexShape.up ℤ).Rel 0 (0 + 1) by simp) (i + 1) (by simp)]
  have hsingle : (((single₀).obj ℱ).d 0 (0 + 1)) = 0 := rfl
  rw [hsingle, Functor.map_zero, CategoryTheory.Limits.zero_comp, smul_zero,
    CategoryTheory.Limits.comp_zero, add_zero]
  rw [show ComplexShape.ε₁
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, 0) = 1 by
      rfl, one_smul]
  rw [← Category.assoc]
  rw [tensor_single0_diagonal_iso_inv_naturality E ℱ i (i + 1)
      (show (ComplexShape.up ℤ).Rel i (i + 1) by simp)]
  simp [HomologicalComplex.ιTensorObj, Category.assoc]

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: tensoring a cochain complex with the degree-zero single complex
`ℱ[0]` is canonically the same as applying `tensorRight ℱ` degreewise. -/
private noncomputable def tensor_single0_complex_iso
    (E : CochainComplex Mod ℤ) (ℱ : Mod) :
    HomologicalComplex.tensorObj E ((single₀).obj ℱ) ≅
      ((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ tensor_single0_component_iso E ℱ n)
    (fun i j hij ↦ by
      -- Insert the inverse-component identities and rewrite using the inverse square.
      calc
        tensor_single0_component_hom E ℱ i ≫
            (((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j
          = tensor_single0_component_hom E ℱ i ≫
              ((((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j ≫
                tensor_single0_component_inv E ℱ j) ≫
              tensor_single0_component_hom E ℱ j := by
                calc
                  tensor_single0_component_hom E ℱ i ≫
                      (((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j
                    = (tensor_single0_component_hom E ℱ i ≫
                        (((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j) ≫
                        𝟙 _ := by simp
                  _ = (tensor_single0_component_hom E ℱ i ≫
                        (((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j) ≫
                        ((tensor_single0_component_iso E ℱ j).inv ≫
                          (tensor_single0_component_iso E ℱ j).hom) := by
                            rw [← (tensor_single0_component_iso E ℱ j).inv_hom_id]
                  _ = (tensor_single0_component_hom E ℱ i ≫
                        (((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j) ≫
                        (tensor_single0_component_inv E ℱ j ≫
                          tensor_single0_component_hom E ℱ j) := by
                            rfl
                  _ = tensor_single0_component_hom E ℱ i ≫
                        ((((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j ≫
                          tensor_single0_component_inv E ℱ j) ≫
                        tensor_single0_component_hom E ℱ j := by
                          simp [Category.assoc]
        _ = tensor_single0_component_hom E ℱ i ≫
              (tensor_single0_component_inv E ℱ i ≫
                (HomologicalComplex.tensorObj E ((single₀).obj ℱ)).d i j) ≫
              tensor_single0_component_hom E ℱ j := by
                rw [(tensor_single0_component_inv_comm E ℱ i j hij).symm]
        _ = (HomologicalComplex.tensorObj E ((single₀).obj ℱ)).d i j ≫
              tensor_single0_component_hom E ℱ j := by
                calc
                  tensor_single0_component_hom E ℱ i ≫
                      (tensor_single0_component_inv E ℱ i ≫
                        (HomologicalComplex.tensorObj E ((single₀).obj ℱ)).d i j) ≫
                      tensor_single0_component_hom E ℱ j
                    = (tensor_single0_component_hom E ℱ i ≫
                        tensor_single0_component_inv E ℱ i) ≫
                        ((HomologicalComplex.tensorObj E ((single₀).obj ℱ)).d i j ≫
                          tensor_single0_component_hom E ℱ j) := by
                            simp [Category.assoc]
                  _ = ((tensor_single0_component_iso E ℱ i).hom ≫
                        (tensor_single0_component_iso E ℱ i).inv) ≫
                        ((HomologicalComplex.tensorObj E ((single₀).obj ℱ)).d i j ≫
                          tensor_single0_component_hom E ℱ j) := by
                            rfl
                  _ = 𝟙 _ ≫
                        ((HomologicalComplex.tensorObj E ((single₀).obj ℱ)).d i j ≫
                          tensor_single0_component_hom E ℱ j) := by
                            rw [(tensor_single0_component_iso E ℱ i).hom_inv_id]
                  _ = (HomologicalComplex.tensorObj E ((single₀).obj ℱ)).d i j ≫
                        tensor_single0_component_hom E ℱ j := by
                          simp
      )

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [MonoidalPreadditive Mod]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: the exactness hypothesis on `E ⊗ ℱ[0]` can be transported to the
mapped complex obtained from right tensoring by `ℱ`. -/
private theorem exactAt_map_tensorRight_of_exactAt_tensor_single0
    (E : CochainComplex Mod ℤ) (ℱ : Mod) (i : ℤ)
    (h : (HomologicalComplex.tensorObj E ((single₀).obj ℱ)).ExactAt i) :
    (((tensorRight ℱ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).ExactAt i := by
  -- The tensor-single comparison is a complex isomorphism, so exactness transports across it.
  exact HomologicalComplex.ExactAt.of_iso h (tensor_single0_complex_iso E ℱ)

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [MonoidalPreadditive Mod]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: specializing the tensor exactness hypothesis to the tensor unit
recovers exactness of the original complex. -/
private theorem exactAt_of_exactAt_tensor_single0_tensorUnit
    (E : CochainComplex Mod ℤ) (i : ℤ)
    (h : (HomologicalComplex.tensorObj E ((single₀).obj (𝟙_ Mod))).ExactAt i) :
    E.ExactAt i := by
  let eTensor :
      HomologicalComplex.tensorObj E ((single₀).obj (𝟙_ Mod)) ≅
        (((tensorRight (𝟙_ Mod)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) :=
    tensor_single0_complex_iso E (𝟙_ Mod)
  let eUnit :
      (((tensorRight (𝟙_ Mod)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) ≅
        (((𝟭 Mod).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) :=
    (NatIso.mapHomologicalComplex (rightUnitorNatIso Mod) (ComplexShape.up ℤ)).app E
  let eId :
      (((𝟭 Mod).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) ≅ E :=
    (Functor.mapHomologicalComplexIdIso Mod (ComplexShape.up ℤ)).app E
  -- Transport exactness first across the tensor-single comparison, then across the right unitor,
  -- and finally remove the identity functor wrapper on complexes.
  exact HomologicalComplex.ExactAt.of_iso
    (HomologicalComplex.ExactAt.of_iso
      (HomologicalComplex.ExactAt.of_iso h eTensor) eUnit)
    eId

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [MonoidalPreadditive Mod]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: the tensor-unit specialization already gives the explicit exact
three-term row used in the source proof. -/
private theorem differential_pair_exact_of_exactAt_tensor_single0_tensorUnit
    (E : CochainComplex Mod ℤ) (a : ℤ)
    (h : (HomologicalComplex.tensorObj E ((single₀).obj (𝟙_ Mod))).ExactAt (a - 1)) :
    (E.sc' (a - 2) (a - 1) a).Exact := by
  have hprev : (ComplexShape.up ℤ).prev (a - 1) = a - 2 := by
    calc
      (ComplexShape.up ℤ).prev (a - 1) = (a - 1) - 1 := by
        simpa using (CochainComplex.prev ℤ (a - 1))
      _ = a - 2 := by omega
  have hnext : (ComplexShape.up ℤ).next (a - 1) = a := by
    calc
      (ComplexShape.up ℤ).next (a - 1) = (a - 1) + 1 := by
        simpa using (CochainComplex.next ℤ (a - 1))
      _ = a := by omega
  -- First recover exactness of `E` itself, then rewrite it onto the displayed source row.
  rw [← HomologicalComplex.exactAt_iff' E (a - 2) (a - 1) a hprev hnext]
  exact exactAt_of_exactAt_tensor_single0_tensorUnit E (a - 1) h

omit [MonoidalPreadditive Mod] hAbelian
  [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
    CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]
  [MonoidalCategory Mod]
  [(curriedTensor Mod).Additive]
  [∀ M : Mod, ((curriedTensor Mod).obj M).Additive]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: exactness at degree `a - 1` is the same as exactness of the
three-term differential row `E^{a - 2} ⟶ E^{a - 1} ⟶ E^a`. -/
private theorem differential_pair_exact_of_exactAt
    (E : CochainComplex Mod ℤ) (a : ℤ)
    (h : E.ExactAt (a - 1)) :
    (E.sc' (a - 2) (a - 1) a).Exact := by
  have hprev : (ComplexShape.up ℤ).prev (a - 1) = a - 2 := by
    calc
      (ComplexShape.up ℤ).prev (a - 1) = (a - 1) - 1 := by
        simpa using (CochainComplex.prev ℤ (a - 1))
      _ = a - 2 := by omega
  have hnext : (ComplexShape.up ℤ).next (a - 1) = a := by
    calc
      (ComplexShape.up ℤ).next (a - 1) = (a - 1) + 1 := by
        simpa using (CochainComplex.next ℤ (a - 1))
      _ = a := by omega
  -- Rewrite the owner `ExactAt` statement onto the explicit three-term short complex.
  rwa [← HomologicalComplex.exactAt_iff' E (a - 2) (a - 1) a hprev hnext]

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: the cokernel of the ordinary degree-`a - 1` differential agrees
with the source-facing cokernel of `dFrom (a - 1)`. -/
private noncomputable def differential_cokernel_iso_cokernel_dFrom
    (E : CochainComplex Mod ℤ) (a : ℤ) :
    cokernel (E.d (a - 1) a) ≅ cokernel (E.dFrom (a - 1)) := by
  have hrel : (ComplexShape.up ℤ).Rel (a - 1) a := by
    simp
  let eCurr : E.X a ≅ E.xNext (a - 1) := (E.xNextIso hrel).symm
  -- Rewrite the target differential through the canonical `xNext` identification.
  refine cokernel.mapIso (E.d (a - 1) a) (E.dFrom (a - 1)) (Iso.refl _) eCurr ?_
  simpa [eCurr, E.dFrom_eq hrel]

omit [MonoidalPreadditive Mod] hAbelian
  [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
    CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]
  [MonoidalCategory Mod]
  [(curriedTensor Mod).Additive]
  [∀ M : Mod, ((curriedTensor Mod).obj M).Additive]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: the two consecutive differentials around degree `a - 1` compose to
zero on the explicit source row `E^{a - 2} ⟶ E^{a - 1} ⟶ E^a`. -/
private theorem differential_comp_zero
    (E : CochainComplex Mod ℤ) (a : ℤ) :
    E.d (a - 2) (a - 1) ≫ E.d (a - 1) a = 0 := by
  -- This is the square-zero differential identity specialized to consecutive degrees.
  simpa using E.d_comp_d (a - 2) (a - 1) a

/-
These tail helpers do not use projective resolutions; omitting that proof-only infrastructure keeps
their hidden parameter surface stable for later reuse in the final source-facing theorem.
-/
omit [MonoidalPreadditive Mod] hAbelian
  [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
    CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]
  [MonoidalCategory Mod]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: the source tail row ending in the ordinary differential cokernel is
the canonical short complex descended from `E^{a - 2} ⟶ E^{a - 1} ⟶ E^a`. -/
private theorem differential_tail_condition
    (E : CochainComplex Mod ℤ) (a : ℤ) :
    cokernel.desc (E.d (a - 2) (a - 1)) (E.d (a - 1) a)
        (differential_comp_zero E a) ≫
      cokernel.π (E.d (a - 1) a) = 0 := by
  -- This is the defining cokernel relation for the descended map.
  apply (cancel_epi (cokernel.π (E.d (a - 2) (a - 1)))).1
  simpa [Category.assoc] using cokernel.condition (E.d (a - 1) a)

omit [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: package the source tail
`cokernel(d^{a - 2}) ⟶ E^a ⟶ cokernel(d^{a - 1})`. -/
private abbrev differential_tail
    (E : CochainComplex Mod ℤ) (a : ℤ) :
    ShortComplex Mod :=
  ShortComplex.mk
    (cokernel.desc (E.d (a - 2) (a - 1)) (E.d (a - 1) a) (differential_comp_zero E a))
    (cokernel.π (E.d (a - 1) a))
    (differential_tail_condition E a)

omit [MonoidalCategory Mod]
  [(curriedTensor Mod).Additive]
  [∀ M : Mod, ((curriedTensor Mod).obj M).Additive]
  [MonoidalPreadditive Mod]
  [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
    CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: the descended tail map has the same image as the ordinary
degree-`a - 1` differential. -/
private theorem imageSubobject_differential_tail_f
    (E : CochainComplex Mod ℤ) (a : ℤ) :
    imageSubobject (differential_tail E a).f = imageSubobject (E.d (a - 1) a) := by
  have hcomp :
      cokernel.π (E.d (a - 2) (a - 1)) ≫ (differential_tail E a).f =
        E.d (a - 1) a := by
    simp [differential_tail]
  let P : Subobject (E.X a) := imageSubobject (differential_tail E a).f
  let σ : E.X (a - 1) ⟶ (P : Mod) :=
    cokernel.π (E.d (a - 2) (a - 1)) ≫ factorThruImageSubobject (differential_tail E a).f
  have hσ :
      σ ≫ P.arrow = E.d (a - 1) a := by
    simpa [σ, P, Category.assoc] using hcomp
  have hle :
      imageSubobject (σ ≫ P.arrow) ≤ imageSubobject P.arrow :=
    imageSubobject_comp_le σ P.arrow
  haveI : Epi (Subobject.ofLE _ _ hle) :=
    imageSubobject_comp_le_epi_of_epi σ P.arrow
  letI : IsRegularEpiCategory Mod := by infer_instance
  have hmReg : RegularEpi (Subobject.ofLE _ _ hle) :=
    regularEpiOfEpi (Subobject.ofLE _ _ hle)
  haveI : IsIso (Subobject.ofLE _ _ hle) :=
    isIso_of_regularEpi_of_mono (Subobject.ofLE _ _ hle) hmReg
  have hEq :
      imageSubobject (σ ≫ P.arrow) = imageSubobject P.arrow := by
    exact Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ hle)) (by
      simp [Subobject.ofLE_arrow])
  have hImage :
      imageSubobject (E.d (a - 1) a) = P := by
    simpa [hσ, P, imageSubobject_mono] using hEq
  simpa [P] using hImage.symm

omit [MonoidalCategory Mod]
  [(curriedTensor Mod).Additive]
  [∀ M : Mod, ((curriedTensor Mod).obj M).Additive]
  [MonoidalPreadditive Mod]
  [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
    CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]
  hAbelian
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: the tail row
`cokernel(d^{a - 2}) ⟶ E^a ⟶ cokernel(d^{a - 1})` is always exact at the middle term. The
remaining source-faithful work is to prove the descended left map is monic when the boundary row
of `E` is exact. -/
private theorem differential_tail_exact
    (E : CochainComplex Mod ℤ) (a : ℤ) :
    (differential_tail E a).Exact := by
  have hkernel :
      imageSubobject (E.d (a - 1) a) =
        kernelSubobject (cokernel.π (E.d (a - 1) a)) := by
    -- The ordinary cokernel sequence of `E.d (a - 1) a` is exact.
    simpa using
      (ShortComplex.exact_iff_image_eq_kernel
        (ShortComplex.mk
          (E.d (a - 1) a)
          (cokernel.π (E.d (a - 1) a))
          (cokernel.condition (E.d (a - 1) a)))).1
        (ShortComplex.exact_cokernel (E.d (a - 1) a))
  -- Replace the image of the descended map by the image of the original differential.
  exact
    (ShortComplex.exact_iff_image_eq_kernel (differential_tail E a)).2 <| by
      simpa [differential_tail] using
        (imageSubobject_differential_tail_f E a).trans hkernel

omit [MonoidalCategory Mod]
  [(curriedTensor Mod).Additive]
  [∀ M : Mod, ((curriedTensor Mod).obj M).Additive]
  hAbelian
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: if the boundary row
`K^{a - 2} ⟶ K^{a - 1} ⟶ K^a` is exact, then the descended tail map
`cokernel(d^{a - 2}) ⟶ K^a` is monic. -/
private theorem differential_tail_f_mono_of_exactAt
    (K : CochainComplex Mod ℤ) (a : ℤ)
    (h : K.ExactAt (a - 1)) :
    Mono (differential_tail K a).f := by
  have hExactPair :
      (K.sc' (a - 2) (a - 1) a).Exact :=
    differential_pair_exact_of_exactAt K a h
  -- The source row is exact, so the generic exact-cokernel descent API shows that the quotient
  -- map `cokernel(d^{a - 2}) ⟶ K^a` is already monic.
  simpa [differential_tail] using hExactPair.mono_cokernelDesc

omit [MonoidalCategory Mod]
  [(curriedTensor Mod).Additive]
  [∀ M : Mod, ((curriedTensor Mod).obj M).Additive]
  [MonoidalPreadditive Mod]
  [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
    CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]
  hAbelian
  [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 21.46.2: exactness of the boundary row upgrades the tail
`cokernel(d^{a - 2}) ⟶ K^a ⟶ cokernel(d^{a - 1})` to a short exact sequence. -/
private theorem shortExact_differential_tail_of_exactAt
    (K : CochainComplex Mod ℤ) (a : ℤ)
    (h : K.ExactAt (a - 1)) :
    (differential_tail K a).ShortExact := by
  have hMono : Mono (differential_tail K a).f :=
    differential_tail_f_mono_of_exactAt K a h
  -- The exact middle term was established earlier; monicity on the left now lets the standard
  -- short-complex constructor package the source tail row.
  exact ShortComplex.ShortExact.mk' (differential_tail_exact K a) hMono inferInstance

end

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [hAbelian : Abelian (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ M : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj M).Additive]
variable [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "single₀" => CochainComplex.singleFunctor Mod (0 : ℤ)

/-- Lemma 21.46.2: if `E^•` is bounded above, each term `E^n` is a flat `𝒪`-module, and
tensoring with any degree-zero `𝒪`-module is exact outside `[a, b]`, then the cokernel of the
differential `E^{a - 1} ⟶ E^a` is flat. -/
@[stacks 08G0]
theorem isFlat_cokernel_dFrom_of_boundedAbove_of_flat_terms_of_hasTorAmplitudeIn
    (E : CochainComplex Mod ℤ) (a b : ℤ)
    (hbounded : CochainComplex.minus Mod E)
    (hFlat : ∀ n : ℤ, IsFlat 𝒪 (E.X n))
    (hTor :
      ∀ (ℱ : Mod) (i : ℤ), i ∉ Set.Icc a b →
        (HomologicalComplex.tensorObj E
          ((single₀).obj ℱ)).ExactAt i) :
    IsFlat 𝒪 (cokernel (E.dFrom (a - 1))) := by
  sorry

/-- Canonical termwise-flat companion to Lemma 21.46.2: if `E^•` is bounded above and termwise
flat in the owner sense `CochainComplex.IsTermwiseFlat E`, and tensoring with any degree-zero
`𝒪`-module is exact outside `[a, b]`, then the cokernel of the differential
`E^{a - 1} ⟶ E^a` is flat. -/
theorem isFlat_cokernel_dFrom_of_boundedAbove_of_termwiseFlat_of_hasTorAmplitudeIn
    (E : CochainComplex Mod ℤ) (a b : ℤ)
    (hbounded : CochainComplex.minus Mod E)
    (hFlat : CochainComplex.IsTermwiseFlat E)
    (hTor :
      ∀ (ℱ : Mod) (i : ℤ), i ∉ Set.Icc a b →
        (HomologicalComplex.tensorObj E
          ((single₀).obj ℱ)).ExactAt i) :
    IsFlat 𝒪 (cokernel (E.dFrom (a - 1))) :=
  isFlat_cokernel_dFrom_of_boundedAbove_of_flat_terms_of_hasTorAmplitudeIn
    E a b hbounded ((CochainComplex.isTermwiseFlat_iff E).1 hFlat) hTor

end

end SheafOfModules.RingedSite
