import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap13.Lemma_13_27_9
import StacksProject_2024.Chap13.Remark_13_12_4
import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap15.Definition_15_28_2
import StacksProject_2024.Chap15.Definition_15_59_13
import StacksProject_2024.Chap15.Definition_15_89_1
import StacksProject_2024.Chap15.Lemma_15_28_8
import StacksProject_2024.Chap15.Lemma_15_28_6
import StacksProject_2024.Chap15.Lemma_15_60_1
import StacksProject_2024.Chap15.Lemma_15_60_2
import StacksProject_2024.Chap15.Lemma_15_67_3
import StacksProject_2024.Chap15.Lemma_15_67_8
import StacksProject_2024.Chap15.Lemma_15_67_20
import StacksProject_2024.Chap15.Definition_15_92_4
import StacksProject_2024.Chap15.Situation_15_92_15

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open ComplexShape
open DerivedCategory.TStructure
open ModuleCat.MonoidalCategory
open scoped DerivedTensorChangeOfRings
open scoped DerivedTensorProduct KoszulComplex

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] {r : ℕ}

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)
local notation "KMod" => HomotopyCategory (ModuleCat A) (ComplexShape.up ℤ)
local notation "Bounded" => (t.bounded : ObjectProperty DMod)

local instance : MonoidalCategory KMod :=
  CategoryTheory.homotopyCategory_monoidalCategory

/- Domain-style sampling:
- primary domain: derived-complete objects in `D(A)`, tested against the canonical quotient object
  `(A / I)[0]` and the first powered Koszul stage `K_1^•` in the derived category;
- sampled owner-side declarations:
  `DerivedCategory.IsDerivedCompleteWithRespectTo`,
  `DerivedCategory.singleFunctor`,
  `CategoryTheory.derivedTensorProduct`,
  `derivedCompletionKoszulPowersDerivedInverseSystem`;
- best owner abstraction: the source-facing owner is still the derived-completeness predicate
  `K.IsDerivedCompleteWithRespectTo I`, while the positivity conditions are expressed by the
  canonical t-structure owner `DerivedCategory.IsLE 0` on the relevant derived tensor products
  with the degree-zero quotient object and the stage-`0` Koszul-power object from Situation
  `15.92.15`;
- primitive data: the generator family `f : Fin r → A`, the derived object `K`, and the owner
  hypothesis of derived completeness with respect to `Ideal.span (Set.range f)`;
- derived API: the degree-zero embedding `single₀`, the powered Koszul tower owner
  `derivedCompletionKoszulPowersDerivedInverseSystem`, and the derived tensor notation
  `K ⊗[A]^L L`, so the theorem should not expose raw functor-application or
  extension-localization internals.

Source/core/bridge triage:
- `source-facing`: the TFAE criterion for nonpositive cohomology under derived completeness;
- `core/canonical`: `K.IsDerivedCompleteWithRespectTo I`, `DerivedCategory.IsLE 0`,
  `DerivedCategory.singleFunctor`, `derivedTensorProduct`, and
  `derivedCompletionKoszulPowersDerivedInverseSystem`;
- `bridge/view`: the stage-`0` powered-Koszul object realizing the textbook first Koszul complex
  `K_1^•`. -/

-- Proof sketch: `(1) → (2)` is exactness of derived tensor with the degree-zero quotient object.
-- `(2) → (3)` is the tensor-with-Koszul implication from Lemma `15.89.7`, using that the first
-- powered Koszul stage computes a bounded `I`-power-torsion object with zeroth homology `A / I`.
-- For `(3) → (1)`, descend on the Koszul length as in the textbook proof, using the
-- distinguished triangles for successive partial Koszul complexes together with derived
-- completeness and Lemmas `15.92.6` and `15.92.7` to force the positive cohomology groups to
-- vanish.
/-- Helper for Lemma 15.92.19: stage `0` of the powered Koszul tower is the ordinary extended
Koszul complex on the original family `f`. -/
private abbrev ordinaryDerivedKoszul {s : ℕ} (g : Fin s → A) : DMod :=
  DerivedCategory.Q.obj
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj (K^•(g)))

/-- Helper for Lemma 15.92.19: the unique empty generator family. -/
private abbrev emptyKoszulFamily : Fin 0 → A := fun i ↦ Fin.elim0 i

/-- Helper for Lemma 15.92.19: the ordinary Koszul chain complex on the empty family. -/
private abbrev emptyOrdinaryKoszulChain : ChainComplex (ModuleCat A) ℕ :=
  K^•(emptyKoszulFamily (A := A))

/-- Helper for Lemma 15.92.19: every positive exterior power of the zero free module `Fin 0 → A`
is the zero object. -/
private theorem isZero_exteriorPower_empty_local (i : ℕ) (hi : 1 ≤ i) :
    IsZero ((ModuleCat.of A (Fin 0 → A)).exteriorPower i) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi) with ⟨j, rfl⟩
  -- Proof comment: every alternating tensor in positive degree is built from the unique zero
  -- vector of `Fin 0 → A`, so the whole exterior power is zero.
  have hbot :
      (⋀[A]^(j + 1) (Fin 0 → A) : Submodule A (ExteriorAlgebra A (Fin 0 → A))) = ⊥ := by
    calc
      (⋀[A]^(j + 1) (Fin 0 → A) : Submodule A (ExteriorAlgebra A (Fin 0 → A))) =
          Submodule.span A (Set.range (ExteriorAlgebra.ιMulti A (j + 1) :
            (Fin (j + 1) → Fin 0 → A) → ExteriorAlgebra A (Fin 0 → A))) := by
        symm
        exact exteriorPower.ιMulti_span_fixedDegree (R := A) (n := j + 1) (M := Fin 0 → A)
      _ = ⊥ := by
        apply le_antisymm
        · rw [Submodule.span_le]
          rintro _ ⟨f, rfl⟩
          have hf : f = 0 := funext fun k ↦ Subsingleton.elim _ _
          rw [hf]
          simpa using (ExteriorAlgebra.ιMulti A (j + 1)).map_zero
        · exact bot_le
  refine ⟨fun x y ↦ ?_⟩
  have hx : x = 0 := by
    simpa [hbot] using x.2
  have hy : y = 0 := by
    simpa [hbot] using y.2
  exact hx.trans hy.symm

/-- Helper for Lemma 15.92.19: for the empty family, the first Koszul differential is the zero
linear form. -/
private theorem ordinary_koszul_empty_first_differential_linearMap_eq_linearForm :
    (exteriorPower.zeroEquiv A (Fin 0 → A)).toLinearMap.comp
        (koszulDifferentialLinearMap (koszulLinearForm (emptyKoszulFamily (A := A))) 0) =
      (koszulLinearForm (emptyKoszulFamily (A := A))).comp
        (exteriorPower.oneEquiv A (Fin 0 → A)).toLinearMap := by
  -- Proof comment: in degree `1`, the differential contracts against the defining linear form,
  -- and `⋀¹(0)` is identified with the underlying zero free module.
  apply exteriorPower.linearMap_ext
  ext m
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply]
  have hone :
      (exteriorPower.oneEquiv A (Fin 0 → A)) (exteriorPower.ιMulti A 1 m) = m 0 := by
    simpa using (exteriorPower.oneEquiv_ιMulti (R := A) (M := Fin 0 → A) (f := m))
  have hone' :
      (koszulLinearForm (emptyKoszulFamily (A := A)))
          ((exteriorPower.oneEquiv A (Fin 0 → A)) (exteriorPower.ιMulti A 1 m)) =
        (koszulLinearForm (emptyKoszulFamily (A := A))) (m 0) := by
    simp [hone]
  have hone'' :
      (koszulLinearForm (emptyKoszulFamily (A := A)))
          ((exteriorPower.oneEquiv A (Fin 0 → A)).toLinearMap
            (exteriorPower.ιMulti A 1 m)) =
        (koszulLinearForm (emptyKoszulFamily (A := A))) (m 0) := by
    simpa using hone'
  rw [hone'']
  apply_fun (exteriorPower.zeroEquiv A (Fin 0 → A)).symm using
    (exteriorPower.zeroEquiv A (Fin 0 → A)).symm.injective
  simp [exteriorPower.zeroEquiv_symm_apply]
  apply Subtype.ext
  simpa [ExteriorAlgebra.ιMulti, Algebra.algebraMap_eq_smul_one, koszulDifferentialLinearMap] using
    (CliffordAlgebra.contractLeft_ι
      (Q := 0) (d := koszulLinearForm (emptyKoszulFamily (A := A))) (x := m 0))

/-- Helper for Lemma 15.92.19: the first empty-family Koszul differential vanishes after
identifying degree `0` with `A`. -/
private theorem ordinary_koszul_empty_first_differential_comp_iso0_eq_zero :
    (emptyOrdinaryKoszulChain (A := A)).d 1 0 ≫
      (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom = 0 := by
  -- Proof comment: the empty-family linear form is zero because every vector in `Fin 0 → A`
  -- vanishes.
  change
    ModuleCat.ofHom
      (((exteriorPower.zeroEquiv A (Fin 0 → A)).toLinearMap.comp
        (koszulDifferentialLinearMap
          (koszulLinearForm (emptyKoszulFamily (A := A))) 0))) = 0
  change ModuleCat.ofHom _ = ModuleCat.ofHom 0
  congr 1
  rw [ordinary_koszul_empty_first_differential_linearMap_eq_linearForm]
  ext x
  have hx : x = 0 := funext fun i ↦ funext fun j ↦ Fin.elim0 j
  simp [hx, koszulLinearForm]

/-- Helper for Lemma 15.92.19: the empty-family Koszul chain complex is the degree-zero single
chain complex on `A`. -/
private noncomputable abbrev ordinary_koszul_empty_chain_single_iso :
    emptyOrdinaryKoszulChain (A := A) ≅
      (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A A) := by
  let hom :
      emptyOrdinaryKoszulChain (A := A) ⟶
        (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A A) :=
    (ChainComplex.toSingle₀Equiv
        (emptyOrdinaryKoszulChain (A := A))
        (ModuleCat.of A A)).symm
      ⟨(ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom,
        ordinary_koszul_empty_first_differential_comp_iso0_eq_zero⟩
  let inv :
      (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A A) ⟶
        emptyOrdinaryKoszulChain (A := A) :=
    (ChainComplex.fromSingle₀Equiv
        (emptyOrdinaryKoszulChain (A := A))
        (ModuleCat.of A A)).symm
      ((ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv)
  refine CategoryTheory.Iso.mk hom inv ?_ ?_
  · -- Proof comment: compare the composite on the empty-family stage degreewise.
    apply HomologicalComplex.hom_ext
    intro i
    cases i with
    | zero =>
        have hhom0 :
            hom.f 0 = (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom := by
          simpa [hom] using
            (ChainComplex.toSingle₀Equiv_symm_apply_f_zero
              (C := emptyOrdinaryKoszulChain (A := A))
              (X := ModuleCat.of A A)
              (f := (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom)
              (hf := ordinary_koszul_empty_first_differential_comp_iso0_eq_zero))
        have hinv0 :
            inv.f 0 = (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv := by
          simpa [inv] using
            (ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
              (C := emptyOrdinaryKoszulChain (A := A))
              (X := ModuleCat.of A A)
              (f := (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv))
        simpa [HomologicalComplex.comp_f, hhom0, hinv0] using
          (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom_inv_id
    | succ m =>
        exact
          (isZero_exteriorPower_empty_local (m + 1) (Nat.succ_le_succ (Nat.zero_le m))).eq_of_src _ _
  · -- Proof comment: maps out of a degree-zero single chain complex are determined in degree `0`.
    apply HomologicalComplex.from_single_hom_ext
    have hhom0 :
        hom.f 0 = (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom := by
      simpa [hom] using
        (ChainComplex.toSingle₀Equiv_symm_apply_f_zero
          (C := emptyOrdinaryKoszulChain (A := A))
          (X := ModuleCat.of A A)
          (f := (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom)
          (hf := ordinary_koszul_empty_first_differential_comp_iso0_eq_zero))
    have hinv0 :
        inv.f 0 = (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv := by
      simpa [inv] using
        (ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
          (C := emptyOrdinaryKoszulChain (A := A))
          (X := ModuleCat.of A A)
          (f := (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv))
    simpa [HomologicalComplex.comp_f, hhom0, hinv0] using
      (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv_hom_id

/-- Helper for Lemma 15.92.19: the empty ordinary derived Koszul object is `A[0]`. -/
private noncomputable def ordinary_koszul_empty_iso_single0 :
    ordinaryDerivedKoszul (emptyKoszulFamily (A := A)) ≅
      (single₀).obj (ModuleCat.of A A) :=
  DerivedCategory.Q.mapIso
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).mapIso
        ordinary_koszul_empty_chain_single_iso) ≪≫
          (HomologicalComplex.extendSingleIso
            ComplexShape.embeddingDownNat (ModuleCat.of A A) (0 : ℕ) (0 : ℤ) rfl)) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app (ModuleCat.of A A)

private noncomputable def stage_zero_powered_koszul_iso_ordinary
    (f : Fin r → A) :
    (derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op 0) ≅
      ordinaryDerivedKoszul f := by
  have hk : K^•[0](f) = K^•(f) := by
    simp
  -- Proof comment: the stage-`0` powered tuple is exactly `(f₁^(0+1), …, fᵣ^(0+1))`, so only
  -- the trivial normalization `x^1 = x` remains before applying `Q`.
  simpa [derivedCompletionKoszulPowersDerivedInverseSystem, koszulPowerInverseSystem] using
    DerivedCategory.Q.mapIso
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).mapIso (eqToIso hk))

/-- Helper for Lemma 15.92.19: the quotient functor `Q` carries the standard monoidal structure
needed to compare ordinary tensor complexes with derived tensor products. -/
private noncomputable instance quotientFunctorMonoidal :
    (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DMod).Monoidal := by
  change (((HomotopyCategory.quotient (ModuleCat A) (ComplexShape.up ℤ)) ⋙
      (DerivedCategory.Qh :
        HomotopyCategory (ModuleCat A) (ComplexShape.up ℤ) ⥤ DMod))).Monoidal
  infer_instance

/-- Helper for Lemma 15.92.19: tensoring two strictly nonpositive cochain complexes stays
strictly nonpositive. -/
private theorem tensorObj_isStrictlyLE_of_isStrictlyLE
    {E F : CochainComplex (ModuleCat A) ℤ} {a b : ℤ}
    (hE : E.IsStrictlyLE a) (hF : F.IsStrictlyLE b) :
    CochainComplex.IsStrictlyLE (HomologicalComplex.tensorObj E F) (a + b) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
  change 𝟙 ((CategoryTheory.GradedObject.Monoidal.tensorObj E.X F.X) n) = 0
  -- Proof comment: above the sum cutoff, every `(p,q)` summand lies beyond one of the two
  -- support bounds, so that tensor summand already vanishes.
  apply CategoryTheory.GradedObject.Monoidal.tensorObj_ext
  intro p q h
  have hpq : a < p ∨ b < q := by
    omega
  cases hpq with
  | inl hp =>
      let T : ModuleCat A ⥤ ModuleCat A :=
        (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat A)).flip.obj (F.X q)
      have hzero : IsZero (E.X p) := E.isZero_of_isStrictlyLE a p hp
      have hsrc : IsZero (T.obj (E.X p)) := CategoryTheory.Functor.map_isZero T hzero
      simpa [T, Category.assoc] using
        hsrc.eq_of_src (CategoryTheory.GradedObject.Monoidal.ιTensorObj E.X F.X p q n h) 0
  | inr hq =>
      let T : ModuleCat A ⥤ ModuleCat A :=
        (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat A)).obj (E.X p)
      have hzero : IsZero (F.X q) := F.isZero_of_isStrictlyLE b q hq
      have hsrc : IsZero (T.obj (F.X q)) := CategoryTheory.Functor.map_isZero T hzero
      simpa [T, Category.assoc] using
        hsrc.eq_of_src (CategoryTheory.GradedObject.Monoidal.ιTensorObj E.X F.X p q n h) 0

/-- Helper for Lemma 15.92.19: tensoring a nonpositive derived object with a degree-zero module
stays nonpositive. -/
private lemma tensor_single_isLE_zero_of_isLE_zero
    (L : DMod) (hL : L.IsLE 0) (M : ModuleCat A) :
    (L ⊗[A]^L (single₀).obj M).IsLE 0 := by
  -- Route correction: instead of importing an earlier private helper through a broken path, prove
  -- the source-faithful bridge directly from a strict `≤ 0` representative of `L`.
  letI : L.IsLE 0 := hL
  obtain ⟨P, hPle, ⟨eP⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE L 0
  let Tsingle : CochainComplex (ModuleCat A) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M
  have hTsingle : Tsingle.IsStrictlyLE 0 := by
    infer_instance
  have hTensorStrict :
      CochainComplex.IsStrictlyLE (HomologicalComplex.tensorObj P Tsingle) 0 :=
    tensorObj_isStrictlyLE_of_isStrictlyLE hPle hTsingle
  have hTensorDerivedLE :
      (DerivedCategory.Q.obj (HomologicalComplex.tensorObj P Tsingle)).IsLE 0 := by
    letI : CochainComplex.IsStrictlyLE (HomologicalComplex.tensorObj P Tsingle) 0 := hTensorStrict
    infer_instance
  let eTensor :
      DerivedCategory.Q.obj (HomologicalComplex.tensorObj P Tsingle) ≅
        ((DerivedCategory.Q.obj P) ⊗[A]^L (single₀).obj M) :=
    (Functor.Monoidal.μIso
      (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DMod) P Tsingle).symm ≪≫
      ((Iso.refl _) ⊗ᵢ
        (DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app M) ≪≫
        derivedCategory_tensorObj_iso_derivedTensorProduct
          (DerivedCategory.Q.obj P) ((single₀).obj M)
  have hRepresentedLE :
      ((DerivedCategory.Q.obj P) ⊗[A]^L (single₀).obj M).IsLE 0 := by
    -- Proof comment: the strict tensor model is already nonpositive, and the standard monoidal
    -- comparison moves that bound to the public derived tensor owner.
    letI : (DerivedCategory.Q.obj (HomologicalComplex.tensorObj P Tsingle)).IsLE 0 :=
      hTensorDerivedLE
    exact t.isLE_of_iso eTensor 0
  -- Proof comment: finally transport the bound from the chosen strict representative of `L`.
  letI : ((DerivedCategory.Q.obj P) ⊗[A]^L (single₀).obj M).IsLE 0 := hRepresentedLE
  exact t.isLE_of_iso (((derivedTensorProduct ((single₀).obj M)).mapIso eP).symm) 0

/-- Helper for Lemma 15.92.19: derived tensor product is functorial in the right variable once
the tensor symmetry is used to switch to left-variable functoriality. -/
private noncomputable def derivedTensorProduct_right_map_iso
    {X Y Z : DMod} (e : Y ≅ Z) :
    X ⊗[A]^L Y ≅ X ⊗[A]^L Z :=
  derivedTensorProduct_comm X Y ≪≫
    ((derivedTensorProduct X).mapIso e) ≪≫
      (derivedTensorProduct_comm Z X)

/-- Helper for Lemma 15.92.19: tensoring with the empty ordinary Koszul stage is the tensor-unit
identification `K ⊗ A[0] ≅ K`. -/
private noncomputable def tensor_ordinary_koszul_empty_iso
    (K : DMod) :
    K ⊗[A]^L ordinaryDerivedKoszul (emptyKoszulFamily (A := A)) ≅ K :=
  derivedTensorProduct_right_map_iso
      (X := K) ordinary_koszul_empty_iso_single0 ≪≫
    regular_single0_derivedTensor_iso_local (R := A) K

/-- Helper for Lemma 15.92.19: the empty ordinary Koszul tensor stage is nonpositive exactly when
`K` itself is nonpositive. -/
private theorem tensor_ordinary_koszul_empty_isLE_zero_iff
    (K : DMod) :
    (K ⊗[A]^L ordinaryDerivedKoszul (emptyKoszulFamily (A := A))).IsLE 0 ↔ K.IsLE 0 := by
  constructor
  · intro h
    letI :
        (K ⊗[A]^L ordinaryDerivedKoszul (emptyKoszulFamily (A := A))).IsLE 0 := h
    exact t.isLE_of_iso (tensor_ordinary_koszul_empty_iso K) 0
  · intro h
    letI : K.IsLE 0 := h
    exact t.isLE_of_iso (tensor_ordinary_koszul_empty_iso K).symm 0

/-- Helper for Lemma 15.92.19: if an ideal annihilates a module, then the module is already
power torsion for that ideal. -/
private theorem isIdealPowerTorsion_of_le_annihilator
    {M : Type*} [AddCommGroup M] [Module A M]
    (I : Ideal A) (hI : I ≤ Module.annihilator A M) :
    Module.IsIdealPowerTorsion I M := by
  -- Proof comment: exponent `1` suffices because every element of `I` already acts by zero.
  rw [Module.isIdealPowerTorsion_iff]
  intro x
  refine ⟨1, ?_⟩
  intro a
  have ha : (a : A) ∈ I := by
    simpa using a.2
  exact Module.mem_annihilator.mp (hI ha) x

/-- Helper for Lemma 15.92.19: if an element lies in the annihilator ideal, then its scalar
endomorphism on the module is zero. -/
private theorem lsmul_toModuleEnd_eq_zero_of_mem_annihilator
    {N : Type u} [AddCommGroup N] [Module A N]
    (I : Ideal A) (hI : I ≤ Module.annihilator A N) {a : A} (ha : a ∈ I) :
    (Algebra.lsmul A A N a : Module.End A N) = 0 := by
  -- Proof comment: an annihilating scalar acts as the zero endomorphism on every vector.
  ext x
  exact Module.mem_annihilator.mp (hI ha) x

/-- Helper for Lemma 15.92.19: an `A`-module annihilated by `I` carries its canonical
`A ⧸ I`-module structure. -/
private noncomputable abbrev quotientModuleOfLeAnnihilator
    (I : Ideal A) (N : Type u) [AddCommGroup N] [Module A N]
    (hI : I ≤ Module.annihilator A N) :
    Module (A ⧸ I) N :=
  Module.compHom N <|
    Ideal.Quotient.lift I (Algebra.lsmul A A N).toRingHom
      (fun a ha ↦ lsmul_toModuleEnd_eq_zero_of_mem_annihilator (I := I) (N := N) hI ha)

/-- Helper for Lemma 15.92.19: after equipping `N` with its quotient-ring action, restricting
scalars back to `A` recovers the original `A`-module. -/
private noncomputable def restrictScalars_quotientModule_iso
    (I : Ideal A) (N : Type u) [AddCommGroup N] [Module A N]
    (hI : I ≤ Module.annihilator A N) :
    let _ : Module (A ⧸ I) N := quotientModuleOfLeAnnihilator (A := A) I N hI
    ((ModuleCat.restrictScalars (Ideal.Quotient.mkₐ A I).toRingHom).obj
      (ModuleCat.of (A ⧸ I) N)) ≅ ModuleCat.of A N := by
  let _ : Module (A ⧸ I) N := quotientModuleOfLeAnnihilator (A := A) I N hI
  -- Proof comment: both module structures act by the same scalar formula, so the identity map
  -- is linear in both directions.
  refine CategoryTheory.Iso.mk
    (ModuleCat.ofHom (LinearMap.id : N →ₗ[A] N))
    (ModuleCat.ofHom (LinearMap.id : N →ₗ[A] N))
    ?_ ?_
  · ext x
    rfl
  · ext x
    rfl

/-- Helper for Lemma 15.92.19: restriction of scalars sends a degree-zero `B`-module object to
the corresponding degree-zero `A`-module object. -/
private noncomputable def restrictScalars_single_zero_iso
    {B : Type u} [CommRing B] [Algebra A B]
    (M : ModuleCat B) :
    (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj
      ((DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ)).obj M)) ≅
      ((single₀).obj ((ModuleCat.restrictScalars (algebraMap A B)).obj M)) := by
  -- Proof comment: restriction of scalars is exact, so compute it on the cochain-level single
  -- complex and fold back to the public degree-zero owner.
  exact
    ((((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat B) (0 : ℤ)).app M)) ≪≫
      (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategoryFactors.app
        ((CochainComplex.singleFunctor (ModuleCat B) (0 : ℤ)).obj M) ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapCochainComplexSingleFunctor
          (ModuleCat.restrictScalars (algebraMap A B))
          (0 : ℤ)).app M) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
        ((ModuleCat.restrictScalars (algebraMap A B)).obj M)).symm)

/-- Helper for Lemma 15.92.19: restricting scalars commutes with homology in derived module
categories. -/
private noncomputable def restrictScalars_homology_iso
    {B : Type u} [CommRing B] [Algebra A B]
    (L : DerivedCategory (ModuleCat B)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat A) n).obj
        (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L) ≅
      (ModuleCat.restrictScalars (algebraMap A B)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat B) n).obj L) := by
  let K := DerivedCategory.Q.objPreimage L
  let FK :=
    (((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)
  let eB :
      ((DerivedCategory.homologyFunctor (ModuleCat B) n).obj L) ≅
        K.homology n :=
    ((DerivedCategory.homologyFunctor (ModuleCat B) n).mapIso
      (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat B) n).app K
  -- Proof comment: compute homology on a chosen cochain representative and use that restriction
  -- of scalars commutes with the short-complex homology construction.
  exact
    (DerivedCategory.homologyFunctor (ModuleCat A) n).mapIso
        ((((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).mapIso
          (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
          ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategoryFactors.app K)) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat A) n).app FK ≪≫
      (K.sc n).mapHomologyIso (ModuleCat.restrictScalars (algebraMap A B)) ≪≫
      (ModuleCat.restrictScalars (algebraMap A B)).mapIso eB.symm

/-- Helper for Lemma 15.92.19: the ordinary Koszul chain complex has no terms above exterior
degree `r`. -/
private theorem ordinary_koszul_chain_X_isZero_of_gt
    (f : Fin r → A) (j : ℕ) (hj : r < j) :
    IsZero ((K^•(f)).X j) := by
  -- Proof comment: `K^•(f).X j` is the `j`th exterior power of `A^r`, whose standard basis is
  -- empty once `j` exceeds the rank `r`.
  change IsZero ((ModuleCat.of A (Fin r → A)).exteriorPower j)
  rw [ModuleCat.isZero_iff_subsingleton]
  let B :
      Module.Basis (Set.powersetCard (Fin r) j) A
        ↥(⋀[A]^j (Fin r → A)) :=
    Module.Basis.exteriorPower j (Pi.basisFun A (Fin r))
  have hempty : IsEmpty (Set.powersetCard (Fin r) j) := by
    refine ⟨fun s ↦ ?_⟩
    have hs : ((s : Finset (Fin r)).card) = j := by
      simpa using s.2
    have hsle : ((s : Finset (Fin r)).card) ≤ r := by
      simpa using Finset.card_le_univ (s := (s : Finset (Fin r)))
    omega
  refine ⟨fun x y ↦ ?_⟩
  apply B.repr.injective
  have hx : B.repr x = 0 := Subsingleton.elim _ _
  have hy : B.repr y = 0 := Subsingleton.elim _ _
  exact hx.trans hy.symm

/-- Helper for Lemma 15.92.19: the ordinary derived Koszul object has no cohomology below
degree `-r`. -/
private theorem ordinary_derived_koszul_isGE_neg_r
    (f : Fin r → A) :
    (ordinaryDerivedKoszul f).IsGE (-((r : ℕ) : ℤ)) := by
  -- Proof comment: degree `i` of the extended cochain model is chain degree `Int.toNat (-i)`,
  -- which vanishes once `i < -r`.
  rw [DerivedCategory.isGE_Q_obj_iff]
  let K : CochainComplex (ModuleCat A) ℤ :=
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj (K^•(f)))
  change K.IsGE (-((r : ℕ) : ℤ))
  letI : K.IsStrictlyGE (-((r : ℕ) : ℤ)) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    have hnonneg : 0 ≤ -i := by
      omega
    let e : K.X i ≅ (K^•(f)).X (Int.toNat (-i)) :=
      (K^•(f)).extendXIso ComplexShape.embeddingDownNat (by
        simpa [K, ComplexShape.embeddingDownNat, Int.toNat_of_nonneg hnonneg] using
          (show -((Int.toNat (-i) : ℕ) : ℤ) = i by
            rw [Int.toNat_of_nonneg hnonneg]
            omega))
    have htoNat : ((Int.toNat (-i) : ℕ) : ℤ) = -i := by
      exact Int.toNat_of_nonneg hnonneg
    have hjgt : r < Int.toNat (-i) := by
      have hlt : ((r : ℕ) : ℤ) < ((Int.toNat (-i) : ℕ) : ℤ) := by
        rw [htoNat]
        omega
      exact_mod_cast hlt
    exact (ordinary_koszul_chain_X_isZero_of_gt f (Int.toNat (-i)) hjgt).of_iso e
  infer_instance

/-- Helper for Lemma 15.92.19: the ordinary derived Koszul object is nonpositive. -/
private theorem ordinary_derived_koszul_isLE_zero
    (f : Fin r → A) :
    (ordinaryDerivedKoszul f).IsLE 0 := by
  -- Proof comment: the extended cochain representative still has no positive-degree terms.
  rw [DerivedCategory.isLE_Q_obj_iff]
  let K : CochainComplex (ModuleCat A) ℤ :=
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj (K^•(f)))
  change K.IsLE 0
  letI : K.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    by_cases hpre : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = i
    · obtain ⟨j, hj⟩ := hpre
      have hnonpos : (ComplexShape.embeddingDownNat.f j : ℤ) ≤ 0 := by
        simpa [ComplexShape.embeddingDownNat]
      have hi_nonpos : i ≤ 0 := by
        calc
          i = ComplexShape.embeddingDownNat.f j := hj.symm
          _ ≤ 0 := hnonpos
      omega
    · simpa [K] using
        ((K^•(f)).isZero_extend_X
          ComplexShape.embeddingDownNat i (fun j hij ↦ hpre ⟨j, hij⟩))
  infer_instance

/-- Helper for Lemma 15.92.19: each nonpositive cohomology object of the ordinary derived Koszul
stage is annihilated by the span ideal generated by `f`. -/
private theorem ordinary_derived_koszul_homology_annihilator
    (f : Fin r → A) (i : ℤ) (hi : i ≤ 0) :
    Ideal.span (Set.range f) ≤ Module.annihilator A
      ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj (ordinaryDerivedKoszul f)) := by
  -- Proof comment: transport derived cohomology through the `embeddingDownNat` comparison and
  -- then use that the span ideal annihilates ordinary Koszul homology on the chain model.
  let j : ℕ := Int.toNat (-i)
  have hnonneg : 0 ≤ -i := by
    omega
  have hj : ComplexShape.embeddingDownNat.f j = i := by
    dsimp [j]
    rw [Int.toNat_of_nonneg hnonneg]
    simp [ComplexShape.embeddingDownNat]
  let eH :
      ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj (ordinaryDerivedKoszul f)) ≅
        (K^•(f)).homology j :=
    ((DerivedCategory.homologyFunctorFactors (ModuleCat A) i).app
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj (K^•(f))))) ≪≫
        ((K^•(f)).extendHomologyIso ComplexShape.embeddingDownNat hj)
  have hAnn :
      Ideal.span (Set.range f) ≤ Module.annihilator A ((K^•(f)).homology j) := by
    simpa [j] using ideal_span_le_annihilator_koszulComplex_homology (f := f) j
  intro a ha
  exact Module.mem_annihilator.mpr <| fun x ↦ by
    apply eH.toLinearEquiv.injective
    -- Proof comment: after transporting `x` to ordinary Koszul homology, annihilation is exactly
    -- the standard Koszul homology fact.
    simpa using Module.mem_annihilator.mp (hAnn ha) (eH.hom x)

/-- Helper for Lemma 15.92.19: each nonpositive cohomology object of the ordinary derived Koszul
stage is torsion for the span ideal generated by `f`. -/
private theorem ordinary_derived_koszul_homology_isIdealPowerTorsion
    (f : Fin r → A) (i : ℤ) (hi : i ≤ 0) :
    Module.IsIdealPowerTorsion (Ideal.span (Set.range f))
      ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj (ordinaryDerivedKoszul f)) := by
  -- Proof comment: the annihilator statement proved just above is the sharper source fact, and
  -- power torsion is the immediate corollary needed by the bounded-width tensor package.
  exact
    isIdealPowerTorsion_of_le_annihilator
      (I := Ideal.span (Set.range f))
      (ordinary_derived_koszul_homology_annihilator f i hi)

/-- Helper for Lemma 15.92.19: the ordinary derived Koszul object is bounded. -/
private theorem ordinary_derived_koszul_bounded
    (f : Fin r → A) :
    Bounded (ordinaryDerivedKoszul f) := by
  -- Proof comment: the ordinary Koszul object lies between the explicit bounds `-r` and `0`.
  change (∃ n, (ordinaryDerivedKoszul f).IsGE n) ∧ ∃ n, (ordinaryDerivedKoszul f).IsLE n
  exact ⟨⟨-((r : ℕ) : ℤ), ordinary_derived_koszul_isGE_neg_r f⟩,
    ⟨0, ordinary_derived_koszul_isLE_zero f⟩⟩

/-- Helper for Lemma 15.92.19: annihilator containment is preserved by a linear equivalence. -/
private theorem le_annihilator_of_linearEquiv
    (I : Ideal A)
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N)
    (hM : I ≤ Module.annihilator A M) :
    I ≤ Module.annihilator A N := by
  intro a ha
  rw [Module.mem_annihilator]
  intro x
  apply e.symm.injective
  simpa using Module.mem_annihilator.mp (hM ha) (e.symm x)

/-- Helper for Lemma 15.92.19: the width-induction base case reduces annihilated degree-zero
modules to the quotient test object `(A / I)[0]`. -/
private theorem tensor_annihilated_single_isLE_zero_of_modIdeal
    (I : Ideal A) (K : DMod)
    (hKI :
      (K ⊗[A]^L (single₀).obj (ModuleCat.of A (A ⧸ I))).IsLE 0)
    (N : ModuleCat A)
    (hN : I ≤ Module.annihilator A N) :
    (K ⊗[A]^L (single₀).obj N).IsLE 0 := by
  -- Proof comment: the remaining forward blocker is the quotient-base-change comparison for
  -- `I`-annihilated modules. Once `K ⊗^L_A (A / I)[0]` is viewed over `A / I`, tensoring with the
  -- induced degree-zero `A / I`-module `N` is the ordinary degree-zero tensor-preservation step.
  -- TODO: equip `N` with its canonical `A ⧸ I`-module structure, compare
  -- `restrictScalars (((K ⊗^L_A[A/I]) ⊗^L_{A/I} N[0]))` with `K ⊗^L_A N[0]`, and transport the
  -- `IsLE 0` bound back through restriction of scalars using the quotient homology comparison.
  let _ := hKI
  let _ := hN
  sorry

/-- Helper for Lemma 15.92.19: shifting the right tensor factor shifts the total derived tensor
product by the same amount. -/
private noncomputable def derivedTensorProduct_right_shift_iso
    (X Y : DMod) (d : ℤ) :
    X ⊗[A]^L (Y⟦d⟧) ≅ (X ⊗[A]^L Y)⟦d⟧ :=
  derivedTensorProduct_comm X (Y⟦d⟧) ≪≫
    (((derivedTensorProduct_commShift X).commShiftIso d).app Y) ≪≫
      ((shiftFunctor DMod d).mapIso (derivedTensorProduct_comm Y X))

/-- Helper for Lemma 15.92.19: once the degree-zero tensor bound is known for a module, the same
bound holds for the corresponding single object placed in any nonpositive degree. -/
private theorem tensor_singleFunctor_isLE_zero_of_single0
    (K : DMod) {M : ModuleCat A} {c : ℤ}
    (hK : (K ⊗[A]^L (single₀).obj M).IsLE 0)
    (hc : c ≤ 0) :
    (K ⊗[A]^L (DerivedCategory.singleFunctor (ModuleCat A) c).obj M).IsLE 0 := by
  let eSingle :
      (DerivedCategory.singleFunctor (ModuleCat A) c).obj M ≅
        ((single₀).obj M)⟦-c⟧ :=
    -- Proof comment: rewrite the degree-`c` single object as the shifted degree-zero single
    -- object on the same module.
    (shiftShiftNeg ((DerivedCategory.singleFunctor (ModuleCat A) c).obj M) c).symm ≪≫
      (shiftFunctor DMod (-c)).mapIso
        (singleFunctor_shifted_single0_iso_canonical (R := A) M c)
  have hShifted : (K ⊗[A]^L (((single₀).obj M)⟦-c⟧)).IsLE c := by
    have hBaseShift : ((K ⊗[A]^L (single₀).obj M)⟦-c⟧).IsLE c := by
      -- Proof comment: shifting a nonpositive object by `-c` moves the cutoff from `0` to `c`.
      letI : (K ⊗[A]^L (single₀).obj M).IsLE 0 := hK
      simpa using (t.isLE_shift (K ⊗[A]^L (single₀).obj M) 0 (-c) c)
    -- Proof comment: transport the shifted cutoff across the canonical tensor/shift comparison.
    letI : ((K ⊗[A]^L (single₀).obj M)⟦-c⟧).IsLE c := hBaseShift
    exact
      t.isLE_of_iso
        (derivedTensorProduct_right_shift_iso K ((single₀).obj M) (-c)).symm
        c
  have hShiftedZero : (K ⊗[A]^L (((single₀).obj M)⟦-c⟧)).IsLE 0 := by
    -- Proof comment: the stronger cutoff `≤ c` implies `≤ 0` because `c ≤ 0`.
    rw [DerivedCategory.isLE_iff] at hShifted ⊢
    intro i hi
    exact hShifted i (lt_of_le_of_lt hc hi)
  -- Proof comment: transport the shifted degree-zero bound back to the original degree-`c`
  -- single object.
  letI : (K ⊗[A]^L (((single₀).obj M)⟦-c⟧)).IsLE 0 := hShiftedZero
  exact t.isLE_of_iso (derivedTensorProduct_right_map_iso (X := K) eSingle.symm) 0

/-- Helper for Lemma 15.92.19: a bounded nonpositive derived object whose nonpositive homology is
annihilated by `I` inherits the quotient-test tensor bound. -/
private theorem tensor_isLE_zero_of_bounded_annihilated_homology
    (I : Ideal A) (K : DMod)
    (hKI :
      (K ⊗[A]^L (single₀).obj (ModuleCat.of A (A ⧸ I))).IsLE 0) :
    ∀ n : ℕ, ∀ L : DMod,
      L.IsGE (-((n : ℤ))) →
      L.IsLE 0 →
      (∀ i ≤ 0,
        I ≤ Module.annihilator A
          ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj L)) →
      (K ⊗[A]^L L).IsLE 0 := by
  -- Proof comment: the width-zero case is already reduced to
  -- `tensor_annihilated_single_isLE_zero_of_modIdeal`, and the successor case follows the same
  -- truncation-triangle induction as Lemma `15.89.7`.
  -- TODO: the remaining blocker is the dependency-closed homology comparison
  -- `H^i(L) ≅ H^i(τ_{\ge a + 1} L)` for `a + 1 ≤ i`, together with a stable right-tensor
  -- triangle package for the successor step.
  let _ := hKI
  sorry

/-- Helper for Lemma 15.92.19: after normalizing stage `0` to the ordinary extended Koszul
complex, the remaining `(2) → (3)` step is exactly the bounded ideal-power-torsion package
needed by Lemma `15.89.7`. -/
private theorem tensor_ordinary_koszul_isLE_zero_of_modIdeal
    (f : Fin r → A) (K : DMod)
    (hKI :
      (K ⊗[A]^L (single₀).obj (ModuleCat.of A (A ⧸ Ideal.span (Set.range f)))).IsLE 0) :
    (K ⊗[A]^L ordinaryDerivedKoszul f).IsLE 0 := by
  -- Route correction: keep the source proof local and dependency-closed by replaying the bounded
  -- width induction directly with the sharper annihilator package proved above for ordinary Koszul
  -- homology.
  exact
    tensor_isLE_zero_of_bounded_annihilated_homology
      (I := Ideal.span (Set.range f))
      K hKI r
      (ordinaryDerivedKoszul f)
      (ordinary_derived_koszul_isGE_neg_r f)
      (ordinary_derived_koszul_isLE_zero f)
      (ordinary_derived_koszul_homology_annihilator f)

/-- Helper for Lemma 15.92.19: the stage-`0` powered Koszul object should be handled by the
bounded ideal-power-torsion tensor criterion from Lemma `15.89.7`. -/
private theorem tensor_koszul_stage_zero_isLE_zero_of_modIdeal
    (f : Fin r → A) (K : DMod)
    (hKI :
      (K ⊗[A]^L (single₀).obj (ModuleCat.of A (A ⧸ Ideal.span (Set.range f)))).IsLE 0) :
    (K ⊗[A]^L (derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op 0)).IsLE 0 := by
  -- Proof comment: replace the public stage-`0` owner by the ordinary extended Koszul complex,
  -- then isolate the remaining bounded/torsion package as a separate helper.
  let LOrd :
      DMod :=
    ordinaryDerivedKoszul f
  have hOrd : (K ⊗[A]^L LOrd).IsLE 0 :=
    tensor_ordinary_koszul_isLE_zero_of_modIdeal f K hKI
  letI : (K ⊗[A]^L LOrd).IsLE 0 := hOrd
  exact
    t.isLE_of_iso
      (derivedTensorProduct_right_map_iso
        (X := K) (stage_zero_powered_koszul_iso_ordinary f)).symm 0

/-- Helper for Lemma 15.92.19: after normalizing stage `0` to the ordinary extended Koszul
complex, the remaining `(3) → (1)` step is the descending induction on partial Koszul lengths
from the textbook proof. -/
private theorem derived_complete_isLE_zero_of_tensor_ordinary_koszul_isLE_zero
    (f : Fin r → A) (K : DMod)
    (hK : K.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f)))
    (hKoszul : (K ⊗[A]^L ordinaryDerivedKoszul f).IsLE 0) :
    K.IsLE 0 := by
  -- Proof comment: the stage normalization is done, so the remaining blocker is now exactly the
  -- `Fin.init` / `Fin.last` descent on ordinary partial Koszul complexes from the source proof.
  -- Proof comment: the empty-stage base case is now isolated by
  -- `tensor_ordinary_koszul_empty_isLE_zero_iff`, so only the ordinary partial-Koszul triangle
  -- and the descending step remain to be transported.
  -- TODO: transport `koszulComplex_iso_homotopyCofiber_truncate_last` to a distinguished
  -- triangle in `D(A)`, prove the partial tensor stages stay derived complete, and use the long
  -- exact homology sequence plus Lemmas `15.92.6` and `15.92.7` to descend the `IsLE 0` bound.
  sorry

/-- Helper for Lemma 15.92.19: the implication from the first Koszul stage back to `K.IsLE 0`
should follow by descending on the partial Koszul length. -/
private theorem derived_complete_isLE_zero_of_tensor_koszul_stage_zero_isLE_zero
    (f : Fin r → A) (K : DMod)
    (hK : K.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f)))
    (hKoszul :
      (K ⊗[A]^L (derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op 0)).IsLE 0) :
    K.IsLE 0 := by
  -- Proof comment: first normalize the public stage-`0` owner to the ordinary extended Koszul
  -- complex, then defer the remaining descent to the source-faithful ordinary-Koszul helper.
  have hOrd :
      (K ⊗[A]^L ordinaryDerivedKoszul f).IsLE 0 := by
    letI :
        (K ⊗[A]^L (derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op 0)).IsLE 0 :=
      hKoszul
    exact
      t.isLE_of_iso
        (derivedTensorProduct_right_map_iso
          (X := K) (stage_zero_powered_koszul_iso_ordinary f)) 0
  exact
    derived_complete_isLE_zero_of_tensor_ordinary_koszul_isLE_zero f K hK hOrd

/-- Lemma 15.92.19: let `I = (f₁, \ldots, fᵣ)` and let `K` be derived complete with respect to
`I`. Then the following are equivalent: `K` has no positive cohomology; the derived tensor product
`K \otimes_A^{\mathbf L} (A / I)[0]` has no positive cohomology; and the derived tensor product
with the first Koszul complex `K_1^•` from Situation `15.92.15`, represented by the stage `0`
object of the powered Koszul inverse system, has no positive cohomology. -/
theorem derivedComplete_isLE_zero_tfae_of_span_range
    (f : Fin r → A) (K : DMod)
    (hK : K.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f))) :
    List.TFAE [
      K.IsLE 0,
      (K ⊗[A]^L (single₀).obj (ModuleCat.of A (A ⧸ Ideal.span (Set.range f)))).IsLE 0,
      (K ⊗[A]^L (derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op 0)).IsLE 0
    ] := by
  -- Proof comment: keep the textbook route explicit by proving the easy quotient implication
  -- first, then isolating the stage-`0` Koszul packaging step and the descending induction step as
  -- the two remaining source-faithful blockers.
  tfae_have 1 → 2 := by
    intro h₁
    -- Proof comment: this is the direct source implication that degree-zero tensor factors do not
    -- create positive cohomology.
    exact
      tensor_single_isLE_zero_of_isLE_zero
        K h₁ (ModuleCat.of A (A ⧸ Ideal.span (Set.range f)))
  tfae_have 2 → 3 := by
    intro h₂
    exact tensor_koszul_stage_zero_isLE_zero_of_modIdeal f K h₂
  tfae_have 3 → 1 := by
    intro h₃
    exact
      derived_complete_isLE_zero_of_tensor_koszul_stage_zero_isLE_zero
        f K hK h₃
  tfae_finish

end

end CategoryTheory
