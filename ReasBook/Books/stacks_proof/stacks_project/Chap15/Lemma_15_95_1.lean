import StacksProject_2024.Chap04.Example_4_22_6
import StacksProject_2024.Chap15.Situation_15_92_15
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SequentialProObjectMorphismRep
open scoped KoszulComplex

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] {r : ℕ}

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single0" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/- Domain-style sampling for Lemma 15.95.1:
- primary domain: sequential pro-object comparison between the powered Koszul tower in `D(A)` and
  the degree-zero image of the powered quotient tower from Situation `15.92.15`;
- sampled owner declarations:
  `koszulPowerQuotientStage`,
  `koszulPowerQuotientInverseSystem`,
  `derivedCompletionKoszulPowersDerivedInverseSystem`,
  `SequentialProObjectMorphismRep.toProObjectHom`;
- best owner abstraction: the quotient side should reuse the source-facing module-level owner
  `koszulPowerQuotientInverseSystem` and pass to `D(A)` by whiskering with the canonical degree-zero
  single functor, while the comparison itself should be expressed through a sequential
  representative together with the induced owner-level morphism of pro-objects
  `a.toProObjectHom`;
- primitive data: the powered quotient modules `A / (f_1^(n+1), \ldots, f_r^(n+1))` from
  Situation `15.92.15`;
- derived API: their images in `D(A)` and the resulting pro-isomorphism statement.

Source/core/bridge triage:
- `source-facing`: the pro-isomorphism between the powered Koszul tower and the quotient tower;
- `core/canonical`: `koszulPowerQuotientInverseSystem`,
  `derivedCompletionKoszulPowersDerivedInverseSystem`, `SequentialProObjectMorphismRep`, and
  `SequentialProObjectMorphismRep.toProObjectHom`;
- `bridge/view`: the degree-zero single-functor realization of the quotient tower inside `D(A)`. -/

/-- The `n`th quotient stage `A / (f_1^(n+1), \ldots, f_r^(n+1))`, viewed in degree `0` in
`D(A)`. -/
abbrev derivedCompletionPowerQuotientDerivedStage
    (f : Fin r → A) (n : ℕ) : DMod :=
  (single0).obj (koszulPowerQuotientStage f n)

/-- The inverse system of quotient objects
`(A / (f_1^(n+1), \ldots, f_r^(n+1)))[0]` in `D(A)`, obtained by applying the degree-zero single
functor to the owner tower `koszulPowerQuotientInverseSystem f` from Situation `15.92.15`. -/
abbrev derivedCompletionPowerQuotientDerivedInverseSystem
    (f : Fin r → A) : ℕᵒᵖ ⥤ DMod :=
  koszulPowerQuotientInverseSystem f ⋙ single0

end

end CategoryTheory

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ}

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single0" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)
local notation "singleCpx₀" => ChainComplex.single₀ (ModuleCat A)
local notation "singleCpxℤ₀" => HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℤ) (0 : ℤ)

/-- Helper for Lemma 15.95.1: the degree-zero quotient map from the `n`th powered Koszul stage
to `A / (f_1^(n+1), \ldots, f_r^(n+1))`. -/
abbrev koszul_power_zero_quotient_map
    (f : Fin r → A) (n : ℕ) :
    (K^•[n](f)).X 0 ⟶ koszulPowerQuotientStage f n :=
  show ModuleCat.of A (⋀[A]^0 (Fin r → A)) ⟶
      ModuleCat.of A (A ⧸ koszulPowerIdeal f n) from
    (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin r → A))).hom ≫
      ModuleCat.ofHom ((Ideal.Quotient.mkₐ A (koszulPowerIdeal f n)).toLinearMap)

/-- Helper for Lemma 15.95.1: after transporting degree `0` to `A`, the range of the first
powered Koszul differential is the powered ideal. -/
theorem koszul_power_first_differential_generator_eval
    (f : Fin r → A) (n : ℕ) (m : Fin 1 → Fin r → A) :
    (koszulDifferentialLinearMap
        (koszulLinearForm (fun i ↦ f i ^ (n + 1))) 0
        (exteriorPower.ιMulti A 1 m) :
      ExteriorAlgebra A (Fin r → A)) =
      algebraMap A (ExteriorAlgebra A (Fin r → A))
        ((koszulLinearForm (fun i ↦ f i ^ (n + 1))) (m 0)) := by
  -- Unfold the first differential back to contraction on the ambient exterior algebra.
  change
    CliffordAlgebra.contractLeft
        (koszulLinearForm (fun i ↦ f i ^ (n + 1)))
        (exteriorPower.ιMulti A 1 m) =
      algebraMap A (ExteriorAlgebra A (Fin r → A))
        ((koszulLinearForm (fun i ↦ f i ^ (n + 1))) (m 0))
  simpa [koszulDifferentialLinearMap] using
    (CliffordAlgebra.contractLeft_ι
      (φ := koszulLinearForm (fun i ↦ f i ^ (n + 1))) (m := m 0))

/-- Helper for Lemma 15.95.1: after transporting `⋀¹(A^r)` to `A^r` and `⋀⁰(A^r)` to `A`, the
first powered Koszul differential is the tuple linear form. -/
theorem koszul_power_first_differential_linearMap_eq_linearForm
    (f : Fin r → A) (n : ℕ) :
    (exteriorPower.zeroEquiv A (Fin r → A)).toLinearMap.comp
        (koszulDifferentialLinearMap
          (koszulLinearForm (fun i ↦ f i ^ (n + 1))) 0) =
      (koszulLinearForm (fun i ↦ f i ^ (n + 1))).comp
        (exteriorPower.oneEquiv A (Fin r → A)).toLinearMap := by
  -- Route correction: normalize the generator calculation before transporting through `⋀¹` and
  -- `⋀⁰`.
  apply exteriorPower.linearMap_ext
  ext m
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply]
  have hone :
      (exteriorPower.oneEquiv A (Fin r → A)) (exteriorPower.ιMulti A 1 m) = m 0 := by
    simpa using (exteriorPower.oneEquiv_ιMulti (R := A) (M := Fin r → A) (f := m))
  have hone' :
      (koszulLinearForm (fun i ↦ f i ^ (n + 1)))
          ((exteriorPower.oneEquiv A (Fin r → A)) (exteriorPower.ιMulti A 1 m)) =
        (koszulLinearForm (fun i ↦ f i ^ (n + 1))) (m 0) := by
    simpa [hone]
  have hone'' :
      (koszulLinearForm (fun i ↦ f i ^ (n + 1)))
          ((exteriorPower.oneEquiv A (Fin r → A)).toLinearMap
            (exteriorPower.ιMulti A 1 m)) =
        (koszulLinearForm (fun i ↦ f i ^ (n + 1))) (m 0) := by
    simpa using hone'
  rw [hone'']
  apply_fun (exteriorPower.zeroEquiv A (Fin r → A)).symm using
    (exteriorPower.zeroEquiv A (Fin r → A)).symm.injective
  simp only [Nat.reduceAdd, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Fin.isValue]
  rw [exteriorPower.zeroEquiv_symm_apply]
  apply Subtype.ext
  simpa [ExteriorAlgebra.ιMulti, Algebra.algebraMap_eq_smul_one] using
    koszul_power_first_differential_generator_eval f n m

/-- Helper for Lemma 15.95.1: after transporting degree `0` to `A`, the range of the first
powered Koszul differential is the powered ideal. -/
theorem koszul_power_first_differential_range_eq_power_ideal
    (f : Fin r → A) (n : ℕ) :
    LinearMap.range
        (((K^•[n](f)).d 1 0) ≫
          (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin r → A))).hom).hom =
      koszulPowerIdeal f n := by
  -- Transport the first differential to the standard tuple linear form on `A^r`.
  change
    LinearMap.range
        ((exteriorPower.zeroEquiv A (Fin r → A)).toLinearMap.comp
          (koszulDifferentialLinearMap
            (koszulLinearForm (fun i ↦ f i ^ (n + 1))) 0)) =
      koszulPowerIdeal f n
  rw [koszul_power_first_differential_linearMap_eq_linearForm]
  have hrange :
      LinearMap.range
          ((koszulLinearForm (fun i ↦ f i ^ (n + 1))).comp
            (exteriorPower.oneEquiv A (Fin r → A)).toLinearMap) =
        LinearMap.range (koszulLinearForm (fun i ↦ f i ^ (n + 1))) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(exteriorPower.oneEquiv A (Fin r → A)) y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨(exteriorPower.oneEquiv A (Fin r → A)).symm y, by simp⟩
  rw [hrange]
  simpa [koszulPowerIdeal] using
    ((Module.range_piEquiv (Fin r) A A (fun i ↦ f i ^ (n + 1))).trans Ideal.submodule_span_eq)

/-- Helper for Lemma 15.95.1: the first differential of the `n`th powered Koszul stage lands in
the powered ideal, so the degree-zero quotient map annihilates it. -/
theorem koszul_power_zero_quotient_map_comp_d_eq_zero
    (f : Fin r → A) (n : ℕ) :
    (K^•[n](f)).d 1 0 ≫ koszul_power_zero_quotient_map f n = 0 := by
  -- Read the image of the differential inside the quotient source after identifying `⋀⁰` with
  -- `A`, then use the quotient criterion for vanishing.
  ext x
  have hxmem :
      ((((K^•[n](f)).d 1 0) ≫
          (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin r → A))).hom).hom) x ∈
        koszulPowerIdeal f n := by
    rw [← koszul_power_first_differential_range_eq_power_ideal f n]
    exact ⟨x, rfl⟩
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hxmem

/-- Helper for Lemma 15.95.1: the degree-zero quotient maps commute with the adjacent transition
maps in the powered Koszul and quotient towers. -/
theorem koszul_power_zero_quotient_map_naturality
    (f : Fin r → A) (n : ℕ) :
    (koszulPowerStep f n).f 0 ≫ koszul_power_zero_quotient_map f n =
      koszul_power_zero_quotient_map f (n + 1) ≫ koszulPowerQuotientStep f n := by
  -- In degree `0`, the Koszul transition is the identity under `⋀⁰ ≃ A`.
  change
    ModuleCat.exteriorPower.map (ModuleCat.ofHom (koszulPowerStepLinearMap f)) 0 ≫
        (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin r → A))).hom ≫
          ModuleCat.ofHom ((Ideal.Quotient.mkₐ A (koszulPowerIdeal f n)).toLinearMap) =
      ((ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin r → A))).hom ≫
          ModuleCat.ofHom ((Ideal.Quotient.mkₐ A (koszulPowerIdeal f (n + 1))).toLinearMap)) ≫
        ModuleCat.ofHom ((Ideal.Quotient.factorₐ A (koszulPowerIdeal_succ_le f n)).toLinearMap)
  rw [← Category.assoc]
  rw [ModuleCat.exteriorPower.iso₀_hom_naturality
      (f := ModuleCat.ofHom (koszulPowerStepLinearMap f))]
  ext x
  rfl

/-- Helper for Lemma 15.95.1: the canonical degree-zero quotient map on the `n`th powered Koszul
stage, viewed as a chain map to the degree-zero single complex on
`A / (f_1^(n+1), \ldots, f_r^(n+1))`. -/
abbrev koszulPowerQuotientChainMap
    (f : Fin r → A) (n : ℕ) :
    K^•[n](f) ⟶ (singleCpx₀).obj (koszulPowerQuotientStage f n) :=
  (ChainComplex.toSingle₀Equiv (K^•[n](f)) (koszulPowerQuotientStage f n)).symm
    ⟨koszul_power_zero_quotient_map f n,
      koszul_power_zero_quotient_map_comp_d_eq_zero f n⟩

/-- Helper for Lemma 15.95.1: the chain-level quotient maps are compatible with the transition
maps in the powered Koszul and quotient towers. -/
theorem koszulPowerQuotientChainMap_naturality
    (f : Fin r → A) (n : ℕ) :
    koszulPowerStep f n ≫ koszulPowerQuotientChainMap f n =
      koszulPowerQuotientChainMap f (n + 1) ≫
        (singleCpx₀).map (koszulPowerQuotientStep f n) := by
  -- Maps into `single₀` are determined by their degree-zero component.
  apply HomologicalComplex.to_single_hom_ext
  -- The degree-zero component is exactly the quotient square established above.
  simpa [koszulPowerQuotientChainMap, Category.assoc] using
    koszul_power_zero_quotient_map_naturality f n

/-- Helper for Lemma 15.95.1: the stagewise quotient chain maps induce the canonical morphism
from the `n`th powered Koszul stage in `D(A)` to the `n`th quotient stage in degree `0`. -/
abbrev derivedCompletionKoszulToPowerQuotientStage
    (f : Fin r → A) (n : ℕ) :
    (derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n) ⟶
      derivedCompletionPowerQuotientDerivedStage f n :=
  DerivedCategory.Q.map
      (HomologicalComplex.extendMap
        (koszulPowerQuotientChainMap f n) ComplexShape.embeddingDownNat) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.extendSingleIso
          ComplexShape.embeddingDownNat
          (koszulPowerQuotientStage f n)
          (0 : ℕ) (0 : ℤ) rfl).hom) ≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      (koszulPowerQuotientStage f n)).inv

/-- Helper for Lemma 15.95.1: naturality of `homologyFunctorFactors` rewrites the `Q.map` part of
the stagewise comparison to the chain-level homology map on the extended complexes. -/
theorem derived_completion_koszul_stage_h0_source_naturality
    (f : Fin r → A) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
        (DerivedCategory.Q.map
          (HomologicalComplex.extendMap
            (koszulPowerQuotientChainMap f n)
            ComplexShape.embeddingDownNat)) ≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
        (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
          ((singleCpx₀).obj (koszulPowerQuotientStage f n))))) =
    ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj (K^•[n](f))))) ≫
      HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap
          (koszulPowerQuotientChainMap f n)
          ComplexShape.embeddingDownNat) 0 := by
  -- Naturality compares derived homology of `Q.map` with chain-level homology of the extended
  -- representative map.
  simpa using
    (DerivedCategory.homologyFunctorFactors_hom_naturality (C := ModuleCat A)
      (HomologicalComplex.extendMap
        (koszulPowerQuotientChainMap f n)
        ComplexShape.embeddingDownNat) 0)

/-- Helper for Lemma 15.95.1: the `extendSingleIso` factor in degree `0` is already controlled by
`homologyFunctorFactors`; this isolates the transport part of the quotient-side comparison. -/
theorem derived_completion_koszul_stage_h0_extend_single_naturality
    (M : ModuleCat A) :
    ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
        ((singleCpx₀).obj M)))) ≫
      HomologicalComplex.homologyMap
        ((HomologicalComplex.extendSingleIso
          ComplexShape.embeddingDownNat
          M
          (0 : ℕ) (0 : ℤ) rfl).hom) 0 =
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
        (DerivedCategory.Q.map
          ((HomologicalComplex.extendSingleIso
            ComplexShape.embeddingDownNat
            M
            (0 : ℕ) (0 : ℤ) rfl).hom)) ≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
        ((singleCpxℤ₀).obj M)) := by
  -- Route correction: isolate the transport across `extendSingleIso` before combining it with the
  -- separate `singleFunctorIsoCompQ` comparison.
  simpa using
    (DerivedCategory.homologyFunctorFactors_hom_naturality (C := ModuleCat A)
      ((HomologicalComplex.extendSingleIso
        ComplexShape.embeddingDownNat
        M
        (0 : ℕ) (0 : ℤ) rfl).hom) 0).symm

/-- Helper for Lemma 15.95.1: in the `ℤ`-indexed degree-zero single complex, the incoming
differential into degree `0` vanishes. -/
theorem single0_z_objXSelf_comp_d_eq_zero
    (M : ModuleCat A) :
    ((singleCpxℤ₀).obj M).d (-1) 0 ≫
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℤ) (0 : ℤ) M).hom = 0 := by
  -- The `up ℤ` single complex has no nontrivial incoming differential at the unique nonzero term.
  rw [HomologicalComplex.single_obj_d]
  simp [HomologicalComplex.singleObjXSelf]

/-- Helper for Lemma 15.95.1: in `ComplexShape.up ℤ`, the predecessor of degree `0` is `-1`. -/
theorem complexShape_up_prev_zero : (ComplexShape.up ℤ).prev (0 : ℤ) = (-1 : ℤ) := by
  simp

/-- Helper for Lemma 15.95.1: on the `ℤ`-indexed degree-zero single complex, the canonical map
from zeroth opcycles to `M` is the descended degree-zero component. -/
theorem single0_z_opcycles_self_inv_eq_descOpcycles
    (M : ModuleCat A) :
    (HomologicalComplex.singleObjOpcyclesSelfIso
      (ComplexShape.up ℤ) (0 : ℤ) M).inv =
    ((singleCpxℤ₀).obj M).descOpcycles
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℤ) (0 : ℤ) M).hom
      (-1) (by simp) (single0_z_objXSelf_comp_d_eq_zero (A := A) M) := by
  -- As in the nat-indexed case, both maps are determined by their composites with `pOpcycles`.
  apply (cancel_epi (((singleCpxℤ₀).obj M).pOpcycles 0)).1
  calc
    ((singleCpxℤ₀).obj M).pOpcycles 0 ≫
        (HomologicalComplex.singleObjOpcyclesSelfIso
          (ComplexShape.up ℤ) (0 : ℤ) M).inv =
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℤ) (0 : ℤ) M).hom := by
          simpa using
            (HomologicalComplex.pOpcycles_singleObjOpcyclesSelfIso_inv
              (c := ComplexShape.up ℤ) (j := (0 : ℤ)) (A := M))
    _ =
      ((singleCpxℤ₀).obj M).pOpcycles 0 ≫
        ((singleCpxℤ₀).obj M).descOpcycles
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℤ) (0 : ℤ) M).hom
          (-1) (by simp) (single0_z_objXSelf_comp_d_eq_zero (A := A) M) := by
            symm
            simpa using
              (HomologicalComplex.p_descOpcycles
                (K := (singleCpxℤ₀).obj M)
                (i := (0 : ℤ))
                (k := (HomologicalComplex.singleObjXSelf
                  (ComplexShape.up ℤ) (0 : ℤ) M).hom)
                (j := (-1 : ℤ))
              (hj := by simp)
              (hk := single0_z_objXSelf_comp_d_eq_zero (A := A) M))

/-- Helper for Lemma 15.95.1: on a degree-zero single chain complex, the canonical comparison
from zeroth opcycles to the underlying module is the map descended from the degree-zero term. -/
theorem single0_objXSelf_comp_d_eq_zero
    (M : ModuleCat A) :
    ((singleCpx₀).obj M).d 1 0 ≫
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom = 0 := by
  -- In the degree-zero single complex, the incoming differential is zero.
  rw [HomologicalComplex.single_obj_d]
  simp [ChainComplex.single₀ObjXSelf]
  rfl

/-- Helper for Lemma 15.95.1: on a degree-zero single chain complex, the canonical comparison
from zeroth opcycles to the underlying module is the map descended from the degree-zero term. -/
theorem single0_opcycles_self_inv_eq_descOpcycles
    (M : ModuleCat A) :
    (HomologicalComplex.singleObjOpcyclesSelfIso
      (ComplexShape.down ℕ) (0 : ℕ) M).inv =
    ((singleCpx₀).obj M).descOpcycles
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom
      1 (by simp) (single0_objXSelf_comp_d_eq_zero (A := A) M) := by
  -- Both maps out of `opcycles₀(single₀ M)` are determined by their composites with
  -- `pOpcycles`, and those composites are the same degree-zero identity map.
  apply (cancel_epi (((singleCpx₀).obj M).pOpcycles 0)).1
  calc
    ((singleCpx₀).obj M).pOpcycles 0 ≫
        (HomologicalComplex.singleObjOpcyclesSelfIso
          (ComplexShape.down ℕ) (0 : ℕ) M).inv =
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom := by
          simpa [ChainComplex.single₀ObjXSelf] using
            (HomologicalComplex.pOpcycles_singleObjOpcyclesSelfIso_inv
              (c := ComplexShape.down ℕ) (j := (0 : ℕ)) (A := M))
    _ =
      ((singleCpx₀).obj M).pOpcycles 0 ≫
        ((singleCpx₀).obj M).descOpcycles
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) (0 : ℕ) M).hom
          1 (by simp) (single0_objXSelf_comp_d_eq_zero (A := A) M) := by
            symm
            simpa using
              (HomologicalComplex.p_descOpcycles
                (K := (singleCpx₀).obj M)
                (i := (0 : ℕ))
                (k := (HomologicalComplex.singleObjXSelf
                  (ComplexShape.down ℕ) (0 : ℕ) M).hom)
                (j := 1)
                (hj := by simp)
                (hk := single0_objXSelf_comp_d_eq_zero (A := A) M))

/-- Helper for Lemma 15.95.1: the degree-zero owner component of
`DerivedCategory.singleFunctorsPostcompQIso` is the identity. -/
theorem DerivedCategory.singleFunctorsPostcompQIso_hom_app_zero_eq_id
    (M : ModuleCat A) :
    (((DerivedCategory.singleFunctorsPostcompQIso (ModuleCat A)).hom.hom (0 : ℤ)).app M) = 𝟙 _ := by
  -- Unfold the owner comparison to the homotopy-level single functor and the localization
  -- comparison; on a degree-zero single complex both components are identities.
  simp [DerivedCategory.singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso]
  rfl

/-- Helper for Lemma 15.95.1: the degree-zero component of `extendSingleIso` is the expected
transport from the extended nat-indexed single complex to the `ℤ`-indexed single complex. -/
theorem HomologicalComplex.extendSingleIso_zero_component_comp_single_obj_x_self
    (M : ModuleCat A) :
    ((HomologicalComplex.extendSingleIso
        ComplexShape.embeddingDownNat
        M
        (0 : ℕ) (0 : ℤ) rfl).hom).f 0 ≫
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℤ) (0 : ℤ) M).hom =
    (((singleCpx₀).obj M).extendXIso
      (e := ComplexShape.embeddingDownNat) (i := (0 : ℕ)) (i' := (0 : ℤ)) rfl).hom ≫
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom := by
  -- The owner formula for `extendSingleIso.hom.f 0` already contains the desired transport; the
  -- terminal `singleObjXSelf` cancels against its inverse on the `ℤ`-indexed single complex.
  simpa [Category.assoc] using
    congrArg
      (fun t ↦
        t ≫
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℤ) (0 : ℤ) M).hom)
      (HomologicalComplex.extendSingleIso_hom_f
        (e := ComplexShape.embeddingDownNat)
        (X := M)
        (i := (0 : ℕ))
        (i' := (0 : ℤ))
        (h := rfl))

/-- Helper for Lemma 15.95.1: the nat-indexed degree-zero single-complex comparison remains a
cycle after extending from `ℕ` to `ℤ`. -/
theorem single0_extend_objXSelf_comp_d_eq_zero
    (M : ModuleCat A) :
    (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
        ((singleCpx₀).obj M)).d (-1) 0) ≫
      (((singleCpx₀).obj M).extendXIso
        (e := ComplexShape.embeddingDownNat) (i := (0 : ℕ)) (i' := (0 : ℤ)) rfl).hom ≫
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom = 0 := by
  -- This is the owner-side `d_comp_eq_zero_iff` bridge for the degree-zero nat single complex.
  exact
    ((HomologicalComplex.extend.d_comp_eq_zero_iff
      (K := (singleCpx₀).obj M)
      (e := ComplexShape.embeddingDownNat)
      (j := (0 : ℕ))
      (j' := (0 : ℤ))
      (hj' := rfl)
      (i := (1 : ℕ))
      (i' := (-1 : ℤ))
      (hi := by simp)
      (hi' := by simp)
      (φ := (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom)).mp
      (single0_objXSelf_comp_d_eq_zero (A := A) M))

/-- Helper for Lemma 15.95.1: on the extended degree-zero single complex, the owner
`extendOpcyclesIso` transport to nat-indexed opcycles is already the descended degree-zero
component. -/
theorem HomologicalComplex.extendOpcyclesIso_hom_comp_single0_opcycles_self_inv
    (M : ModuleCat A) :
    ((((singleCpx₀).obj M).extendOpcyclesIso
        (e := ComplexShape.embeddingDownNat) (j := (0 : ℕ)) (j' := (0 : ℤ)) rfl).hom ≫
      (HomologicalComplex.singleObjOpcyclesSelfIso
        (ComplexShape.down ℕ) (0 : ℕ) M).inv) =
    (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
        ((singleCpx₀).obj M)).descOpcycles
      ((((singleCpx₀).obj M).extendXIso
          (e := ComplexShape.embeddingDownNat) (i := (0 : ℕ)) (i' := (0 : ℤ)) rfl).hom ≫
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.down ℕ) (0 : ℕ) M).hom)
      (-1) (by simp) (single0_extend_objXSelf_comp_d_eq_zero (A := A) M)) := by
  -- As in the single-complex case, both candidate maps out of opcycles are determined by their
  -- composites with `pOpcycles 0`.
  have hp_desc :
      (((singleCpx₀).obj M).extendXIso
        (e := ComplexShape.embeddingDownNat) (i := (0 : ℕ)) (i' := (0 : ℤ)) rfl).hom ≫
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.down ℕ) (0 : ℕ) M).hom =
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
          ((singleCpx₀).obj M)).pOpcycles 0) ≫
        (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
          ((singleCpx₀).obj M)).descOpcycles
          ((((singleCpx₀).obj M).extendXIso
              (e := ComplexShape.embeddingDownNat) (i := (0 : ℕ)) (i' := (0 : ℤ)) rfl).hom ≫
            (HomologicalComplex.singleObjXSelf
              (ComplexShape.down ℕ) (0 : ℕ) M).hom)
          (-1) (by simp) (single0_extend_objXSelf_comp_d_eq_zero (A := A) M)) := by
    symm
    simpa [Category.assoc] using
      (HomologicalComplex.p_descOpcycles
        (K := ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
          ((singleCpx₀).obj M)))
        (i := (0 : ℤ))
        (k := (((singleCpx₀).obj M).extendXIso
          (e := ComplexShape.embeddingDownNat) (i := (0 : ℕ)) (i' := (0 : ℤ)) rfl).hom ≫
            (HomologicalComplex.singleObjXSelf
              (ComplexShape.down ℕ) (0 : ℕ) M).hom)
        (j := (-1 : ℤ))
        (hj := by simp)
        (hk := single0_extend_objXSelf_comp_d_eq_zero (A := A) M))
  apply (cancel_epi
    ((((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
      ((singleCpx₀).obj M)).pOpcycles 0))).1
  have h₁ :
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
          ((singleCpx₀).obj M)).pOpcycles 0) ≫
          (((singleCpx₀).obj M).extendOpcyclesIso
              (e := ComplexShape.embeddingDownNat) (j := (0 : ℕ)) (j' := (0 : ℤ)) rfl).hom ≫
          (HomologicalComplex.singleObjOpcyclesSelfIso
            (ComplexShape.down ℕ) (0 : ℕ) M).inv =
        ((((singleCpx₀).obj M).extendXIso
            (e := ComplexShape.embeddingDownNat) (i := (0 : ℕ)) (i' := (0 : ℤ)) rfl).hom ≫
          ((singleCpx₀).obj M).pOpcycles 0) ≫
          (HomologicalComplex.singleObjOpcyclesSelfIso
            (ComplexShape.down ℕ) (0 : ℕ) M).inv := by
    simp [Category.assoc]
  have h₂ :
      ((((singleCpx₀).obj M).extendXIso
          (e := ComplexShape.embeddingDownNat) (i := (0 : ℕ)) (i' := (0 : ℤ)) rfl).hom ≫
        ((singleCpx₀).obj M).pOpcycles 0) ≫
        (HomologicalComplex.singleObjOpcyclesSelfIso
          (ComplexShape.down ℕ) (0 : ℕ) M).inv =
      (((singleCpx₀).obj M).extendXIso
        (e := ComplexShape.embeddingDownNat) (i := (0 : ℕ)) (i' := (0 : ℤ)) rfl).hom ≫
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.down ℕ) (0 : ℕ) M).hom := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          (((singleCpx₀).obj M).extendXIso
              (e := ComplexShape.embeddingDownNat) (i := (0 : ℕ)) (i' := (0 : ℤ)) rfl).hom ≫
            t)
        (HomologicalComplex.pOpcycles_singleObjOpcyclesSelfIso_inv
          (c := ComplexShape.down ℕ) (j := (0 : ℕ)) (A := M))
  exact h₁.trans (h₂.trans hp_desc)

/-- Helper for Lemma 15.95.1: the source-side degree-zero `extendSingleIso` opcycles comparison
already equals the common descended map on the explicit extended single complex. -/
theorem HomologicalComplex.extendSingleIso_opcycles_self_comparison
    (M : ModuleCat A) :
    HomologicalComplex.opcyclesMap
        ((HomologicalComplex.extendSingleIso
          ComplexShape.embeddingDownNat
          M
          (0 : ℕ) (0 : ℤ) rfl).hom) 0 ≫
      (HomologicalComplex.singleObjOpcyclesSelfIso
        (ComplexShape.up ℤ) (0 : ℤ) M).inv =
    (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
        ((singleCpx₀).obj M)).descOpcycles
      ((((singleCpx₀).obj M).extendXIso
          (e := ComplexShape.embeddingDownNat) (i := (0 : ℕ)) (i' := (0 : ℤ)) rfl).hom ≫
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.down ℕ) (0 : ℕ) M).hom)
      (-1) (complexShape_up_prev_zero) (single0_extend_objXSelf_comp_d_eq_zero (A := A) M)) := by
  -- Rewrite the source-side opcycles comparison to the descended-map normal form on the
  -- `ℤ`-indexed single complex, and then replace the degree-zero component by the owner formula
  -- for `extendSingleIso`.
  calc
    HomologicalComplex.opcyclesMap
          ((HomologicalComplex.extendSingleIso
            ComplexShape.embeddingDownNat
            M
            (0 : ℕ) (0 : ℤ) rfl).hom) 0 ≫
        (HomologicalComplex.singleObjOpcyclesSelfIso
          (ComplexShape.up ℤ) (0 : ℤ) M).inv =
      HomologicalComplex.opcyclesMap
          ((HomologicalComplex.extendSingleIso
            ComplexShape.embeddingDownNat
            M
            (0 : ℕ) (0 : ℤ) rfl).hom) 0 ≫
        ((singleCpxℤ₀).obj M).descOpcycles
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℤ) (0 : ℤ) M).hom
          (-1) (complexShape_up_prev_zero) (single0_z_objXSelf_comp_d_eq_zero (A := A) M) := by
            rw [single0_z_opcycles_self_inv_eq_descOpcycles]
    _ =
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
        ((singleCpx₀).obj M)).descOpcycles
        ((((singleCpx₀).obj M).extendXIso
            (e := ComplexShape.embeddingDownNat) (i := (0 : ℕ)) (i' := (0 : ℤ)) rfl).hom ≫
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) (0 : ℕ) M).hom)
        (-1) (complexShape_up_prev_zero) (single0_extend_objXSelf_comp_d_eq_zero (A := A) M)) := by
            simpa [Category.assoc,
              HomologicalComplex.extendSingleIso_zero_component_comp_single_obj_x_self
                (A := A) (M := M)] using
              (HomologicalComplex.opcyclesMap_comp_descOpcycles
                (K := ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
                  ((singleCpx₀).obj M)))
                (L := (singleCpxℤ₀).obj M)
                (φ := (HomologicalComplex.extendSingleIso
                  ComplexShape.embeddingDownNat
                  M
                  (0 : ℕ) (0 : ℤ) rfl).hom)
                (i := (0 : ℤ))
                (k := (HomologicalComplex.singleObjXSelf
                  (ComplexShape.up ℤ) (0 : ℤ) M).hom)
                (j := (-1 : ℤ))
                (hj := complexShape_up_prev_zero)
                (hk := single0_z_objXSelf_comp_d_eq_zero (A := A) M))

/-- Helper for Lemma 15.95.1: the chain-level zeroth-homology transport across `extendSingleIso`
matches the owner `extendHomologyIso` comparison for a degree-zero single complex. -/
theorem HomologicalComplex.extendSingleIso_homology_self_comparison
    (M : ModuleCat A) :
    HomologicalComplex.homologyMap
        ((HomologicalComplex.extendSingleIso
          ComplexShape.embeddingDownNat
          M
          (0 : ℕ) (0 : ℤ) rfl).hom) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.up ℤ) (0 : ℤ) M).hom =
    (((singleCpx₀).obj M).extendHomologyIso ComplexShape.embeddingDownNat (by simp)).hom ≫
      (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.down ℕ) (0 : ℕ) M).hom := by
  let h0z : ComplexShape.embeddingDownNat.f (0 : ℕ) = (0 : ℤ) := rfl
  let e0 :
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
          ((singleCpx₀).obj M)).homology 0 ⟶ ((singleCpx₀).obj M).homology 0) :=
    (((singleCpx₀).obj M).extendHomologyIso ComplexShape.embeddingDownNat h0z).hom
  let commonDesc :
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
          ((singleCpx₀).obj M)).opcycles 0 ⟶ M) :=
    (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
        ((singleCpx₀).obj M)).descOpcycles
      ((((singleCpx₀).obj M).extendXIso
          (e := ComplexShape.embeddingDownNat) (i := (0 : ℕ)) (i' := (0 : ℤ)) rfl).hom ≫
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.down ℕ) (0 : ℕ) M).hom)
      (-1) (complexShape_up_prev_zero) (single0_extend_objXSelf_comp_d_eq_zero (A := A) M))
  have hdesc_transport :
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
          ((singleCpx₀).obj M)).homologyι 0) ≫ commonDesc =
        e0 ≫
          ((singleCpx₀).obj M).homologyι 0 ≫
          (HomologicalComplex.singleObjOpcyclesSelfIso
            (ComplexShape.down ℕ) (0 : ℕ) M).inv := by
    -- First rewrite the common descended map through the owner `extendOpcyclesIso`, then move the
    -- resulting `homologyι` term back across `extendHomologyIso`.
    calc
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
          ((singleCpx₀).obj M)).homologyι 0) ≫ commonDesc =
        (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
            ((singleCpx₀).obj M)).homologyι 0) ≫
          (((singleCpx₀).obj M).extendOpcyclesIso
              (e := ComplexShape.embeddingDownNat) (j := (0 : ℕ)) (j' := (0 : ℤ)) rfl).hom ≫
          (HomologicalComplex.singleObjOpcyclesSelfIso
            (ComplexShape.down ℕ) (0 : ℕ) M).inv := by
              symm
              simpa [commonDesc, Category.assoc] using
                congrArg
                  (fun t ↦
                    (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
                        ((singleCpx₀).obj M)).homologyι 0) ≫ t)
                  (HomologicalComplex.extendOpcyclesIso_hom_comp_single0_opcycles_self_inv
                    (A := A) (M := M))
      _ =
        e0 ≫
          ((singleCpx₀).obj M).homologyι 0 ≫
          (HomologicalComplex.singleObjOpcyclesSelfIso
            (ComplexShape.down ℕ) (0 : ℕ) M).inv := by
              symm
              simpa [e0, h0z, Category.assoc] using
                (HomologicalComplex.extendHomologyIso_hom_homologyι_assoc
                  ((singleCpx₀).obj M)
                  ComplexShape.embeddingDownNat
                  (j := (0 : ℕ))
                  (j' := (0 : ℤ))
                  h0z
                  (h := (HomologicalComplex.singleObjOpcyclesSelfIso
                    (ComplexShape.down ℕ) (0 : ℕ) M).inv))
  have hleft :
      HomologicalComplex.homologyMap
            ((HomologicalComplex.extendSingleIso
              ComplexShape.embeddingDownNat
              M
              (0 : ℕ) (0 : ℤ) rfl).hom) 0 ≫
          (HomologicalComplex.singleObjHomologySelfIso
            (ComplexShape.up ℤ) (0 : ℤ) M).hom =
        (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
            ((singleCpx₀).obj M)).homologyι 0) ≫ commonDesc := by
    -- Rewrite the source-side `H₀(single₀ M)` comparison through `homologyι`, then apply the
    -- established opcycles comparison for `extendSingleIso`.
    calc
    HomologicalComplex.homologyMap
          ((HomologicalComplex.extendSingleIso
            ComplexShape.embeddingDownNat
            M
            (0 : ℕ) (0 : ℤ) rfl).hom) 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.up ℤ) (0 : ℤ) M).hom =
      HomologicalComplex.homologyMap
          ((HomologicalComplex.extendSingleIso
            ComplexShape.embeddingDownNat
            M
            (0 : ℕ) (0 : ℤ) rfl).hom) 0 ≫
        ((singleCpxℤ₀).obj M).homologyι 0 ≫
        (HomologicalComplex.singleObjOpcyclesSelfIso
          (ComplexShape.up ℤ) (0 : ℤ) M).inv := by
            simp [HomologicalComplex.singleObjHomologySelfIso, Category.assoc]
    _ =
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
          ((singleCpx₀).obj M)).homologyι 0) ≫
        HomologicalComplex.opcyclesMap
          ((HomologicalComplex.extendSingleIso
            ComplexShape.embeddingDownNat
            M
            (0 : ℕ) (0 : ℤ) rfl).hom) 0 ≫
        (HomologicalComplex.singleObjOpcyclesSelfIso
          (ComplexShape.up ℤ) (0 : ℤ) M).inv := by
            simpa [Category.assoc] using
              (HomologicalComplex.homologyι_naturality_assoc
                ((HomologicalComplex.extendSingleIso
                  ComplexShape.embeddingDownNat
                  M
                  (0 : ℕ) (0 : ℤ) rfl).hom)
                (0 : ℤ)
                (h := (HomologicalComplex.singleObjOpcyclesSelfIso
                  (ComplexShape.up ℤ) (0 : ℤ) M).inv))
    _ =
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
          ((singleCpx₀).obj M)).homologyι 0) ≫ commonDesc := by
            simpa [Category.assoc] using
              congrArg
                (fun t ↦
                  (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
                      ((singleCpx₀).obj M)).homologyι 0) ≫ t)
                (HomologicalComplex.extendSingleIso_opcycles_self_comparison
                  (A := A) (M := M))
  have hright :
      e0 ≫
          ((singleCpx₀).obj M).homologyι 0 ≫
          (HomologicalComplex.singleObjOpcyclesSelfIso
            (ComplexShape.down ℕ) (0 : ℕ) M).inv =
        e0 ≫
          (HomologicalComplex.singleObjHomologySelfIso
            (ComplexShape.down ℕ) (0 : ℕ) M).hom := by
    -- Finally rewrite the target-side single-complex `H₀` identification back from `homologyι`.
    have hsingle :
        (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.down ℕ) (0 : ℕ) M).hom =
      ((singleCpx₀).obj M).homologyι 0 ≫
        (HomologicalComplex.singleObjOpcyclesSelfIso
          (ComplexShape.down ℕ) (0 : ℕ) M).inv := by
            simp [HomologicalComplex.singleObjHomologySelfIso]
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          e0 ≫ t)
        hsingle.symm
  have hfinal :
      HomologicalComplex.homologyMap
            ((HomologicalComplex.extendSingleIso
              ComplexShape.embeddingDownNat
              M
              (0 : ℕ) (0 : ℤ) rfl).hom) 0 ≫
          (HomologicalComplex.singleObjHomologySelfIso
            (ComplexShape.up ℤ) (0 : ℤ) M).hom =
        e0 ≫
          (HomologicalComplex.singleObjHomologySelfIso
            (ComplexShape.down ℕ) (0 : ℕ) M).hom :=
    hleft.trans (hdesc_transport.trans hright)
  simpa [e0, h0z] using hfinal

/-- Helper for Lemma 15.95.1: after moving the degree-zero fully faithful comparison for
`singleFunctor`, the `singleFunctorIsoCompQ` component contributes only the identity on zeroth
homology. -/
theorem DerivedCategory.homologyFunctor_map_singleFunctorIsoCompQ_inv_app_zero_eq_id
    (M : ModuleCat A) :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
        (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app M).inv) =
      𝟙 _ := by
  -- The comparison `singleFunctorIsoCompQ` is definitionally `Iso.refl`, so its inverse is the
  -- identity and the homology functor preserves that identity.
  change
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
        (𝟙 ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj M)) =
      𝟙 _
  simp

/-- Helper for Lemma 15.95.1: at degree `0`, the owner comparison
`singleFunctorCompHomologyFunctorIso` is exactly the `homologyFunctorFactors` leg followed by the
canonical single-complex homology identification. -/
theorem DerivedCategory.singleFunctorCompHomologyFunctorIso_app_zero_owner_formula
    (M : ModuleCat A) :
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) (0 : ℤ)).app M).hom =
      (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
        (𝟙 (((singleFunctors (ModuleCat A)).functor (0 : ℤ)).obj M)) ≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
        (((CochainComplex.singleFunctors (ModuleCat A)).functor (0 : ℤ)).obj M)) ≫
      (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.up ℤ) (0 : ℤ) M).hom := by
  -- Unfold the owner composite once; the `singleFunctorsPostcompQIso` degree-zero component is
  -- the identity, and the remaining factors are the explicit `H.map (𝟙)` leg, the
  -- `homologyFunctorFactors` comparison, and `singleObjHomologySelfIso`.
  simp [DerivedCategory.singleFunctorCompHomologyFunctorIso,
    DerivedCategory.singleFunctorsPostcompQIso_hom_app_zero_eq_id]
  let α :=
    ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
      (((CochainComplex.singleFunctors (ModuleCat A)).functor (0 : ℤ)).obj M))
  let β :=
    (HomologicalComplex.singleObjHomologySelfIso
      (ComplexShape.up ℤ) (0 : ℤ) M).hom
  -- The residual transport is `H^0` applied to the identity on the derived single object.
  have hmap :
      (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
          (𝟙 (((DerivedCategory.singleFunctors (ModuleCat A)).functor (0 : ℤ)).obj M)) =
        𝟙 _ := by
    simp
  -- Postcomposing the identity comparison with the two owner legs yields the desired formula.
  refine (congrArg (fun t ↦ t ≫ α ≫ β) hmap).trans ?_
  calc
    𝟙 _ ≫ α ≫ β = (𝟙 _ ≫ α) ≫ β := by simp
    _ = α ≫ β := by simp [α, β]

/-- Helper for Lemma 15.95.1: after unfolding the owner `singleFunctor` comparison on a
degree-zero single complex, the only residual map is the identity on derived homology between the
two `homologyFunctorFactors` legs. -/
theorem DerivedCategory.single0_h0_tail_owner_expansion
    (M : ModuleCat A) :
    ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).inv.app
        ((singleCpxℤ₀).obj M)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
        (𝟙 (((singleFunctors (ModuleCat A)).functor (0 : ℤ)).obj M)) ≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
        (((CochainComplex.singleFunctors (ModuleCat A)).functor (0 : ℤ)).obj M)) ≫
      (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.up ℤ) (0 : ℤ) M).hom =
    (HomologicalComplex.singleObjHomologySelfIso
      (ComplexShape.up ℤ) (0 : ℤ) M).hom := by
  -- The middle factor is `H^0` applied to the identity, so the composite is the usual
  -- `inv ≫ hom` cancellation for `homologyFunctorFactors`.
  simpa [Functor.map_id, Category.assoc] using
    (((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).app
      ((singleCpxℤ₀).obj M)).inv_hom_id_assoc
        ((HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.up ℤ) (0 : ℤ) M).hom))

/-- Helper for Lemma 15.95.1: on a degree-zero `ℤ`-indexed single complex, the residual derived
`H^0` tail through `homologyFunctorFactors` is exactly the canonical chain-level
`singleObjHomologySelfIso`. -/
theorem DerivedCategory.single0_h0_tail_eq_singleObjHomologySelfIso
    (M : ModuleCat A) :
    ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).inv.app
        ((singleCpxℤ₀).obj M)) ≫
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) (0 : ℤ)).app
        M).hom =
      (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.up ℤ) (0 : ℤ) M).hom := by
  -- Route correction: first expose the owner formula for
  -- `singleFunctorCompHomologyFunctorIso.app`; once the explicit `H.map (𝟙)` leg is visible, the
  -- remaining composite is exactly the existing `homologyFunctorFactors` cancellation.
  rw [DerivedCategory.singleFunctorCompHomologyFunctorIso_app_zero_owner_formula (A := A) M]
  simpa [Category.assoc] using
    DerivedCategory.single0_h0_tail_owner_expansion (A := A) M

/-- Helper for Lemma 15.95.1: the derived `H^0` tail attached to the extended degree-zero single
complex is the canonical chain-level `H_0(single₀ M) ≅ M` comparison after transporting back
along `extendHomologyIso`. -/
theorem derived_single0_h0_transport_eq_singleObjHomologySelfIso
    (M : ModuleCat A) :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
        (DerivedCategory.Q.map
          ((HomologicalComplex.extendSingleIso
            ComplexShape.embeddingDownNat
            M
            (0 : ℕ) (0 : ℤ) rfl).hom)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
        (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app M).inv) ≫
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) (0 : ℤ)).app
        M).hom =
      ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
        ((singleCpx₀).obj M)))) ≫
      (((singleCpx₀).obj M).extendHomologyIso ComplexShape.embeddingDownNat (by simp)).hom ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) (0 : ℕ) M).hom := by
  -- Route correction: isolate the degree-zero single-object tail first, then move the
  -- `Q.map extendSingleIso` factor across `homologyFunctorFactors`, and finally replace the
  -- chain-level tail by the owner `extendSingleIso` homology comparison.
  have htail :
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) (0 : ℤ)).app
          M).hom =
        ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
          ((singleCpxℤ₀).obj M)) ≫
        (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.up ℤ) (0 : ℤ) M).hom := by
    have hcancel :
        ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
            ((singleCpxℤ₀).obj M)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).inv.app
            ((singleCpxℤ₀).obj M)) ≫
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) (0 : ℤ)).app
            M).hom =
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) (0 : ℤ)).app
          M).hom := by
      simpa [Category.assoc] using
        (((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).app
          ((singleCpxℤ₀).obj M)).hom_inv_id_assoc
            (((DerivedCategory.singleFunctorCompHomologyFunctorIso
              (ModuleCat A) (0 : ℤ)).app M).hom))
    have htail' :
        ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
            ((singleCpxℤ₀).obj M)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).inv.app
            ((singleCpxℤ₀).obj M)) ≫
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) (0 : ℤ)).app
            M).hom =
        ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
          ((singleCpxℤ₀).obj M)) ≫
        (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.up ℤ) (0 : ℤ) M).hom := by
      rw [DerivedCategory.single0_h0_tail_eq_singleObjHomologySelfIso (A := A) M]
      simp
    exact hcancel.symm.trans htail'
  have hstep1 :
      (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
            (DerivedCategory.Q.map
              ((HomologicalComplex.extendSingleIso
                ComplexShape.embeddingDownNat
                M
                (0 : ℕ) (0 : ℤ) rfl).hom)) ≫
          (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
            (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app M).inv) ≫
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) (0 : ℤ)).app
            M).hom =
        (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
            (DerivedCategory.Q.map
              ((HomologicalComplex.extendSingleIso
                ComplexShape.embeddingDownNat
                M
                (0 : ℕ) (0 : ℤ) rfl).hom)) ≫
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) (0 : ℤ)).app
            M).hom := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
              (DerivedCategory.Q.map
                ((HomologicalComplex.extendSingleIso
                  ComplexShape.embeddingDownNat
                  M
                  (0 : ℕ) (0 : ℤ) rfl).hom)) ≫
            t ≫
            ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) (0 : ℤ)).app
              M).hom)
        (DerivedCategory.homologyFunctor_map_singleFunctorIsoCompQ_inv_app_zero_eq_id
          (A := A) M)
  have hstep2 :
      (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
            (DerivedCategory.Q.map
              ((HomologicalComplex.extendSingleIso
                ComplexShape.embeddingDownNat
                M
                (0 : ℕ) (0 : ℤ) rfl).hom)) ≫
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) (0 : ℤ)).app
            M).hom =
        (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
            (DerivedCategory.Q.map
              ((HomologicalComplex.extendSingleIso
                ComplexShape.embeddingDownNat
                M
                (0 : ℕ) (0 : ℤ) rfl).hom)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
            ((singleCpxℤ₀).obj M)) ≫
          (HomologicalComplex.singleObjHomologySelfIso
            (ComplexShape.up ℤ) (0 : ℤ) M).hom := by
    rw [htail]
    simp [Category.assoc]
  have hstep3 :
      (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
            (DerivedCategory.Q.map
              ((HomologicalComplex.extendSingleIso
                ComplexShape.embeddingDownNat
                M
                (0 : ℕ) (0 : ℤ) rfl).hom)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
            ((singleCpxℤ₀).obj M)) ≫
          (HomologicalComplex.singleObjHomologySelfIso
            (ComplexShape.up ℤ) (0 : ℤ) M).hom =
        ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
          (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
            ((singleCpx₀).obj M)))) ≫
          HomologicalComplex.homologyMap
            ((HomologicalComplex.extendSingleIso
              ComplexShape.embeddingDownNat
              M
              (0 : ℕ) (0 : ℤ) rfl).hom) 0 ≫
          (HomologicalComplex.singleObjHomologySelfIso
            (ComplexShape.up ℤ) (0 : ℤ) M).hom := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          t ≫
            (HomologicalComplex.singleObjHomologySelfIso
              (ComplexShape.up ℤ) (0 : ℤ) M).hom)
        (derived_completion_koszul_stage_h0_extend_single_naturality
          (A := A) (M := M)).symm
  have hstep4 :
      ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
          (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
            ((singleCpx₀).obj M)))) ≫
        HomologicalComplex.homologyMap
          ((HomologicalComplex.extendSingleIso
            ComplexShape.embeddingDownNat
            M
            (0 : ℕ) (0 : ℤ) rfl).hom) 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.up ℤ) (0 : ℤ) M).hom =
      ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
        (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
          ((singleCpx₀).obj M)))) ≫
        (((singleCpx₀).obj M).extendHomologyIso ComplexShape.embeddingDownNat (by simp)).hom ≫
        (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.down ℕ) (0 : ℕ) M).hom := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
            (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
              ((singleCpx₀).obj M)))) ≫ t)
        (HomologicalComplex.extendSingleIso_homology_self_comparison
          (A := A) (M := M))
  exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))

/-- Helper for Lemma 15.95.1: after transporting the target single complex back from `ℤ` to `ℕ`,
the `extendHomologyIso` comparison moves from the target side to the source side of the quotient
chain map. -/
theorem extend_homology_map_koszulPowerQuotientChainMap_transport
    (f : Fin r → A) (n : ℕ) :
    HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap
          (koszulPowerQuotientChainMap f n)
          ComplexShape.embeddingDownNat) 0 ≫
      (((singleCpx₀).obj (koszulPowerQuotientStage f n)).extendHomologyIso
        ComplexShape.embeddingDownNat (by simp)).hom ≫
      (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom =
    ((K^•[n](f)).extendHomologyIso ComplexShape.embeddingDownNat (by simp)).hom ≫
      HomologicalComplex.homologyMap (koszulPowerQuotientChainMap f n) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom := by
  -- Move the `extendHomologyIso` transport to the source complex, then postcompose by the
  -- canonical identification of `H₀(single₀(-))` with the underlying module.
  have htransport :=
    HomologicalComplex.extendHomologyIso_hom_naturality
      (φ := koszulPowerQuotientChainMap f n)
      (e := ComplexShape.embeddingDownNat)
      (j := (0 : ℕ))
      (j' := (0 : ℤ))
      (hj' := rfl)
  exact
    (congrArg
      (fun t ↦
        t ≫
          (HomologicalComplex.singleObjHomologySelfIso
            (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom)
      htransport).trans (by simp [Category.assoc])

/-- Helper for Lemma 15.95.1: the quotient chain map into the degree-zero single complex induces
the canonical quotient map on zeroth homology. -/
theorem homology_map_koszulPowerQuotientChainMap_eq_zero_homology_to_quotient
    (f : Fin r → A) (n : ℕ) :
    HomologicalComplex.homologyMap (koszulPowerQuotientChainMap f n) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom =
    koszulPowerZeroHomologyToQuotient f n := by
  -- Rewrite the target `H₀(single₀ M)` comparison through opcycles, then descend the degree-zero
  -- component of `koszulPowerQuotientChainMap`.
  have hf_zero :
      (koszulPowerQuotientChainMap f n).f 0 =
        koszul_power_zero_quotient_map f n := by
    simpa [koszulPowerQuotientChainMap] using
      (ChainComplex.toSingle₀Equiv_symm_apply_f_zero
        (C := K^•[n](f))
        (X := koszulPowerQuotientStage f n)
        (f := koszul_power_zero_quotient_map f n)
        (hf := koszul_power_zero_quotient_map_comp_d_eq_zero f n))
  have hcomponent :
      (koszulPowerQuotientChainMap f n).f 0 ≫
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom =
        koszul_power_zero_quotient_map f n := by
    simpa [ChainComplex.single₀ObjXSelf, hf_zero]
  have hopcycles :
      HomologicalComplex.opcyclesMap (koszulPowerQuotientChainMap f n) 0 ≫
          (HomologicalComplex.singleObjOpcyclesSelfIso
            (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).inv =
        (K^•[n](f)).descOpcycles
          ((koszulPowerQuotientChainMap f n).f 0 ≫
            (HomologicalComplex.singleObjXSelf
              (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom)
          1 (by simp) (by
            simpa [Category.assoc, hcomponent] using
              koszul_power_zero_quotient_map_comp_d_eq_zero (A := A) (f := f) (n := n)) := by
    calc
      HomologicalComplex.opcyclesMap (koszulPowerQuotientChainMap f n) 0 ≫
          (HomologicalComplex.singleObjOpcyclesSelfIso
            (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).inv =
      HomologicalComplex.opcyclesMap (koszulPowerQuotientChainMap f n) 0 ≫
          ((singleCpx₀).obj (koszulPowerQuotientStage f n)).descOpcycles
            (HomologicalComplex.singleObjXSelf
              (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom
            1 (by simp)
            (single0_objXSelf_comp_d_eq_zero (A := A) (koszulPowerQuotientStage f n)) := by
              rw [single0_opcycles_self_inv_eq_descOpcycles]
      _ =
        (K^•[n](f)).descOpcycles
          ((koszulPowerQuotientChainMap f n).f 0 ≫
            (HomologicalComplex.singleObjXSelf
              (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom)
          1 (by simp) (by
            simpa [Category.assoc, hcomponent] using
              koszul_power_zero_quotient_map_comp_d_eq_zero (A := A) (f := f) (n := n)) := by
              simpa [Category.assoc] using
                (HomologicalComplex.opcyclesMap_comp_descOpcycles
                  (K := K^•[n](f))
                  (L := (singleCpx₀).obj (koszulPowerQuotientStage f n))
                  (φ := koszulPowerQuotientChainMap f n)
                  (i := (0 : ℕ))
                  (k := (HomologicalComplex.singleObjXSelf
                    (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom)
                  (j := 1)
                  (hj := by simp)
                  (hk := single0_objXSelf_comp_d_eq_zero (A := A) (koszulPowerQuotientStage f n)))
  have hdesc :
      (K^•[n](f)).descOpcycles
          ((koszulPowerQuotientChainMap f n).f 0 ≫
            (HomologicalComplex.singleObjXSelf
              (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom)
          1 (by simp) (by
            simpa [Category.assoc, hcomponent] using
              koszul_power_zero_quotient_map_comp_d_eq_zero (A := A) (f := f) (n := n)) =
        (K^•[n](f)).descOpcycles
          (koszul_power_zero_quotient_map f n)
          1 (by simp) (koszul_power_zero_quotient_map_comp_d_eq_zero f n) := by
    -- Descended opcycle maps are also determined by their composites with `pOpcycles`.
    apply (cancel_epi ((K^•[n](f)).pOpcycles 0)).1
    calc
      (K^•[n](f)).pOpcycles 0 ≫
          (K^•[n](f)).descOpcycles
            ((koszulPowerQuotientChainMap f n).f 0 ≫
              (HomologicalComplex.singleObjXSelf
                (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom)
            1 (by simp) (by
              simpa [Category.assoc, hcomponent] using
                koszul_power_zero_quotient_map_comp_d_eq_zero (A := A) (f := f) (n := n)) =
        (koszulPowerQuotientChainMap f n).f 0 ≫
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom := by
              simpa using
                (HomologicalComplex.p_descOpcycles
                  (K := K^•[n](f))
                  (i := (0 : ℕ))
                  (k := (koszulPowerQuotientChainMap f n).f 0 ≫
                    (HomologicalComplex.singleObjXSelf
                      (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom)
                  (j := 1)
                  (hj := by simp)
                  (hk := by
                    simpa [Category.assoc, hcomponent] using
                      koszul_power_zero_quotient_map_comp_d_eq_zero (A := A) (f := f) (n := n)))
      _ = koszul_power_zero_quotient_map f n := hcomponent
      _ =
        (K^•[n](f)).pOpcycles 0 ≫
          (K^•[n](f)).descOpcycles
            (koszul_power_zero_quotient_map f n)
            1 (by simp) (koszul_power_zero_quotient_map_comp_d_eq_zero f n) := by
              symm
              simpa using
                (HomologicalComplex.p_descOpcycles
                  (K := K^•[n](f))
                  (i := (0 : ℕ))
                  (k := koszul_power_zero_quotient_map f n)
                  (j := 1)
                  (hj := by simp)
                  (hk := koszul_power_zero_quotient_map_comp_d_eq_zero f n))
  calc
    HomologicalComplex.homologyMap (koszulPowerQuotientChainMap f n) 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom =
      HomologicalComplex.homologyMap (koszulPowerQuotientChainMap f n) 0 ≫
        ((singleCpx₀).obj (koszulPowerQuotientStage f n)).homologyι 0 ≫
        (HomologicalComplex.singleObjOpcyclesSelfIso
          (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).inv := by
            simp [Category.assoc]
    _ =
      (K^•[n](f)).homologyι 0 ≫
        HomologicalComplex.opcyclesMap (koszulPowerQuotientChainMap f n) 0 ≫
        (HomologicalComplex.singleObjOpcyclesSelfIso
          (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).inv := by
            rw [HomologicalComplex.homologyι_naturality_assoc]
    _ =
      (K^•[n](f)).homologyι 0 ≫
        (K^•[n](f)).descOpcycles
          ((koszulPowerQuotientChainMap f n).f 0 ≫
            (HomologicalComplex.singleObjXSelf
              (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom)
          1 (by simp) (by
            simpa [Category.assoc, hcomponent] using
              koszul_power_zero_quotient_map_comp_d_eq_zero (A := A) (f := f) (n := n)) := by
            simpa [Category.assoc] using
              congrArg (fun t ↦ (K^•[n](f)).homologyι 0 ≫ t) hopcycles
    _ =
      (K^•[n](f)).homologyι 0 ≫
        (K^•[n](f)).descOpcycles
          (koszul_power_zero_quotient_map f n)
          1 (by simp) (koszul_power_zero_quotient_map_comp_d_eq_zero f n) := by
            simpa [Category.assoc] using
              congrArg (fun t ↦ (K^•[n](f)).homologyι 0 ≫ t) hdesc
    _ = koszulPowerZeroHomologyToQuotient f n := by
      -- The remaining term is the owner definition of `koszulPowerZeroHomologyToQuotient`.
      simp [koszulPowerZeroHomologyToQuotient]

/-- Helper for Lemma 15.95.1: after transporting the target single complex back from `ℤ` to `ℕ`,
the extended quotient chain map induces the canonical zeroth-homology quotient map. -/
theorem extend_homology_map_koszulPowerQuotientChainMap_eq
    (f : Fin r → A) (n : ℕ) :
    HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap
          (koszulPowerQuotientChainMap f n)
          ComplexShape.embeddingDownNat) 0 ≫
      (((singleCpx₀).obj (koszulPowerQuotientStage f n)).extendHomologyIso
        ComplexShape.embeddingDownNat (by simp)).hom ≫
      (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom =
    ((K^•[n](f)).extendHomologyIso ComplexShape.embeddingDownNat (by simp)).hom ≫
      koszulPowerZeroHomologyToQuotient f n := by
  have hjK : ComplexShape.embeddingDownNat.f (0 : ℕ) = (0 : ℤ) := rfl
  let eK :
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj (K^•[n](f))).homology 0) ⟶
        ((K^•[n](f)).homology 0) :=
    ((K^•[n](f)).extendHomologyIso ComplexShape.embeddingDownNat hjK).hom
  have htransport :
      HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap
            (koszulPowerQuotientChainMap f n)
            ComplexShape.embeddingDownNat) 0 ≫
        (((singleCpx₀).obj (koszulPowerQuotientStage f n)).extendHomologyIso
          ComplexShape.embeddingDownNat (by simp)).hom ≫
        (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom =
      eK ≫
        (HomologicalComplex.homologyMap (koszulPowerQuotientChainMap f n) 0 ≫
          (HomologicalComplex.singleObjHomologySelfIso
            (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom) := by
    -- First isolate the transport from `ℤ` back to `ℕ`.
    simpa [eK, Category.assoc] using
      extend_homology_map_koszulPowerQuotientChainMap_transport (A := A) (f := f) (n := n)
  have hquot :
      eK ≫
        (HomologicalComplex.homologyMap (koszulPowerQuotientChainMap f n) 0 ≫
          (HomologicalComplex.singleObjHomologySelfIso
            (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom) =
      eK ≫ koszulPowerZeroHomologyToQuotient f n := by
    -- Then replace the remaining chain-level homology map by the canonical quotient map.
    simpa [eK, Category.assoc] using
      congrArg (fun t ↦ eK ≫ t)
        (homology_map_koszulPowerQuotientChainMap_eq_zero_homology_to_quotient
          (A := A) (f := f) (n := n))
  exact (htransport.trans hquot).trans (by simp [eK])

/-- Helper for Lemma 15.95.1: after passing to degree-zero homology, the stagewise comparison
recovers the canonical zeroth-homology quotient map. -/
theorem derived_completion_koszul_to_power_quotient_stage_h0_eq
    (f : Fin r → A) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
        (derivedCompletionKoszulToPowerQuotientStage f n) ≫
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) (0 : ℤ)).app
        (koszulPowerQuotientStage f n)).hom =
      ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
        (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj (K^•[n](f))))) ≫
      ((K^•[n](f)).extendHomologyIso ComplexShape.embeddingDownNat (by simp)).hom ≫
      koszulPowerZeroHomologyToQuotient f n := by
  -- Route correction: the source-side `Q.map` factor is isolated by
  -- `derived_completion_koszul_stage_h0_source_naturality`. The remaining transport now splits
  -- into the corrected single-object bridge
  -- `derived_single0_h0_transport_eq_singleObjHomologySelfIso` and the chain-level rewrite
  -- `extend_homology_map_koszulPowerQuotientChainMap_eq`.
  have hsource := derived_completion_koszul_stage_h0_source_naturality f n
  have htransport :=
    derived_single0_h0_transport_eq_singleObjHomologySelfIso
      (A := A) (M := koszulPowerQuotientStage f n)
  have hchain :=
    extend_homology_map_koszulPowerQuotientChainMap_eq (A := A) (f := f) (n := n)
  let h0z : ComplexShape.embeddingDownNat.f (0 : ℕ) = (0 : ℤ) := rfl
  -- First expand the stage map and replace the quotient-side derived tail by the isolated
  -- single-object transport comparison.
  have hstage :
      (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
          (derivedCompletionKoszulToPowerQuotientStage f n) ≫
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) (0 : ℤ)).app
          (koszulPowerQuotientStage f n)).hom =
      (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
          (DerivedCategory.Q.map
            (HomologicalComplex.extendMap
              (koszulPowerQuotientChainMap f n)
              ComplexShape.embeddingDownNat)) ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
          (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
            ((singleCpx₀).obj (koszulPowerQuotientStage f n))))) ≫
        (((singleCpx₀).obj (koszulPowerQuotientStage f n)).extendHomologyIso
          ComplexShape.embeddingDownNat h0z).hom ≫
        (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom := by
    simp only [derivedCompletionKoszulToPowerQuotientStage, Functor.map_comp, Category.assoc]
    exact congrArg
      (fun t ↦
        (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
            (DerivedCategory.Q.map
              (HomologicalComplex.extendMap
                (koszulPowerQuotientChainMap f n)
                ComplexShape.embeddingDownNat)) ≫
          t)
      htransport
  -- Next move the source-side `Q.map` factor across `homologyFunctorFactors`.
  have hsource' :
      (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
          (DerivedCategory.Q.map
            (HomologicalComplex.extendMap
              (koszulPowerQuotientChainMap f n)
              ComplexShape.embeddingDownNat)) ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
          (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
            ((singleCpx₀).obj (koszulPowerQuotientStage f n))))) ≫
        (((singleCpx₀).obj (koszulPowerQuotientStage f n)).extendHomologyIso
          ComplexShape.embeddingDownNat h0z).hom ≫
        (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom =
      ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
        (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj (K^•[n](f))))) ≫
      HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap
          (koszulPowerQuotientChainMap f n)
          ComplexShape.embeddingDownNat) 0 ≫
      (((singleCpx₀).obj (koszulPowerQuotientStage f n)).extendHomologyIso
        ComplexShape.embeddingDownNat h0z).hom ≫
      (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          t ≫
            (((singleCpx₀).obj (koszulPowerQuotientStage f n)).extendHomologyIso
              ComplexShape.embeddingDownNat h0z).hom ≫
            (HomologicalComplex.singleObjHomologySelfIso
              (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom)
        hsource
  -- Finally replace the remaining chain-level composite by the quotient map on zeroth homology.
  have hchain' :
      ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
        (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj (K^•[n](f))))) ≫
      HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap
          (koszulPowerQuotientChainMap f n)
          ComplexShape.embeddingDownNat) 0 ≫
      (((singleCpx₀).obj (koszulPowerQuotientStage f n)).extendHomologyIso
        ComplexShape.embeddingDownNat h0z).hom ≫
      (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.down ℕ) (0 : ℕ) (koszulPowerQuotientStage f n)).hom =
      ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
        (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj (K^•[n](f))))) ≫
      ((K^•[n](f)).extendHomologyIso ComplexShape.embeddingDownNat h0z).hom ≫
      koszulPowerZeroHomologyToQuotient f n := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          ((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
            (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj (K^•[n](f))))) ≫ t)
        hchain
  exact
    hstage.trans <|
      hsource'.trans <|
        hchain'.trans <|
          by simp

/-- Helper for Lemma 15.95.1: the corrected stagewise degree-zero comparison is an isomorphism.
After rewriting through the owner-level transport identifications, it factors through the
canonical zeroth-homology quotient isomorphism from Situation `15.92.15`. -/
theorem derived_completion_koszul_to_power_quotient_stage_h0_isIso
    (f : Fin r → A) (n : ℕ) :
    IsIso
      ((DerivedCategory.homologyFunctor (ModuleCat A) 0).map
        (derivedCompletionKoszulToPowerQuotientStage f n)) := by
  letI :
      IsIso
        (((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) (0 : ℤ)).app
          (koszulPowerQuotientStage f n)).hom) := by
    infer_instance
  letI : IsIso (koszulPowerZeroHomologyToQuotient f n) :=
    koszulPowerZeroHomologyToQuotient_isIso f n
  let h0z : ComplexShape.embeddingDownNat.f (0 : ℕ) = (0 : ℤ) := rfl
  have hcomp :
      IsIso
        ((DerivedCategory.homologyFunctor (ModuleCat A) 0).map
            (derivedCompletionKoszulToPowerQuotientStage f n) ≫
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) (0 : ℤ)).app
            (koszulPowerQuotientStage f n)).hom) := by
    -- Rewrite the repaired degree-zero comparison into the composite of the standard source
    -- transport isomorphisms and the canonical quotient comparison.
    rw [derived_completion_koszul_to_power_quotient_stage_h0_eq (A := A) (f := f) (n := n)]
    have htransport :
        IsIso
          (((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
              (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
                (K^•[n](f))))) ≫
            ((K^•[n](f)).extendHomologyIso ComplexShape.embeddingDownNat h0z).hom) := by
      infer_instance
    letI : IsIso
        ((((DerivedCategory.homologyFunctorFactors (ModuleCat A) 0).hom.app
              (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
                (K^•[n](f))))) ≫
            ((K^•[n](f)).extendHomologyIso ComplexShape.embeddingDownNat h0z).hom) ≫
          koszulPowerZeroHomologyToQuotient f n) := by
      infer_instance
    simpa [Category.assoc]
  -- Cancel the target-side degree-zero single-functor comparison to recover the original stage
  -- map.
  exact
    IsIso.of_isIso_comp_right
      ((DerivedCategory.homologyFunctor (ModuleCat A) 0).map
        (derivedCompletionKoszulToPowerQuotientStage f n))
      (((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) (0 : ℤ)).app
        (koszulPowerQuotientStage f n)).hom)

/-- Helper for Lemma 15.95.1: extending a degree-zero single-complex map from `ℕ` to `ℤ`
commutes with the canonical `extendSingleIso` identification. -/
theorem extend_single0_map_comp_extendSingleIso_hom
    {M N : ModuleCat A} (g : M ⟶ N) :
    HomologicalComplex.extendMap ((singleCpx₀).map g) ComplexShape.embeddingDownNat ≫
        (HomologicalComplex.extendSingleIso
          ComplexShape.embeddingDownNat N (0 : ℕ) (0 : ℤ) rfl).hom =
      (HomologicalComplex.extendSingleIso
        ComplexShape.embeddingDownNat M (0 : ℕ) (0 : ℤ) rfl).hom ≫
        (singleCpxℤ₀).map g := by
  -- Compare both chain maps degreewise: all components vanish away from degree `0`, and the
  -- remaining degree-zero component is exactly `g`.
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst hi
    -- In degree `0`, both sides are the canonical single-complex realization of `g`.
    simp [HomologicalComplex.comp_f,
      HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := 0) (i' := 0)
        (by simp),
      HomologicalComplex.extendSingleIso_hom_f (e := ComplexShape.embeddingDownNat)
        (X := N) (i := 0) (i' := 0) (h := rfl),
      HomologicalComplex.extendSingleIso_hom_f (e := ComplexShape.embeddingDownNat)
        (X := M) (i := 0) (i' := 0) (h := rfl),
      HomologicalComplex.single_map_f_self, Category.assoc]
  · by_cases hpre : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = i
    · obtain ⟨j, rfl⟩ := hpre
      cases j with
      | zero =>
          contradiction
      | succ j =>
          -- Away from degree `0`, both sides land in the zero object of the target single complex.
          exact
            (HomologicalComplex.isZero_single_obj_X
              (ComplexShape.up ℤ) (0 : ℤ) N (-((Nat.succ j : ℕ) : ℤ)) (by omega)).eq_of_tgt _ _
    · exact (((singleCpx₀).obj M).isZero_extend_X
        ComplexShape.embeddingDownNat i (fun j hij ↦ hpre ⟨j, hij⟩)).eq_of_src _ _

/-- Helper for Lemma 15.95.1: after passing to `D(A)`, the quotient transition map still commutes
with the `extendSingleIso` transport and the canonical `singleFunctorIsoCompQ` bridge. -/
theorem derived_completion_power_quotient_transport_naturality
    (f : Fin r → A) (n : ℕ) :
    DerivedCategory.Q.map
        (HomologicalComplex.extendMap
          ((singleCpx₀).map (koszulPowerQuotientStep f n))
          ComplexShape.embeddingDownNat) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.extendSingleIso
          ComplexShape.embeddingDownNat
          (koszulPowerQuotientStage f n)
          (0 : ℕ) (0 : ℤ) rfl).hom) ≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
        (koszulPowerQuotientStage f n)).inv =
    DerivedCategory.Q.map
        ((HomologicalComplex.extendSingleIso
          ComplexShape.embeddingDownNat
          (koszulPowerQuotientStage f (n + 1))
          (0 : ℕ) (0 : ℤ) rfl).hom) ≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
        (koszulPowerQuotientStage f (n + 1))).inv ≫
      (single0).map (koszulPowerQuotientStep f n) := by
  -- First pass the chain-level `extendSingleIso` compatibility through `Q`.
  have htransport :
      DerivedCategory.Q.map
          (HomologicalComplex.extendMap
            ((singleCpx₀).map (koszulPowerQuotientStep f n))
            ComplexShape.embeddingDownNat) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.extendSingleIso
            ComplexShape.embeddingDownNat
            (koszulPowerQuotientStage f n)
            (0 : ℕ) (0 : ℤ) rfl).hom) =
      DerivedCategory.Q.map
          ((HomologicalComplex.extendSingleIso
            ComplexShape.embeddingDownNat
            (koszulPowerQuotientStage f (n + 1))
            (0 : ℕ) (0 : ℤ) rfl).hom) ≫
        DerivedCategory.Q.map
          ((singleCpxℤ₀).map (koszulPowerQuotientStep f n)) := by
    simpa [Functor.map_comp] using
      congrArg DerivedCategory.Q.map
        (extend_single0_map_comp_extendSingleIso_hom
          (g := koszulPowerQuotientStep f n))
  -- Then rewrite the remaining term by naturality of the canonical bridge
  -- `singleFunctorIsoCompQ.inv`.
  have hsingle :
      DerivedCategory.Q.map
          ((singleCpxℤ₀).map (koszulPowerQuotientStep f n)) ≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
          (koszulPowerQuotientStage f n)).inv =
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
          (koszulPowerQuotientStage f (n + 1))).inv ≫
        (single0).map (koszulPowerQuotientStep f n) := by
    simpa using
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).inv.naturality
        (koszulPowerQuotientStep f n))
  calc
    DerivedCategory.Q.map
        (HomologicalComplex.extendMap
          ((singleCpx₀).map (koszulPowerQuotientStep f n))
          ComplexShape.embeddingDownNat) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.extendSingleIso
          ComplexShape.embeddingDownNat
          (koszulPowerQuotientStage f n)
          (0 : ℕ) (0 : ℤ) rfl).hom) ≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
        (koszulPowerQuotientStage f n)).inv =
    (DerivedCategory.Q.map
        (HomologicalComplex.extendMap
          ((singleCpx₀).map (koszulPowerQuotientStep f n))
          ComplexShape.embeddingDownNat) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.extendSingleIso
          ComplexShape.embeddingDownNat
          (koszulPowerQuotientStage f n)
          (0 : ℕ) (0 : ℤ) rfl).hom)) ≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
        (koszulPowerQuotientStage f n)).inv := by
          simp [Category.assoc]
    _ =
      (DerivedCategory.Q.map
          ((HomologicalComplex.extendSingleIso
            ComplexShape.embeddingDownNat
            (koszulPowerQuotientStage f (n + 1))
            (0 : ℕ) (0 : ℤ) rfl).hom) ≫
        DerivedCategory.Q.map
          ((singleCpxℤ₀).map (koszulPowerQuotientStep f n))) ≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
          (koszulPowerQuotientStage f n)).inv := by
            rw [htransport]
    _ =
      DerivedCategory.Q.map
          ((HomologicalComplex.extendSingleIso
            ComplexShape.embeddingDownNat
            (koszulPowerQuotientStage f (n + 1))
            (0 : ℕ) (0 : ℤ) rfl).hom) ≫
        (DerivedCategory.Q.map
            ((singleCpxℤ₀).map (koszulPowerQuotientStep f n)) ≫
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
            (koszulPowerQuotientStage f n)).inv) := by
              simp [Category.assoc]
    _ =
      DerivedCategory.Q.map
          ((HomologicalComplex.extendSingleIso
            ComplexShape.embeddingDownNat
            (koszulPowerQuotientStage f (n + 1))
            (0 : ℕ) (0 : ℤ) rfl).hom) ≫
        (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
            (koszulPowerQuotientStage f (n + 1))).inv ≫
          (single0).map (koszulPowerQuotientStep f n)) := by
              rw [hsingle]
              rfl
    _ =
      DerivedCategory.Q.map
          ((HomologicalComplex.extendSingleIso
            ComplexShape.embeddingDownNat
            (koszulPowerQuotientStage f (n + 1))
            (0 : ℕ) (0 : ℤ) rfl).hom) ≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
          (koszulPowerQuotientStage f (n + 1))).inv ≫
        (single0).map (koszulPowerQuotientStep f n) := by
              rfl

/-- Helper for Lemma 15.95.1: the stagewise derived comparison maps are compatible with the
successor transitions in the two inverse systems. -/
theorem derivedCompletionKoszulToPowerQuotientStage_naturality
    (f : Fin r → A) (n : ℕ) :
    (derivedCompletionKoszulPowersDerivedInverseSystem f).map (homOfLE (Nat.le_succ n)).op ≫
        derivedCompletionKoszulToPowerQuotientStage f n =
      derivedCompletionKoszulToPowerQuotientStage f (n + 1) ≫
        (derivedCompletionPowerQuotientDerivedInverseSystem f).map
          (homOfLE (Nat.le_succ n)).op := by
  -- Rewrite the source step through the chain-level naturality square after extending and
  -- localizing.
  have hsource :
      DerivedCategory.Q.map
          (HomologicalComplex.extendMap
            (koszulPowerStep f n)
            ComplexShape.embeddingDownNat) ≫
        DerivedCategory.Q.map
          (HomologicalComplex.extendMap
            (koszulPowerQuotientChainMap f n)
            ComplexShape.embeddingDownNat) =
      DerivedCategory.Q.map
          (HomologicalComplex.extendMap
            (koszulPowerQuotientChainMap f (n + 1))
            ComplexShape.embeddingDownNat) ≫
        DerivedCategory.Q.map
          (HomologicalComplex.extendMap
            ((singleCpx₀).map (koszulPowerQuotientStep f n))
            ComplexShape.embeddingDownNat) := by
    simpa [Functor.map_comp, HomologicalComplex.extendMap_comp] using
      congrArg DerivedCategory.Q.map
        (congrArg
          (fun k ↦ HomologicalComplex.extendMap k ComplexShape.embeddingDownNat)
          (koszulPowerQuotientChainMap_naturality f n))
  have hsource_post :
      DerivedCategory.Q.map
          (HomologicalComplex.extendMap
            (koszulPowerStep f n)
            ComplexShape.embeddingDownNat) ≫
        DerivedCategory.Q.map
          (HomologicalComplex.extendMap
            (koszulPowerQuotientChainMap f n)
            ComplexShape.embeddingDownNat) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.extendSingleIso
            ComplexShape.embeddingDownNat
            (koszulPowerQuotientStage f n)
            (0 : ℕ) (0 : ℤ) rfl).hom) ≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
          (koszulPowerQuotientStage f n)).inv =
      (DerivedCategory.Q.map
          (HomologicalComplex.extendMap
            (koszulPowerQuotientChainMap f (n + 1))
            ComplexShape.embeddingDownNat) ≫
        DerivedCategory.Q.map
          (HomologicalComplex.extendMap
            ((singleCpx₀).map (koszulPowerQuotientStep f n))
            ComplexShape.embeddingDownNat)) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.extendSingleIso
            ComplexShape.embeddingDownNat
            (koszulPowerQuotientStage f n)
            (0 : ℕ) (0 : ℤ) rfl).hom) ≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
          (koszulPowerQuotientStage f n)).inv := by
    -- Postcompose the chain-level source square by the fixed quotient-side tail.
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          t ≫
            DerivedCategory.Q.map
              ((HomologicalComplex.extendSingleIso
                ComplexShape.embeddingDownNat
                (koszulPowerQuotientStage f n)
                (0 : ℕ) (0 : ℤ) rfl).hom) ≫
              ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
                (koszulPowerQuotientStage f n)).inv)
        hsource
  have htransport_post :
      (DerivedCategory.Q.map
          (HomologicalComplex.extendMap
            (koszulPowerQuotientChainMap f (n + 1))
            ComplexShape.embeddingDownNat) ≫
        DerivedCategory.Q.map
          (HomologicalComplex.extendMap
            ((singleCpx₀).map (koszulPowerQuotientStep f n))
            ComplexShape.embeddingDownNat)) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.extendSingleIso
            ComplexShape.embeddingDownNat
            (koszulPowerQuotientStage f n)
            (0 : ℕ) (0 : ℤ) rfl).hom) ≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
          (koszulPowerQuotientStage f n)).inv =
      DerivedCategory.Q.map
          (HomologicalComplex.extendMap
            (koszulPowerQuotientChainMap f (n + 1))
            ComplexShape.embeddingDownNat) ≫
        (DerivedCategory.Q.map
            ((HomologicalComplex.extendSingleIso
              ComplexShape.embeddingDownNat
              (koszulPowerQuotientStage f (n + 1))
              (0 : ℕ) (0 : ℤ) rfl).hom) ≫
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
            (koszulPowerQuotientStage f (n + 1))).inv) ≫
        (single0).map (koszulPowerQuotientStep f n) := by
    -- Precompose the quotient-side transport identity by the already-fixed source comparison.
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          DerivedCategory.Q.map
              (HomologicalComplex.extendMap
                (koszulPowerQuotientChainMap f (n + 1))
                ComplexShape.embeddingDownNat) ≫
            t)
        (derived_completion_power_quotient_transport_naturality f n)
  -- The quotient-side transport square was isolated above, so the final comparison is just a
  -- reassembly of these two components.
  have hstart :
      (derivedCompletionKoszulPowersDerivedInverseSystem f).map (homOfLE (Nat.le_succ n)).op ≫
          derivedCompletionKoszulToPowerQuotientStage f n =
        DerivedCategory.Q.map
            (HomologicalComplex.extendMap
              (koszulPowerStep f n)
              ComplexShape.embeddingDownNat) ≫
          (DerivedCategory.Q.map
              (HomologicalComplex.extendMap
                (koszulPowerQuotientChainMap f n)
                ComplexShape.embeddingDownNat) ≫
            DerivedCategory.Q.map
              ((HomologicalComplex.extendSingleIso
                ComplexShape.embeddingDownNat
                (koszulPowerQuotientStage f n)
                (0 : ℕ) (0 : ℤ) rfl).hom) ≫
            ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
              (koszulPowerQuotientStage f n)).inv) := by
    simp [derivedCompletionKoszulPowersDerivedInverseSystem,
      derivedCompletionKoszulToPowerQuotientStage, Category.assoc,
      Functor.ofOpSequence_map_homOfLE_succ]
  have hend :
      DerivedCategory.Q.map
          (HomologicalComplex.extendMap
            (koszulPowerStep f n)
            ComplexShape.embeddingDownNat) ≫
        (DerivedCategory.Q.map
            (HomologicalComplex.extendMap
              (koszulPowerQuotientChainMap f n)
              ComplexShape.embeddingDownNat) ≫
          DerivedCategory.Q.map
            ((HomologicalComplex.extendSingleIso
              ComplexShape.embeddingDownNat
              (koszulPowerQuotientStage f n)
              (0 : ℕ) (0 : ℤ) rfl).hom) ≫
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
            (koszulPowerQuotientStage f n)).inv) =
        derivedCompletionKoszulToPowerQuotientStage f (n + 1) ≫
          (derivedCompletionPowerQuotientDerivedInverseSystem f).map
            (homOfLE (Nat.le_succ n)).op := by
    rw [hsource_post]
    rw [htransport_post]
    simp [derivedCompletionKoszulToPowerQuotientStage,
      derivedCompletionPowerQuotientDerivedInverseSystem, Category.assoc,
      Functor.ofOpSequence_map_homOfLE_succ]
  exact hstart.trans hend

/-- Helper for Lemma 15.95.1: the powered Koszul-to-quotient comparison is a morphism of the two
sequential inverse systems in `D(A)`. -/
abbrev derivedCompletionKoszulToPowerQuotientNatTrans
    (f : Fin r → A) :
    derivedCompletionKoszulPowersDerivedInverseSystem f ⟶
      derivedCompletionPowerQuotientDerivedInverseSystem f :=
  NatTrans.ofOpSequence
    (fun n ↦ derivedCompletionKoszulToPowerQuotientStage f n)
    (fun n ↦ by
      simpa using derivedCompletionKoszulToPowerQuotientStage_naturality f n)

/-- Helper for Lemma 15.95.1: a pro-isomorphism representative induces an isomorphism of the
associated sequential pro-objects. -/
theorem isIso_toProObjectHom_of_isProIsomorphism
    {X Y : ℕᵒᵖ ⥤ DMod} (a : SequentialProObjectMorphismRep X Y)
    (ha : a.IsProIsomorphism) :
    IsIso a.toProObjectHom := by
  -- Evaluate on every test object and use the Chapter 4 bridge from pro-isomorphisms to
  -- Hom-colimit bijectivity.
  letI : ∀ Z : DMod, IsIso (a.toProObjectHom.app Z) := fun Z ↦
    (CategoryTheory.isIso_iff_bijective (a.toProObjectHom.app Z)).2
      (SequentialProObjectMorphismRep.isProIsomorphism_toProObjectHom_app_bijective ha Z)
  exact NatIso.isIso_of_isIso_app a.toProObjectHom

/-- Helper for Lemma 15.95.1: a natural isomorphism of sequential inverse systems is already a
pro-isomorphism in the Chapter 4 representative calculus. -/
theorem SequentialProObjectMorphismRep.ofNatTrans_isProIsomorphism_of_natIso
    {C : Type*} [Category C] {X Y : ℕᵒᵖ ⥤ C} (e : X ≅ Y) :
    (SequentialProObjectMorphismRep.ofNatTrans e.hom).IsProIsomorphism := by
  -- Use the inverse natural isomorphism as the reverse representative.
  refine ⟨SequentialProObjectMorphismRep.ofNatTrans e.inv, ?_, ?_⟩
  · -- With identity reindexing on both sides, the common-refinement equations reduce to the
    -- component identity `e.hom.app n ≫ e.inv.app n = 𝟙`.
    refine ⟨OrderHom.id, fun n ↦ le_rfl, fun n ↦ le_rfl, ?_⟩
    intro n
    change
      X.map (homOfLE (le_rfl : n ≤ n)).op ≫
          (e.hom.app (Opposite.op n) ≫ e.inv.app (Opposite.op n)) =
        X.map (homOfLE (le_rfl : n ≤ n)).op ≫ 𝟙 (X.obj (Opposite.op n))
    simpa [Category.assoc] using
      congrArg (fun t ↦ X.map (homOfLE (le_rfl : n ≤ n)).op ≫ t) (e.hom_inv_id_app (Opposite.op n))
  · -- The symmetric common-refinement equation is the other component identity of the natural
    -- isomorphism.
    refine ⟨OrderHom.id, fun n ↦ le_rfl, fun n ↦ le_rfl, ?_⟩
    intro n
    change
      Y.map (homOfLE (le_rfl : n ≤ n)).op ≫
          (e.inv.app (Opposite.op n) ≫ e.hom.app (Opposite.op n)) =
        Y.map (homOfLE (le_rfl : n ≤ n)).op ≫ 𝟙 (Y.obj (Opposite.op n))
    simpa [Category.assoc] using
      congrArg (fun t ↦ Y.map (homOfLE (le_rfl : n ≤ n)).op ≫ t) (e.inv_hom_id_app (Opposite.op n))

/-- Helper for Lemma 15.95.1: the `j`th term of a powered Koszul stage vanishes above the top
exterior degree `r`. -/
theorem koszul_power_stage_X_isZero_of_gt
    (f : Fin r → A) (n j : ℕ) (hj : r < j) :
    CategoryTheory.Limits.IsZero ((K^•[n](f)).X j) := by
  -- Identify the term with the `j`th exterior power of `A^r`, whose basis is empty for `j > r`.
  change CategoryTheory.Limits.IsZero ((ModuleCat.of A (Fin r → A)).exteriorPower j)
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

/-- Helper for Lemma 15.95.1: the powered Koszul stage in degree `n` should be uniformly bounded
below by `-r` in `D(A)`. -/
theorem derived_completion_koszul_stage_isGE_neg_r
    (f : Fin r → A) (n : ℕ) :
    ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n)).IsGE
      (-((r : ℕ) : ℤ)) := by
  -- Unfold the derived stage back to the extended cochain model and prove the lower support bound
  -- degreewise before passing through `Q`.
  dsimp [derivedCompletionKoszulPowersDerivedInverseSystem, koszulPowerInverseSystem]
  rw [DerivedCategory.isGE_Q_obj_iff]
  let K : CochainComplex (ModuleCat A) ℤ :=
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj (K^•[n](f)))
  change K.IsGE (-((r : ℕ) : ℤ))
  letI : K.IsStrictlyGE (-((r : ℕ) : ℤ)) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    have hneg : 0 ≤ -i := by
      omega
    let e : K.X i ≅ (K^•[n](f)).X (Int.toNat (-i)) :=
      (K^•[n](f)).extendXIso ComplexShape.embeddingDownNat (by
        simpa [K, ComplexShape.embeddingDownNat, Int.toNat_of_nonneg hneg] using
          (show -((Int.toNat (-i) : ℕ) : ℤ) = i by
            rw [Int.toNat_of_nonneg hneg]
            omega))
    have htoNat : ((Int.toNat (-i) : ℕ) : ℤ) = -i := by
      exact Int.toNat_of_nonneg hneg
    have hjgt : r < Int.toNat (-i) := by
      have hlt : ((r : ℕ) : ℤ) < ((Int.toNat (-i) : ℕ) : ℤ) := by
        rw [htoNat]
        omega
      exact_mod_cast hlt
    -- Degree `i` in the extended cochain complex is the source chain degree `Int.toNat (-i)`,
    -- which is strictly above the top exterior degree `r`.
    exact (koszul_power_stage_X_isZero_of_gt f n (Int.toNat (-i)) hjgt).of_iso e
  infer_instance

/-- Helper for Lemma 15.95.1: the negative derived homology of the `n`th powered Koszul stage is
the ordinary positive chain homology of `K^•[n](f)` after the standard `extend` transport from
`ℕ`-chains to `ℤ`-cochains. -/
noncomputable abbrev derived_koszul_negative_homology_stage_iso
    (f : Fin r → A) (p n : ℕ) :
    ((DerivedCategory.homologyFunctor (ModuleCat A) (-(p : ℤ))).obj
      ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n))) ≅
      (K^•[n](f)).homology p :=
  ((DerivedCategory.homologyFunctorFactors (ModuleCat A) (-(p : ℤ))).app
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
        (K^•[n](f))))) ≪≫
    ((K^•[n](f)).extendHomologyIso ComplexShape.embeddingDownNat (by simp))

/-- Helper for Lemma 15.95.1: after conjugating the negative derived homology transition of the
powered Koszul tower by the stagewise transport to chain homology, one recovers the actual
chain-level homology transition of `koszulPowerInverseSystem f`. -/
theorem power_quotient_negative_homology_stage_isZero
    (f : Fin r → A) (p n : ℕ) (hp : 0 < p) :
    CategoryTheory.Limits.IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat A) (-(p : ℤ))).obj
        ((derivedCompletionPowerQuotientDerivedInverseSystem f).obj (Opposite.op n))) := by
  -- Every quotient stage is concentrated in degree `0`, so negative homology vanishes.
  have hneg : (-(p : ℤ)) < 0 := by
    omega
  change
    CategoryTheory.Limits.IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat A) (-(p : ℤ))).obj
        ((single0).obj (koszulPowerQuotientStage f n)))
  letI : ((single0).obj (koszulPowerQuotientStage f n)).IsGE 0 := by
    infer_instance
  exact DerivedCategory.isZero_of_isGE _ 0 _ hneg

/-- Helper for Lemma 15.95.1: once the negative source tower is normalized to ordinary chain
homology and the quotient side is reduced to the zero tower, the remaining comparison is exactly
the source-faithful Artin-Rees vanishing package for those chain-homology transitions. -/
theorem negative_koszul_cohomology_comparison_isProIsomorphism
    (f : Fin r → A) (p : ℕ) (hp : 0 < p) (hpr : p ≤ r) :
    (SequentialProObjectMorphismRep.ofNatTrans
      (Functor.whiskerRight
        (derivedCompletionKoszulToPowerQuotientNatTrans f)
        (DerivedCategory.homologyFunctor (ModuleCat A) (-(p : ℤ))))).IsProIsomorphism := by
  -- Route correction: the source stages have been normalized by
  -- `derived_koszul_negative_homology_stage_iso`, while the quotient stages are already zero by
  -- `power_quotient_negative_homology_stage_isZero`.
  -- TODO: add the missing Artin-Rees transport showing that, after conjugating the normalized
  -- `H^(-(p : ℤ))` transitions to chain homology, one obtains a uniformly shifted zero system.
  -- With that transport in hand, package the source-to-zero and zero-to-target comparisons by
  -- the standard `SequentialProObjectMorphismRep.ofShiftNatTrans` calculus.
  sorry

/-- Helper for Lemma 15.95.1: once the canonical comparison is known to be a pro-isomorphism on
every homology tower in the bounded window `[-r, 0]`, the tower map itself is a pro-isomorphism.
This isolates the remaining source-faithful work to the negative degrees. -/
theorem derivedCompletionKoszulToPowerQuotientNatTrans_isProIsomorphism_of_window
    (f : Fin r → A)
    (hAGE :
      ∀ n : ℕ,
        ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n)).IsGE
          (-((r : ℕ) : ℤ)))
    (hALE :
      ∀ n : ℕ,
        ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n)).IsLE 0)
    (hneg :
      ∀ p : ℕ, 0 < p → p ≤ r →
        (SequentialProObjectMorphismRep.ofNatTrans
          (Functor.whiskerRight
            (derivedCompletionKoszulToPowerQuotientNatTrans f)
            (DerivedCategory.homologyFunctor (ModuleCat A) (-(p : ℤ))))).IsProIsomorphism) :
    (SequentialProObjectMorphismRep.ofNatTrans
      (derivedCompletionKoszulToPowerQuotientNatTrans f)).IsProIsomorphism := by
  -- TODO: package the already-proved stagewise `H^0` isomorphisms into a natural isomorphism,
  -- combine it with the target bounds `[0, 0]` and
  -- the negative-degree hypothesis `hneg`, then apply the Chapter 13 bounded-window criterion.
  -- This step is currently blocked externally because the intended imported owner
  -- `stacks_project.Chap13.Lemma_13_42_5` does not compile in the workspace.
  sorry

-- Proof sketch: for each `n`, the powered Koszul complex `K_n^•` fits into the canonical
-- distinguished triangle whose degree-zero term is the quotient `A/(f_1^(n+1), …, f_r^(n+1))`.
-- By the pro-truncation criterion from the derived-category references cited in the textbook, it
-- suffices to show that the negative truncation tower is pro-zero; for bounded powered Koszul
-- complexes over a Noetherian ring, this reduces to eventual vanishing of the negative cohomology
-- transition maps, which follows from Artin-Rees together with the annihilation statement of
-- Lemma `15.28.6`.
/-- Lemma 15.95.1: if `A` is Noetherian, then the powered Koszul tower
`(K(A; f_1^(n+1), \ldots, f_r^(n+1)))_n` and the quotient tower
`(A / (f_1^(n+1), \ldots, f_r^(n+1)))[0]_n`, viewed as sequential pro-objects of `D(A)`, are
isomorphic. This is the item-file indexing convention in which stage `0` corresponds to the
textbook stage `n = 1`. -/
@[stacks 0921]
theorem exists_pro_isomorphism_derived_completion_koszul_powers_to_power_quotients
    (f : Fin r → A) :
    ∃ a :
        SequentialProObjectMorphismRep
          (derivedCompletionKoszulPowersDerivedInverseSystem f)
          (derivedCompletionPowerQuotientDerivedInverseSystem f),
      IsIso a.toProObjectHom := by
  let a :
      SequentialProObjectMorphismRep
        (derivedCompletionKoszulPowersDerivedInverseSystem f)
        (derivedCompletionPowerQuotientDerivedInverseSystem f) :=
    SequentialProObjectMorphismRep.ofNatTrans (derivedCompletionKoszulToPowerQuotientNatTrans f)
  have hAGE :
      ∀ n : ℕ,
        ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n)).IsGE
          (-((r : ℕ) : ℤ)) := by
    intro n
    -- The remaining lower-bound support claim is isolated as the last stage-boundedness blocker.
    exact derived_completion_koszul_stage_isGE_neg_r (A := A) (r := r) f n
  have hALE :
      ∀ n : ℕ,
        ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n)).IsLE 0 := by
    intro n
    -- The upper bound is already carried by the extended Koszul stage.
    dsimp [derivedCompletionKoszulPowersDerivedInverseSystem]
    infer_instance
  have hpro : a.IsProIsomorphism := by
    -- Route correction: the theorem is now reduced to the packaged Chapter 13 criterion. The only
    -- remaining source-faithful blocker is the negative-degree Artin-Rees comparison.
    refine derivedCompletionKoszulToPowerQuotientNatTrans_isProIsomorphism_of_window
      (A := A) (r := r) f hAGE hALE ?_
    intro p hp hpr
    -- The remaining negative-degree comparison has been isolated as the Artin-Rees packaging
    -- helper above.
    exact negative_koszul_cohomology_comparison_isProIsomorphism
      (A := A) (r := r) (f := f) p hp hpr
  refine ⟨a, ?_⟩
  exact isIso_toProObjectHom_of_isProIsomorphism a hpro

end
