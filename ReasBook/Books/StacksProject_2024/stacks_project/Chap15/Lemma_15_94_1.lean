import Mathlib
import StacksProject_2024.Chap04.Example_4_22_6
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap15.Definition_15_89_1
import StacksProject_2024.Chap15.Lemma_15_28_8
import StacksProject_2024.Chap15.Lemma_15_94_1.Index
import StacksProject_2024.Chap15.PrincipalIdeal
import StacksProject_2024.Chap15.Situation_15_92_15

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open CochainComplex.HomComplex
open CochainComplex.HomComplex.Cochain
open Opposite
open SequentialInverseSystem
open SequentialProObjectMorphismRep
open scoped IdealPowerTorsion KoszulComplex

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)
local notation "singleCpx₀" => CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)
private abbrev principalPowerKoszulTower (f : A) : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat A) :=
  derivedCompletionKoszulPowersDerivedInverseSystem (fun _ : Fin 1 ↦ f)
private abbrev principalPowerKoszulStage (f : A) (n : ℕ) : DerivedCategory (ModuleCat A) :=
  (principalPowerKoszulTower f).obj (op n)
private abbrev principalPowerQuotientTower (f : A) : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat A) :=
  koszulPowerQuotientInverseSystem (fun _ : Fin 1 ↦ f) ⋙ single₀
private abbrev principalPowerQuotientStage (f : A) (n : ℕ) : DerivedCategory (ModuleCat A) :=
  (principalPowerQuotientTower f).obj (op n)
local notation "Kstage(" f ", " n ")" =>
  principalPowerKoszulStage f n
local notation "Qstage(" f ", " n ")" =>
  principalPowerQuotientStage f n
local notation "Ktower(" f ")" =>
  principalPowerKoszulTower f
local notation "Qtower(" f ")" =>
  principalPowerQuotientTower f

/- Domain-style sampling for Lemma 15.94.1:
- primary domain: sequential pro-object comparisons between the one-variable powered Koszul tower
  and the principal-power quotient tower in `D(A)`;
- sampled owner declarations:
  `SequentialProObjectMorphismRep`,
  `derivedCompletionKoszulPowersDerivedInverseSystem`,
  `koszulPowerQuotientStage`,
  `koszulPowerQuotientInverseSystem`,
  `CategoryTheory.CommSq`;
- best owner abstraction: the chapter powered-Koszul and quotient inverse-system owners
  `derivedCompletionKoszulPowersDerivedInverseSystem` and
  `koszulPowerQuotientInverseSystem`, with
  `SequentialProObjectMorphismRep` as the owner for the resulting pro-object comparisons;
- primitive data: the stagewise quotient maps out of the two-term Koszul complexes;
- derived API: the identity-reindex and shift-by-`c` representatives, their source-facing
  stagewise comparison maps, and the induced pro-object isomorphism statement.

Source/core/bridge triage:
- `source-facing`: the comparison maps between the Koszul and quotient towers;
- `core/canonical`: `SequentialProObjectMorphismRep ...` and `.toProObjectHom`;
- `bridge/view`: the one-variable specializations of the chapter powered-Koszul and quotient
  towers, together with the explicit stagewise maps assembling into those representatives. -/

/-- The owner-level bounded-torsion condition `A[f^∞] = A[f^c]` is equivalent to eventual
constancy of the source-facing principal-power torsion stages from `c` onward. -/
theorem fPowerTorsion_eq_iff_stabilizesFrom (f : A) (c : ℕ) :
    (A[f^∞] : Submodule A A) = (A[f ^ c] : Submodule A A) ↔
      ∀ m : ℕ, c ≤ m → (A[f ^ m] : Submodule A A) = (A[f ^ c] : Submodule A A) := by
  constructor
  · intro hstable m hcm
    apply le_antisymm
    · intro x hx
      have hxInf : x ∈ (A[f^∞] : Submodule A A) := by
        rw [Submodule.mem_torsion'_iff]
        rw [Submodule.mem_torsionBy_iff] at hx
        exact ⟨⟨f ^ m, ⟨m, rfl⟩⟩, by simpa using hx⟩
      rw [← hstable]
      exact hxInf
    · exact Submodule.torsionBy_le_torsionBy_of_dvd (f ^ c) (f ^ m) (pow_dvd_pow f hcm)
  · intro hstable
    apply le_antisymm
    · intro x hx
      rw [Submodule.mem_torsion'_iff] at hx
      rcases hx with ⟨⟨a, ha⟩, hx⟩
      rcases (Submonoid.mem_powers_iff a f).mp ha with ⟨m, rfl⟩
      have hxm : x ∈ (A[f ^ (max c m)] : Submodule A A) :=
        (Submodule.torsionBy_le_torsionBy_of_dvd (f ^ m) (f ^ max c m)
          (pow_dvd_pow f (Nat.le_max_right c m))) hx
      rw [← hstable (max c m) (Nat.le_max_left c m)]
      exact hxm
    · intro x hx
      rw [Submodule.mem_torsion'_iff]
      rw [Submodule.mem_torsionBy_iff] at hx
      exact ⟨⟨f ^ c, ⟨c, rfl⟩⟩, by simpa using hx⟩

private theorem range_fin1_power (f : A) (n : ℕ) :
    Set.range (fun _ : Fin 1 ↦ f ^ (n + 1)) = ({f ^ (n + 1)} : Set A) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    simp
  · intro hx
    refine ⟨0, ?_⟩
    simpa using hx.symm

private theorem principalPowerSingletonIdeal_eq (f : A) (n : ℕ) :
    koszulPowerIdeal (fun _ : Fin 1 ↦ f) n = principalPowerIdeal f (n + 1) := by
  rw [koszulPowerIdeal, principalPowerIdeal, range_fin1_power, Ideal.span_singleton_pow]

/-- The module endomorphism `A ⟶ A` given by multiplication by `f^n`. -/
private abbrev principalPowerKoszulMap (f : A) (n : ℕ) :
    ModuleCat.of A A ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom (LinearMap.mulRight A (f ^ n))

/-- The quotient module `A / (f^n)`. -/
private abbrev principalPowerQuotientModule (f : A) (n : ℕ) : ModuleCat A :=
  ModuleCat.of A (A ⧸ principalPowerIdeal f n)

/-- The quotient map `A ⟶ A / (f^n)`. -/
private abbrev principalPowerQuotientMk (f : A) (n : ℕ) :
    ModuleCat.of A A ⟶ principalPowerQuotientModule f n :=
  ModuleCat.ofHom ((Ideal.Quotient.mkₐ A (principalPowerIdeal f n)).toLinearMap)

private abbrev principalPowerKoszulModelComplex (f : A) (n : ℕ) :
    CochainComplex (ModuleCat A) ℤ :=
  CochainComplex.mappingCone ((singleCpx₀).map (principalPowerKoszulMap f n))

/-- Helper for Lemma 15.94.1: the one-generator powered Koszul stage is the homotopy cofiber of
multiplication by `f^(n+1)` on the truncated `Fin 0` stage, exactly as in Lemma `15.28.8`. -/
private noncomputable abbrev principalPowerSingletonKoszul_homotopyCofiber_eq (f : A) (n : ℕ) :
    K^•(fun _ : Fin 1 ↦ f ^ (n + 1)) ≅
      HomologicalComplex.homotopyCofiber
        ((f ^ (n + 1)) • 𝟙 (K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))))) :=
  koszulComplex_iso_homotopyCofiber_truncate_last (f := fun _ : Fin 1 ↦ f ^ (n + 1))

/-- Helper for Lemma 15.94.1: every positive exterior power of the zero free module `Fin 0 → A`
is already the zero object. -/
private theorem isZero_exteriorPower_empty (i : ℕ) (hi : 1 ≤ i) :
    CategoryTheory.Limits.IsZero ((ModuleCat.of A (Fin 0 → A)).exteriorPower i) := by
  -- Positive exterior powers of the empty free module are generated only by the zero tensor.
  rw [ModuleCat.isZero_iff_subsingleton]
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi) with ⟨j, rfl⟩
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
          rintro _ ⟨g, rfl⟩
          have hg : g = 0 := funext fun k ↦ Subsingleton.elim _ _
          rw [hg]
          simpa using (ExteriorAlgebra.ιMulti A (j + 1)).map_zero
        · exact bot_le
  refine ⟨fun x y ↦ ?_⟩
  have hx : x = 0 := by
    simpa [hbot] using x.2
  have hy : y = 0 := by
    simpa [hbot] using y.2
  exact hx.trans hy.symm

/-- Helper for Lemma 15.94.1: after transporting the first empty-family Koszul differential
through `⋀¹(0) ≃ 0` and `⋀⁰(0) ≃ A`, it becomes the zero linear form on `Fin 0 → A`. -/
private theorem empty_family_first_differential_linearMap_eq_linearForm (f : A) (n : ℕ) :
    (exteriorPower.zeroEquiv A (Fin 0 → A)).toLinearMap.comp
        (koszulDifferentialLinearMap
          (koszulLinearForm (Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1)))) 0) =
      (koszulLinearForm (Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1)))).comp
        (exteriorPower.oneEquiv A (Fin 0 → A)).toLinearMap := by
  -- Route correction: normalize the first differential on generators before identifying the
  -- empty-family stage with a degree-zero single complex.
  apply exteriorPower.linearMap_ext
  ext m
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply]
  have hone :
      (exteriorPower.oneEquiv A (Fin 0 → A)) (exteriorPower.ιMulti A 1 m) = m 0 := by
    simpa using (exteriorPower.oneEquiv_ιMulti (R := A) (M := Fin 0 → A) (f := m))
  have hone' :
      (koszulLinearForm (Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))))
          ((exteriorPower.oneEquiv A (Fin 0 → A)) (exteriorPower.ιMulti A 1 m)) =
        (koszulLinearForm (Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1)))) (m 0) := by
    simp [hone]
  have hone'' :
      (koszulLinearForm (Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))))
          ((exteriorPower.oneEquiv A (Fin 0 → A)).toLinearMap
            (exteriorPower.ιMulti A 1 m)) =
        (koszulLinearForm (Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1)))) (m 0) := by
    simpa using hone'
  rw [hone'']
  apply_fun (exteriorPower.zeroEquiv A (Fin 0 → A)).symm using
    (exteriorPower.zeroEquiv A (Fin 0 → A)).symm.injective
  simp [exteriorPower.zeroEquiv_symm_apply]
  apply Subtype.ext
  simpa [ExteriorAlgebra.ιMulti, Algebra.algebraMap_eq_smul_one, koszulDifferentialLinearMap] using
    (CliffordAlgebra.contractLeft_ι
      (Q := 0) (d := koszulLinearForm (Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1)))) (x := m 0))

/-- Helper for Lemma 15.94.1: the first empty-family Koszul differential vanishes after
transporting degree `0` through `⋀⁰(0) ≃ A`. -/
private theorem empty_family_first_differential_comp_iso0_eq_zero (f : A) (n : ℕ) :
    (K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1)))).d 1 0 ≫
      (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom = 0 := by
  -- Once the first differential is rewritten as the empty-family linear form, it is zero because
  -- every vector in `Fin 0 → A` is the zero vector.
  change
    ModuleCat.ofHom
      (((exteriorPower.zeroEquiv A (Fin 0 → A)).toLinearMap.comp
        (koszulDifferentialLinearMap
          (koszulLinearForm (Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1)))) 0))) = 0
  change ModuleCat.ofHom _ = ModuleCat.ofHom 0
  congr 1
  rw [empty_family_first_differential_linearMap_eq_linearForm]
  ext x
  have hx : x = 0 := funext fun i ↦ funext fun j ↦ Fin.elim0 j
  simp [hx, koszulLinearForm]

/-- Helper for Lemma 15.94.1: the empty-family `Fin 0` Koszul stage is already the degree-zero
single chain complex on `A`. -/
private noncomputable abbrev empty_family_koszul_single_iso (f : A) (n : ℕ) :
    K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))) ≅
      (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A A) := by
  let hom :
      K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))) ⟶
        (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A A) :=
    (ChainComplex.toSingle₀Equiv
        (K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))))
        (ModuleCat.of A A)).symm
      ⟨(ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom,
        empty_family_first_differential_comp_iso0_eq_zero f n⟩
  let inv :
      (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A A) ⟶
        K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))) :=
    (ChainComplex.fromSingle₀Equiv
        (K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))))
        (ModuleCat.of A A)).symm
      ((ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv)
  refine CategoryTheory.Iso.mk hom inv ?_ ?_
  · -- Compare the endomorphism of the empty-family Koszul stage degreewise.
    apply HomologicalComplex.hom_ext
    intro i
    cases i with
    | zero =>
        -- Degree `0` is exactly `⋀⁰(0) ≃ A ≃ ⋀⁰(0)`.
        have hhom0 :
            hom.f 0 = (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom := by
          simpa [hom] using
            (ChainComplex.toSingle₀Equiv_symm_apply_f_zero
              (C := K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))))
              (X := ModuleCat.of A A)
              (f := (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom)
              (hf := empty_family_first_differential_comp_iso0_eq_zero f n))
        have hinv0 :
            inv.f 0 = (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv := by
          simpa [inv] using
            (ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
              (C := K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))))
              (X := ModuleCat.of A A)
              (f := (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv))
        simpa [HomologicalComplex.comp_f, hhom0, hinv0] using
          (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom_inv_id
    | succ m =>
        -- Every positive degree of the empty-family Koszul stage is already zero.
        exact
          (isZero_exteriorPower_empty (m + 1) (Nat.succ_le_succ (Nat.zero_le m))).eq_of_src _ _
  · -- Maps out of a degree-zero single chain complex are determined by their degree-zero component.
    apply HomologicalComplex.from_single_hom_ext
    -- Degree `0` is again the inverse pair `A ≃ ⋀⁰(0)`.
    have hhom0 :
        hom.f 0 = (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom := by
      simpa [hom] using
        (ChainComplex.toSingle₀Equiv_symm_apply_f_zero
          (C := K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))))
          (X := ModuleCat.of A A)
          (f := (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom)
          (hf := empty_family_first_differential_comp_iso0_eq_zero f n))
    have hinv0 :
        inv.f 0 = (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv := by
      simpa [inv] using
        (ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
          (C := K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))))
          (X := ModuleCat.of A A)
          (f := (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv))
    simpa [HomologicalComplex.comp_f, hhom0, hinv0] using
      (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv_hom_id

/-- Helper for Lemma 15.94.1: the degree-zero identification `⋀⁰(0) ≃ A` transports scalar
multiplication on `⋀⁰(0)` to right multiplication on `A`. -/
private theorem empty_exteriorPower_iso0_conjugates_mulRight (r : A) :
    (r • 𝟙 ((ModuleCat.of A (Fin 0 → A)).exteriorPower 0)) =
      (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom ≫
        ModuleCat.ofHom (LinearMap.mulRight A r) ≫
          (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv := by
  -- Apply `⋀⁰(0) ≃ A`; after this transport both sides are the same multiplication map on `A`.
  ext x
  have hhom_injective :
      Function.Injective
        ((ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom.hom) := by
    intro y z hyz
    have hyz' := congrArg
      (fun t ↦ (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv.hom t) hyz
    simpa using hyz'
  apply_fun ((ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom.hom) using
    hhom_injective
  simp [mul_comm]

/-- Helper for Lemma 15.94.1: on the nat-indexed empty-family Koszul stage, scalar
multiplication by `f^(n+1)` is conjugate to the degree-zero single-complex map induced by
multiplication on `A`. -/
private theorem empty_family_koszul_single_iso_conjugates_scalar (f : A) (n : ℕ) :
    ((f ^ (n + 1)) • 𝟙 (K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))))) =
      (empty_family_koszul_single_iso f n).hom ≫
        (ChainComplex.single₀ (ModuleCat A)).map (principalPowerKoszulMap f (n + 1)) ≫
          (empty_family_koszul_single_iso f n).inv := by
  -- Compare both chain maps degreewise. Degree `0` is the transported scalar action from the
  -- previous helper, and every positive degree vanishes because the empty-family stage is zero.
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      have hs :
          (((f ^ (n + 1)) • 𝟙 (K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1)))))).f 0 =
            ModuleCat.ofHom
              ((f ^ (n + 1)) •
                (LinearMap.id :
                  ((ModuleCat.of A (Fin 0 → A)).exteriorPower 0) →ₗ[A]
                    ((ModuleCat.of A (Fin 0 → A)).exteriorPower 0))) := by
        rfl
      -- Reuse the explicit degree-zero components of `empty_family_koszul_single_iso`.
      have hhom0 :
          (empty_family_koszul_single_iso f n).hom.f 0 =
            (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom := by
        simpa [empty_family_koszul_single_iso] using
          (ChainComplex.toSingle₀Equiv_symm_apply_f_zero
            (C := K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))))
            (X := ModuleCat.of A A)
            (f := (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom)
            (hf := empty_family_first_differential_comp_iso0_eq_zero f n))
      have hinv0 :
          (empty_family_koszul_single_iso f n).inv.f 0 =
            (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv := by
        simpa [empty_family_koszul_single_iso] using
          (ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
            (C := K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))))
            (X := ModuleCat.of A A)
            (f := (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv))
      have hsingle0 :
          ((ChainComplex.single₀ (ModuleCat A)).map
              (principalPowerKoszulMap f (n + 1))).f 0 =
            principalPowerKoszulMap f (n + 1) := by
        simpa using
          (HomologicalComplex.single_map_f_self
            (V := ModuleCat A) (c := ComplexShape.down ℕ) (j := (0 : ℕ))
            (f := principalPowerKoszulMap f (n + 1)))
      -- After identifying degree `0` with `A`, the statement is exactly the module-level
      -- conjugation lemma above.
      rw [hs]
      -- Normalize the right-hand component to the explicit `⋀⁰(0) ≃ A` conjugation.
      rw [show
          ((empty_family_koszul_single_iso f n).hom ≫
            (ChainComplex.single₀ (ModuleCat A)).map (principalPowerKoszulMap f (n + 1)) ≫
            (empty_family_koszul_single_iso f n).inv).f 0 =
            (empty_family_koszul_single_iso f n).hom.f 0 ≫
              principalPowerKoszulMap f (n + 1) ≫
              (empty_family_koszul_single_iso f n).inv.f 0 by
            simp [HomologicalComplex.comp_f, hsingle0]]
      rw [hhom0, hinv0]
      simpa [principalPowerKoszulMap] using
        empty_exteriorPower_iso0_conjugates_mulRight
          (A := A) (r := f ^ (n + 1))
  | succ m =>
      -- Positive degrees of the empty-family stage are zero, so there is only one map out of
      -- them on either side.
      exact
        (isZero_exteriorPower_empty (m + 1) (Nat.succ_le_succ (Nat.zero_le m))).eq_of_src _ _

/-- Helper for Lemma 15.94.1: extending the empty-family `Fin 0` Koszul stage to `ℤ` gives the
canonical degree-zero single complex on `A`. -/
private abbrev empty_family_koszul_extended_single_iso (f : A) (n : ℕ) :
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
      (K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))))) ≅
    (singleCpx₀).obj (ModuleCat.of A A) :=
  -- Route correction: first normalize the empty-family stage on the nat-indexed chain complex,
  -- then extend that normalization to `ℤ` via the canonical `extendSingleIso`.
  ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).mapIso
      (empty_family_koszul_single_iso f n)) ≪≫
    (HomologicalComplex.extendSingleIso
      ComplexShape.embeddingDownNat (ModuleCat.of A A) (0 : ℕ) (0 : ℤ) rfl)

/-- Helper for Lemma 15.94.1: extending a degree-zero single-complex map from `ℕ` to `ℤ`
commutes with the canonical `extendSingleIso` identification. -/
private theorem extend_single0_map_transport {M N : ModuleCat A} (g : M ⟶ N) :
    HomologicalComplex.extendMap ((ChainComplex.single₀ (ModuleCat A)).map g)
        ComplexShape.embeddingDownNat ≫
      (HomologicalComplex.extendSingleIso
        ComplexShape.embeddingDownNat N (0 : ℕ) (0 : ℤ) rfl).hom =
    (HomologicalComplex.extendSingleIso
      ComplexShape.embeddingDownNat M (0 : ℕ) (0 : ℤ) rfl).hom ≫
      (singleCpx₀).map g := by
  -- Rewrite the target as the explicit `up ℤ` single-complex map, then follow the standard
  -- degreewise proof.
  change HomologicalComplex.extendMap ((ChainComplex.single₀ (ModuleCat A)).map g)
      ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.extendSingleIso
      ComplexShape.embeddingDownNat N (0 : ℕ) (0 : ℤ) rfl).hom =
      (HomologicalComplex.extendSingleIso
        ComplexShape.embeddingDownNat M (0 : ℕ) (0 : ℤ) rfl).hom ≫
        (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℤ) (0 : ℤ)).map g
  -- Compare both chain maps degreewise: away from degree `0` every single-complex term is zero,
  -- and at degree `0` both components are the canonical realization of `g`.
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst hi
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
          -- Away from degree `0`, the target single complex is zero.
          exact
            (HomologicalComplex.isZero_single_obj_X
              (ComplexShape.up ℤ) (0 : ℤ) N (-((Nat.succ j : ℕ) : ℤ)) (by omega)).eq_of_tgt _ _
    · -- If `i` is not in the image of the embedding, the extended source term is also zero.
      exact (((ChainComplex.single₀ (ModuleCat A)).obj M).isZero_extend_X
        ComplexShape.embeddingDownNat i (fun j hij ↦ hpre ⟨j, hij⟩)).eq_of_src _ _

/-- Helper for Lemma 15.94.1: on `embeddingDownNat`, the extension functor map is definitionally
the owner-level `extendMap`. -/
private theorem embeddingDownNat_extendFunctor_map_eq_extendMap
    {C D : ChainComplex (ModuleCat A) ℕ} (φ : C ⟶ D) :
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map φ) =
      HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat :=
  rfl

/-- Helper for Lemma 15.94.1: the degree-zero witness in `extendSingleIso` is proof-irrelevant. -/
private theorem extendSingleIso_zero_proof_irrel
    (X : ModuleCat A)
    (h₁ h₂ : ComplexShape.embeddingDownNat.f (0 : ℕ) = (0 : ℤ)) :
    HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat X (0 : ℕ) (0 : ℤ) h₁ =
      HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat X (0 : ℕ) (0 : ℤ) h₂ := by
  -- The endpoint witness is a proposition, so the resulting single-complex identification does
  -- not depend on which proof is chosen.
  cases Subsingleton.elim h₁ h₂
  rfl

/-- Helper for Lemma 15.94.1: conjugating an endomorphism by `extendSingleIso` in degree `0` is
independent of the proof used to identify the endpoint `0`. -/
private theorem extendSingleIso_zero_conjugation_proof_irrel
    (X : ModuleCat A)
    (φ : (singleCpx₀).obj X ⟶ (singleCpx₀).obj X)
    (h₁ h₂ : ComplexShape.embeddingDownNat.f (0 : ℕ) = (0 : ℤ)) :
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat X (0 : ℕ) (0 : ℤ) h₁).hom ≫
        φ ≫
          (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat X (0 : ℕ) (0 : ℤ)
            h₁).inv =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat X (0 : ℕ) (0 : ℤ) h₂).hom ≫
        φ ≫
          (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat X (0 : ℕ) (0 : ℤ)
            h₂).inv := by
  -- Proof irrelevance already identifies the two isomorphisms, so the conjugated composite is
  -- literally the same morphism on both sides.
  cases extendSingleIso_zero_proof_irrel (A := A) X h₁ h₂
  rfl

/-- Helper for Lemma 15.94.1: after transporting the extended empty-family scalar endomorphism
through the canonical `Fin 0`-to-`singleCpx₀` identification, one gets the explicit degree-zero
single-complex map induced by multiplication by `f^(n+1)`. -/
private theorem empty_family_koszul_extended_single_iso_conjugates_scalar (f : A) (n : ℕ) :
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map
        (((f ^ (n + 1)) •
          𝟙 (K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))))))) =
      (empty_family_koszul_extended_single_iso f n).hom ≫
        (singleCpx₀).map (principalPowerKoszulMap f (n + 1)) ≫
          (empty_family_koszul_extended_single_iso f n).inv := by
  -- Route correction: the nat-indexed conjugation is already proved, and the remaining issue is
  -- purely transport/coercion across `extendMap` and the proof argument in `extendSingleIso`.
  let e₀ := empty_family_koszul_single_iso f n
  let e₁ :=
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).mapIso e₀)
  let e₂ :=
    HomologicalComplex.extendSingleIso
      ComplexShape.embeddingDownNat (ModuleCat.of A A) (0 : ℕ) (0 : ℤ) rfl
  have hnat :
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map
          (((f ^ (n + 1)) •
            𝟙 (K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))))))) =
        e₁.hom ≫
          HomologicalComplex.extendMap
            ((ChainComplex.single₀ (ModuleCat A)).map
              (principalPowerKoszulMap f (n + 1)))
            ComplexShape.embeddingDownNat ≫
            e₁.inv := by
    -- Extend the nat-indexed conjugation square and rewrite the result in the owner notation.
    simpa [e₁, Functor.map_comp, HomologicalComplex.extendMap_comp,
      embeddingDownNat_extendFunctor_map_eq_extendMap] using
      congrArg
        (fun k ↦ HomologicalComplex.extendMap k ComplexShape.embeddingDownNat)
        (empty_family_koszul_single_iso_conjugates_scalar f n)
  have htransport :
      HomologicalComplex.extendMap
          ((ChainComplex.single₀ (ModuleCat A)).map
            (principalPowerKoszulMap f (n + 1)))
          ComplexShape.embeddingDownNat =
        e₂.hom ≫
          (singleCpx₀).map (principalPowerKoszulMap f (n + 1)) ≫
            e₂.inv := by
    -- The degree-zero single-complex transport is already isolated in
    -- `extend_single0_map_transport`.
    calc
      HomologicalComplex.extendMap
          ((ChainComplex.single₀ (ModuleCat A)).map
            (principalPowerKoszulMap f (n + 1)))
          ComplexShape.embeddingDownNat =
        HomologicalComplex.extendMap
            ((ChainComplex.single₀ (ModuleCat A)).map
              (principalPowerKoszulMap f (n + 1)))
            ComplexShape.embeddingDownNat ≫
          (e₂.hom ≫ e₂.inv) := by simp
      _ =
        ((HomologicalComplex.extendMap
              ((ChainComplex.single₀ (ModuleCat A)).map
                (principalPowerKoszulMap f (n + 1)))
              ComplexShape.embeddingDownNat ≫
            e₂.hom) ≫
          e₂.inv) := by
            simp [Category.assoc]
      _ =
        (e₂.hom ≫ (singleCpx₀).map (principalPowerKoszulMap f (n + 1))) ≫
          e₂.inv := by
            simpa [e₂] using
              congrArg
                (fun t ↦ t ≫ e₂.inv)
                (extend_single0_map_transport
                  (A := A) (g := principalPowerKoszulMap f (n + 1)))
      _ =
        e₂.hom ≫
          (singleCpx₀).map (principalPowerKoszulMap f (n + 1)) ≫
            e₂.inv := by simp [Category.assoc]
  have hcombined :
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map
          (((f ^ (n + 1)) •
            𝟙 (K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))))))) =
        e₁.hom ≫
          e₂.hom ≫
            (singleCpx₀).map (principalPowerKoszulMap f (n + 1)) ≫
              e₂.inv ≫
                e₁.inv := by
    -- The extended scalar map factors through the two consecutive transport isomorphisms.
    calc
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map
          (((f ^ (n + 1)) •
            𝟙 (K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))))))) =
        e₁.hom ≫
          HomologicalComplex.extendMap
            ((ChainComplex.single₀ (ModuleCat A)).map
              (principalPowerKoszulMap f (n + 1)))
            ComplexShape.embeddingDownNat ≫
              e₁.inv := hnat
      _ =
        e₁.hom ≫
          (e₂.hom ≫
            (singleCpx₀).map (principalPowerKoszulMap f (n + 1)) ≫
              e₂.inv) ≫
            e₁.inv := by
              simpa [Category.assoc] using
                congrArg
                  (fun t ↦ e₁.hom ≫ t ≫ e₁.inv)
                  htransport
      _ =
        e₁.hom ≫
          e₂.hom ≫
            (singleCpx₀).map (principalPowerKoszulMap f (n + 1)) ≫
              e₂.inv ≫
                e₁.inv := by simp [Category.assoc]
  -- Reassociate the two transport isomorphisms into the public extended-stage identification.
  simpa [empty_family_koszul_extended_single_iso, e₁, e₂, Category.assoc] using hcombined

/-- Helper for Lemma 15.94.1: positive cochain degrees of the extended homotopy cofiber vanish,
so the remaining cone-bridge work only has to compare degrees `0` and `-1`. -/
private theorem extend_homotopyCofiber_isZero_pos
    {C : ChainComplex (ModuleCat A) ℕ} (φ : C ⟶ C) (m : ℕ) :
    CategoryTheory.Limits.IsZero
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
        (HomologicalComplex.homotopyCofiber φ)).X (m + 1 : ℤ)) := by
  -- Positive integers are not in the image of `n ↦ -n`, so the extension is zero there.
  change CategoryTheory.Limits.IsZero (((HomologicalComplex.homotopyCofiber φ).extend
      ComplexShape.embeddingDownNat).X (m + 1 : ℤ))
  apply (HomologicalComplex.homotopyCofiber φ).isZero_extend_X
    ComplexShape.embeddingDownNat (m + 1 : ℤ)
  intro i hi
  dsimp [ComplexShape.embeddingDownNat] at hi
  omega

/-- Helper for Lemma 15.94.1: after the empty-family stage is transported to the degree-zero
single complex on `A`, the extended homotopy cofiber is the explicit two-term mapping cone on
multiplication by `f^(n+1)`. -/
private noncomputable abbrev extended_empty_family_homotopyCofiber_to_mappingCone_iso
    (f : A) (n : ℕ) :
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
      (HomologicalComplex.homotopyCofiber
        (((f ^ (n + 1)) • 𝟙 (K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1)))))))) ≅
      principalPowerKoszulModelComplex f (n + 1) :=
  by
    -- Route correction: this singleton-cone normalization is the persistent structural blocker, so
    -- we now instantiate the canonical owner theorem from the dedicated helper file instead of
    -- reproving the same transport-heavy cone comparison locally.
    simpa [principalPowerKoszulModelComplex] using
      CategoryTheory.extend_homotopyCofiber_conjugate_single_map_iso_mappingCone
        (A := A)
        (((f ^ (n + 1)) • 𝟙 (K^•(Fin.init (fun _ : Fin 1 ↦ f ^ (n + 1))))))
        (principalPowerKoszulMap f (n + 1))
        (empty_family_koszul_extended_single_iso f n)
        (empty_family_koszul_extended_single_iso_conjugates_scalar f n)

private abbrev principalPowerKoszulStageIso (f : A) (n : ℕ) :
    Kstage(f, n) ≅ DerivedCategory.Q.obj (principalPowerKoszulModelComplex f (n + 1)) :=
  -- Rewrite the one-variable Koszul stage through the canonical cone model, then localize.
  DerivedCategory.Q.mapIso
    (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).mapIso
        (principalPowerSingletonKoszul_homotopyCofiber_eq f n)) ≪≫
      (extended_empty_family_homotopyCofiber_to_mappingCone_iso f n))

private theorem principalPowerSingletonQuotientDerived_eq (f : A) (n : ℕ) :
    Qstage(f, n) = (single₀).obj (principalPowerQuotientModule f (n + 1)) := by
  simpa [principalPowerQuotientStage, principalPowerQuotientTower, principalPowerQuotientModule,
    koszulPowerQuotientStage] using
    congrArg (fun I : Ideal A ↦ (single₀).obj (ModuleCat.of A (A ⧸ I)))
      (principalPowerSingletonIdeal_eq f n)

private abbrev principalPowerQuotientStageIso (f : A) (n : ℕ) :
    Qstage(f, n) ≅
      DerivedCategory.Q.obj ((singleCpx₀).obj (principalPowerQuotientModule f (n + 1))) :=
  eqToIso (principalPowerSingletonQuotientDerived_eq f n) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      (principalPowerQuotientModule f (n + 1))

-- Proof sketch: the quotient map kills the image of multiplication by `f^n` because
-- `f^n ∈ (f^n)`.
/-- The quotient map `A ⟶ A / (f^n)` annihilates multiplication by `f^n`. -/
private theorem principalPowerKoszulMap_comp_quotientMk (f : A) (n : ℕ) :
    principalPowerKoszulMap f n ≫ principalPowerQuotientMk f n = 0 := by
  -- Evaluate the composite on an element and check the result lies in `(f^n)`.
  rw [principalPowerKoszulMap, principalPowerQuotientMk]
  change
    ModuleCat.ofHom
        (((Ideal.Quotient.mkₐ A (principalPowerIdeal f n)).toLinearMap).comp
          (LinearMap.mulRight A (f ^ n))) = 0
  change
    ModuleCat.ofHom
        (((Ideal.Quotient.mkₐ A (principalPowerIdeal f n)).toLinearMap).comp
          (LinearMap.mulRight A (f ^ n))) =
      ModuleCat.ofHom 0
  congr 1
  apply LinearMap.ext
  intro x
  change Ideal.Quotient.mk (principalPowerIdeal f n) (x * f ^ n) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  rw [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

private theorem singleCpx_principalPowerKoszulMap_comp_quotientMk (f : A) (n : ℕ) :
    (singleCpx₀).map (principalPowerKoszulMap f n) ≫
        (singleCpx₀).map (principalPowerQuotientMk f n) =
      0 := by
  simpa using
    congrArg (fun φ ↦ (singleCpx₀).map φ) (principalPowerKoszulMap_comp_quotientMk f n)

-- Proof sketch: apply `mappingCone.desc` with zero cochain and the quotient map on the degree-zero
-- term; the previous theorem gives the required vanishing condition.
/-- The zero cochain witnesses the factorization of the quotient map through the two-term Koszul
mapping cone. -/
private theorem principalPowerKoszulToQuotientComplexMap_desc_condition (f : A) (n : ℕ) :
    δ (-1) 0
        (0 :
          Cochain
            ((singleCpx₀).obj (ModuleCat.of A A))
            ((singleCpx₀).obj (principalPowerQuotientModule f n))
            (-1)) =
      Cochain.ofHom
        (((singleCpx₀).map (principalPowerKoszulMap f n)) ≫
          (singleCpx₀).map (principalPowerQuotientMk f n)) := by
  rw [δ_zero]
  simp [singleCpx_principalPowerKoszulMap_comp_quotientMk]

/-- The canonical chain map from the two-term Koszul complex `A \xrightarrow{f^n} A` to the
single complex on `A / (f^n)`. -/
private abbrev principalPowerKoszulToQuotientComplexMap (f : A) (n : ℕ) :
    principalPowerKoszulModelComplex f n ⟶
      (singleCpx₀).obj (principalPowerQuotientModule f n) :=
  CochainComplex.mappingCone.desc
    ((singleCpx₀).map (principalPowerKoszulMap f n))
    0
    ((singleCpx₀).map (principalPowerQuotientMk f n))
    (principalPowerKoszulToQuotientComplexMap_desc_condition f n)

/-- Helper for Lemma 15.94.1: the forward comparison
`A \xrightarrow{f^n} A \to A / (f^n)` packaged as a short complex of degree-zero single cochain
complexes. -/
private abbrev principalPowerForwardShortComplex (f : A) (n : ℕ) :
    ShortComplex (CochainComplex (ModuleCat A) ℤ) :=
  (ShortComplex.mk
      (principalPowerKoszulMap f n)
      (principalPowerQuotientMk f n)
      (principalPowerKoszulMap_comp_quotientMk f n)).map singleCpx₀

/-- Helper for Lemma 15.94.1: the principal ideals `(f^(n+2)) ⊆ (f^(n+1))` give the canonical
transition map on the quotient stages. -/
private abbrev principalPowerQuotientStep (f : A) (n : ℕ) :
    principalPowerQuotientModule f (n + 2) ⟶ principalPowerQuotientModule f (n + 1) :=
  ModuleCat.ofHom <|
    (Ideal.Quotient.factorₐ A <| by
      -- Rewrite the one-generator ideals through the chapter quotient owner and use its
      -- monotonicity in the exponent.
      simpa [principalPowerSingletonIdeal_eq] using
        (koszulPowerIdeal_succ_le (fun _ : Fin 1 ↦ f) n)).toLinearMap

/-- Helper for Lemma 15.94.1: multiplying first by `f` and then by `f^(n+1)` is multiplication by
`f^(n+2)`. This is the left square in the adjacent powered transition. -/
private theorem principalPowerKoszulMap_step_comp (f : A) (n : ℕ) :
    principalPowerKoszulMap f 1 ≫ principalPowerKoszulMap f (n + 1) =
      principalPowerKoszulMap f (n + 2) := by
  -- Evaluate the composite on elements and combine the powers of `f`.
  rw [principalPowerKoszulMap, principalPowerKoszulMap, principalPowerKoszulMap]
  change
    ModuleCat.ofHom
        ((LinearMap.mulRight A (f ^ (n + 1))).comp (LinearMap.mulRight A (f ^ 1))) =
      ModuleCat.ofHom (LinearMap.mulRight A (f ^ (n + 2)))
  congr 1
  apply LinearMap.ext
  intro x
  calc
    (LinearMap.mulRight A (f ^ (n + 1))) ((LinearMap.mulRight A (f ^ 1)) x) =
      (x * f) * f ^ (n + 1) := by simp [LinearMap.mulRight_apply, pow_one]
    _ = x * (f * f ^ (n + 1)) := by ac_rfl
    _ = x * (f ^ 1 * f ^ (n + 1)) := by simp [pow_one]
    _ = x * f ^ (1 + (n + 1)) := by rw [← pow_add]
    _ = x * f ^ (n + 2) := by
      congr 2
      omega
    _ = (LinearMap.mulRight A (f ^ (n + 2))) x := by simp [LinearMap.mulRight_apply]

/-- Helper for Lemma 15.94.1: the quotient transition map carries the universal class of `a`
modulo `(f^(n+2))` to the universal class of `a` modulo `(f^(n+1))`. -/
private theorem principalPowerQuotientMk_step_naturality (f : A) (n : ℕ) :
    principalPowerQuotientMk f (n + 2) ≫ principalPowerQuotientStep f n =
      principalPowerQuotientMk f (n + 1) := by
  -- Both composites are the canonical quotient map sending `a` to its class modulo `(f^(n+1))`.
  rw [principalPowerQuotientMk, principalPowerQuotientStep]
  change
    ModuleCat.ofHom
        (((Ideal.Quotient.factorₐ A
          (show principalPowerIdeal f (n + 2) ≤ principalPowerIdeal f (n + 1) by
            simpa [principalPowerSingletonIdeal_eq] using
              (koszulPowerIdeal_succ_le (fun _ : Fin 1 ↦ f) n))).toLinearMap).comp
          ((Ideal.Quotient.mkₐ A (principalPowerIdeal f (n + 2))).toLinearMap)) =
      ModuleCat.ofHom ((Ideal.Quotient.mkₐ A (principalPowerIdeal f (n + 1))).toLinearMap)
  rfl

/-- Helper for Lemma 15.94.1: the adjacent powers define a morphism of the forward short complexes
`A \xrightarrow{f^(n+2)} A \to A/(f^(n+2))` to
`A \xrightarrow{f^(n+1)} A \to A/(f^(n+1))`. -/
private abbrev principalPowerForwardShortComplex_step (f : A) (n : ℕ) :
    principalPowerForwardShortComplex f (n + 2) ⟶
      principalPowerForwardShortComplex f (n + 1) :=
  ShortComplex.Hom.mk
    ((singleCpx₀).map (principalPowerKoszulMap f 1))
    (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
    ((singleCpx₀).map (principalPowerQuotientStep f n))
    (by
      -- The left square is multiplication-by-`f` followed by multiplication-by-`f^(n+1)`.
      simpa [Functor.map_comp] using
        congrArg (fun φ ↦ (singleCpx₀).map φ) (principalPowerKoszulMap_step_comp f n))
    (by
      -- The right square is the universal compatibility of quotient maps with factor maps.
      simpa [Functor.map_comp] using
        congrArg (fun φ ↦ (singleCpx₀).map φ) (principalPowerQuotientMk_step_naturality f n).symm)

/-- Helper for Lemma 15.94.1: the explicit cone map to the quotient complex is exactly the
canonical `mappingCone.descShortComplex` morphism for the forward short complex. -/
private theorem principalPowerKoszulToQuotientComplexMap_eq_descShortComplex
    (f : A) (n : ℕ) :
    principalPowerKoszulToQuotientComplexMap f n =
      CochainComplex.mappingCone.descShortComplex
        (principalPowerForwardShortComplex f n) := by
  -- Both sides are the same `mappingCone.desc` presentation of the quotient map.
  rfl

/-- Helper for Lemma 15.94.1: the adjacent-stage map from the two-term Koszul cone to the quotient
complex is exactly the owner naturality square for `mappingCone.descShortComplex`. -/
private theorem principalPowerKoszulToQuotientComplexMap_step_naturality
    (f : A) (n : ℕ) :
    CochainComplex.mappingCone.map
        ((singleCpx₀).map (principalPowerKoszulMap f (n + 2)))
        ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
        ((singleCpx₀).map (principalPowerKoszulMap f 1))
        (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
        (principalPowerForwardShortComplex_step f n).comm₁₂.symm ≫
      principalPowerKoszulToQuotientComplexMap f (n + 1) =
        principalPowerKoszulToQuotientComplexMap f (n + 2) ≫
          (singleCpx₀).map (principalPowerQuotientStep f n) := by
  -- Route correction: isolate the owner `descShortComplex` naturality square before transporting
  -- it through the stage identifications in `D(A)`.
  simpa [principalPowerKoszulToQuotientComplexMap_eq_descShortComplex] using
    CochainComplex.mappingCone.descShortComplex_naturality
      (principalPowerForwardShortComplex_step f n)

/-- The stagewise canonical map
`(A \xrightarrow{f^(n+1)} A) ⟶ A/(f^(n+1))`,
viewed as a map from the one-variable specialization of the chapter powered-Koszul stage. -/
private abbrev principalPowerKoszulToQuotient (f : A) (n : ℕ) :
    Ktower(f).obj (op n) ⟶ Qtower(f).obj (op n) :=
  (principalPowerKoszulStageIso f n).hom ≫
    DerivedCategory.Q.map (principalPowerKoszulToQuotientComplexMap f (n + 1)) ≫
      (principalPowerQuotientStageIso f n).inv

-- Proof sketch: both towers are built from adjacent powers of `f`, and the quotient map out of
-- the two-term complex is functorial with respect to the transition maps.
-- Helper for Lemma 15.94.1: first isolate the quotient-stage transport of the successor map
-- before inserting it into the forward comparison square.
/-- Helper for Lemma 15.94.1: the explicit principal-power quotient stage is the owner quotient
stage for the singleton family `fun _ : Fin 1 ↦ f` after rewriting the ideal
`(f^(n+1)) = koszulPowerIdeal (fun _ ↦ f) n`. -/
private theorem principalPowerQuotientModule_eq_owner_stage
    (f : A) (n : ℕ) :
    principalPowerQuotientModule f (n + 1) =
      koszulPowerQuotientStage (fun _ : Fin 1 ↦ f) n := by
  -- Proof comment: both quotient modules are defined by the same ideal once the singleton
  -- Koszul ideal is identified with the principal ideal `(f^(n+1))`.
  simpa [principalPowerQuotientModule, koszulPowerQuotientStage] using
    congrArg (fun I : Ideal A ↦ ModuleCat.of A (A ⧸ I))
      (principalPowerSingletonIdeal_eq f n).symm

/-- Helper for Lemma 15.94.1: the successor morphism in the specialized quotient tower is the
image under `single₀` of the owner quotient-step map for the singleton family `fun _ ↦ f`. -/
private theorem principalPowerQuotientTower_step_map
    (f : A) (n : ℕ) :
    Qtower(f).map (homOfLE (Nat.le_succ n)).op =
      (single₀).map (koszulPowerQuotientStep (fun _ : Fin 1 ↦ f) n) := by
  -- Proof comment: `Qtower(f)` is literally the singleton quotient inverse system whiskered by
  -- `single₀`, so its successor map is definitionally the whiskered owner successor.
  simpa [principalPowerQuotientTower, Functor.ofOpSequence_map_homOfLE_succ]

/-- Helper for Lemma 15.94.1: transporting quotient classes along the module equality induced by
an equality of ideals fixes representatives. -/
private theorem moduleCat_quotient_eqToHom_mk
    {I J : Ideal A} (h : I = J) (x : A) :
    eqToHom (congrArg (fun K : Ideal A ↦ ModuleCat.of A (A ⧸ K)) h)
      ((Ideal.Quotient.mk I) x) =
    (Ideal.Quotient.mk J) x := by
  -- Proof comment: once the ideal equality is literal, the transport is the identity on the
  -- quotient type.
  cases h
  rfl

/-- Helper for Lemma 15.94.1: transporting a quotient class along the singleton-owner stage
identification preserves its representative. -/
private theorem principalPowerQuotientModule_eq_owner_stage_mk_transport
    (f : A) (n : ℕ) (x : A) :
    eqToHom (principalPowerQuotientModule_eq_owner_stage f n)
      ((Ideal.Quotient.mk (principalPowerIdeal f (n + 1))) x) =
    (Ideal.Quotient.mk (koszulPowerIdeal (fun _ : Fin 1 ↦ f) n)) x := by
  -- Proof comment: once the singleton ideal equality is specialized, the transported quotient
  -- class is definitionally the same universal class.
  have hstage :
      principalPowerQuotientModule_eq_owner_stage f n =
        congrArg (fun I : Ideal A ↦ ModuleCat.of A (A ⧸ I))
          (principalPowerSingletonIdeal_eq f n).symm := by
    -- Proof comment: the displayed stage equality is proposition-valued, so we may replace the
    -- proof term by the explicit quotient-module equality coming from the singleton ideal.
    exact Subsingleton.elim _ _
  rw [hstage]
  -- Proof comment: after replacing the stage equality by the explicit quotient equality, the
  -- transported class is just the same representative in the target quotient.
  simpa using
    moduleCat_quotient_eqToHom_mk (A := A) (principalPowerSingletonIdeal_eq f n).symm x

/-- Helper for Lemma 15.94.1: at the `ModuleCat` level, the explicit principal-power quotient
successor is exactly the singleton-owner quotient successor after transporting the source and
target modules along the canonical stage equalities. -/
private theorem principalPowerQuotientStep_transport_under_owner_stage
    (f : A) (n : ℕ) :
    principalPowerQuotientStep f n ≫
      eqToHom (principalPowerQuotientModule_eq_owner_stage f n) =
    eqToHom (principalPowerQuotientModule_eq_owner_stage f (n + 1)) ≫
      koszulPowerQuotientStep (fun _ : Fin 1 ↦ f) n := by
  -- Proof comment: after rewriting both quotient stages through the same singleton ideal, both
  -- sides should be the same quotient factor map on representatives.
  -- Route correction: evaluate on quotient generators first, and only then rewrite the singleton
  -- owner transports using the explicit `Ideal.quotEquivOfEq_mk` formula above.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro x
  -- Proof comment: both composites send the class of `x` to the class of the same representative
  -- in the owner quotient stage.
  calc
    (principalPowerQuotientStep f n ≫
        eqToHom (principalPowerQuotientModule_eq_owner_stage f n))
        ((Ideal.Quotient.mk (principalPowerIdeal f (n + 2))) x) =
      eqToHom (principalPowerQuotientModule_eq_owner_stage f n)
        ((Ideal.Quotient.mk (principalPowerIdeal f (n + 1))) x) := by
        simp [principalPowerQuotientStep, Ideal.Quotient.factorₐ, Ideal.Quotient.factor,
          RingHom.comp_apply]
    _ = (Ideal.Quotient.mk (koszulPowerIdeal (fun _ : Fin 1 ↦ f) n)) x := by
        simpa using principalPowerQuotientModule_eq_owner_stage_mk_transport f n x
    _ = (koszulPowerQuotientStep (fun _ : Fin 1 ↦ f) n)
          ((Ideal.Quotient.mk (koszulPowerIdeal (fun _ : Fin 1 ↦ f) (n + 1))) x) := by
        simp [koszulPowerQuotientStep, Ideal.Quotient.factorₐ, Ideal.Quotient.factor,
          RingHom.comp_apply]
    _ = (koszulPowerQuotientStep (fun _ : Fin 1 ↦ f) n)
          (eqToHom (principalPowerQuotientModule_eq_owner_stage f (n + 1))
            ((Ideal.Quotient.mk (principalPowerIdeal f (n + 2))) x)) := by
        rw [principalPowerQuotientModule_eq_owner_stage_mk_transport]
    _ = (eqToHom (principalPowerQuotientModule_eq_owner_stage f (n + 1)) ≫
          koszulPowerQuotientStep (fun _ : Fin 1 ↦ f) n)
          ((Ideal.Quotient.mk (principalPowerIdeal f (n + 2))) x) := by
        rfl

/-- Helper for Lemma 15.94.1: postcomposing with `eqToHom` is proof-irrelevant. -/
private theorem principalPower_comp_eqToHom_eq
    {C : Type*} [Category C] {X Y Z : C} (f : Z ⟶ X) (p q : X = Y) :
    f ≫ eqToHom p = f ≫ eqToHom q := by
  -- Proof comment: once both endpoint equalities are literal, the transport map is the identity.
  cases p
  cases q
  rfl

/-- Helper for Lemma 15.94.1: precomposing with `eqToHom` is proof-irrelevant. -/
private theorem principalPower_eqToHom_comp_eq
    {C : Type*} [Category C] {X Y Z : C} (p q : X = Y) (f : Y ⟶ Z) :
    eqToHom p ≫ f = eqToHom q ≫ f := by
  -- Proof comment: once both source equalities are literal, the transport map is the identity.
  cases p
  cases q
  rfl

/-- Helper for Lemma 15.94.1: applying `single₀` to a transported quotient module map gives the
corresponding transport in `D(A)`. -/
private theorem principalPower_single0_map_eqToHom
    {M N : ModuleCat A} (h : M = N) :
    (single₀).map (eqToHom h) =
      eqToHom (congrArg (fun X ↦ (single₀).obj X) h) := by
  -- Proof comment: once the module equality is literal, both sides are the identity on the same
  -- degree-zero single object.
  -- Route correction: separate the strict `single₀` transport from the
  -- `singleFunctorIsoCompQ` bridge; after `h = rfl`, both sides are literally `𝟙`.
  cases h
  simp

/-- Helper for Lemma 15.94.1: after passing a transported module map through `singleCpx₀` and the
derived localization functor, the residual transport is exactly the naturality square of
`singleFunctorIsoCompQ.inv`. -/
private theorem principalPower_single0_map_eqToHom_via_singleFunctorIsoCompQ
    {M N : ModuleCat A} (h : M = N) :
    DerivedCategory.Q.map ((singleCpx₀).map (eqToHom h)) ≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app N).inv =
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app M).inv ≫
      eqToHom (congrArg (fun X : ModuleCat A ↦ (single₀).obj X) h) := by
  -- Proof comment: the requested whiskered transport is not a new calculation; it is exactly the
  -- inverse naturality identity of the canonical comparison between `Q ⋙ singleCpx₀` and
  -- `single₀`.
  calc
    DerivedCategory.Q.map ((singleCpx₀).map (eqToHom h)) ≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app N).inv =
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app M).inv ≫
        (single₀).map (eqToHom h) := by
          simpa using
            ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).inv.naturality
              (eqToHom h))
    _ =
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app M).inv ≫
        eqToHom (congrArg (fun X : ModuleCat A ↦ (single₀).obj X) h) := by
          rw [principalPower_single0_map_eqToHom]

/-- Helper for Lemma 15.94.1: after passing through `singleCpx₀` and `Q`, the module-level
quotient transport becomes the `eqToIso` normalization used in
`principalPowerQuotientStageIso`. -/
private theorem principalPowerQuotientStep_transport_under_owner_stage_derived
    (f : A) (n : ℕ) :
    (single₀).map (principalPowerQuotientStep f n) ≫
      (eqToIso (principalPowerSingletonQuotientDerived_eq f n)).inv =
    (eqToIso (principalPowerSingletonQuotientDerived_eq f (n + 1))).inv ≫
      (single₀).map (koszulPowerQuotientStep (fun _ : Fin 1 ↦ f) n) := by
  -- Proof comment: transport the strict `ModuleCat` square directly through `single₀`, so the
  -- only remaining identifications are the canonical stage equalities.
  -- Route correction: keep the `singleFunctorIsoCompQ` bridge out of this lemma; it belongs in
  -- the final reassociation for `principalPowerQuotientStageIso_inv_step`.
  have hmap :
      (single₀).map
          (principalPowerQuotientStep f n ≫
            eqToHom (principalPowerQuotientModule_eq_owner_stage f n)) =
        (single₀).map
          (eqToHom (principalPowerQuotientModule_eq_owner_stage f (n + 1)) ≫
            koszulPowerQuotientStep (fun _ : Fin 1 ↦ f) n) := by
    exact congrArg (fun φ ↦ (single₀).map φ)
      (principalPowerQuotientStep_transport_under_owner_stage f n)
  have hderived :
      principalPowerSingletonQuotientDerived_eq f n =
        (congrArg
          (fun X : ModuleCat A ↦ (single₀).obj X)
          (principalPowerQuotientModule_eq_owner_stage f n)).symm := by
    -- Proof comment: both equalities express the same singleton-stage identification in `D(A)`.
    exact Subsingleton.elim _ _
  have hderived_succ :
      principalPowerSingletonQuotientDerived_eq f (n + 1) =
        (congrArg
          (fun X : ModuleCat A ↦ (single₀).obj X)
          (principalPowerQuotientModule_eq_owner_stage f (n + 1))).symm := by
    -- Proof comment: the successor stage uses the identical quotient-to-owner equality pattern.
    exact Subsingleton.elim _ _
  simpa [Functor.map_comp, principalPower_single0_map_eqToHom, hderived, hderived_succ] using hmap

/-- Helper for Lemma 15.94.1: after passing to `D(A)`, the principal-power quotient successor map
still commutes with the quotient-stage transport and the canonical `singleFunctorIsoCompQ`
bridge. -/
private theorem principalPowerQuotientStageIso_inv_step
    (f : A) (n : ℕ) :
    DerivedCategory.Q.map ((singleCpx₀).map (principalPowerQuotientStep f n)) ≫
      (principalPowerQuotientStageIso f n).inv =
    (principalPowerQuotientStageIso f (n + 1)).inv ≫
      Qtower(f).map (homOfLE (Nat.le_succ n)).op := by
  -- Proof comment: the quotient-stage isomorphism is exactly the derived transport into the
  -- singleton quotient owner, followed by the canonical `singleFunctorIsoCompQ` bridge.
  -- Route correction: once the owner transport is localized, the remaining bridge is purely the
  -- functoriality of `singleFunctorIsoCompQ.inv`.
  have hsingle :
      DerivedCategory.Q.map ((singleCpx₀).map (principalPowerQuotientStep f n)) ≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
          (principalPowerQuotientModule f (n + 1))).inv =
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
          (principalPowerQuotientModule f (n + 2))).inv ≫
        (single₀).map (principalPowerQuotientStep f n) := by
    -- Proof comment: naturality of `singleFunctorIsoCompQ.inv` isolates the residual `Q`-image
    -- of the strict single-complex map.
    simpa using
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).inv.naturality
        (principalPowerQuotientStep f n))
  have htransport :
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
          (principalPowerQuotientModule f (n + 2))).inv ≫
        ((single₀).map (principalPowerQuotientStep f n) ≫
          (eqToIso (principalPowerSingletonQuotientDerived_eq f n)).inv) =
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
          (principalPowerQuotientModule f (n + 2))).inv ≫
        ((eqToIso (principalPowerSingletonQuotientDerived_eq f (n + 1))).inv ≫
          (single₀).map (koszulPowerQuotientStep (fun _ : Fin 1 ↦ f) n)) := by
    -- Proof comment: once the `Q`-bridge is peeled off, the remaining square is exactly the
    -- localized owner-stage transport.
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
            (principalPowerQuotientModule f (n + 2))).inv ≫ k)
        (principalPowerQuotientStep_transport_under_owner_stage_derived f n)
  have hstart :
      DerivedCategory.Q.map ((singleCpx₀).map (principalPowerQuotientStep f n)) ≫
          (principalPowerQuotientStageIso f n).inv =
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
            (principalPowerQuotientModule f (n + 2))).inv ≫
          ((single₀).map (principalPowerQuotientStep f n) ≫
            (eqToIso (principalPowerSingletonQuotientDerived_eq f n)).inv) := by
    calc
      DerivedCategory.Q.map ((singleCpx₀).map (principalPowerQuotientStep f n)) ≫
          (principalPowerQuotientStageIso f n).inv =
        (DerivedCategory.Q.map ((singleCpx₀).map (principalPowerQuotientStep f n)) ≫
            ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
              (principalPowerQuotientModule f (n + 1))).inv) ≫
          (eqToIso (principalPowerSingletonQuotientDerived_eq f n)).inv := by
            simp [principalPowerQuotientStageIso, Category.assoc]
      _ =
        (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
            (principalPowerQuotientModule f (n + 2))).inv ≫
          (single₀).map (principalPowerQuotientStep f n)) ≫
            (eqToIso (principalPowerSingletonQuotientDerived_eq f n)).inv := by
              rw [hsingle]
              rfl
      _ =
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
            (principalPowerQuotientModule f (n + 2))).inv ≫
          ((single₀).map (principalPowerQuotientStep f n) ≫
            (eqToIso (principalPowerSingletonQuotientDerived_eq f n)).inv) := by
              simp [Category.assoc]
  have hfinish :
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
          (principalPowerQuotientModule f (n + 2))).inv ≫
        ((eqToIso (principalPowerSingletonQuotientDerived_eq f (n + 1))).inv ≫
          (single₀).map (koszulPowerQuotientStep (fun _ : Fin 1 ↦ f) n)) =
      (principalPowerQuotientStageIso f (n + 1)).inv ≫
        Qtower(f).map (homOfLE (Nat.le_succ n)).op := by
    -- Proof comment: the target is exactly the expanded successor-side stage isomorphism.
    simp [principalPowerQuotientStageIso, principalPowerQuotientTower_step_map, Category.assoc]
  exact hstart.trans (htransport.trans hfinish)

private theorem principalPowerTorsionLift_condition (f : A) (c : ℕ) :
    (A[f ^ c] : Submodule A A) ≤ LinearMap.ker (LinearMap.mulRight A (f ^ c)) := by
  intro x hx
  rw [Submodule.mem_torsionBy_iff] at hx
  change x * f ^ c = 0
  simpa [smul_eq_mul, mul_comm] using hx

/-- The quotient module `A / A[f^c]`. -/
private abbrev principalPowerTorsionQuotientModule (f : A) (c : ℕ) : ModuleCat A :=
  ModuleCat.of A (A ⧸ (A[f ^ c] : Submodule A A))

/-- The map `A / A[f^c] ⟶ A` given by multiplication by `f^c`. -/
private abbrev principalPowerTorsionLift (f : A) (c : ℕ) :
    principalPowerTorsionQuotientModule f c ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom <|
    Submodule.liftQ
      (A[f ^ c] : Submodule A A)
      (LinearMap.mulRight A (f ^ c))
      (principalPowerTorsionLift_condition f c)

private theorem principalPowerTorsionTopMap_condition (f : A) (c n : ℕ) :
    (A[f ^ c] : Submodule A A) ≤ LinearMap.ker (LinearMap.mulRight A (f ^ (c + n + 1))) := by
  intro x hx
  rw [Submodule.mem_torsionBy_iff] at hx
  change x * f ^ (c + n + 1) = 0
  have hx' : x * f ^ c = 0 := by
    simpa [smul_eq_mul, mul_comm] using hx
  calc
    x * f ^ (c + n + 1) = x * (f ^ c * f ^ (n + 1)) := by
      rw [show c + n + 1 = c + (n + 1) by omega, pow_add]
    _ = (x * f ^ c) * f ^ (n + 1) := by ac_rfl
    _ = 0 := by rw [hx', zero_mul]

private abbrev principalPowerTorsionTopMap (f : A) (c n : ℕ) :
    principalPowerTorsionQuotientModule f c ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom <|
    Submodule.liftQ
      (A[f ^ c] : Submodule A A)
      (LinearMap.mulRight A (f ^ (c + n + 1)))
      (principalPowerTorsionTopMap_condition f c n)

private abbrev principalPowerTorsionComplex (f : A) (c n : ℕ) :
    CochainComplex (ModuleCat A) ℤ :=
  CochainComplex.mappingCone ((singleCpx₀).map (principalPowerTorsionTopMap f c n))

private theorem principalPowerQuotientToKoszulRoof_comm (f : A) (c n : ℕ) :
    CommSq
      ((singleCpx₀).map (principalPowerTorsionTopMap f c n))
      ((singleCpx₀).map (principalPowerTorsionLift f c))
      (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
      ((singleCpx₀).map (principalPowerKoszulMap f (n + 1))) := by
  -- The two routes are both multiplication by `f^(c+n+1)` on the quotient `A / A[f^c]`.
  have hmul :
      principalPowerTorsionTopMap f c n =
        principalPowerTorsionLift f c ≫ principalPowerKoszulMap f (n + 1) := by
    rw [principalPowerTorsionTopMap, principalPowerTorsionLift, principalPowerKoszulMap]
    change
      ModuleCat.ofHom
          (Submodule.liftQ (A[f ^ c] : Submodule A A)
            (LinearMap.mulRight A (f ^ (c + n + 1)))
            (principalPowerTorsionTopMap_condition f c n)) =
        ModuleCat.ofHom
          ((LinearMap.mulRight A (f ^ (n + 1))).comp
            (Submodule.liftQ (A[f ^ c] : Submodule A A)
              (LinearMap.mulRight A (f ^ c))
              (principalPowerTorsionLift_condition f c)))
    congr 1
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    change a * f ^ (c + n + 1) = (a * f ^ c) * f ^ (n + 1)
    calc
      a * f ^ (c + n + 1) = a * (f ^ c * f ^ (n + 1)) := by
        rw [show c + n + 1 = c + (n + 1) by omega, pow_add]
      _ = (a * f ^ c) * f ^ (n + 1) := by ac_rfl
  refine CommSq.mk ?_
  -- Apply the degree-zero single-complex functor to the module-level equality.
  simpa [Functor.map_comp] using congrArg (fun φ ↦ (singleCpx₀).map φ) hmul

private abbrev principalPowerQuotientToKoszulRoofMap (f : A) (c n : ℕ) :
    principalPowerTorsionComplex f c n ⟶ principalPowerKoszulModelComplex f (n + 1) :=
  CochainComplex.mappingCone.map
    ((singleCpx₀).map (principalPowerTorsionTopMap f c n))
    ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
    ((singleCpx₀).map (principalPowerTorsionLift f c))
    (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
    (principalPowerQuotientToKoszulRoof_comm f c n).w

private theorem principalPowerTorsionTopMap_comp_quotientMk (f : A) (c n : ℕ) :
    principalPowerTorsionTopMap f c n ≫ principalPowerQuotientMk f (c + n + 1) = 0 := by
  -- Evaluate on quotient representatives and use that `f^(c+n+1)` generates the target ideal.
  rw [principalPowerTorsionTopMap, principalPowerQuotientMk]
  change
    ModuleCat.ofHom
        (((Ideal.Quotient.mkₐ A (principalPowerIdeal f (c + n + 1))).toLinearMap).comp
          (Submodule.liftQ (A[f ^ c] : Submodule A A)
            (LinearMap.mulRight A (f ^ (c + n + 1)))
            (principalPowerTorsionTopMap_condition f c n))) = 0
  change
    ModuleCat.ofHom
        (((Ideal.Quotient.mkₐ A (principalPowerIdeal f (c + n + 1))).toLinearMap).comp
          (Submodule.liftQ (A[f ^ c] : Submodule A A)
            (LinearMap.mulRight A (f ^ (c + n + 1)))
            (principalPowerTorsionTopMap_condition f c n))) =
      ModuleCat.ofHom 0
  congr 1
  apply LinearMap.ext
  intro x
  refine Quotient.inductionOn x ?_
  intro a
  change Ideal.Quotient.mk (principalPowerIdeal f (c + n + 1)) (a * f ^ (c + n + 1)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  rw [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

private theorem singleCpx_principalPowerTorsionTopMap_comp_quotientMk (f : A) (c n : ℕ) :
    (singleCpx₀).map (principalPowerTorsionTopMap f c n) ≫
        (singleCpx₀).map (principalPowerQuotientMk f (c + n + 1)) =
      0 := by
  simpa using
    congrArg
      (fun φ ↦ (singleCpx₀).map φ)
      (principalPowerTorsionTopMap_comp_quotientMk f c n)

private theorem principalPowerTorsionComplexToQuotient_desc_condition (f : A) (c n : ℕ) :
    δ (-1) 0
        (0 :
          Cochain
            ((singleCpx₀).obj (principalPowerTorsionQuotientModule f c))
            ((singleCpx₀).obj (principalPowerQuotientModule f (c + n + 1)))
            (-1)) =
      Cochain.ofHom
        (((singleCpx₀).map (principalPowerTorsionTopMap f c n)) ≫
          (singleCpx₀).map (principalPowerQuotientMk f (c + n + 1))) := by
  rw [δ_zero]
  simp [singleCpx_principalPowerTorsionTopMap_comp_quotientMk]

private def principalPowerTorsionComplexToQuotientComplexMap (f : A) (c n : ℕ) :
    principalPowerTorsionComplex f c n ⟶
      (singleCpx₀).obj (principalPowerQuotientModule f (c + n + 1)) :=
  CochainComplex.mappingCone.desc
    ((singleCpx₀).map (principalPowerTorsionTopMap f c n))
    0
    ((singleCpx₀).map (principalPowerQuotientMk f (c + n + 1)))
    (principalPowerTorsionComplexToQuotient_desc_condition f c n)

/-- Helper for Lemma 15.94.1: the stabilized comparison
`A / A[f^c] \xrightarrow{\cdot f^{c+n+1}} A \to A / (f^{c+n+1})`
packaged as a short complex of degree-zero single cochain complexes. -/
private abbrev principalPowerStableShortComplex (f : A) (c n : ℕ) :
    ShortComplex (CochainComplex (ModuleCat A) ℤ) :=
  (ShortComplex.mk
      (principalPowerTorsionTopMap f c n)
      (principalPowerQuotientMk f (c + n + 1))
      (principalPowerTorsionTopMap_comp_quotientMk f c n)).map singleCpx₀

/-- Helper for Lemma 15.94.1: multiplication by `f` preserves the stabilized torsion submodule
`A[f^c]`, so it descends to the quotient `A / A[f^c]`. -/
private theorem principalPowerTorsionQuotientStep_condition (f : A) (c : ℕ) :
    (A[f ^ c] : Submodule A A) ≤
      Submodule.comap (LinearMap.mulRight A f) (A[f ^ c] : Submodule A A) := by
  -- An element annihilated by `f^c` stays annihilated after one more multiplication by `f`.
  intro x hx
  rw [Submodule.mem_comap]
  rw [Submodule.mem_torsionBy_iff] at hx ⊢
  have hx' : x * f ^ c = 0 := by
    simpa [smul_eq_mul, mul_comm] using hx
  change f ^ c * (LinearMap.mulRight A f x) = 0
  calc
    f ^ c * (LinearMap.mulRight A f x) = (x * f ^ c) * f := by
      simp [LinearMap.mulRight_apply]
      ac_rfl
    _ = 0 := by rw [hx', zero_mul]

/-- Helper for Lemma 15.94.1: multiplication by `f` on `A` induces the successor endomorphism of
the stabilized quotient `A / A[f^c]`. -/
private abbrev principalPowerTorsionQuotientStep (f : A) (c : ℕ) :
    principalPowerTorsionQuotientModule f c ⟶ principalPowerTorsionQuotientModule f c :=
  ModuleCat.ofHom <|
    Submodule.mapQ
      (A[f ^ c] : Submodule A A)
      (A[f ^ c] : Submodule A A)
      (LinearMap.mulRight A f)
      (principalPowerTorsionQuotientStep_condition f c)

/-- Helper for Lemma 15.94.1: on the stabilized roof object, multiplying first by `f` and then by
`f^(c+n+1)` agrees with the next roof map `f^(c+n+2)`. -/
private theorem principalPowerTorsionQuotientStep_comp_topMap (f : A) (c n : ℕ) :
    principalPowerTorsionQuotientStep f c ≫ principalPowerTorsionTopMap f c n =
      principalPowerTorsionTopMap f c (n + 1) := by
  -- Compare both quotient lifts on representatives of `A / A[f^c]`.
  rw [principalPowerTorsionQuotientStep, principalPowerTorsionTopMap, principalPowerTorsionTopMap]
  change
    ModuleCat.ofHom
        ((Submodule.liftQ (A[f ^ c] : Submodule A A)
          (LinearMap.mulRight A (f ^ (c + n + 1)))
          (principalPowerTorsionTopMap_condition f c n)).comp
          (Submodule.mapQ
            (A[f ^ c] : Submodule A A)
            (A[f ^ c] : Submodule A A)
            (LinearMap.mulRight A f)
            (principalPowerTorsionQuotientStep_condition f c))) =
      ModuleCat.ofHom
        (Submodule.liftQ (A[f ^ c] : Submodule A A)
          (LinearMap.mulRight A (f ^ (c + (n + 1) + 1)))
          (principalPowerTorsionTopMap_condition f c (n + 1)))
  congr 1
  apply LinearMap.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro a
  have hmapQ :
      (Submodule.mapQ
          (A[f ^ c] : Submodule A A)
          (A[f ^ c] : Submodule A A)
          (LinearMap.mulRight A f)
          (principalPowerTorsionQuotientStep_condition f c))
        (Submodule.Quotient.mk a) =
        (Submodule.Quotient.mk ((LinearMap.mulRight A f) a) :
          A ⧸ (A[f ^ c] : Submodule A A)) := by
    simpa using
      DFunLike.congr_fun
        (Submodule.mapQ_mkQ
          (A[f ^ c] : Submodule A A)
          (A[f ^ c] : Submodule A A)
          (LinearMap.mulRight A f)) a
  change
    ((Submodule.liftQ (A[f ^ c] : Submodule A A)
      (LinearMap.mulRight A (f ^ (c + n + 1)))
      (principalPowerTorsionTopMap_condition f c n))
      ((Submodule.mapQ
        (A[f ^ c] : Submodule A A)
        (A[f ^ c] : Submodule A A)
        (LinearMap.mulRight A f)
        (principalPowerTorsionQuotientStep_condition f c)) (Submodule.Quotient.mk a))) =
    (Submodule.liftQ (A[f ^ c] : Submodule A A)
      (LinearMap.mulRight A (f ^ (c + (n + 1) + 1)))
      (principalPowerTorsionTopMap_condition f c (n + 1)))
      (Submodule.Quotient.mk a)
  rw [hmapQ, Submodule.liftQ_apply, Submodule.liftQ_apply]
  change (a * f) * f ^ (c + n + 1) = a * f ^ (c + (n + 1) + 1)
  calc
    (a * f) * f ^ (c + n + 1) = a * (f ^ (c + n + 1) * f) := by ac_rfl
    _ = a * f ^ (c + n + 2) := by rw [← pow_succ]
    _ = a * f ^ (c + (n + 1) + 1) := by
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Helper for Lemma 15.94.1: the stabilized short complexes carry a successor morphism whose
left component is multiplication by `f` on `A / A[f^c]`, middle component is the identity on `A`,
and right component is the quotient transition
`A / (f^(c+n+2)) ⟶ A / (f^(c+n+1))`. -/
private abbrev principalPowerStableShortComplex_step (f : A) (c n : ℕ) :
    principalPowerStableShortComplex f c (n + 1) ⟶
      principalPowerStableShortComplex f c n :=
  ShortComplex.Hom.mk
    ((singleCpx₀).map (principalPowerTorsionQuotientStep f c))
    (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
    ((singleCpx₀).map (principalPowerQuotientStep f (c + n)))
    (by
      -- The left square is multiplication-by-`f` followed by multiplication-by-`f^(c+n+1)`.
      simpa [Functor.map_comp] using
        congrArg
          (fun φ ↦ (singleCpx₀).map φ)
          (principalPowerTorsionQuotientStep_comp_topMap f c n))
    (by
      -- The right square is the universal compatibility of quotient maps with factor maps.
      simpa [Functor.map_comp] using
        congrArg
          (fun φ ↦ (singleCpx₀).map φ)
          (principalPowerQuotientMk_step_naturality f (c + n)).symm)

/-- Helper for Lemma 15.94.1: the stabilized cone map to the quotient complex is exactly the
canonical `mappingCone.descShortComplex` morphism for the stable short complex. -/
private theorem principalPowerTorsionComplexToQuotientComplexMap_eq_descShortComplex
    (f : A) (c n : ℕ) :
    principalPowerTorsionComplexToQuotientComplexMap f c n =
      CochainComplex.mappingCone.descShortComplex
        (principalPowerStableShortComplex f c n) := by
  -- Both sides are the same `mappingCone.desc` presentation of the stabilized quotient map.
  rfl

/-- Helper for Lemma 15.94.1: a stable equality `A[f^∞] = A[f^c]` identifies every later
principal-power torsion stage `A[f^(c+n+1)]` with the stage `A[f^c]`. -/
private theorem principalPowerTorsionStage_eq_of_stable
    (f : A) (c n : ℕ)
    (hstable : (A[f^∞] : Submodule A A) = (A[f ^ c] : Submodule A A)) :
    (A[f ^ (c + n + 1)] : Submodule A A) = (A[f ^ c] : Submodule A A) := by
  -- Translate the global stabilization hypothesis into eventual constancy of the finite stages.
  have hstages := (fPowerTorsion_eq_iff_stabilizesFrom f c).mp hstable
  -- The stage `c + n + 1` lies beyond `c`, so the stabilized value is exactly `A[f^c]`.
  simpa [Nat.add_assoc] using hstages (c + n + 1) (Nat.le_add_right c (n + 1))

/-- Helper for Lemma 15.94.1: once the `f`-power torsion stabilizes at stage `c`, the module
sequence
`A / A[f^c] \xrightarrow{\cdot f^{c+n+1}} A \to A / (f^{c+n+1})`
is short exact. -/
private theorem principalPowerTorsionShortExact_of_stable
    (f : A) (c n : ℕ)
    (hstage : (A[f ^ (c + n + 1)] : Submodule A A) = (A[f ^ c] : Submodule A A)) :
    (ShortComplex.mk
        (principalPowerTorsionTopMap f c n)
        (principalPowerQuotientMk f (c + n + 1))
        (principalPowerTorsionTopMap_comp_quotientMk f c n)).ShortExact := by
  let S : ShortComplex (ModuleCat A) :=
    ShortComplex.mk
      (principalPowerTorsionTopMap f c n)
      (principalPowerQuotientMk f (c + n + 1))
      (principalPowerTorsionTopMap_comp_quotientMk f c n)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- The image of multiplication by `f^(c+n+1)` is exactly the kernel of the quotient map.
    change S.Exact
    rw [S.moduleCat_exact_iff_range_eq_ker]
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      refine LinearMap.mem_ker.mpr ?_
      refine Quotient.inductionOn' q ?_
      intro a
      change Ideal.Quotient.mk (principalPowerIdeal f (c + n + 1)) (a * f ^ (c + n + 1)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      rw [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · intro hx
      change Ideal.Quotient.mk (principalPowerIdeal f (c + n + 1)) x = 0 at hx
      rw [Ideal.Quotient.eq_zero_iff_mem] at hx
      rw [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow] at hx
      rcases Ideal.mem_span_singleton'.mp hx with ⟨a, ha⟩
      refine LinearMap.mem_range.mpr ?_
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      simpa [principalPowerTorsionTopMap, Submodule.liftQ_apply] using ha
  · -- Stabilization identifies the kernel of the left map with zero, so the left term injects.
    refine (ModuleCat.mono_iff_injective _).2 ?_
    change Function.Injective ⇑(ModuleCat.Hom.hom (principalPowerTorsionTopMap f c n))
    exact
      (LinearMap.ker_eq_bot.mp <|
        LinearMap.ker_eq_bot'.mpr <|
          fun q ↦ by
            refine Quotient.inductionOn' q ?_
            intro a hq
            change Submodule.Quotient.mk a = 0
            have ha_zero : a * f ^ (c + n + 1) = 0 := by
              simpa [principalPowerTorsionTopMap, Submodule.liftQ_apply] using hq
            have ha_mem :
                a ∈ (A[f ^ (c + n + 1)] : Submodule A A) := by
              rw [Submodule.mem_torsionBy_iff]
              simpa [smul_eq_mul, mul_comm] using ha_zero
            rw [hstage] at ha_mem
            change Submodule.Quotient.mk a = Submodule.Quotient.mk (0 : A)
            exact (Submodule.Quotient.eq (A[f ^ c] : Submodule A A)).2 (by simpa using ha_mem))
  · -- Every quotient class is represented by some element of `A`, so the quotient map is onto.
    refine (ModuleCat.epi_iff_surjective _).2 ?_
    intro q
    refine Quotient.inductionOn' q ?_
    intro a
    refine ⟨a, ?_⟩
    rfl

private theorem principalPowerTorsionComplexToQuotientComplexMap_quasiIso
    (f : A) (c n : ℕ)
    (hstage : (A[f ^ (c + n + 1)] : Submodule A A) = (A[f ^ c] : Submodule A A)) :
    QuasiIso (principalPowerTorsionComplexToQuotientComplexMap f c n) := by
  -- Transport the stabilized module short exact sequence to cochain complexes concentrated in
  -- degree `0`, then invoke the owner quasi-isomorphism for `mappingCone.descShortComplex`.
  have hshort :
      (principalPowerStableShortComplex f c n).ShortExact := by
    let F := HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℤ) (0 : ℤ)
    have hmapped :=
      (principalPowerTorsionShortExact_of_stable f c n hstage).map_of_exact F
    -- The local wrapper is exactly the image of the stabilized module short complex under the
    -- degree-zero single-complex functor.
    simpa [principalPowerStableShortComplex, F, CochainComplex.singleFunctor] using hmapped
  -- The comparison morphism was already written in exactly this owner normal form.
  simpa [principalPowerTorsionComplexToQuotientComplexMap_eq_descShortComplex] using
    CochainComplex.mappingCone.quasiIso_descShortComplex hshort

private instance principalPowerTorsionComplexToQuotientComplexMap_isIso
    (f : A) (c n : ℕ)
    (hstage : (A[f ^ (c + n + 1)] : Submodule A A) = (A[f ^ c] : Submodule A A)) :
    IsIso (DerivedCategory.Q.map (principalPowerTorsionComplexToQuotientComplexMap f c n)) := by
  letI : QuasiIso (principalPowerTorsionComplexToQuotientComplexMap f c n) :=
    principalPowerTorsionComplexToQuotientComplexMap_quasiIso f c n hstage
  infer_instance

private abbrev principalPowerTorsionComplexToQuotientIso (f : A) (c n : ℕ) :
    (hstage : (A[f ^ (c + n + 1)] : Submodule A A) = (A[f ^ c] : Submodule A A)) →
    DerivedCategory.Q.obj (principalPowerTorsionComplex f c n) ≅
      DerivedCategory.Q.obj ((singleCpx₀).obj (principalPowerQuotientModule f (c + n + 1))) :=
  fun hstage ↦
    letI : IsIso (DerivedCategory.Q.map (principalPowerTorsionComplexToQuotientComplexMap f c n)) :=
      principalPowerTorsionComplexToQuotientComplexMap_isIso f c n hstage
    asIso (DerivedCategory.Q.map (principalPowerTorsionComplexToQuotientComplexMap f c n))

/-- The stagewise reverse comparison map of Lemma 15.94.1, indexed so that stage `0` corresponds
to the textbook exponent `n = 1`. It is the source-facing map
`A/(f^(c + n)) ⟶ (A \xrightarrow{f^n} A)` obtained from the Stacks proof diagram with
`A / A[f^c]` as an intermediate roof object. -/
private abbrev principalPowerQuotientToKoszulStable
    (f : A) (c n : ℕ)
    (hstable : (A[f^∞] : Submodule A A) = (A[f ^ c] : Submodule A A)) :
    Qtower(f).obj (op (c + n)) ⟶ Ktower(f).obj (op n) :=
  (principalPowerQuotientStageIso f (c + n)).hom ≫
      (principalPowerTorsionComplexToQuotientIso f c n
        (principalPowerTorsionStage_eq_of_stable f c n hstable)).symm.hom ≫
        DerivedCategory.Q.map (principalPowerQuotientToKoszulRoofMap f c n) ≫
          (principalPowerKoszulStageIso f n).inv

/-- Helper for Lemma 15.94.1: the stabilized cone map to the quotient complex commutes with the
successor morphism of the stabilized short complexes. -/
private theorem principalPowerTorsionComplexToQuotientComplexMap_step_naturality
    (f : A) (c n : ℕ) :
    CochainComplex.mappingCone.map
        ((singleCpx₀).map (principalPowerTorsionTopMap f c (n + 1)))
        ((singleCpx₀).map (principalPowerTorsionTopMap f c n))
        ((singleCpx₀).map (principalPowerTorsionQuotientStep f c))
        (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
        (principalPowerStableShortComplex_step f c n).comm₁₂.symm ≫
      principalPowerTorsionComplexToQuotientComplexMap f c n =
        principalPowerTorsionComplexToQuotientComplexMap f c (n + 1) ≫
          (singleCpx₀).map (principalPowerQuotientStep f (c + n)) := by
  -- The stabilized quotient comparison is already a `descShortComplex`, so the owner naturality
  -- theorem applies verbatim.
  simpa [principalPowerTorsionComplexToQuotientComplexMap_eq_descShortComplex] using
    CochainComplex.mappingCone.descShortComplex_naturality
      (principalPowerStableShortComplex_step f c n)

/-- Helper for Lemma 15.94.1: after localizing, the inverse of the stabilized quotient
quasi-isomorphism transports the successor map on quotient stages to the explicit cone successor
map on the roof complex. -/
private theorem principalPowerTorsionComplexToQuotientIso_symm_step
    (f : A) (c n : ℕ)
    (hstable : (A[f^∞] : Submodule A A) = (A[f ^ c] : Submodule A A)) :
    DerivedCategory.Q.map ((singleCpx₀).map (principalPowerQuotientStep f (c + n))) ≫
      (principalPowerTorsionComplexToQuotientIso f c n
        (principalPowerTorsionStage_eq_of_stable f c n hstable)).symm.hom =
    (principalPowerTorsionComplexToQuotientIso f c (n + 1)
      (principalPowerTorsionStage_eq_of_stable f c (n + 1) hstable)).symm.hom ≫
      DerivedCategory.Q.map
        (CochainComplex.mappingCone.map
          ((singleCpx₀).map (principalPowerTorsionTopMap f c (n + 1)))
          ((singleCpx₀).map (principalPowerTorsionTopMap f c n))
          ((singleCpx₀).map (principalPowerTorsionQuotientStep f c))
          (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
          (principalPowerStableShortComplex_step f c n).comm₁₂.symm) := by
  -- Proof comment: localize the strict `descShortComplex` square and then cancel the two
  -- quotient-stage isomorphisms on the right and left.
  let eₙ :=
    principalPowerTorsionComplexToQuotientIso f c n
      (principalPowerTorsionStage_eq_of_stable f c n hstable)
  let eₙ₁ :=
    principalPowerTorsionComplexToQuotientIso f c (n + 1)
      (principalPowerTorsionStage_eq_of_stable f c (n + 1) hstable)
  have hchain :
      DerivedCategory.Q.map
          (CochainComplex.mappingCone.map
            ((singleCpx₀).map (principalPowerTorsionTopMap f c (n + 1)))
            ((singleCpx₀).map (principalPowerTorsionTopMap f c n))
            ((singleCpx₀).map (principalPowerTorsionQuotientStep f c))
            (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
            (principalPowerStableShortComplex_step f c n).comm₁₂.symm) ≫
        eₙ.hom =
      eₙ₁.hom ≫
        DerivedCategory.Q.map ((singleCpx₀).map (principalPowerQuotientStep f (c + n))) := by
    -- Proof comment: this is the already-isolated chain-level naturality square, lifted by `Q`.
    simpa [eₙ, eₙ₁, principalPowerTorsionComplexToQuotientIso, Category.assoc] using
      congrArg DerivedCategory.Q.map
        (principalPowerTorsionComplexToQuotientComplexMap_step_naturality f c n)
  apply (cancel_mono eₙ.hom).1
  calc
    (DerivedCategory.Q.map ((singleCpx₀).map (principalPowerQuotientStep f (c + n))) ≫
          eₙ.symm.hom) ≫
        eₙ.hom =
      DerivedCategory.Q.map ((singleCpx₀).map (principalPowerQuotientStep f (c + n))) := by
        simp [eₙ, Category.assoc]
    _ =
      eₙ₁.symm.hom ≫
        (DerivedCategory.Q.map
            (CochainComplex.mappingCone.map
              ((singleCpx₀).map (principalPowerTorsionTopMap f c (n + 1)))
              ((singleCpx₀).map (principalPowerTorsionTopMap f c n))
              ((singleCpx₀).map (principalPowerTorsionQuotientStep f c))
              (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
              (principalPowerStableShortComplex_step f c n).comm₁₂.symm) ≫
          eₙ.hom) := by
            simpa [Category.assoc] using
              (congrArg (fun t ↦ eₙ₁.symm.hom ≫ t) hchain).symm
    _ =
      (eₙ₁.symm.hom ≫
          DerivedCategory.Q.map
            (CochainComplex.mappingCone.map
              ((singleCpx₀).map (principalPowerTorsionTopMap f c (n + 1)))
              ((singleCpx₀).map (principalPowerTorsionTopMap f c n))
              ((singleCpx₀).map (principalPowerTorsionQuotientStep f c))
              (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
              (principalPowerStableShortComplex_step f c n).comm₁₂.symm)) ≫
        eₙ.hom := by
          simp [Category.assoc]

/-- Helper for Lemma 15.94.1: multiplication by `f` on the stabilized quotient followed by the
lift `A / A[f^c] ⟶ A` agrees with first lifting and then multiplying by `f`. -/
private theorem principalPowerTorsionQuotientStep_comp_lift (f : A) (c : ℕ) :
    principalPowerTorsionQuotientStep f c ≫ principalPowerTorsionLift f c =
      principalPowerTorsionLift f c ≫ principalPowerKoszulMap f 1 := by
  -- Proof comment: both quotient lifts send the class of `a` to `a * f^(c+1)` in `A`.
  rw [principalPowerTorsionQuotientStep, principalPowerTorsionLift, principalPowerKoszulMap]
  change
    ModuleCat.ofHom
        ((Submodule.liftQ (A[f ^ c] : Submodule A A)
          (LinearMap.mulRight A (f ^ c))
          (principalPowerTorsionLift_condition f c)).comp
          (Submodule.mapQ
            (A[f ^ c] : Submodule A A)
            (A[f ^ c] : Submodule A A)
            (LinearMap.mulRight A f)
            (principalPowerTorsionQuotientStep_condition f c))) =
      ModuleCat.ofHom
        ((LinearMap.mulRight A (f ^ 1)).comp
          (Submodule.liftQ (A[f ^ c] : Submodule A A)
            (LinearMap.mulRight A (f ^ c))
            (principalPowerTorsionLift_condition f c)))
  congr 1
  apply LinearMap.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro a
  have hmapQ :
      (Submodule.mapQ
          (A[f ^ c] : Submodule A A)
          (A[f ^ c] : Submodule A A)
          (LinearMap.mulRight A f)
          (principalPowerTorsionQuotientStep_condition f c))
        (Submodule.Quotient.mk a) =
        (Submodule.Quotient.mk ((LinearMap.mulRight A f) a) :
          A ⧸ (A[f ^ c] : Submodule A A)) := by
    simpa using
      DFunLike.congr_fun
        (Submodule.mapQ_mkQ
          (A[f ^ c] : Submodule A A)
          (A[f ^ c] : Submodule A A)
          (LinearMap.mulRight A f)) a
  change
    ((Submodule.liftQ (A[f ^ c] : Submodule A A)
      (LinearMap.mulRight A (f ^ c))
      (principalPowerTorsionLift_condition f c))
      ((Submodule.mapQ
        (A[f ^ c] : Submodule A A)
        (A[f ^ c] : Submodule A A)
        (LinearMap.mulRight A f)
        (principalPowerTorsionQuotientStep_condition f c)) (Submodule.Quotient.mk a))) =
    (LinearMap.mulRight A (f ^ 1))
      ((Submodule.liftQ (A[f ^ c] : Submodule A A)
        (LinearMap.mulRight A (f ^ c))
        (principalPowerTorsionLift_condition f c))
        (Submodule.Quotient.mk a))
  rw [hmapQ, Submodule.liftQ_apply, Submodule.liftQ_apply]
  simp [LinearMap.mulRight_apply, pow_one]
  ac_rfl

/-- Helper for Lemma 15.94.1: the roof maps over `A / A[f^c]` commute with the successor
transition from stage `n + 1` to stage `n`. -/
private theorem principalPowerQuotientToKoszulRoofMap_step_naturality
    (f : A) (c n : ℕ) :
    CochainComplex.mappingCone.map
        ((singleCpx₀).map (principalPowerTorsionTopMap f c (n + 1)))
        ((singleCpx₀).map (principalPowerTorsionTopMap f c n))
        ((singleCpx₀).map (principalPowerTorsionQuotientStep f c))
        (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
        (principalPowerStableShortComplex_step f c n).comm₁₂.symm ≫
      principalPowerQuotientToKoszulRoofMap f c n =
        principalPowerQuotientToKoszulRoofMap f c (n + 1) ≫
          CochainComplex.mappingCone.map
            ((singleCpx₀).map (principalPowerKoszulMap f (n + 2)))
            ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
            ((singleCpx₀).map (principalPowerKoszulMap f 1))
            (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
            (principalPowerForwardShortComplex_step f n).comm₁₂.symm := by
  -- Flatten both composites to the same `mappingCone.map`, so only the top-left square over the
  -- roof object remains to be compared.
  have hlift_step :
      (singleCpx₀).map (principalPowerTorsionQuotientStep f c) ≫
        (singleCpx₀).map (principalPowerTorsionLift f c) =
      (singleCpx₀).map (principalPowerTorsionLift f c) ≫
        (singleCpx₀).map (principalPowerKoszulMap f 1) := by
    -- Transport the module-level compatibility `·f` across the degree-zero single-complex
    -- functor before comparing the two cone composites.
    simpa [Functor.map_comp] using
      congrArg
        (fun φ ↦ (singleCpx₀).map φ)
        (principalPowerTorsionQuotientStep_comp_lift f c)
  have hleft_comp_comm :
      ((singleCpx₀).map (principalPowerTorsionTopMap f c (n + 1))) ≫
          𝟙 ((singleCpx₀).obj (ModuleCat.of A A)) =
        ((singleCpx₀).map (principalPowerTorsionQuotientStep f c) ≫
            (singleCpx₀).map (principalPowerTorsionLift f c)) ≫
          ((singleCpx₀).map (principalPowerKoszulMap f (n + 1))) := by
    -- The left normalized square is the composite of the stabilized roof square and the
    -- original roof square at stage `n`.
    calc
      ((singleCpx₀).map (principalPowerTorsionTopMap f c (n + 1))) ≫
          𝟙 ((singleCpx₀).obj (ModuleCat.of A A)) =
        ((singleCpx₀).map (principalPowerTorsionQuotientStep f c) ≫
            (singleCpx₀).map (principalPowerTorsionTopMap f c n)) ≫
          𝟙 ((singleCpx₀).obj (ModuleCat.of A A)) := by
            simpa [Category.assoc] using
              reassoc_of% (principalPowerStableShortComplex_step f c n).comm₁₂.symm
      _ =
        ((singleCpx₀).map (principalPowerTorsionQuotientStep f c) ≫
            ((singleCpx₀).map (principalPowerTorsionLift f c) ≫
              (singleCpx₀).map (principalPowerKoszulMap f (n + 1)))) ≫
          𝟙 ((singleCpx₀).obj (ModuleCat.of A A)) := by
            rw [reassoc_of% (principalPowerQuotientToKoszulRoof_comm f c n).w]
      _ =
        ((singleCpx₀).map (principalPowerTorsionQuotientStep f c) ≫
            (singleCpx₀).map (principalPowerTorsionLift f c)) ≫
          ((singleCpx₀).map (principalPowerKoszulMap f (n + 1))) := by
            simp [Category.assoc]
  have hright_comp_comm :
      ((singleCpx₀).map (principalPowerTorsionTopMap f c (n + 1))) ≫
          𝟙 ((singleCpx₀).obj (ModuleCat.of A A)) =
        ((singleCpx₀).map (principalPowerTorsionLift f c) ≫
            (singleCpx₀).map (principalPowerKoszulMap f 1)) ≫
          ((singleCpx₀).map (principalPowerKoszulMap f (n + 1))) := by
    -- The right normalized square is the roof square at stage `n + 1`, followed by the explicit
    -- adjacent-power square on the Koszul side.
    calc
      ((singleCpx₀).map (principalPowerTorsionTopMap f c (n + 1))) ≫
          𝟙 ((singleCpx₀).obj (ModuleCat.of A A)) =
        ((singleCpx₀).map (principalPowerTorsionLift f c) ≫
            (singleCpx₀).map (principalPowerKoszulMap f (n + 2))) ≫
          𝟙 ((singleCpx₀).obj (ModuleCat.of A A)) := by
            rw [(principalPowerQuotientToKoszulRoof_comm f c (n + 1)).w]
            simp [Category.assoc]
      _ =
        ((singleCpx₀).map (principalPowerTorsionLift f c) ≫
            (singleCpx₀).map (principalPowerKoszulMap f 1)) ≫
          ((singleCpx₀).map (principalPowerKoszulMap f (n + 1))) := by
            simp [Category.assoc]
            rw [← reassoc_of% (principalPowerForwardShortComplex_step f n).comm₁₂.symm]
  calc
    CochainComplex.mappingCone.map
        ((singleCpx₀).map (principalPowerTorsionTopMap f c (n + 1)))
        ((singleCpx₀).map (principalPowerTorsionTopMap f c n))
        ((singleCpx₀).map (principalPowerTorsionQuotientStep f c))
        (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
        (principalPowerStableShortComplex_step f c n).comm₁₂.symm ≫
      principalPowerQuotientToKoszulRoofMap f c n =
      CochainComplex.mappingCone.map
        ((singleCpx₀).map (principalPowerTorsionTopMap f c (n + 1)))
        ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
        ((singleCpx₀).map (principalPowerTorsionQuotientStep f c) ≫
          (singleCpx₀).map (principalPowerTorsionLift f c))
        (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
        hleft_comp_comm := by
            simpa [principalPowerQuotientToKoszulRoofMap] using
              (CochainComplex.mappingCone.map_comp
                (φ₁ := ((singleCpx₀).map (principalPowerTorsionTopMap f c (n + 1))))
                (φ₂ := ((singleCpx₀).map (principalPowerTorsionTopMap f c n)))
                (φ₃ := ((singleCpx₀).map (principalPowerKoszulMap f (n + 1))))
                (a := (singleCpx₀).map (principalPowerTorsionQuotientStep f c))
                (b := 𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
                (a' := (singleCpx₀).map (principalPowerTorsionLift f c))
                (b' := 𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
                (comm := (principalPowerStableShortComplex_step f c n).comm₁₂.symm)
                (comm' := (principalPowerQuotientToKoszulRoof_comm f c n).w)).symm
    _ =
      CochainComplex.mappingCone.map
        ((singleCpx₀).map (principalPowerTorsionTopMap f c (n + 1)))
        ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
        ((singleCpx₀).map (principalPowerTorsionLift f c) ≫
          (singleCpx₀).map (principalPowerKoszulMap f 1))
        (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
        hright_comp_comm := by
            rw [hlift_step]
    _ =
      principalPowerQuotientToKoszulRoofMap f c (n + 1) ≫
        CochainComplex.mappingCone.map
          ((singleCpx₀).map (principalPowerKoszulMap f (n + 2)))
          ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
          ((singleCpx₀).map (principalPowerKoszulMap f 1))
          (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
          (principalPowerForwardShortComplex_step f n).comm₁₂.symm := by
            simpa [principalPowerQuotientToKoszulRoofMap] using
              (CochainComplex.mappingCone.map_comp
                (φ₁ := ((singleCpx₀).map (principalPowerTorsionTopMap f c (n + 1))))
                (φ₂ := ((singleCpx₀).map (principalPowerKoszulMap f (n + 2))))
                (φ₃ := ((singleCpx₀).map (principalPowerKoszulMap f (n + 1))))
                (a := (singleCpx₀).map (principalPowerTorsionLift f c))
                (b := 𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
                (a' := (singleCpx₀).map (principalPowerKoszulMap f 1))
                (b' := 𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
                (comm := (principalPowerQuotientToKoszulRoof_comm f c (n + 1)).w)
                (comm' := (principalPowerForwardShortComplex_step f n).comm₁₂.symm))

/-- Helper for Lemma 15.94.1: the quotient-stage transport identifies the shifted quotient tower
successor with the explicit quotient map of the single-complex model. -/
private theorem principalPowerQuotientStageIso_hom_step
    (f : A) (n : ℕ) :
    Qtower(f).map (homOfLE (Nat.le_succ n)).op ≫
      (principalPowerQuotientStageIso f n).hom =
    (principalPowerQuotientStageIso f (n + 1)).hom ≫
      DerivedCategory.Q.map ((singleCpx₀).map (principalPowerQuotientStep f n)) := by
  -- Proof comment: the inverse-step identity is already proved, so precompose by the successor
  -- stage isomorphism and then cancel the current-stage inverse on the right.
  have hcur :
      (principalPowerQuotientStageIso f n).hom ≫
        (principalPowerQuotientStageIso f n).inv =
      𝟙 _ := by
    simpa using (principalPowerQuotientStageIso f n).hom_inv_id
  have hsucc :
      (principalPowerQuotientStageIso f (n + 1)).hom ≫
        (principalPowerQuotientStageIso f (n + 1)).inv =
      𝟙 _ := by
    simpa using (principalPowerQuotientStageIso f (n + 1)).hom_inv_id
  apply (cancel_mono (principalPowerQuotientStageIso f n).inv).1
  calc
    (Qtower(f).map (homOfLE (Nat.le_succ n)).op ≫
        (principalPowerQuotientStageIso f n).hom) ≫
          (principalPowerQuotientStageIso f n).inv =
      Qtower(f).map (homOfLE (Nat.le_succ n)).op ≫
        ((principalPowerQuotientStageIso f n).hom ≫
          (principalPowerQuotientStageIso f n).inv) := by
            simp [Category.assoc]
    _ =
      Qtower(f).map (homOfLE (Nat.le_succ n)).op := by
            rw [hcur]
            simp
    _ =
      𝟙 _ ≫ Qtower(f).map (homOfLE (Nat.le_succ n)).op := by
            simp
    _ =
      ((principalPowerQuotientStageIso f (n + 1)).hom ≫
          (principalPowerQuotientStageIso f (n + 1)).inv) ≫
        Qtower(f).map (homOfLE (Nat.le_succ n)).op := by
            rw [← hsucc]
    _ =
      (principalPowerQuotientStageIso f (n + 1)).hom ≫
        ((principalPowerQuotientStageIso f (n + 1)).inv ≫
          Qtower(f).map (homOfLE (Nat.le_succ n)).op) := by
            simp [Category.assoc]
    _ =
      (principalPowerQuotientStageIso f (n + 1)).hom ≫
        (DerivedCategory.Q.map ((singleCpx₀).map (principalPowerQuotientStep f n)) ≫
          (principalPowerQuotientStageIso f n).inv) := by
            rw [principalPowerQuotientStageIso_inv_step]
    _ =
      (principalPowerQuotientStageIso f (n + 1)).hom ≫
        DerivedCategory.Q.map ((singleCpx₀).map (principalPowerQuotientStep f n)) ≫
          (principalPowerQuotientStageIso f n).inv := by
            simp [Category.assoc]
    _ =
      ((principalPowerQuotientStageIso f (n + 1)).hom ≫
        DerivedCategory.Q.map ((singleCpx₀).map (principalPowerQuotientStep f n))) ≫
          (principalPowerQuotientStageIso f n).inv := by
            simp [Category.assoc]

/-- Helper for Lemma 15.94.1: the powered-Koszul stage transport identifies the tower successor
with the explicit cone map between the forward two-term models. -/
private theorem principalPowerKoszulStageIso_hom_step
    (f : A) (n : ℕ) :
    Ktower(f).map (homOfLE (Nat.le_succ n)).op ≫
      (principalPowerKoszulStageIso f n).hom =
    (principalPowerKoszulStageIso f (n + 1)).hom ≫
      DerivedCategory.Q.map
        (CochainComplex.mappingCone.map
          ((singleCpx₀).map (principalPowerKoszulMap f (n + 2)))
          ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
          ((singleCpx₀).map (principalPowerKoszulMap f 1))
          (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
          (principalPowerForwardShortComplex_step f n).comm₁₂.symm) := by
  -- TODO: rewrite the owner successor `koszulPowerStep` through the singleton-cone bridge.
  sorry

/-- Helper for Lemma 15.94.1: equivalently, the inverse Koszul-stage transport rewrites the tower
successor as the explicit cone map between the forward models. -/
private theorem principalPowerKoszulStageIso_inv_step
    (f : A) (n : ℕ) :
    (principalPowerKoszulStageIso f (n + 1)).inv ≫
      Ktower(f).map (homOfLE (Nat.le_succ n)).op =
    DerivedCategory.Q.map
      (CochainComplex.mappingCone.map
        ((singleCpx₀).map (principalPowerKoszulMap f (n + 2)))
        ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
        ((singleCpx₀).map (principalPowerKoszulMap f 1))
        (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
        (principalPowerForwardShortComplex_step f n).comm₁₂.symm) ≫
      (principalPowerKoszulStageIso f n).inv := by
  -- Proof comment: right-compose with the current-stage transport and use the forward-form
  -- successor square `principalPowerKoszulStageIso_hom_step`, exactly as on the quotient side.
  have hcur :
      (principalPowerKoszulStageIso f n).inv ≫
        (principalPowerKoszulStageIso f n).hom =
      𝟙 _ := by
    simpa using (principalPowerKoszulStageIso f n).inv_hom_id
  have hsucc :
      (principalPowerKoszulStageIso f (n + 1)).inv ≫
        (principalPowerKoszulStageIso f (n + 1)).hom =
      𝟙 _ := by
    simpa using (principalPowerKoszulStageIso f (n + 1)).inv_hom_id
  apply (cancel_mono (principalPowerKoszulStageIso f n).hom).1
  calc
    ((principalPowerKoszulStageIso f (n + 1)).inv ≫
        Ktower(f).map (homOfLE (Nat.le_succ n)).op) ≫
          (principalPowerKoszulStageIso f n).hom =
      (principalPowerKoszulStageIso f (n + 1)).inv ≫
        (Ktower(f).map (homOfLE (Nat.le_succ n)).op ≫
          (principalPowerKoszulStageIso f n).hom) := by
            simp [Category.assoc]
    _ =
      (principalPowerKoszulStageIso f (n + 1)).inv ≫
        ((principalPowerKoszulStageIso f (n + 1)).hom ≫
          DerivedCategory.Q.map
            (CochainComplex.mappingCone.map
              ((singleCpx₀).map (principalPowerKoszulMap f (n + 2)))
              ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
              ((singleCpx₀).map (principalPowerKoszulMap f 1))
              (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
              (principalPowerForwardShortComplex_step f n).comm₁₂.symm)) := by
              rw [principalPowerKoszulStageIso_hom_step]
    _ =
      ((principalPowerKoszulStageIso f (n + 1)).inv ≫
          (principalPowerKoszulStageIso f (n + 1)).hom) ≫
        DerivedCategory.Q.map
          (CochainComplex.mappingCone.map
            ((singleCpx₀).map (principalPowerKoszulMap f (n + 2)))
            ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
            ((singleCpx₀).map (principalPowerKoszulMap f 1))
            (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
            (principalPowerForwardShortComplex_step f n).comm₁₂.symm) := by
              simp [Category.assoc]
    _ =
      𝟙 _ ≫
        DerivedCategory.Q.map
          (CochainComplex.mappingCone.map
            ((singleCpx₀).map (principalPowerKoszulMap f (n + 2)))
            ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
            ((singleCpx₀).map (principalPowerKoszulMap f 1))
            (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
            (principalPowerForwardShortComplex_step f n).comm₁₂.symm) := by
              rw [hsucc]
    _ =
      DerivedCategory.Q.map
        (CochainComplex.mappingCone.map
          ((singleCpx₀).map (principalPowerKoszulMap f (n + 2)))
          ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
          ((singleCpx₀).map (principalPowerKoszulMap f 1))
          (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
          (principalPowerForwardShortComplex_step f n).comm₁₂.symm) := by
            simp
    _ =
      DerivedCategory.Q.map
        (CochainComplex.mappingCone.map
          ((singleCpx₀).map (principalPowerKoszulMap f (n + 2)))
          ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
          ((singleCpx₀).map (principalPowerKoszulMap f 1))
          (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
          (principalPowerForwardShortComplex_step f n).comm₁₂.symm) ≫
        𝟙 _ := by
          simp
    _ =
      DerivedCategory.Q.map
        (CochainComplex.mappingCone.map
          ((singleCpx₀).map (principalPowerKoszulMap f (n + 2)))
          ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
          ((singleCpx₀).map (principalPowerKoszulMap f 1))
          (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
          (principalPowerForwardShortComplex_step f n).comm₁₂.symm) ≫
        ((principalPowerKoszulStageIso f n).inv ≫
          (principalPowerKoszulStageIso f n).hom) := by
            rw [hcur]
    _ =
      (DerivedCategory.Q.map
          (CochainComplex.mappingCone.map
            ((singleCpx₀).map (principalPowerKoszulMap f (n + 2)))
            ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
            ((singleCpx₀).map (principalPowerKoszulMap f 1))
            (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
            (principalPowerForwardShortComplex_step f n).comm₁₂.symm) ≫
        (principalPowerKoszulStageIso f n).inv) ≫
          (principalPowerKoszulStageIso f n).hom := by
            simp [Category.assoc]

/-- Helper for Lemma 15.94.1: the forward comparison maps commute with the successor
transitions of the one-variable Koszul and quotient towers. -/
private theorem principalPowerKoszulToQuotient_step_naturality
    (f : A) (n : ℕ) :
    Ktower(f).map (homOfLE (Nat.le_succ n)).op ≫
        principalPowerKoszulToQuotient f n =
      principalPowerKoszulToQuotient f (n + 1) ≫
        Qtower(f).map (homOfLE (Nat.le_succ n)).op := by
  -- Proof comment: isolate the source-stage transport, insert the already-proved chain-level
  -- quotient naturality square, and finish on the target side with the quotient-stage inverse
  -- transport.
  have hchain :
      DerivedCategory.Q.map
          (CochainComplex.mappingCone.map
            ((singleCpx₀).map (principalPowerKoszulMap f (n + 2)))
            ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
            ((singleCpx₀).map (principalPowerKoszulMap f 1))
            (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
            (principalPowerForwardShortComplex_step f n).comm₁₂.symm) ≫
        DerivedCategory.Q.map (principalPowerKoszulToQuotientComplexMap f (n + 1)) =
      DerivedCategory.Q.map (principalPowerKoszulToQuotientComplexMap f (n + 2)) ≫
        DerivedCategory.Q.map ((singleCpx₀).map (principalPowerQuotientStep f n)) := by
    -- Proof comment: this is exactly the localized `mappingCone.descShortComplex` naturality
    -- square already isolated at the cochain level.
    simpa [Functor.map_comp] using
      congrArg DerivedCategory.Q.map
        (principalPowerKoszulToQuotientComplexMap_step_naturality f n)
  calc
    Ktower(f).map (homOfLE (Nat.le_succ n)).op ≫
        principalPowerKoszulToQuotient f n =
      (Ktower(f).map (homOfLE (Nat.le_succ n)).op ≫
          (principalPowerKoszulStageIso f n).hom) ≫
        DerivedCategory.Q.map (principalPowerKoszulToQuotientComplexMap f (n + 1)) ≫
          (principalPowerQuotientStageIso f n).inv := by
            simp [principalPowerKoszulToQuotient, Category.assoc]
    _ =
      ((principalPowerKoszulStageIso f (n + 1)).hom ≫
          DerivedCategory.Q.map
            (CochainComplex.mappingCone.map
              ((singleCpx₀).map (principalPowerKoszulMap f (n + 2)))
              ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
              ((singleCpx₀).map (principalPowerKoszulMap f 1))
              (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
              (principalPowerForwardShortComplex_step f n).comm₁₂.symm)) ≫
        DerivedCategory.Q.map (principalPowerKoszulToQuotientComplexMap f (n + 1)) ≫
          (principalPowerQuotientStageIso f n).inv := by
            rw [principalPowerKoszulStageIso_hom_step]
    _ =
      (principalPowerKoszulStageIso f (n + 1)).hom ≫
        (DerivedCategory.Q.map
            (CochainComplex.mappingCone.map
              ((singleCpx₀).map (principalPowerKoszulMap f (n + 2)))
              ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
              ((singleCpx₀).map (principalPowerKoszulMap f 1))
              (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
              (principalPowerForwardShortComplex_step f n).comm₁₂.symm) ≫
          DerivedCategory.Q.map (principalPowerKoszulToQuotientComplexMap f (n + 1))) ≫
            (principalPowerQuotientStageIso f n).inv := by
              simp [Category.assoc]
    _ =
      (principalPowerKoszulStageIso f (n + 1)).hom ≫
        (DerivedCategory.Q.map (principalPowerKoszulToQuotientComplexMap f (n + 2)) ≫
          DerivedCategory.Q.map ((singleCpx₀).map (principalPowerQuotientStep f n))) ≫
            (principalPowerQuotientStageIso f n).inv := by
              rw [hchain]
    _ =
      (principalPowerKoszulStageIso f (n + 1)).hom ≫
        DerivedCategory.Q.map (principalPowerKoszulToQuotientComplexMap f (n + 2)) ≫
          (DerivedCategory.Q.map ((singleCpx₀).map (principalPowerQuotientStep f n)) ≫
            (principalPowerQuotientStageIso f n).inv) := by
              simp [Category.assoc]
    _ =
      (principalPowerKoszulStageIso f (n + 1)).hom ≫
        DerivedCategory.Q.map (principalPowerKoszulToQuotientComplexMap f (n + 2)) ≫
          ((principalPowerQuotientStageIso f (n + 1)).inv ≫
            Qtower(f).map (homOfLE (Nat.le_succ n)).op) := by
              rw [principalPowerQuotientStageIso_inv_step]
    _ =
      principalPowerKoszulToQuotient f (n + 1) ≫
        Qtower(f).map (homOfLE (Nat.le_succ n)).op := by
          simp [principalPowerKoszulToQuotient, Category.assoc]

/-- Naturality of the canonical stagewise maps from the powered Koszul tower to the canonical
quotient tower owner. -/
private theorem principalPowerKoszulToQuotient_naturality
    (f : A) {i j : ℕᵒᵖ} (h : i ⟶ j) :
    Ktower(f).map h ≫ principalPowerKoszulToQuotient f j.unop =
      principalPowerKoszulToQuotient f i.unop ≫
        Qtower(f).map h :=
  by
    -- Package the already-isolated successor square into a natural transformation on the whole
    -- op-sequence, then read off its naturality at the requested morphism `h`.
    let α : Ktower(f) ⟶ Qtower(f) :=
      NatTrans.ofOpSequence
        (fun n ↦ principalPowerKoszulToQuotient f n)
        (fun n ↦ by
          simpa using principalPowerKoszulToQuotient_step_naturality f n)
    simpa using α.naturality h

private abbrev principalPowerKoszulToQuotientNatTrans (f : A) :
    Ktower(f) ⟶ Qtower(f) :=
  { app := fun n ↦
      show Ktower(f).obj n ⟶ Qtower(f).obj n from principalPowerKoszulToQuotient f n.unop
    naturality := fun _ _ h ↦ principalPowerKoszulToQuotient_naturality f h }

/-- Lemma 15.94.1 (1): the canonical quotient maps
`(A \xrightarrow{f^(n+1)} A) ⟶ A/(f^(n+1))`
define the identity-reindex representative from the one-variable powered-Koszul tower to the
canonical quotient tower owner. -/
abbrev principalPowerKoszulToQuotientRep (f : A) :
    SequentialProObjectMorphismRep (Ktower(f)) (Qtower(f)) :=
  ofNatTrans (principalPowerKoszulToQuotientNatTrans f)

/-- Helper for Lemma 15.94.1: the stabilized reverse comparison maps commute with the successor
transitions of the shifted quotient tower and the Koszul tower. -/
private theorem principalPowerQuotientToKoszulStable_step_naturality
    (f : A) (c n : ℕ)
    (hstable : (A[f^∞] : Submodule A A) = (A[f ^ c] : Submodule A A)) :
    (SequentialInverseSystem.shift (Qtower(f)) c).map (homOfLE (Nat.le_succ n)).op ≫
        principalPowerQuotientToKoszulStable f c n hstable =
      principalPowerQuotientToKoszulStable f c (n + 1) hstable ≫
        Ktower(f).map (homOfLE (Nat.le_succ n)).op := by
  -- Rewrite the shifted quotient successor through the quotient-stage transport, then insert the
  -- stabilized roof square and finish on the Koszul side with the inverse-stage transport.
  let eₙ :=
    principalPowerTorsionComplexToQuotientIso f c n
      (principalPowerTorsionStage_eq_of_stable f c n hstable)
  let eₙ₁ :=
    principalPowerTorsionComplexToQuotientIso f c (n + 1)
      (principalPowerTorsionStage_eq_of_stable f c (n + 1) hstable)
  have hshift :
      (SequentialInverseSystem.shift (Qtower(f)) c).map (homOfLE (Nat.le_succ n)).op =
        Qtower(f).map (homOfLE (Nat.le_succ (c + n))).op := by
    -- The shifted successor at stage `n` is exactly the original quotient successor at stage
    -- `c + n`.
    simpa [SequentialInverseSystem.transitionMap, Nat.add_assoc] using
      (SequentialInverseSystem.shift_transitionMap
        (F := Qtower(f)) c (hij := Nat.le_succ n))
  have hroof :
      DerivedCategory.Q.map
          (CochainComplex.mappingCone.map
            ((singleCpx₀).map (principalPowerTorsionTopMap f c (n + 1)))
            ((singleCpx₀).map (principalPowerTorsionTopMap f c n))
            ((singleCpx₀).map (principalPowerTorsionQuotientStep f c))
            (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
            (principalPowerStableShortComplex_step f c n).comm₁₂.symm) ≫
        DerivedCategory.Q.map (principalPowerQuotientToKoszulRoofMap f c n) =
      DerivedCategory.Q.map (principalPowerQuotientToKoszulRoofMap f c (n + 1)) ≫
        DerivedCategory.Q.map
          (CochainComplex.mappingCone.map
            ((singleCpx₀).map (principalPowerKoszulMap f (n + 2)))
            ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
            ((singleCpx₀).map (principalPowerKoszulMap f 1))
            (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
            (principalPowerForwardShortComplex_step f n).comm₁₂.symm) := by
    -- Localize the strict roof square before inserting it into the stagewise comparison.
    simpa [Functor.map_comp] using
      congrArg DerivedCategory.Q.map
        (principalPowerQuotientToKoszulRoofMap_step_naturality f c n)
  calc
    (SequentialInverseSystem.shift (Qtower(f)) c).map (homOfLE (Nat.le_succ n)).op ≫
        principalPowerQuotientToKoszulStable f c n hstable =
      (Qtower(f).map (homOfLE (Nat.le_succ (c + n))).op ≫
          (principalPowerQuotientStageIso f (c + n)).hom) ≫
        eₙ.symm.hom ≫
          DerivedCategory.Q.map (principalPowerQuotientToKoszulRoofMap f c n) ≫
            (principalPowerKoszulStageIso f n).inv := by
              rw [hshift]
              simp [principalPowerQuotientToKoszulStable, eₙ, Category.assoc]
    _ =
      ((principalPowerQuotientStageIso f (c + (n + 1))).hom ≫
          DerivedCategory.Q.map ((singleCpx₀).map (principalPowerQuotientStep f (c + n)))) ≫
        eₙ.symm.hom ≫
          DerivedCategory.Q.map (principalPowerQuotientToKoszulRoofMap f c n) ≫
            (principalPowerKoszulStageIso f n).inv := by
              simpa [Nat.add_assoc, Category.assoc] using
                congrArg
                  (fun t ↦
                    t ≫
                      eₙ.symm.hom ≫
                        DerivedCategory.Q.map (principalPowerQuotientToKoszulRoofMap f c n) ≫
                          (principalPowerKoszulStageIso f n).inv)
                  (principalPowerQuotientStageIso_hom_step f (c + n))
    _ =
      (principalPowerQuotientStageIso f (c + (n + 1))).hom ≫
        (DerivedCategory.Q.map ((singleCpx₀).map (principalPowerQuotientStep f (c + n))) ≫
          eₙ.symm.hom) ≫
            DerivedCategory.Q.map (principalPowerQuotientToKoszulRoofMap f c n) ≫
              (principalPowerKoszulStageIso f n).inv := by
                simp [Category.assoc]
    _ =
      (principalPowerQuotientStageIso f (c + (n + 1))).hom ≫
        (eₙ₁.symm.hom ≫
          DerivedCategory.Q.map
            (CochainComplex.mappingCone.map
              ((singleCpx₀).map (principalPowerTorsionTopMap f c (n + 1)))
              ((singleCpx₀).map (principalPowerTorsionTopMap f c n))
              ((singleCpx₀).map (principalPowerTorsionQuotientStep f c))
              (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
              (principalPowerStableShortComplex_step f c n).comm₁₂.symm)) ≫
            DerivedCategory.Q.map (principalPowerQuotientToKoszulRoofMap f c n) ≫
              (principalPowerKoszulStageIso f n).inv := by
                simpa [eₙ, eₙ₁, Category.assoc] using
                  congrArg
                    (fun t ↦
                      (principalPowerQuotientStageIso f (c + (n + 1))).hom ≫
                        t ≫
                          DerivedCategory.Q.map (principalPowerQuotientToKoszulRoofMap f c n) ≫
                            (principalPowerKoszulStageIso f n).inv)
                    (principalPowerTorsionComplexToQuotientIso_symm_step f c n hstable)
    _ =
      (principalPowerQuotientStageIso f (c + (n + 1))).hom ≫
        eₙ₁.symm.hom ≫
          (DerivedCategory.Q.map (principalPowerQuotientToKoszulRoofMap f c (n + 1)) ≫
            DerivedCategory.Q.map
              (CochainComplex.mappingCone.map
                ((singleCpx₀).map (principalPowerKoszulMap f (n + 2)))
                ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
                ((singleCpx₀).map (principalPowerKoszulMap f 1))
                (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
                (principalPowerForwardShortComplex_step f n).comm₁₂.symm)) ≫
              (principalPowerKoszulStageIso f n).inv := by
                simpa [Category.assoc] using
                  congrArg
                    (fun t ↦
                      (principalPowerQuotientStageIso f (c + (n + 1))).hom ≫
                        eₙ₁.symm.hom ≫
                          t ≫
                            (principalPowerKoszulStageIso f n).inv)
                    hroof
    _ =
      (principalPowerQuotientStageIso f (c + (n + 1))).hom ≫
        eₙ₁.symm.hom ≫
          DerivedCategory.Q.map (principalPowerQuotientToKoszulRoofMap f c (n + 1)) ≫
            (DerivedCategory.Q.map
                (CochainComplex.mappingCone.map
                  ((singleCpx₀).map (principalPowerKoszulMap f (n + 2)))
                  ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
                  ((singleCpx₀).map (principalPowerKoszulMap f 1))
                  (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
                  (principalPowerForwardShortComplex_step f n).comm₁₂.symm) ≫
              (principalPowerKoszulStageIso f n).inv) := by
                simp [Category.assoc]
    _ =
      (principalPowerQuotientStageIso f (c + (n + 1))).hom ≫
        eₙ₁.symm.hom ≫
          DerivedCategory.Q.map (principalPowerQuotientToKoszulRoofMap f c (n + 1)) ≫
            ((principalPowerKoszulStageIso f (n + 1)).inv ≫
              Ktower(f).map (homOfLE (Nat.le_succ n)).op) := by
                simpa [Category.assoc] using
                  congrArg
                    (fun t ↦
                      (principalPowerQuotientStageIso f (c + (n + 1))).hom ≫
                        eₙ₁.symm.hom ≫
                          DerivedCategory.Q.map
                            (principalPowerQuotientToKoszulRoofMap f c (n + 1)) ≫
                              t)
                    (principalPowerKoszulStageIso_inv_step f n)
    _ =
      principalPowerQuotientToKoszulStable f c (n + 1) hstable ≫
        Ktower(f).map (homOfLE (Nat.le_succ n)).op := by
          simp [principalPowerQuotientToKoszulStable, eₙ₁, Category.assoc]

/-- Naturality of the shifted stagewise reverse maps with respect to the canonical quotient
tower owner. -/
private theorem principalPowerQuotientToKoszulStable_naturality
    (f : A) (c : ℕ)
    (hstable : (A[f^∞] : Submodule A A) = (A[f ^ c] : Submodule A A))
    {i j : ℕᵒᵖ} (h : i ⟶ j) :
    (SequentialInverseSystem.shift (Qtower(f)) c).map h ≫
        principalPowerQuotientToKoszulStable f c j.unop hstable =
      principalPowerQuotientToKoszulStable f c i.unop hstable ≫
        Ktower(f).map h := by
  -- Package the successor-step square into a natural transformation on the shifted quotient
  -- system, then invoke its naturality at `h`.
  let α : SequentialInverseSystem.shift (Qtower(f)) c ⟶ Ktower(f) :=
    NatTrans.ofOpSequence
      (fun n ↦ principalPowerQuotientToKoszulStable f c n hstable)
      (fun n ↦ by
        simpa using principalPowerQuotientToKoszulStable_step_naturality f c n hstable)
  simpa using α.naturality h

private abbrev principalPowerQuotientToKoszulShiftStableNatTrans
    (f : A) (c : ℕ)
    (hstable : (A[f^∞] : Submodule A A) = (A[f ^ c] : Submodule A A)) :
    SequentialInverseSystem.shift (Qtower(f)) c ⟶ Ktower(f) :=
  { app := fun n ↦
      show (SequentialInverseSystem.shift (Qtower(f)) c).obj n ⟶ Ktower(f).obj n from
        principalPowerQuotientToKoszulStable f c n.unop hstable
    naturality := fun _ _ h ↦ by
      simpa using principalPowerQuotientToKoszulStable_naturality f c hstable h }

/-- Helper for Lemma 15.94.1: the stabilized reverse stage maps assemble into the private
shift-by-`c` representative used on the honest branch of the source proof. -/
private abbrev principalPowerQuotientToKoszulShiftStableRep
    (f : A) (c : ℕ)
    (hstable : (A[f^∞] : Submodule A A) = (A[f ^ c] : Submodule A A)) :
    SequentialProObjectMorphismRep (Qtower(f)) (Ktower(f)) :=
  ofShiftNatTrans c (principalPowerQuotientToKoszulShiftStableNatTrans f c hstable)

/-- Lemma 15.94.1 (2): the reverse comparison maps
`A/(f^(c + n)) ⟶ (A \xrightarrow{f^n} A)` assemble to the canonical shift-by-`c`
representative from the principal-power quotient tower to the powered Koszul tower. -/
abbrev principalPowerQuotientToKoszulShiftRep (f : A) (c : ℕ) :
    SequentialProObjectMorphismRep (Qtower(f)) (Ktower(f)) :=
  if hstable : (A[f^∞] : Submodule A A) = (A[f ^ c] : Submodule A A) then
    principalPowerQuotientToKoszulShiftStableRep f c hstable
  else
    ofShiftNatTrans c 0


-- Proof sketch: the stabilization hypothesis identifies the torsion submodules `A[f^m]` with
-- `A[f^c]` for all sufficiently large stages, so the explicit reverse representative above and the
-- forward representative `principalPowerKoszulToQuotientRep f` become inverse after common
-- refinement in the canonical owner `SequentialProObjectMorphismRep.IsProIsomorphism`.
/-- Helper for Lemma 15.94.1: at stage `n`, the reverse comparison followed by the forward
 comparison is exactly the `c`-step transition in the quotient tower. -/
private theorem principalPower_reverse_forward_eq_transition
    (f : A) (c n : ℕ)
    (hstable : (A[f^∞] : Submodule A A) = (A[f ^ c] : Submodule A A)) :
    principalPowerQuotientToKoszulStable f c n hstable ≫
        principalPowerKoszulToQuotient f n =
      SequentialInverseSystem.transitionMap (Qtower(f)) (Nat.le_add_left n c) := by
  -- The source proof identifies the reverse-forward composite with the quotient transition after
  -- comparing both roofs over the stabilized torsion quotient.
  -- TODO: expand both stage maps through `principalPowerTorsionComplexToQuotientIso`,
  -- transport the composite to the stable short-complex comparison, and simplify to the
  -- quotient transition map.
  sorry

/-- Helper for Lemma 15.94.1: at stage `n`, the forward comparison at stage `c + n` followed by
 the reverse comparison is exactly the `c`-step transition in the Koszul tower. -/
private theorem principalPower_forward_reverse_eq_transition
    (f : A) (c n : ℕ)
    (hstable : (A[f^∞] : Submodule A A) = (A[f ^ c] : Submodule A A)) :
    principalPowerKoszulToQuotient f (c + n) ≫
        principalPowerQuotientToKoszulStable f c n hstable =
      SequentialInverseSystem.transitionMap (Ktower(f)) (Nat.le_add_left n c) := by
  -- The source proof identifies the forward-reverse composite with the Koszul transition after
  -- transporting the stabilized comparison roof back through the cone model of the Koszul stage.
  -- TODO: rewrite the composite through `principalPowerKoszulStageIso` and the stabilized roof
  -- isomorphism, then compare with the `c`-step transition in `Ktower(f)`.
  sorry

/-- Lemma 15.94.1 (2): if the `f`-power torsion submodules `A[f^m]` stabilize from stage
`c`, equivalently if `A[f^∞] = A[f^c]`, then the explicit shift-by-`c` reverse comparison
representative is a pro-isomorphism. -/
theorem principalPowerQuotientToKoszulShift_isProIsomorphism
    (f : A) (c : ℕ)
    (hstable : (A[f^∞] : Submodule A A) = (A[f ^ c] : Submodule A A)) :
    (principalPowerQuotientToKoszulShiftRep f c).IsProIsomorphism := by
  -- On the stable branch the public representative reduces to the honest source-facing roof.
  rw [principalPowerQuotientToKoszulShiftRep]
  simp [hstable]
  let quotientComp :=
    SequentialProObjectMorphismRep.compRep
      (principalPowerQuotientToKoszulShiftStableRep f c hstable)
      (principalPowerKoszulToQuotientRep f)
  let koszulComp :=
    SequentialProObjectMorphismRep.compRep
      (principalPowerKoszulToQuotientRep f)
      (principalPowerQuotientToKoszulShiftStableRep f c hstable)
  refine ⟨principalPowerKoszulToQuotientRep f, ?_, ?_⟩
  · -- The reverse-then-forward composite is already the quotient transition after refining to
    -- the common source stage `n ↦ c + n`.
    refine ⟨quotientComp.reindex, fun n ↦ le_rfl, fun n ↦ ?_, ?_⟩
    · change n ≤ quotientComp.reindex n
      simp [quotientComp, SequentialProObjectMorphismRep.compRep,
        SequentialProObjectMorphismRep.ofShiftNatTrans,
        SequentialProObjectMorphismRep.ofNatTrans]
      exact Nat.le_add_left n c
    · intro n
      simpa [quotientComp, SequentialInverseSystem.transitionMap] using
        principalPower_reverse_forward_eq_transition f c n hstable
  · -- The forward-then-reverse composite is likewise the Koszul transition after the same
    -- common refinement.
    refine ⟨koszulComp.reindex, fun n ↦ le_rfl, fun n ↦ ?_, ?_⟩
    · change n ≤ koszulComp.reindex n
      simp [koszulComp, SequentialProObjectMorphismRep.compRep,
        SequentialProObjectMorphismRep.ofShiftNatTrans,
        SequentialProObjectMorphismRep.ofNatTrans]
      exact Nat.le_add_left n c
    · intro n
      simpa [koszulComp, SequentialInverseSystem.transitionMap] using
        principalPower_forward_reverse_eq_transition f c n hstable

/-- Companion to Lemma 15.94.1 (2): the explicit shift-by-`c` reverse comparison representative
induces an isomorphism of the associated sequential pro-objects. -/
theorem principalPowerQuotientToKoszulShift_isIso
    (f : A) (c : ℕ)
    (hstable : (A[f^∞] : Submodule A A) = (A[f ^ c] : Submodule A A)) :
    IsIso (principalPowerQuotientToKoszulShiftRep f c).toProObjectHom := by
  -- Reduce to the stable branch before comparing with the forward representative in pro-objects.
  rw [principalPowerQuotientToKoszulShiftRep]
  simp [hstable]
  -- Upgrade the stabilized pro-isomorphism to componentwise bijectivity on the associated
  -- pro-object hom, then invoke the owner criterion for natural isomorphisms.
  let η := (principalPowerQuotientToKoszulShiftStableRep f c hstable).toProObjectHom
  have hηbij :
      ∀ X : DerivedCategory (ModuleCat A), Function.Bijective (η.app X) := fun X ↦
        by
          simpa [η, principalPowerQuotientToKoszulShiftRep, hstable] using
            SequentialProObjectMorphismRep.isProIsomorphism_toProObjectHom_app_bijective
              (principalPowerQuotientToKoszulShift_isProIsomorphism f c hstable) X
  letI : ∀ X : DerivedCategory (ModuleCat A), IsIso (η.app X) := fun X ↦
    (CategoryTheory.isIso_iff_bijective (η.app X)).2 (hηbij X)
  have hη : IsIso η := NatIso.isIso_of_isIso_app η
  simpa [η] using hη

end
