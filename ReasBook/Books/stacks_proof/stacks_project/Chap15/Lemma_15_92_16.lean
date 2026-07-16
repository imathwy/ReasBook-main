import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import stacks_proof.stacks_project.Chap13.Definition_13_34_1
import stacks_proof.stacks_project.Chap15.Situation_15_92_15
import stacks_proof.stacks_project.Chap15.Definition_15_59_13
import stacks_proof.stacks_project.Chap15.Lemma_15_59_14
import stacks_proof.stacks_project.Chap15.Definition_15_92_4
import stacks_proof.stacks_project.Chap15.Lemma_15_28_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.SequentialInverseSystem
open ComplexShape
open Opposite
open scoped KoszulComplex

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] {r : ℕ}

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "ModA" => ModuleCat A
local notation "CpxA" => CochainComplex ModA ℤ
local notation "KModA" => HomotopyCategory ModA (ComplexShape.up ℤ)

/- Domain-style sampling for Lemma 15.92.16:
- primary domain: derived-category realizations of the powered Koszul tower and sequential derived
  limits of its tensor image;
- sampled owner declarations:
  `koszulPowerInverseSystem`,
  `ComplexShape.embeddingDownNat.extendFunctor`,
  `DerivedCategory.Q`,
  `DerivedCategory.IsDerivedCompleteWithRespectTo`;
- best owner abstraction: the source-facing derived tower should be obtained from the chapter owner
  `koszulPowerInverseSystem` by the canonical extension-and-localization functor, rather than by a
  parallel stage alias in this file;
- primitive data: the powered Koszul inverse system from Situation `15.92.15`;
- derived API: the tensor tower and the derived-completeness statement for a chosen derived limit.

Source/core/bridge triage:
- `source-facing`: the powered Koszul tensor tower in `D(A)` and the derived-completeness theorem
  for its derived limit;
- `core/canonical`: `koszulPowerInverseSystem`, `ComplexShape.embeddingDownNat.extendFunctor`,
  `DerivedCategory.Q`, and `K.IsDerivedCompleteWithRespectTo I`;
- `bridge/view`: the canonical stage object
  `(derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n)`. -/

/-- The inverse system in `D(A)` whose `n`th stage is the derived tensor product of the `n`th
powered Koszul complex with the fixed object `K`. This is the library-facing model of the tower
`(K \otimes_A^{\mathbf L} K_n^\bullet)_n`. -/
abbrev derivedCompletionKoszulPowerTensorDerivedInverseSystem
    (K : DMod) (f : Fin r → A) : ℕᵒᵖ ⥤ DMod :=
  derivedCompletionKoszulPowersDerivedInverseSystem f ⋙ derivedTensorProduct K

/-- Helper for Lemma 15.92.16: conjugating a `Qh`-image along `quotientCompQhIso` recovers the
corresponding `Q`-image. -/
private theorem quotientCompQhIso_homCongr_map
    {C D : CpxA}
    (φ : C ⟶ D) :
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso ModA).app C)
      ((DerivedCategory.quotientCompQhIso ModA).app D))
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient ModA (ComplexShape.up ℤ)).map φ)) =
        DerivedCategory.Q.map φ := by
  -- Rewrite the conjugated map into the naturality square of `quotientCompQhIso`.
  change
    (DerivedCategory.quotientCompQhIso ModA).inv.app C ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient ModA (ComplexShape.up ℤ)).map φ) ≫
          (DerivedCategory.quotientCompQhIso ModA).hom.app D =
      DerivedCategory.Q.map φ
  have hnat :
      DerivedCategory.Qh.map ((HomotopyCategory.quotient ModA (ComplexShape.up ℤ)).map φ) ≫
          (DerivedCategory.quotientCompQhIso ModA).hom.app D =
        (DerivedCategory.quotientCompQhIso ModA).hom.app C ≫ DerivedCategory.Q.map φ := by
    -- Naturality identifies the `Qh`-image with the `Q`-image up to the comparison isomorphism.
    simpa [Functor.comp_map] using
      (DerivedCategory.quotientCompQhIso ModA).hom.naturality φ
  calc
    (DerivedCategory.quotientCompQhIso ModA).inv.app C ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient ModA (ComplexShape.up ℤ)).map φ) ≫
          (DerivedCategory.quotientCompQhIso ModA).hom.app D =
      (DerivedCategory.quotientCompQhIso ModA).inv.app C ≫
        ((DerivedCategory.quotientCompQhIso ModA).hom.app C ≫ DerivedCategory.Q.map φ) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ (DerivedCategory.quotientCompQhIso ModA).inv.app C ≫ k) hnat
    _ = DerivedCategory.Q.map φ := by
          simpa using
            (Iso.inv_hom_id_assoc ((DerivedCategory.quotientCompQhIso ModA).app C)
              (DerivedCategory.Q.map φ))

/-- Helper for Lemma 15.92.16: a null-homotopic scalar endomorphism of a cochain complex becomes
zero in the derived category. -/
private theorem q_obj_smul_id_eq_zero_of_homotopy_zero
    {C : CpxA} (a : A) (h : Homotopy (a • 𝟙 C) 0) :
    a • 𝟙 (DerivedCategory.Q.obj C) = 0 := by
  -- First kill the morphism in the homotopy quotient.
  have hquot :
      (HomotopyCategory.quotient ModA (ComplexShape.up ℤ)).map (a • 𝟙 C) = 0 := by
    exact (HomotopyCategory.quotient_map_eq_zero_iff (a • 𝟙 C)).2 ⟨h⟩
  have hQh :
      DerivedCategory.Qh.map
          ((HomotopyCategory.quotient ModA (ComplexShape.up ℤ)).map (a • 𝟙 C)) = 0 := by
    simp [hquot]
  -- Then transport that vanishing across the `Qh`-to-`Q` comparison isomorphism.
  have hQ : DerivedCategory.Q.map (a • 𝟙 C) = 0 := by
    have htransport := quotientCompQhIso_homCongr_map (A := A) (φ := a • 𝟙 C)
    rw [hQh] at htransport
    calc
      DerivedCategory.Q.map (a • 𝟙 C) =
        (Iso.homCongr ((DerivedCategory.quotientCompQhIso ModA).app C)
          ((DerivedCategory.quotientCompQhIso ModA).app C)) 0 := htransport.symm
      _ = 0 := by
        change (DerivedCategory.quotientCompQhIso ModA).inv.app C ≫ 0 ≫
            (DerivedCategory.quotientCompQhIso ModA).hom.app C = 0
        rw [CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]
  simpa using hQ

/-- Helper for Lemma 15.92.16: extending a homotopy along `embeddingDownNat` produces the
corresponding homotopy on the cochain model used by the derived Koszul tower. -/
private noncomputable abbrev embeddingDownNat_extend_homotopy
    {C D : ChainComplex ModA ℕ} {φ ψ : C ⟶ D} (h : Homotopy φ ψ) :
    Homotopy
      ((ComplexShape.embeddingDownNat.extendFunctor ModA).map φ)
      ((ComplexShape.embeddingDownNat.extendFunctor ModA).map ψ) := by
  -- The owner `Homotopy.extend` is exactly the chain-to-cochain transport needed here.
  simpa using h.extend ComplexShape.embeddingDownNat

/-- Helper for Lemma 15.92.16: extending a scalar multiple of a chain map along
`embeddingDownNat` is the scalar multiple of the extended map. -/
private theorem embeddingDownNat_extendMap_smul
    {C D : ChainComplex ModA ℕ} (φ : C ⟶ D) (a : A) :
    HomologicalComplex.extendMap (a • φ) ComplexShape.embeddingDownNat =
      a • HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat := by
  -- Compare the extended morphisms componentwise; on image degrees the statement is immediate,
  -- and away from the image both sides vanish.
  ext i' x
  by_cases hi' : ∃ i : ℕ, ComplexShape.embeddingDownNat.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    rw [HomologicalComplex.extendMap_f _ _ hi]
    rw [HomologicalComplex.smul_f_apply, HomologicalComplex.smul_f_apply]
    rw [HomologicalComplex.extendMap_f _ _ hi]
    simp [Linear.comp_smul, Linear.smul_comp]
  · have hz₁ :
        (HomologicalComplex.extendMap (a • φ) ComplexShape.embeddingDownNat).f i' = 0 := by
      exact (C.isZero_extend_X ComplexShape.embeddingDownNat i'
        (fun i hi => hi' ⟨i, hi⟩)).eq_of_src _ _
    have hz₂ :
        (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat).f i' = 0 := by
      exact (C.isZero_extend_X ComplexShape.embeddingDownNat i'
        (fun i hi => hi' ⟨i, hi⟩)).eq_of_src _ _
    rw [hz₁, HomologicalComplex.smul_f_apply, hz₂]
    exact (smul_zero a).symm

/-- Helper for Lemma 15.92.16: extending the scalar identity map along `embeddingDownNat`
produces the scalar identity on the extended cochain complex. -/
private theorem embeddingDownNat_extendMap_smul_id
    (C : ChainComplex ModA ℕ) (a : A) :
    HomologicalComplex.extendMap ((a • 𝟙 C) : C ⟶ C) ComplexShape.embeddingDownNat =
      a • 𝟙 (C.extend ComplexShape.embeddingDownNat) := by
  -- Pull the scalar through `extendMap`, then identify the extended identity.
  rw [embeddingDownNat_extendMap_smul]
  simp

/-- Helper for Lemma 15.92.16: each powered generator acts by zero on the corresponding derived
Koszul stage. -/
private theorem derived_koszul_power_generator_smul_eq_zero
    (f : Fin r → A) (n : ℕ) (i : Fin r) :
    (f i ^ (n + 1) : A) •
        𝟙 ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n)) = 0 := by
  -- Route correction: the source-faithful proof still goes through the Koszul null-homotopy from
  -- Lemma `15.28.6`, but the missing owner bridge is the explicit transport of that homotopy
  -- across `embeddingDownNat.extendFunctor`.
  let g : Fin r → A := fun j ↦ f j ^ (n + 1)
  have hzero :
      Homotopy
        ((g i : A) •
          𝟙 (((ComplexShape.embeddingDownNat.extendFunctor ModA).obj (K^•(g)))))
        0 := by
    -- Transport the standard Koszul null-homotopy for the powered tuple to the cochain model.
    simpa [g, embeddingDownNat_extendMap_smul_id] using
      embeddingDownNat_extend_homotopy
        (A := A)
        (h := koszul_generator_scalar_endomorphism_homotopy_zero g i)
  -- Once the cochain representative is null-homotopic, its image in the derived category vanishes.
  simpa [derivedCompletionKoszulPowersDerivedInverseSystem, g] using
    q_obj_smul_id_eq_zero_of_homotopy_zero (A := A) (a := g i) hzero

/-- Helper for Lemma 15.92.16: scalar annihilation transports across an isomorphism in the
derived category. -/
private theorem smul_id_eq_zero_of_iso
    {X Y : DMod} (a : A) (e : X ≅ Y) (hX : a • 𝟙 X = 0) :
    a • 𝟙 Y = 0 := by
  -- Conjugate the scalar identity equality along the chosen isomorphism.
  have htransport : e.inv ≫ (a • 𝟙 X) ≫ e.hom = 0 := by
    simpa using congrArg (fun φ ↦ e.inv ≫ φ ≫ e.hom) hX
  calc
    a • 𝟙 Y = e.inv ≫ (a • 𝟙 X) ≫ e.hom := by simp
    _ = 0 := htransport

/-- Helper for Lemma 15.92.16: every element of the powered ideal acts by zero on the matching
derived Koszul stage. -/
private theorem derived_koszul_power_stage_smul_eq_zero_of_mem_power_ideal
    (f : Fin r → A) (n : ℕ) {a : A} (ha : a ∈ koszulPowerIdeal f n) :
    a • 𝟙 ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n)) = 0 := by
  rcases (Ideal.mem_span_range_iff_exists_fun).1 ha with ⟨c, hc⟩
  -- Expand `a` in the generators of the powered ideal and use linearity of scalar action.
  calc
    a • 𝟙 ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n)) =
      (∑ i : Fin r, c i * (f i ^ (n + 1))) •
        𝟙 ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n)) := by
          rw [hc]
    _ = ∑ i : Fin r,
        (c i * (f i ^ (n + 1))) •
          𝟙 ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n)) := by
          rw [Finset.sum_smul]
    _ = ∑ i : Fin r,
        c i •
          ((f i ^ (n + 1) : A) •
            𝟙 ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n))) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [smul_smul]
    _ = 0 := by
          refine Finset.sum_eq_zero fun i _ ↦ ?_
          calc
            c i •
                ((f i ^ (n + 1) : A) •
                  𝟙 ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n))) =
              c i • 0 := by
                exact congrArg
                  (fun φ ↦ c i • φ) (derived_koszul_power_generator_smul_eq_zero f n i)
            _ = 0 := by exact smul_zero (c i)

/-- Helper for Lemma 15.92.16: a sufficiently large power of any element of
`Ideal.span (Set.range f)` lies in the stage-`n` powered ideal. -/
private theorem pow_mem_koszulPowerIdeal_of_mem_spanRange
    (f : Fin r → A) (n : ℕ) {a : A} (ha : a ∈ Ideal.span (Set.range f)) :
    a ^ (r * n + 1) ∈ koszulPowerIdeal f n := by
  classical
  rcases (Ideal.mem_span_range_iff_exists_fun).1 ha with ⟨c, hc⟩
  have hsum :
      (∑ i : Fin r, c i * f i) ^ (r * n + 1) ∈
        Ideal.span
          ((((fun i : Fin r ↦ (c i * f i) ^ (n + 1)) '' (Finset.univ : Finset (Fin r))) : Set A)) := by
    -- `sum_pow_mem_span_pow` is the finite-sum pigeonhole step behind the textbook power bound.
    simpa using
      (Ideal.sum_pow_mem_span_pow (s := (Finset.univ : Finset (Fin r)))
        (f := fun i : Fin r ↦ c i * f i) n)
  have hspan :
      Ideal.span
          ((((fun i : Fin r ↦ (c i * f i) ^ (n + 1)) '' (Finset.univ : Finset (Fin r))) : Set A)) ≤
        koszulPowerIdeal f n := by
    -- Each powered summand is a scalar multiple of the corresponding generator `f i ^ (n + 1)`.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, -, rfl⟩
    simpa [mul_pow] using
      (Ideal.mul_mem_left (koszulPowerIdeal f n) (c i ^ (n + 1))
        (Ideal.subset_span ⟨i, rfl⟩) :
          c i ^ (n + 1) * f i ^ (n + 1) ∈ koszulPowerIdeal f n)
  -- Substitute the chosen expansion of `a` and then push the power membership into `J_n`.
  simpa [hc] using hspan hsum

/-- Helper for Lemma 15.92.16: the fixed-right-factor derived tensor functor sends scalar
identities to scalar identities. -/
private theorem derivedTensorProduct_map_smul_id_local
    (K X : DMod) (a : A) :
    (derivedTensorProduct K).map (a • 𝟙 X) = a • 𝟙 ((derivedTensorProduct K).obj X) := by
  sorry

/-- Helper for Lemma 15.92.16: the fixed-right-factor derived tensor functor preserves zero
morphisms. -/
private theorem derivedTensorProduct_map_zero_local
    (K : DMod) {X Y : DMod} :
    (derivedTensorProduct K).map (0 : X ⟶ Y) = 0 := by
  let F : DMod ⥤ DMod := derivedTensorProduct K
  -- Freeze the additive structure here for the same reason as in the scalar adapter above.
  letI : F.CommShift ℤ := by
    simpa [F] using (derivedTensorProduct_commShift K)
  letI : F.IsTriangulated := by
    simpa [F] using (derivedTensorProduct_isTriangulated K)
  letI : F.Additive := inferInstance
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  -- Once the zero-preserving instance is fixed, `map_zero` gives the transport directly.
  simpa [F] using (Functor.map_zero F (0 : X ⟶ Y))

/-- Helper for Lemma 15.92.16: every element of `Ideal.span (Set.range f)` acts nilpotently on
each tensor stage of the powered Koszul tower. -/
private theorem tensor_koszul_power_stage_power_zero_of_mem_spanRange
    (f : Fin r → A) (K : DMod) {a : A} (ha : a ∈ Ideal.span (Set.range f)) (n : ℕ) :
    ∃ e : ℕ,
      (a ^ e : A) •
        𝟙 ((derivedCompletionKoszulPowerTensorDerivedInverseSystem K f).obj (Opposite.op n)) = 0 :=
    by
  refine ⟨r * n + 1, ?_⟩
  have hpow_mem :
      a ^ (r * n + 1) ∈ koszulPowerIdeal f n :=
    pow_mem_koszulPowerIdeal_of_mem_spanRange f n ha
  have hstage_zero :
      (a ^ (r * n + 1) : A) •
          𝟙 ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n)) = 0 :=
    derived_koszul_power_stage_smul_eq_zero_of_mem_power_ideal f n hpow_mem
  let F : DMod ⥤ DMod := derivedTensorProduct K
  -- Map the untensored zero equality through the fixed tensor functor and rewrite only via the
  -- dedicated scalar and zero adapters.
  have htensor_zero := congrArg F.map hstage_zero
  have hmap_zero :
      F.map
          ((a ^ (r * n + 1) : A) •
            𝟙 ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n))) = 0 := by
    calc
      F.map
          ((a ^ (r * n + 1) : A) •
            𝟙 ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n))) =
        F.map (0 :
          (derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n) ⟶
            (derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n)) := htensor_zero
      _ = 0 := by
        simpa [F] using
          (derivedTensorProduct_map_zero_local
            (K := K)
            (X := (derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n))
            (Y := (derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n)))
  calc
    (a ^ (r * n + 1) : A) •
        𝟙 ((derivedCompletionKoszulPowerTensorDerivedInverseSystem K f).obj (Opposite.op n)) =
      F.map
        ((a ^ (r * n + 1) : A) •
          𝟙 ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n))) := by
            simpa [derivedCompletionKoszulPowerTensorDerivedInverseSystem, F] using
              (derivedTensorProduct_map_smul_id_local
                K
                ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n))
                (a ^ (r * n + 1))).symm
    _ = 0 := hmap_zero

/- Domain-style sampling for the localized Lemma 15.92.14 bridge inside Lemma 15.92.16:
- primary domain: derived completeness in `D(A)` and its behavior under sequential derived limits;
- sampled owner declarations:
  `DerivedCategory.IsDerivedCompleteWithRespectTo`,
  `DerivedCategory.isDerivedCompleteWithRespectTo_iff`,
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.DerivedCategory.localizationAwayT_isDerivedLimit`;
- best owner abstraction: the canonical predicate `K.IsDerivedCompleteWithRespectTo I` together
  with the ambient derived-limit owner `IsDerivedLimit Ksys K'`;
- primitive data: the ideal `I`, the inverse system `Ksys`, a stagewise derived-completeness
  witness, and a chosen derived-limit witness;
- derived API: the stronger source-facing bridge where stagewise derived completeness is produced
  from the textbook power-zero hypothesis. -/

/-- Helper for Lemma 15.92.16: shifting a chosen product yields a chosen product of the shifted
family. -/
private theorem hasProduct_shift_local {ι : Type*} (X : ι → DMod) [HasProduct X] (n : ℤ) :
    HasProduct (fun i ↦ (X i)⟦n⟧) := by
  -- Transport the chosen product along the shift functor, which preserves all limits.
  let t :
      IsLimit
        (Fan.mk ((∏ᶜ X)⟦n⟧) (fun i ↦ (Pi.π X i)⟦n⟧')) := by
    simpa using
      (Limits.isLimitOfHasProductOfPreservesLimit (shiftFunctor DMod n) X)
  exact ⟨⟨_, t⟩⟩

/-- Helper for Lemma 15.92.16: applying represented Hom to a product identifies it with the
product of the stagewise represented Hom modules. -/
private noncomputable abbrev preadditiveCoyonedaObj_product_iso_local
    (L : DMod) (X : ℕ → DMod) [HasProduct X] :
    (preadditiveCoyonedaObj L).obj (∏ᶜ X) ≅
      ∏ᶜ fun n ↦ (preadditiveCoyonedaObj L).obj (X n) :=
  let Z : ℕ → ModuleCat (End L)ᵐᵒᵖ := fun n ↦ (preadditiveCoyonedaObj L).obj (X n)
  (LinearEquiv.ofBijective
      (LinearMap.pi fun n ↦
        ModuleCat.Hom.hom ((preadditiveCoyonedaObj L).map (Pi.π X n))) <| by
        constructor
        · intro f g hfg
          apply Pi.hom_ext
          intro n
          have hfg' := congrArg (fun t : (n : ℕ) → (L ⟶ X n) ↦ t n) hfg
          simpa using hfg'
        · intro x
          refine ⟨Pi.lift fun n ↦ x n, ?_⟩
          ext n
          change (Pi.lift fun n ↦ x n) ≫ Pi.π X n = x n
          rw [Pi.lift_π]).toModuleIso ≪≫
    (ModuleCat.piIsoPi Z).symm

/-- Helper for Lemma 15.92.16: multiplication by a unit scalar on an object is an isomorphism. -/
private theorem isIso_units_smul_id_local
    {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (r : Rˣ) (X : C) :
    IsIso ((r : R) • 𝟙 X) := by
  -- The inverse is multiplication by the inverse unit.
  refine ⟨⟨((↑(r⁻¹) : R) • 𝟙 X), ?_, ?_⟩⟩
  · simpa [smul_smul, Linear.comp_units_smul]
  · simpa [smul_smul, Linear.units_smul_comp]

/-- Helper for Lemma 15.92.16: after restricting scalars from `A_(g^e)` to `A`, the endomorphism
`(g^e) • 𝟙` remains an isomorphism. Since localization away from `g` inverts every power of `g`,
this is the exact bridge needed for the source proof route. -/
private theorem localizationAway_power_restrictScalars_smul_id_isIso_local
    (g : A) (e : ℕ) (E : DerivedCategory (ModuleCat (Localization.Away g))) :
    IsIso
      ((g ^ e : A) •
        𝟙 (((ModuleCat.restrictScalars
          (algebraMap A (Localization.Away g))).mapDerivedCategory.obj E))) := by
  let F :=
    (ModuleCat.restrictScalars (algebraMap A (Localization.Away g))).mapDerivedCategory
  let F₀ :=
    (ModuleCat.restrictScalars (algebraMap A (Localization.Away g))).mapHomologicalComplex
      (ComplexShape.up ℤ)
  let C := DerivedCategory.Q.objPreimage E
  let eE : DerivedCategory.Q.obj C ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let eX : F.obj E ≅ DerivedCategory.Q.obj (F₀.obj C) :=
    F.mapIso eE.symm ≪≫ (ModuleCat.restrictScalars
      (algebraMap A (Localization.Away g))).mapDerivedCategoryFactors.app C
  let u : (Localization.Away g)ˣ :=
    (IsLocalization.Away.algebraMap_isUnit g).unit ^ e
  have hcomplex_map :
      F₀.map (((u : Localization.Away g) • 𝟙 C) : C ⟶ C) =
        ((g ^ e : A) • 𝟙 (F₀.obj C)) := by
    -- Restriction of scalars sends the localized unit action to the expected `A`-linear action.
    ext i x
    rw [Functor.mapHomologicalComplex_map_f]
    let y : C.X i := x
    change (((algebraMap A (Localization.Away g)) g ^ e : Localization.Away g) • y =
      ((algebraMap A (Localization.Away g)) (g ^ e) : Localization.Away g) • y)
    simp [map_pow]
  have hsource_iso :
      IsIso (((u : Localization.Away g) • 𝟙 C) : C ⟶ C) := by
    -- Multiplication by a unit is invertible on the concrete preimage complex.
    simpa using
      (isIso_units_smul_id_local (R := Localization.Away g) u C)
  have hcomplex_iso :
      IsIso (((g ^ e : A) • 𝟙 (F₀.obj C)) : F₀.obj C ⟶ F₀.obj C) := by
    -- Mapping preserves the unit-scalar isomorphism at the complex level.
    simpa [hcomplex_map] using
      (Functor.map_isIso F₀
        (((u : Localization.Away g) • 𝟙 C) : C ⟶ C))
  have hderived_iso :
      IsIso
        (((g ^ e : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C))) :
          DerivedCategory.Q.obj (F₀.obj C) ⟶ DerivedCategory.Q.obj (F₀.obj C)) := by
    -- Applying `Q` preserves the complex-level scalar isomorphism.
    simpa [Functor.map_smul] using
      (Functor.map_isIso DerivedCategory.Q
        (((g ^ e : A) • 𝟙 (F₀.obj C)) : F₀.obj C ⟶ F₀.obj C))
  have hconj :
      eX.hom ≫ ((g ^ e : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C))) ≫ eX.inv =
        ((g ^ e : A) • 𝟙 (F.obj E)) := by
    -- Scalar multiplication commutes with the comparison isomorphism to the concrete model.
    apply (cancel_mono eX.hom).1
    calc
      (eX.hom ≫ ((g ^ e : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C))) ≫ eX.inv) ≫ eX.hom =
          eX.hom ≫ ((g ^ e : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C))) := by
            simp
      _ =
          (g ^ e : A) • eX.hom := by
            simp [CategoryTheory.Linear.comp_smul]
      _ = ((g ^ e : A) • 𝟙 (F.obj E)) ≫ eX.hom := by
            simp [CategoryTheory.Linear.smul_comp]
  -- Conjugate the concrete isomorphism back across the comparison isomorphism.
  simpa [hconj] using
    (show IsIso
      (eX.hom ≫ ((g ^ e : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C))) ≫ eX.inv) by
        infer_instance)

/-- Helper for Lemma 15.92.16: if `(g^e) • 𝟙` acts by zero on `K`, then every morphism from an
object of `D(A_g)` to `K` vanishes after restriction of scalars. The localized source already
makes `g^e` invertible, so the source-proof cancellation argument applies verbatim. -/
private theorem localizationAwayDerivedHomVanishingCondition_of_power_zero_action_local
    (g : A) (e : ℕ) (K : DMod)
    (hzero : (g ^ e : A) • 𝟙 K = 0) :
    localizationAwayDerivedHomVanishingCondition g K := by
  intro E
  let F :=
    (ModuleCat.restrictScalars (algebraMap A (Localization.Away g))).mapDerivedCategory
  let X : DMod := F.obj E
  have hsourceIso :
      IsIso ((g ^ e : A) • 𝟙 X) :=
    localizationAway_power_restrictScalars_smul_id_isIso_local g e E
  refine ⟨fun φ ψ ↦ ?_⟩
  have hφ : φ = 0 := by
    -- Cancel the invertible source action after rewriting it across the morphism `φ`.
    have hφzero : ((g ^ e : A) • 𝟙 X) ≫ φ = 0 := by
      calc
        ((g ^ e : A) • 𝟙 X) ≫ φ = (g ^ e : A) • φ := by
          simp [CategoryTheory.Linear.smul_comp]
        _ = φ ≫ ((g ^ e : A) • 𝟙 K) := by
          simp [CategoryTheory.Linear.comp_smul]
        _ = 0 := by
          rw [hzero]
          simp
    have hcancel :
        inv ((g ^ e : A) • 𝟙 X) ≫ (((g ^ e : A) • 𝟙 X) ≫ φ) = φ := by
      simpa [Category.assoc] using
        (IsIso.inv_hom_id_assoc ((g ^ e : A) • 𝟙 X) φ)
    calc
      φ = inv ((g ^ e : A) • 𝟙 X) ≫ (((g ^ e : A) • 𝟙 X) ≫ φ) := by
        exact hcancel.symm
      _ = inv ((g ^ e : A) • 𝟙 X) ≫ 0 := by
        rw [hφzero]
      _ = 0 := by simp
  have hψ : ψ = 0 := by
    -- The same cancellation argument shows every competing morphism `ψ` is also zero.
    have hψzero : ((g ^ e : A) • 𝟙 X) ≫ ψ = 0 := by
      calc
        ((g ^ e : A) • 𝟙 X) ≫ ψ = (g ^ e : A) • ψ := by
          simp [CategoryTheory.Linear.smul_comp]
        _ = ψ ≫ ((g ^ e : A) • 𝟙 K) := by
          simp [CategoryTheory.Linear.comp_smul]
        _ = 0 := by
          rw [hzero]
          simp
    have hcancel :
        inv ((g ^ e : A) • 𝟙 X) ≫ (((g ^ e : A) • 𝟙 X) ≫ ψ) = ψ := by
      simpa [Category.assoc] using
        (IsIso.inv_hom_id_assoc ((g ^ e : A) • 𝟙 X) ψ)
    calc
      ψ = inv ((g ^ e : A) • 𝟙 X) ≫ (((g ^ e : A) • 𝟙 X) ≫ ψ) := by
        exact hcancel.symm
      _ = inv ((g ^ e : A) • 𝟙 X) ≫ 0 := by
        rw [hψzero]
      _ = 0 := by simp
  simpa [hφ, hψ]

/-- Helper for Lemma 15.92.16: an object annihilated by powers of each `f ∈ I` is derived
complete with respect to `I`. -/
private theorem stage_isDerivedCompleteWithRespectTo_of_power_nilpotent_scalars
    (I : Ideal A) (K : DMod)
    (hpow : ∀ f ∈ I, ∃ e : ℕ, (f ^ e : A) • 𝟙 K = 0) :
    K.IsDerivedCompleteWithRespectTo I := by
  -- Test derived completeness against each `f ∈ I`; the localized source turns `f^e` into a unit.
  rw [DerivedCategory.isDerivedCompleteWithRespectTo_iff]
  intro f hf
  rcases hpow f hf with ⟨e, he⟩
  exact localizationAwayDerivedHomVanishingCondition_of_power_zero_action_local f e K he

/-- Helper for Lemma 15.92.16: a derived-complete target has zero represented-Hom module from
any source obtained by restricting scalars from `D(A_f)`. -/
private theorem localized_source_represented_hom_isZero_of_isDerivedCompleteWithRespectTo_local
    (I : Ideal A) (f : A) (hf : f ∈ I) (K : DMod)
    (hK : K.IsDerivedCompleteWithRespectTo I)
    (E : DerivedCategory (ModuleCat (Localization.Away f))) :
    let F := (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
    let L : DMod := F.obj E
    IsZero ((preadditiveCoyonedaObj L).obj K) := by
  let F := (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
  let L : DMod := F.obj E
  -- Derived completeness gives a subsingleton Hom-set from the localized source.
  have hsub : Subsingleton (L ⟶ K) := by
    simpa [F, L] using
      ((DerivedCategory.isDerivedCompleteWithRespectTo_iff K I).1 hK f hf E)
  -- A represented Hom module with subsingleton underlying type is a zero module.
  change IsZero (ModuleCat.of (End L)ᵐᵒᵖ (L ⟶ K))
  letI : Subsingleton (L ⟶ K) := hsub
  exact ModuleCat.isZero_of_subsingleton _

/-- Helper for Lemma 15.92.16: derived completeness also kills the shifted represented-Hom module
from any source obtained by restricting scalars from `D(A_f)`. -/
private theorem localized_source_shifted_represented_hom_isZero_of_isDerivedCompleteWithRespectTo_local
    (I : Ideal A) (f : A) (hf : f ∈ I) (K : DMod)
    (hK : K.IsDerivedCompleteWithRespectTo I)
    (E : DerivedCategory (ModuleCat (Localization.Away f))) :
    let F := (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
    let L : DMod := F.obj E
    IsZero ((preadditiveCoyonedaObj L).obj (K⟦(-1 : ℤ)⟧)) := by
  let F := (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
  let L : DMod := F.obj E
  -- Apply derived completeness to the shifted source object `E⟦1⟧`.
  have hshift_source :
      Subsingleton (F.obj (E⟦(1 : ℤ)⟧) ⟶ K) := by
    exact ((DerivedCategory.isDerivedCompleteWithRespectTo_iff K I).1 hK f hf (E⟦(1 : ℤ)⟧))
  have hshifted : Subsingleton (L⟦(1 : ℤ)⟧ ⟶ K) := by
    let e : F.obj (E⟦(1 : ℤ)⟧) ≅ L⟦(1 : ℤ)⟧ := (F.commShiftIso (1 : ℤ)).app E
    -- Transport the subsingleton statement across the functorial shift comparison.
    refine ⟨fun g h ↦ ?_⟩
    exact (cancel_epi e.hom).1 (hshift_source.elim (e.hom ≫ g) (e.hom ≫ h))
  have hsub : Subsingleton (L ⟶ K⟦(-1 : ℤ)⟧) := by
    let e :
        (L ⟶ K⟦(-1 : ℤ)⟧) ≃ (L⟦(1 : ℤ)⟧ ⟶ K) :=
      (((shiftEquiv DMod (-1 : ℤ)).symm.toAdjunction.homEquiv L K).symm)
    -- Use the standard shift adjunction to move the vanishing statement to the target shift.
    refine ⟨fun g h ↦ e.injective (hshifted.elim (e g) (e h))⟩
  -- Convert the subsingleton morphism group into zero represented-Hom module.
  change IsZero (ModuleCat.of (End L)ᵐᵒᵖ (L ⟶ K⟦(-1 : ℤ)⟧))
  letI : Subsingleton (L ⟶ K⟦(-1 : ℤ)⟧) := hsub
  exact ModuleCat.isZero_of_subsingleton _

/-- Helper for Lemma 15.92.16: if every stage is derived complete, then the ordinary represented
Hom tower from a localized source is stagewise zero. -/
private theorem stagewise_represented_hom_isZero_of_stagewise_complete_local
    (I : Ideal A) (Ksys : ℕᵒᵖ ⥤ DMod) (f : A) (hf : f ∈ I)
    (E : DerivedCategory (ModuleCat (Localization.Away f)))
    (hstage : ∀ n : ℕ, (Ksys.obj (op n)).IsDerivedCompleteWithRespectTo I)
    (n : ℕ) :
    let L : DMod :=
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
    IsZero (((Ksys ⋙ preadditiveCoyonedaObj L).obj (op n))) := by
  let L : DMod :=
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
  -- Apply the object-level represented-Hom vanishing to the `n`-th stage.
  simpa [L] using
    localized_source_represented_hom_isZero_of_isDerivedCompleteWithRespectTo_local
      I f hf (Ksys.obj (op n)) (hstage n) E

/-- Helper for Lemma 15.92.16: if every stage is derived complete, then the shifted represented
Hom tower from a localized source is stagewise zero. -/
private theorem stagewise_shifted_represented_hom_isZero_of_stagewise_complete_local
    (I : Ideal A) (Ksys : ℕᵒᵖ ⥤ DMod) (f : A) (hf : f ∈ I)
    (E : DerivedCategory (ModuleCat (Localization.Away f)))
    (hstage : ∀ n : ℕ, (Ksys.obj (op n)).IsDerivedCompleteWithRespectTo I)
    (n : ℕ) :
    let L : DMod :=
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
    IsZero ((((Ksys ⋙ shiftFunctor DMod (-1 : ℤ)) ⋙ preadditiveCoyonedaObj L).obj (op n))) := by
  let L : DMod :=
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
  -- Apply the shifted object-level vanishing to the `n`-th stage.
  simpa [L] using
    localized_source_shifted_represented_hom_isZero_of_isDerivedCompleteWithRespectTo_local
      I f hf (Ksys.obj (op n)) (hstage n) E

/-- Helper for Lemma 15.92.16: in the Milnor triangle for a derived limit of stagewise derived
complete objects, the represented-Hom group at the middle vertex vanishes for every localized
test object. -/
private theorem represented_hom_middle_isZero_of_stagewise_complete_local
    (I : Ideal A) (Ksys : ℕᵒᵖ ⥤ DMod) (K' : DMod) (f : A) (hf : f ∈ I)
    (E : DerivedCategory (ModuleCat (Localization.Away f)))
    (hstage :
      ∀ n : ℕ, (Ksys.obj (op n)).IsDerivedCompleteWithRespectTo I)
    (hlim : IsDerivedLimit Ksys K') :
    let F := (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
    let L : DMod := F.obj E
    IsZero ((preadditiveCoyoneda.obj (Opposite.op L)).obj K') := by
  let F := (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
  let L : DMod := F.obj E
  let Fadd := preadditiveCoyoneda.obj (Opposite.op L)
  rcases hlim with ⟨hprodKsys, ⟨ι, δ, hδ⟩⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hprodKsys
  have hright_stage :
      ∀ n : ℕ, IsZero (((Ksys ⋙ preadditiveCoyonedaObj L).obj (op n))) := by
    -- The ordinary represented-Hom tower vanishes stagewise because each stage is derived
    -- complete with respect to `I`.
    intro n
    simpa [F, L] using
      stagewise_represented_hom_isZero_of_stagewise_complete_local I Ksys f hf E hstage n
  have hleft_stage :
      ∀ n : ℕ,
        IsZero ((((Ksys ⋙ shiftFunctor DMod (-1 : ℤ)) ⋙ preadditiveCoyonedaObj L).obj
          (op n))) := by
    -- The shifted tower vanishes stagewise by the shifted-source version of the same argument.
    intro n
    simpa [F, L] using
      stagewise_shifted_represented_hom_isZero_of_stagewise_complete_local
        I Ksys f hf E hstage n
  have hright_product_module :
      IsZero ((preadditiveCoyonedaObj L).obj (∏ᶜ inverseSystemFamily Ksys)) := by
    have hpi :
        IsZero
          (∏ᶜ fun n ↦ (preadditiveCoyonedaObj L).obj (Ksys.obj (op n))) := by
      -- The product is zero because each projection lands in a stagewise zero object.
      refine (IsZero.iff_id_eq_zero _).2 ?_
      apply Pi.hom_ext
      intro n
      exact (hright_stage n).eq_of_tgt _ _
    exact hpi.of_iso
      (preadditiveCoyonedaObj_product_iso_local L (inverseSystemFamily Ksys))
  let shiftedFamily : ℕ → DMod := fun n ↦ (Ksys.obj (op n))⟦(-1 : ℤ)⟧
  letI : HasProduct shiftedFamily := hasProduct_shift_local (inverseSystemFamily Ksys) (-1 : ℤ)
  have hleft_product_module :
      IsZero ((preadditiveCoyonedaObj L).obj ((∏ᶜ inverseSystemFamily Ksys)⟦(-1 : ℤ)⟧)) := by
    have hpi :
        IsZero (∏ᶜ fun n ↦ (preadditiveCoyonedaObj L).obj (shiftedFamily n)) := by
      -- The same product argument works after shifting each stage.
      refine (IsZero.iff_id_eq_zero _).2 ?_
      apply Pi.hom_ext
      intro n
      exact (hleft_stage n).eq_of_tgt _ _
    have hshifted_product :
        IsZero ((preadditiveCoyonedaObj L).obj (∏ᶜ shiftedFamily)) := by
      exact hpi.of_iso
        (preadditiveCoyonedaObj_product_iso_local L shiftedFamily)
    let e :
        ((∏ᶜ inverseSystemFamily Ksys)⟦(-1 : ℤ)⟧) ≅
          ∏ᶜ shiftedFamily :=
      PreservesProduct.iso (shiftFunctor DMod (-1 : ℤ)) (inverseSystemFamily Ksys)
    exact hshifted_product.of_iso ((preadditiveCoyonedaObj L).mapIso e)
  have hright_product :
      IsZero (Fadd.obj (∏ᶜ inverseSystemFamily Ksys)) := by
    -- Forget the module structure after identifying the unshifted product module with zero.
    simpa [Fadd] using
      (forget₂ (ModuleCat (End L)ᵐᵒᵖ) AddCommGrpCat).map_isZero hright_product_module
  have hleft_product :
      IsZero (Fadd.obj ((∏ᶜ inverseSystemFamily Ksys)⟦(-1 : ℤ)⟧)) := by
    -- Forget the module structure for the shifted product as well.
    simpa [Fadd] using
      (forget₂ (ModuleCat (End L)ᵐᵒᵖ) AddCommGrpCat).map_isZero hleft_product_module
  let T : Triangle DMod := Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let S :=
    (shortComplexOfDistTriangle T.invRotate (inv_rot_of_distTriang _ hδ)).map Fadd
  have hmiddle_add : IsZero S.X₂ := by
    have hexact : S.Exact := by
      -- Applying represented Hom to the inverse-rotated Milnor triangle gives an exact sequence.
      simpa [S] using Fadd.map_distinguished_exact T.invRotate (inv_rot_of_distTriang _ hδ)
    -- The middle term is zero because the two outer terms are already zero.
    refine hexact.isZero_X₂ ?_ ?_
    · exact hleft_product.eq_of_src _ _
    · exact hright_product.eq_of_tgt _ _
  simpa [F, L, Fadd, S, T] using hmiddle_add

/-- Helper for Lemma 15.92.16: any derived limit of a sequential inverse system of
`I`-derived-complete objects is again derived complete with respect to `I`. -/
private theorem isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise_complete_local
    (I : Ideal A) (Ksys : ℕᵒᵖ ⥤ DMod) (K' : DMod)
    (hstage :
      ∀ n : ℕ, (Ksys.obj (op n)).IsDerivedCompleteWithRespectTo I)
    (hlim : IsDerivedLimit Ksys K') :
    K'.IsDerivedCompleteWithRespectTo I := by
  -- Route correction: keep the source Milnor-triangle proof, but isolate the represented-Hom
  -- middle-term vanishing into a separate helper before invoking the completeness criterion.
  rw [DerivedCategory.isDerivedCompleteWithRespectTo_iff]
  intro f hf E
  let F := (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
  let L : DMod := F.obj E
  have hmiddle_zero :
      IsZero ((preadditiveCoyoneda.obj (Opposite.op L)).obj K') := by
    -- The local Milnor helper is exactly the vanishing statement required by the criterion.
    simpa [F, L] using
      represented_hom_middle_isZero_of_stagewise_complete_local I Ksys K' f hf E hstage hlim
  -- Convert the zero represented-Hom group into the required subsingleton Hom-set.
  simpa [L] using AddCommGrpCat.subsingleton_of_isZero hmiddle_zero

/-- Helper for Lemma 15.92.16: if every stage of a sequential inverse system is annihilated by
powers of every `f ∈ I`, then any derived limit of that system is derived complete with respect
to `I`. -/
private theorem isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise_power_zero_local
    (I : Ideal A) (Ksys : ℕᵒᵖ ⥤ DMod) (K' : DMod)
    (hpow :
      ∀ f ∈ I, ∀ n : ℕ, ∃ e : ℕ, (f ^ e : A) • 𝟙 (Ksys.obj (op n)) = 0)
    (hlim : IsDerivedLimit Ksys K') :
    K'.IsDerivedCompleteWithRespectTo I := by
  -- First make each stage derived complete, then pass completeness through the derived limit.
  apply isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise_complete_local I Ksys K'
  · intro n
    exact stage_isDerivedCompleteWithRespectTo_of_power_nilpotent_scalars I (Ksys.obj (op n))
      (fun f hf ↦ hpow f hf n)
  · exact hlim

-- Proof sketch: Lemma `15.28.6` makes each generator `f i` act null-homotopically on every
-- powered Koszul stage, so each tensor stage satisfies the stagewise annihilation hypothesis from
-- the localized 15.92.14 bridge. Applying that bridge to the chosen derived limit gives derived
-- completeness.
/-- Lemma 15.92.16: in Situation `15.92.15`, if `K'` is a chosen derived limit of the inverse
system obtained by applying the derived tensor functor `- \otimes_A^{\mathbf L} K` to the powered
Koszul tower `(K_n^\bullet)_n`, then `K'` is derived complete with respect to the ideal
`I = (f_1, \ldots, f_r)`. This is the library-facing form of the textbook object
`R \!\varprojlim (K \otimes_A^{\mathbf L} K_n^\bullet)`. -/
@[stacks 091Y]
theorem derivedLimitOfKoszulPowerTensor_isDerivedCompleteWithRespectTo_spanRange
    (f : Fin r → A) (K K' : DMod)
    (hlim : IsDerivedLimit (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) K') :
    K'.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f)) := by
  -- Route correction: the broken imported-owner dependency is replaced by the same source-faithful
  -- stagewise-power-zero bridge proved locally in this file.
  refine isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise_power_zero_local
      (I := Ideal.span (Set.range f))
      (Ksys := derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)
      (K' := K')
      ?_ hlim
  intro a ha n
  exact tensor_koszul_power_stage_power_zero_of_mem_spanRange f K ha n

end

end CategoryTheory
