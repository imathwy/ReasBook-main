import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Monoidal.Preadditive
import StacksProject_2024.stacks_project.Chap21.«21_35_9_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

local notation "D" => RingedSiteDerived J 𝒪

/-- Lemma 21.35.9: the canonical morphism
`M ⊗ L^∨ ⟶ ihom L M`
induces a canonical map
`H⁰(𝒞, M ⊗ L^∨) ⟶ Hom_D(L, M)`,
formalized here as the canonical bridge from morphisms
`𝟙_ D ⟶ M ⊗ L^∨` out of the monoidal unit of `D`
to morphisms `L ⟶ M`. -/
@[stacks 08JD]
noncomputable abbrev ringedSiteDerivedEvaluationH0ToHom
    (L M : D) :
    (𝟙_ D ⟶ M ⊗ L^∨) → (L ⟶ M) :=
  fun s ↦
    MonoidalClosed.uncurry' (s ≫ ringedSiteDerivedEvaluationHom L M)

@[simp] theorem curry'_ringedSiteDerivedEvaluationH0ToHom
    (L M : D) (s : 𝟙_ D ⟶ M ⊗ L^∨) :
    MonoidalClosed.curry' (ringedSiteDerivedEvaluationH0ToHom L M s) =
      s ≫ ringedSiteDerivedEvaluationHom L M := by
  simp [ringedSiteDerivedEvaluationH0ToHom]

/-- The induced map on degree-zero global sections is functorial in the variable `M`. -/
theorem ringedSiteDerivedEvaluationH0ToHom_natural
    {L M₁ M₂ : D} (f : M₁ ⟶ M₂)
    (s : 𝟙_ D ⟶ M₁ ⊗ L^∨) :
    ringedSiteDerivedEvaluationH0ToHom L M₂
        (s ≫ (f ⊗ₘ 𝟙 (L^∨))) =
      ringedSiteDerivedEvaluationH0ToHom L M₁ s ≫ f := by
  have hcomparison :
      (f ⊗ₘ 𝟙 (L^∨)) ≫ ringedSiteDerivedTensorInternalHomComparison M₂ (𝟙_ D) L =
        ringedSiteDerivedTensorInternalHomComparison M₁ (𝟙_ D) L ≫
          (ihom L).map (ρ_ M₁).hom ≫ (ihom L).map f ≫ (ihom L).map (ρ_ M₂).inv := by
    simpa [ringedSiteDerivedDualObject, Category.assoc] using
      (ringedSiteDerivedTensorInternalHomComparison_natural
        f (𝟙 (𝟙_ D)) (𝟙 L)).w
  have htarget :
      (f ⊗ₘ 𝟙 (L^∨)) ≫ ringedSiteDerivedEvaluationHom L M₂ =
        ringedSiteDerivedEvaluationHom L M₁ ≫ (ihom L).map f := by
    calc
      (f ⊗ₘ 𝟙 (L^∨)) ≫ ringedSiteDerivedEvaluationHom L M₂ =
          ((f ⊗ₘ 𝟙 (L^∨)) ≫ ringedSiteDerivedTensorInternalHomComparison M₂ (𝟙_ D) L) ≫
            (ihom L).map (ρ_ M₂).hom := by
              simp [ringedSiteDerivedEvaluationHom, Category.assoc]
      _ =
          (ringedSiteDerivedTensorInternalHomComparison M₁ (𝟙_ D) L ≫
            (ihom L).map (ρ_ M₁).hom ≫ (ihom L).map f ≫ (ihom L).map (ρ_ M₂).inv) ≫
              (ihom L).map (ρ_ M₂).hom := by
                rw [hcomparison]
      _ = ringedSiteDerivedTensorInternalHomComparison M₁ (𝟙_ D) L ≫
            (ihom L).map (ρ_ M₁).hom ≫ (ihom L).map f := by
              simp [Category.assoc]
      _ = ringedSiteDerivedEvaluationHom L M₁ ≫ (ihom L).map f := by
              simp [ringedSiteDerivedEvaluationHom, Category.assoc]
  have hs :
      (s ≫ (f ⊗ₘ 𝟙 (L^∨))) ≫ ringedSiteDerivedEvaluationHom L M₂ =
        (s ≫ ringedSiteDerivedEvaluationHom L M₁) ≫
          (ihom L).map f := by
    simpa [Category.assoc] using congrArg (fun k ↦ s ≫ k) htarget
  apply MonoidalClosed.curry'_injective
  calc
    MonoidalClosed.curry'
        (ringedSiteDerivedEvaluationH0ToHom L M₂
          (s ≫ (f ⊗ₘ 𝟙 (L^∨)))) =
        (s ≫ (f ⊗ₘ 𝟙 (L^∨))) ≫ ringedSiteDerivedEvaluationHom L M₂ := by
          rw [curry'_ringedSiteDerivedEvaluationH0ToHom]
    _ = (s ≫ ringedSiteDerivedEvaluationHom L M₁) ≫ (ihom L).map f := hs
    _ = MonoidalClosed.curry'
          (ringedSiteDerivedEvaluationH0ToHom L M₁ s) ≫ (ihom L).map f := by
          rw [curry'_ringedSiteDerivedEvaluationH0ToHom]
    _ = MonoidalClosed.curry'
          (ringedSiteDerivedEvaluationH0ToHom L M₁ s ≫ f) := by
          rw [MonoidalClosed.curry'_ihom_map]

/-- The canonical degree-zero comparison map is additive in the global-sections variable. -/
theorem ringedSiteDerivedEvaluationH0ToHom_add
    [Preadditive D] [MonoidalPreadditive D]
    (L M : D) (s t : 𝟙_ D ⟶ M ⊗ L^∨) :
    ringedSiteDerivedEvaluationH0ToHom L M (s + t) =
      ringedSiteDerivedEvaluationH0ToHom L M s +
        ringedSiteDerivedEvaluationH0ToHom L M t := by
  unfold ringedSiteDerivedEvaluationH0ToHom MonoidalClosed.uncurry' MonoidalClosed.uncurry
  rw [Preadditive.add_comp, Adjunction.homAddEquiv_symm_add (ihom.adjunction L)]
  exact CategoryTheory.Preadditive.comp_add _ _ _ _ _ _

/-- The additive hom underlying the degree-zero comparison
`H⁰(𝒞, M ⊗ L^∨) ⟶ Hom_D(L, M)`. -/
noncomputable abbrev ringedSiteDerivedEvaluationH0ToHomAddMonoidHom
    [Preadditive D] [MonoidalPreadditive D]
    (L M : D) :
    AddMonoidHom (𝟙_ D ⟶ M ⊗ L^∨) (L ⟶ M) :=
  AddMonoidHom.mk'
    (ringedSiteDerivedEvaluationH0ToHom L M)
    (ringedSiteDerivedEvaluationH0ToHom_add L M)

/-- The degree-zero comparison
`H⁰(𝒞, M ⊗ L^∨) ⟶ Hom_D(L, M)` as a morphism of `AddCommGrpCat`. -/
noncomputable abbrev ringedSiteDerivedEvaluationH0ToHomAddCommGrpHom
    [Preadditive D] [MonoidalPreadditive D]
    (L M : D) :
    AddCommGrpCat.of (𝟙_ D ⟶ M ⊗ L^∨) ⟶
      AddCommGrpCat.of (L ⟶ M) :=
  AddCommGrpCat.ofHom (ringedSiteDerivedEvaluationH0ToHomAddMonoidHom L M)

end

end SheafOfModules.RingedSite
