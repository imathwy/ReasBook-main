import StacksProject_2024.Chap21.Lemma_21_35_7

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

/- Domain-style sampling for 21.35.9.1:
- primary domain: the braided closed monoidal structure on the derived category
  `RingedSiteDerived J 𝒪` of modules on a ringed site;
- sampled owner declarations:
  `RingedSiteDerived`,
  `ringedSiteDerivedTensorInternalHomComparison`,
  `ihom`,
  `CategoryTheory.MonoidalCategory.rightUnitorNatIso`;
- best owner abstraction: the ambient owner is the chapter category `RingedSiteDerived J 𝒪`, and
  the source-facing evaluation map is the tensor-unit specialization of the canonical comparison
  morphism `ringedSiteDerivedTensorInternalHomComparison`, followed by the right-unitor on the
  target of the internal Hom;
- primitive data: the chapter owner category `RingedSiteDerived J 𝒪` together with its braided
  monoidal closed structure;
- derived API: the source-facing dual notation `L^∨`, the comparison morphism
  `M ⊗ L^∨ ⟶ L ⟹ M`, and the derived-dual evaluation `L^∨ ⊗ L ⟶ 𝟙_ D`.

Source/core/bridge triage:
- `source-facing`: `ringedSiteDerivedDualObject`, `ringedSiteDerivedEvaluationHom`, and
  `ringedSiteDerivedDualEvaluation`;
- `core/canonical`: `RingedSiteDerived J 𝒪`, `ihom`, and
  `ringedSiteDerivedTensorInternalHomComparison`;
- `bridge/view`: the specialization to the tensor unit and the right-unitor map
  `(ihom L).map (ρ_ M).hom`. -/

variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

local notation "D" => RingedSiteDerived J 𝒪
set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

/-- The derived dual `L^∨` in `D`, realized as the internal Hom `L ⟹ 𝟙_ D`. -/
abbrev ringedSiteDerivedDualObject (L : D) : D :=
  L ⟹ 𝟙_ D

@[inherit_doc ringedSiteDerivedDualObject]
notation:max L:max "^∨" => ringedSiteDerivedDualObject L

/-- 21.35.9.1: for objects `M` and `L` of `D`, there is a canonical morphism
`M ⊗ L^∨ ⟶ L ⟹ M`.
Here `L^∨ = L ⟹ 𝟙_ D`. The morphism is the tensor-unit specialization of the canonical
tensor/internal-Hom comparison, followed by the right-unitor identification `M ⊗ 𝟙_ D ≅ M`
inside the target internal Hom. -/
@[stacks 08JE]
abbrev ringedSiteDerivedEvaluationHom
    (L M : D) :
    M ⊗ L^∨ ⟶ L ⟹ M :=
  ringedSiteDerivedTensorInternalHomComparison M (𝟙_ D) L ≫
    (ihom L).map (ρ_ M).hom

/- Uncurrying the source-facing evaluation morphism recovers the tensor-unit specialization of the
braiding/evaluation composite from Lemma 21.35.7, followed by the right unitor on the target. -/
@[simp] theorem ringedSiteDerivedEvaluationHom_uncurry
    (L M : D) :
    uncurry (ringedSiteDerivedEvaluationHom L M) =
      (α_ L M L^∨).inv ≫
        (β_ L M).hom ▷ L^∨ ≫
        (α_ M L L^∨).hom ≫
        M ◁ (ihom.ev L).app (𝟙_ D) ≫
        (ρ_ M).hom := by
  rw [ringedSiteDerivedEvaluationHom, MonoidalClosed.uncurry_natural_right]
  simpa using ringedSiteDerivedTensorInternalHomComparison_uncurry M (𝟙_ D) L

/-- The evaluation morphism `ε : L^∨ ⊗ L ⟶ 𝟙_ D` for the internal-Hom dual `L^∨`. -/
abbrev ringedSiteDerivedDualEvaluation
    (L : D) :
    L^∨ ⊗ L ⟶ 𝟙_ D :=
  (β_ L^∨ L).hom ≫ (ihom.ev L).app (𝟙_ D)

/-- The source-facing braided description of `ringedSiteDerivedDualEvaluation` agrees with the
standard closed-category evaluation map. -/
theorem ringedSiteDerivedDualEvaluation_eq_braided_uncurry
    (L : D) :
    ringedSiteDerivedDualEvaluation L =
      (β_ L^∨ L).hom ≫ MonoidalClosed.uncurry (𝟙 L^∨) := by
  simp [ringedSiteDerivedDualEvaluation, MonoidalClosed.uncurry_eq]

end

end SheafOfModules.RingedSite
