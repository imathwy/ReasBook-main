import StacksProject_2024.Chap20.Lemma_20_42_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CartesianClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

/- Domain-style sampling for 20.42.8.1:
- primary domain: the braided closed monoidal structure on `RingedSpaceDerived X`;
- sampled owner declarations:
  `RingedSpaceDerived`,
  `internalHomComposition`,
  `MonoidalClosed.unitIsoSelf`,
  `ihom.ev`;
- best owner abstraction: the source-facing map is the tensor-unit specialization of the canonical
  chapter bridge `internalHomComposition L (𝟙_ D) M`, after identifying `M` with
  `RHom(𝒪_X, M)` via `unitIsoSelf`;
- primitive data: the canonical chapter owner `RingedSpaceDerived X` and its braided monoidal
  closed structure;
- derived API: the source-facing dual notation `L^∨`, the tensor/internal-Hom evaluation morphism
  `M ⊗ L^∨ ⟶ RHom(L, M)`, and the derived-dual evaluation
  `L^∨ ⊗ L ⟶ 𝟙`.

Source/core/bridge triage:
- `source-facing`: `ringedSpaceDerivedDual`, `ringedSpaceDerivedEvaluationHom`, and
  `ringedSpaceDerivedDualEvaluation`;
- `core/canonical`: `RingedSpaceDerived`, `ihom`, `unitIsoSelf`, and `ihom.ev`;
- `bridge/view`: the chapter comparison `internalHomComposition L (𝟙_ D) M` together with the
  identification `M ≅ (𝟙_ D ⟹ M)` from `unitIsoSelf`. -/

local notation "D" => RingedSpaceDerived X

/-- The derived dual `L^∨` of an object `L` of `D(𝒪_X)`. -/
noncomputable abbrev ringedSpaceDerivedDual (L : D) : D :=
  L ⟹ (𝟙_ D)

@[inherit_doc ringedSpaceDerivedDual]
notation:max L:max "^∨" => ringedSpaceDerivedDual L

/-- 20.42.8.1: the canonical morphism
`M ⊗ L^∨ ⟶ RHom(L, M)` in `D(𝒪_X)`. It is obtained by identifying `M` with
`RHom(𝒪_X, M)` and then specializing the chapter comparison morphism
for internal-Hom composition. -/
@[stacks 08I2]
noncomputable abbrev ringedSpaceDerivedEvaluationHom
    (L M : D) :
    M ⊗ L^∨ ⟶ (L ⟹ M) :=
  ((unitIsoSelf M).symm.hom ⊗ₘ 𝟙 L^∨) ≫
    internalHomComposition L (𝟙_ D) M

/-- The source-facing comparison morphism of `20.42.8.1` is the unit-specialized internal-Hom
composition map. -/
theorem ringedSpaceDerivedEvaluationHom_eq_unit_internalHomComposition
    (L M : D) :
    ringedSpaceDerivedEvaluationHom L M =
      ((unitIsoSelf M).symm.hom ⊗ₘ 𝟙 L^∨) ≫
        internalHomComposition L (𝟙_ D) M :=
  rfl

omit [BraidedCategory D] in
private theorem ringedSpaceDerivedUnitIsoSelf_symm_natural
    {M M' : D} (f : M ⟶ M') :
    f ≫ (MonoidalClosed.unitIsoSelf M').symm.hom =
      (MonoidalClosed.unitIsoSelf M).symm.hom ≫
        (ihom (𝟙_ D)).map f := by
  simpa [MonoidalClosed.unitIsoSelf] using
    (unitNatIso.hom.naturality f)

/-- The canonical morphism of `20.42.8.1` is functorial in the target object `M`. -/
theorem ringedSpaceDerivedEvaluationHom_natural_target
    (L : D) {M M' : D} (f : M ⟶ M') :
    CommSq
      (f ⊗ₘ 𝟙 (L^∨))
      (ringedSpaceDerivedEvaluationHom L M)
      (ringedSpaceDerivedEvaluationHom L M')
      ((ihom L).map f) := by
  refine CommSq.mk ?_
  calc
    (f ⊗ₘ 𝟙 (L^∨)) ≫ ringedSpaceDerivedEvaluationHom L M' =
        (((f ≫ (MonoidalClosed.unitIsoSelf M').symm.hom) ⊗ₘ 𝟙 (L^∨)) ≫
          internalHomComposition L (𝟙_ D) M') := by
            rw [ringedSpaceDerivedEvaluationHom_eq_unit_internalHomComposition, ← Category.assoc]
            rw [← MonoidalCategory.comp_tensor_id]
    _ =
        ((((MonoidalClosed.unitIsoSelf M).symm.hom ≫ (ihom (𝟙_ D)).map f) ⊗ₘ 𝟙 (L^∨)) ≫
          internalHomComposition L (𝟙_ D) M') := by
            rw [ringedSpaceDerivedUnitIsoSelf_symm_natural f]
    _ =
        (((MonoidalClosed.unitIsoSelf M).symm.hom ⊗ₘ 𝟙 (L^∨)) ≫
          ((((ihom (𝟙_ D)).map f) ⊗ₘ 𝟙 (L^∨)) ≫
            internalHomComposition L (𝟙_ D) M')) := by
            simp [Category.assoc]
    _ =
        (((MonoidalClosed.unitIsoSelf M).symm.hom ⊗ₘ 𝟙 (L^∨)) ≫
          (internalHomComposition L (𝟙_ D) M ≫ (ihom L).map f)) := by
            rw [internalHomComposition_natural_target_assoc L (𝟙_ D) f]
    _ =
        ringedSpaceDerivedEvaluationHom L M ≫ (ihom L).map f := by
          simp [ringedSpaceDerivedEvaluationHom, Category.assoc]

/-- Expanded equality form of `ringedSpaceDerivedEvaluationHom_natural_target`. -/
theorem ringedSpaceDerivedEvaluationHom_natural_target_assoc
    (L : D) {M M' : D} (f : M ⟶ M') :
    (f ⊗ₘ 𝟙 (L^∨)) ≫ ringedSpaceDerivedEvaluationHom L M' =
      ringedSpaceDerivedEvaluationHom L M ≫ (ihom L).map f := by
  simpa using (ringedSpaceDerivedEvaluationHom_natural_target L f).w

/-- The evaluation morphism
`ε : L^∨ ⊗ L ⟶ 𝟙_ D`. -/
noncomputable abbrev ringedSpaceDerivedDualEvaluation
    (L : D) :
    L^∨ ⊗ L ⟶ 𝟙_ D :=
  (β_ L^∨ L).hom ≫ (ihom.ev L).app (𝟙_ D)

/-- The source-facing braided description of `ringedSpaceDerivedDualEvaluation` agrees with the
standard closed-category evaluation map. -/
theorem ringedSpaceDerivedDualEvaluation_eq_braided_uncurry
    (L : D) :
    ringedSpaceDerivedDualEvaluation L =
      (β_ L^∨ L).hom ≫ MonoidalClosed.uncurry (𝟙 L^∨) := by
  simp [ringedSpaceDerivedDualEvaluation, MonoidalClosed.uncurry_eq]

end

end AlgebraicGeometry.RingedSpace
