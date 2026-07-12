import StacksProject_2024.Chap20.«20_42_0_1»

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

/- Domain-style sampling for Lemma 20.42.5:
- primary domain: internal-Hom composition in a braided monoidal closed derived category of
  `𝒪_X`-modules;
- inspected owner declarations:
  `AlgebraicGeometry.RingedSpace.RingedSpaceDerived`,
  `CategoryTheory.ihom`,
  `CategoryTheory.MonoidalClosed.comp`,
  `CategoryTheory.ihom.ev`,
  `CategoryTheory.MonoidalClosed.curry`;
- best owner abstraction: the closed-monoidal composition morphism `comp K L M` on the ambient
  owner `RingedSpaceDerived X`, together with the standard internal-Hom notation `K ⟹ L`;
- primitive data: the braided monoidal closed structure on `RingedSpaceDerived X` and the three
  objects `K`, `L`, `M`;
- derived API: the Stacks-ordered comparison map obtained by braiding the two internal-Hom factors
  into the order expected by `comp K L M`.

Source/core/bridge triage:
- `source-facing`: the chapter-level morphism
  `RHom(L, M) ⊗^L RHom(K, L) ⟶ RHom(K, M)`;
- `core/canonical`: the ambient internal-Hom owner notation `K ⟹ L` and the composition morphism
  `comp K L M`;
- `bridge/view`: the braiding that swaps the Stacks Project factor order into mathlib's canonical
  order for `comp`.

This item is therefore a `source-facing` bridge built directly from the `core/canonical` owner
data, so the public API should expose the standard internal-Hom notation and the shortest
unambiguous owner form `comp K L M`, rather than raw `(ihom _).obj _` terms or redundant namespace
scaffolding. Downstream constructions that do need the Stacks-ordered factor swap should reuse the
chapter owner `internalHomComposition K L M` rather than re-expanding its braiding-and-`comp`
definition.
-/

section

variable {X : RingedSpace.{u}}

variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

local notation "D" => RingedSpaceDerived X

/-- Lemma 20.42.5: for `K`, `L`, and `M` in `D(𝒪_X)`, there is a canonical morphism
`RHom(L, M) ⊗^L RHom(K, L) ⟶ RHom(K, M)`, functorial in `K`, `L`, and `M`. In the closed
monoidal structure on `D(𝒪_X)`, this is the usual internal-Hom
composition morphism after swapping the two factors into mathlib's order. -/
@[stacks 0A8V]
noncomputable def internalHomComposition
    (K L M : D) :
    (L ⟹ M) ⊗ (K ⟹ L) ⟶ (K ⟹ M) :=
  (β_ (L ⟹ M) (K ⟹ L)).hom ≫ comp K L M

/-- The source-facing comparison of Lemma 20.42.5 is the canonical closed-monoidal composition
map `comp K L M`, transported to the Stacks Project tensor order by the braiding. -/
theorem internalHomComposition_eq_braided_comp
    (K L M : D) :
    internalHomComposition K L M =
      (β_ (L ⟹ M) (K ⟹ L)).hom ≫ comp K L M :=
  rfl

omit [BraidedCategory D] in
private theorem comp_natural_target_assoc
    (K L : D) {M₁ M₂ : D} (f : M₁ ⟶ M₂) :
    (𝟙 (K ⟹ L) ⊗ₘ (ihom L).map f) ≫ comp K L M₂ =
      comp K L M₁ ≫ (ihom K).map f := by
  have hEval :
      L ◁ (ihom L).map f ≫ (ihom.ev L).app M₂ =
        (ihom.ev L).app M₁ ≫ f := by
    simpa [MonoidalClosed.uncurry_eq] using
      (MonoidalClosed.uncurry_ihom_map L f)
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.comp_eq, MonoidalClosed.uncurry_curry]
  rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.comp_eq, MonoidalClosed.uncurry_curry]
  rw [MonoidalClosed.compTranspose_eq, MonoidalClosed.compTranspose_eq]
  calc
    K ◁ (𝟙 (K ⟹ L) ⊗ₘ (ihom L).map f) ≫
        (α_ K (K ⟹ L) (L ⟹ M₂)).inv ≫
        (ihom.ev K).app L ▷ (L ⟹ M₂) ≫
        (ihom.ev L).app M₂ =
      (α_ K (K ⟹ L) (L ⟹ M₁)).inv ≫
        (K ⊗ (K ⟹ L)) ◁ (ihom L).map f ≫
        (ihom.ev K).app L ▷ (L ⟹ M₂) ≫
        (ihom.ev L).app M₂ := by
          simpa [Category.assoc] using
            (MonoidalCategory.associator_inv_naturality_right_assoc K (K ⟹ L) ((ihom L).map f)
              ((ihom.ev K).app L ▷ (L ⟹ M₂) ≫ (ihom.ev L).app M₂))
    _ =
      (α_ K (K ⟹ L) (L ⟹ M₁)).inv ≫
        (ihom.ev K).app L ▷ (L ⟹ M₁) ≫
        (L ◁ (ihom L).map f) ≫
        (ihom.ev L).app M₂ := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ (α_ K (K ⟹ L) (L ⟹ M₁)).inv ≫ k)
              (MonoidalCategory.whisker_exchange_assoc ((ihom.ev K).app L) ((ihom L).map f)
                ((ihom.ev L).app M₂))
    _ =
      ((α_ K (K ⟹ L) (L ⟹ M₁)).inv ≫
        (ihom.ev K).app L ▷ (L ⟹ M₁) ≫
        (ihom.ev L).app M₁) ≫
        f := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                (α_ K (K ⟹ L) (L ⟹ M₁)).inv ≫
                  (ihom.ev K).app L ▷ (L ⟹ M₁) ≫
                  k)
              hEval

/-- The comparison morphism of Lemma 20.42.5 is functorial in the target object `M`. -/
theorem internalHomComposition_natural_target
    (K L : D) {M₁ M₂ : D} (f : M₁ ⟶ M₂) :
    CommSq
      (((ihom L).map f) ⊗ₘ 𝟙 (K ⟹ L))
      (internalHomComposition K L M₁)
      (internalHomComposition K L M₂)
      ((ihom K).map f) := by
  refine CommSq.mk ?_
  calc
    (((ihom L).map f) ⊗ₘ 𝟙 (K ⟹ L)) ≫ internalHomComposition K L M₂ =
      (((ihom L).map f) ⊗ₘ 𝟙 (K ⟹ L)) ≫
        (β_ (L ⟹ M₂) (K ⟹ L)).hom ≫ comp K L M₂ := by
          rfl
    _ =
      (β_ (L ⟹ M₁) (K ⟹ L)).hom ≫
        (𝟙 (K ⟹ L) ⊗ₘ (ihom L).map f) ≫ comp K L M₂ := by
          simpa [Category.assoc] using
            (BraidedCategory.braiding_naturality_assoc ((ihom L).map f) (𝟙 (K ⟹ L))
              (comp K L M₂))
    _ =
      (β_ (L ⟹ M₁) (K ⟹ L)).hom ≫
        (comp K L M₁ ≫ (ihom K).map f) := by
          rw [comp_natural_target_assoc K L f]
    _ = internalHomComposition K L M₁ ≫ (ihom K).map f := by
          simp [internalHomComposition, Category.assoc]

/-- Expanded equality form of `internalHomComposition_natural_target`. -/
theorem internalHomComposition_natural_target_assoc
    (K L : D) {M₁ M₂ : D} (f : M₁ ⟶ M₂) :
    (((ihom L).map f) ⊗ₘ 𝟙 (K ⟹ L)) ≫ internalHomComposition K L M₂ =
      internalHomComposition K L M₁ ≫ (ihom K).map f := by
  simpa using (internalHomComposition_natural_target K L f).w

end

end AlgebraicGeometry.RingedSpace
