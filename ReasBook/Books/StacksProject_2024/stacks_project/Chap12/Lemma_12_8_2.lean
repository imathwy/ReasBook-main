import Mathlib
import StacksProject_2024.stacks_project.Chap12.Lemma_12_5_2
import StacksProject_2024.stacks_project.Chap12.Lemma_12_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe t w v u

namespace CategoryTheory

open MorphismProperty
open Functor

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (S : MorphismProperty C)

/- Domain-style sampling for Lemma 12.8.2:
- primary domain: additive localizations of preadditive categories;
- inspected owner declarations:
  `HasFiniteProducts`,
  `Functor.Additive`,
  `Localization.preadditive`,
  `Localization.functor_additive`;
- best owner abstraction: the additive-category half is expressed by
  `HasFiniteProducts S.Localization`, and the functorial half by `S.Q.Additive`;
- primitive data: the preadditive source category, the morphism property `S`, and the left/right
  calculus-of-fractions hypotheses;
- derived API: the induced preadditive structure on `S.Localization`, the additivity of `S.Q`,
  and the finite-product structure transported across an additive essentially surjective
  localization. -/

/- Source/core/bridge triage for Lemma 12.8.2:
- source-facing: the source lemma says the localization is an additive category and the
  localization functor `Q` is additive;
- core/canonical owners: `HasFiniteProducts S.Localization` and `S.Q.Additive`;
- bridge/view: the preadditive target structure comes from `Localization.preadditive` on the left
  and `Localization.preadditiveOfHasRightCalculusOfFractions` on the right, while
  `hasFiniteProducts_of_essSurj_additive` upgrades that preadditive target to the additive owner. -/

section

variable [HasFiniteProducts C]

private theorem hasFiniteProducts_of_essSurj_additive
    {A : Type u} [Category.{v} A] [Preadditive A] [HasFiniteProducts A]
    {B : Type w} [Category.{t} B] [Preadditive B] (L : A ⥤ B)
    [L.EssSurj] [L.Additive] : HasFiniteProducts B := by
  letI : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
  letI : HasZeroObject A := hasZeroObject_of_hasFiniteBiproducts A
  letI : PreservesFiniteProducts L := Functor.preservesFiniteProductsOfAdditive L
  letI : HasBinaryProducts B := by
    letI : HasBinaryBiproducts A := hasBinaryBiproducts_of_finite_biproducts A
    letI : HasBinaryProducts A := hasBinaryProducts_of_hasBinaryBiproducts
    have (X Y : B) : HasBinaryProduct X Y := by
      letI : HasLimit (pair (L.objPreimage X) (L.objPreimage Y)) := by infer_instance
      letI : HasLimit (pair (L.objPreimage X) (L.objPreimage Y) ⋙ L) :=
        ⟨_, isLimitOfPreserves L (limit.isLimit (pair (L.objPreimage X) (L.objPreimage Y)))⟩
      exact hasLimit_of_iso
        (show pair (L.objPreimage X) (L.objPreimage Y) ⋙ L ≅ pair X Y from
          mapPairIso (L.objObjPreimageIso X) (L.objObjPreimageIso Y))
    exact hasBinaryProducts_of_hasLimit_pair B
  letI : HasZeroObject B := Functor.hasZeroObject_of_additive L
  letI : HasTerminal B := HasZeroObject.hasTerminal
  exact hasFiniteProducts_of_has_binary_and_terminal

-- Proof sketch: in the left-fraction case, use the canonical preadditive owner on
-- `S.Localization` together with the finite-colimit construction available for left localizations,
-- and then recover the additive owner `HasFiniteProducts`. In the right-fraction case, pass to the
-- opposite localization, apply the left-fraction argument there, and transport the resulting
-- finite products back across opposites.
/-- A left-fraction localization of an additive category has finite products. -/
theorem localization_hasFiniteProducts_of_left_calculus_of_fractions
    [S.HasLeftCalculusOfFractions] : HasFiniteProducts S.Localization := by
  letI : Preadditive S.Localization := Localization.preadditive S.Q S
  letI : Additive S.Q := Localization.functor_additive S.Q S
  letI : EssSurj S.Q := Localization.essSurj S.Q S
  exact hasFiniteProducts_of_essSurj_additive S.Q

/-- A right-fraction localization of an additive category has finite products. -/
theorem localization_hasFiniteProducts_of_right_calculus_of_fractions
    [S.HasRightCalculusOfFractions] : HasFiniteProducts S.Localization := by
  letI : Preadditive S.Localizationᵒᵖ := Localization.preadditive S.Q.op S.op
  letI : Additive S.Q.op := Localization.functor_additive S.Q.op S.op
  letI : EssSurj S.Q.op := Localization.essSurj S.Q.op S.op
  letI : HasFiniteProducts S.Localizationᵒᵖ :=
    hasFiniteProducts_of_essSurj_additive S.Q.op
  exact instHasFiniteProductsUnop S.Localization

end

section

variable [S.HasLeftCalculusOfFractions]

/- Lemma 12.8.2, left-fraction additive-functor clause: once
`localization_hasFiniteProducts_of_left_calculus_of_fractions S` supplies finite products on
`S.Localization`, the additivity of the localization functor is the canonical owner theorem
`Localization.functor_additive S.Q S`. -/
#check Localization.functor_additive S.Q S

end

section

variable [S.HasRightCalculusOfFractions]

/- Lemma 12.8.2, right-fraction additive-functor clause: with the canonical preadditive structure
`Localization.preadditiveOfHasRightCalculusOfFractions S.Q S`, the additivity of the localization
functor is the chapter owner theorem
`Localization.functor_additive_of_hasRightCalculusOfFractions S.Q S`. -/
#check Localization.functor_additive_of_hasRightCalculusOfFractions S.Q S

end

end CategoryTheory
