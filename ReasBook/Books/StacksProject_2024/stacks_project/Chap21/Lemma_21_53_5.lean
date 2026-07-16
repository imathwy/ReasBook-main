import StacksProject_2024.stacks_project.Chap21.SheafModuleDerivedTensor
import StacksProject_2024.stacks_project.Chap13.Aux_13_17_1
import StacksProject_2024.stacks_project.Chap18.Definition_18_43_1_Finite
import StacksProject_2024.stacks_project.Chap18.ConstantIdealPowerQuotientSheaf

open CategoryTheory
open CategoryTheory.MonoidalCategory
open DerivedCategory.TStructure
open scoped SheafModuleDerivedTensor

noncomputable section

universe u w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [((J.W : MorphismProperty (Cᵒᵖ ⥤ ModuleCat.{w} Λ))).IsMonoidal]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [CategoryWithHomology (Sheaf J (ModuleCat.{w} Λ))]

local notation "Mod" => Sheaf J (ModuleCat Λ)
local notation "DMod" => DerivedCategory Mod
local notation "Minus" => (t.minus : ObjectProperty DMod)
local notation "single0" => DerivedCategory.singleFunctor Mod (0 : ℤ)
local notation "FiniteTypeLCoh" =>
  derivedCategoryCohomologyInProperty (finiteTypeLocallyConstantModule J Λ)
variable [MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))]

/- Domain-style sampling for Lemma 21.53.5:
- primary domain: derived tensor products with the constant quotient sheaves
  `constantIdealQuotientSheaf J (I ^ n)` and locally constant finite-type cohomology sheaves;
- sampled owner declarations:
  `derivedCategoryCohomologyInProperty`,
  `finiteTypeLocallyConstantModule`,
  `Sheaf.moduleSheafMonoidalCategory`,
  `constantIdealQuotientSheaf`,
  `constantIdealPowerQuotientSheafSystem`;
- best owner abstraction:
  `source-facing`: the inductive ideal-power quotient statement below;
  `core/canonical`: the specialized Chapter 13 cohomology owner `FiniteTypeLCoh`, the Chapter 18
    quotient-sheaf owners `constantIdealQuotientSheaf` and `constantIdealPowerQuotientSheafSystem`,
    the Chapter 21 sheaf monoidal owner `Sheaf.moduleSheafMonoidalCategory`, the bounded-above
    owner `Minus := (t.minus : ObjectProperty DMod)`, and the resulting derived tensor product on
    `DMod`;
  `bridge/view`: the inverse-system presentation
    `(constantIdealPowerQuotientSheafSystem J I).obj (op (n + 1))` of
    `constantIdealQuotientSheaf J (I ^ (n + 1))`, together with any sectionwise annihilator
    calculation, is derived API and should stay off the main theorem surface; the tensor surface
    itself is reused from the scoped bridge `SheafModuleDerivedTensor`.

Primitive data vs derived API:
- primitive data: `I`, `K`, bounded-above cohomology for `K`, the stage-`1` cohomology owner over
  `constantIdealQuotientSheaf J I`;
- derived API: the quotient-tower presentation
  `(constantIdealPowerQuotientSheafSystem J I).obj (op (n + 1))` of the intrinsic stage
  `constantIdealQuotientSheaf J (I ^ (n + 1))`. The `Λ / I^(n + 1)`-module structure is
  intrinsic to this tensor factor, and the explicit witness `∃ a, K.IsLE a` for bounded-above
  membership is bridge data derived from `Minus K`, so both belong off the main theorem surface.

The refinement target is therefore the source-facing theorem surface: reuse the chapter owner for
constant ideal quotient sheaves and the specialized Chapter 13 cohomology owner instead of
duplicating either through theorem-local helper abbreviations. -/

-- Proof sketch: apply the distinguished triangles
-- built from the short exact sequence
-- `I^m / I^(m + 1) → Λ / I^(m + 1) → Λ / I^m`
-- and use the factorization
-- of the graded piece over `Λ ⧸ I`, together with Lemma `21.53.4`. The weak-Serre stability of
-- constant finite-type sheaves propagates the property inductively from the base quotient
-- `Λ / I`, indexed here as stage `n = 0`, to all successor stages `n + 1`.
/-- Lemma 21.53.5: if the cohomology sheaves of
`K ⊗^L (single0).obj (constantIdealQuotientSheaf J I)` are locally constant sheaves of finite
type, then for every positive integer `n : ℕ+` the cohomology sheaves of
`K ⊗^L (single0).obj (constantIdealQuotientSheaf J (I ^ (n : ℕ)))` are locally constant sheaves
of finite type. On the theorem surface below this is expressed directly through the canonical
owners `FiniteTypeLCoh` and `Minus`. -/
@[stacks 094I]
theorem derivedTensor_constantIdealPowerQuotient_cohomology_isFiniteTypeLocallyConstant
    (I : Ideal Λ)
    (K : DMod)
    (hKboundedAbove : Minus K)
    (hcohModI :
      FiniteTypeLCoh (K ⊗^L (single0).obj (constantIdealQuotientSheaf J I)))
    (n : ℕ+) :
    FiniteTypeLCoh
      (K ⊗^L (single0).obj (constantIdealQuotientSheaf J (I ^ (n : ℕ)))) := sorry

/-- Companion `ℕ`-indexed form of Lemma 21.53.5. This keeps the successor-stage surface
`I^(n + 1)` available for induction arguments while the tagged theorem uses the cleaner positive
index `n : ℕ+`. -/
  theorem derivedTensor_constantIdealPowerQuotientSucc_cohomology_isFiniteTypeLocallyConstant
      (I : Ideal Λ)
      (K : DMod)
      (hKboundedAbove : Minus K)
      (hcohModI :
        FiniteTypeLCoh (K ⊗^L (single0).obj (constantIdealQuotientSheaf J I)))
      (n : ℕ) :
      FiniteTypeLCoh
        (K ⊗^L (single0).obj (constantIdealQuotientSheaf J (I ^ (n + 1)))) := by
  simpa using
    derivedTensor_constantIdealPowerQuotient_cohomology_isFiniteTypeLocallyConstant
      I K hKboundedAbove hcohModI ⟨n + 1, Nat.succ_pos n⟩

end

end CategoryTheory.Sheaf
