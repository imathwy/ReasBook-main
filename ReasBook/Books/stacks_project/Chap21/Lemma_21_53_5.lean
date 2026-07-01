import Mathlib
import stacks_project.Chap21.Lemma_21_53_1

open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify J (ModuleCat Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat Λ)]
variable [Abelian (Sheaf J (ModuleCat Λ))]
variable [CategoryWithHomology (Sheaf J (ModuleCat Λ))]

local notation "Mod" => Sheaf J (ModuleCat Λ)
local notation "DMod" => DerivedCategory Mod
local notation "single0" => DerivedCategory.singleFunctor Mod (0 : ℤ)

/-- A sheaf of `\Lambda`-modules is locally constant of finite type over `\Lambda / I^n` when,
after forgetting to `\Lambda`-modules, it is locally constant of finite type and every local
section is annihilated by `I^n`. -/
def IsFiniteTypeLocallyConstantIdealPowerQuotientModule
    (I : Ideal Λ) (n : ℕ) (F : Mod) : Prop :=
  IsFiniteTypeLocallyConstantModule F ∧
    ∀ U : C, (I ^ n) • (⊤ : Submodule Λ (F.1.obj (op U))) ≤ ⊥

-- Proof sketch: the helper predicate was defined by adjoining an `I^n`-annihilation condition to
-- `IsFiniteTypeLocallyConstantModule`, so forgetting that extra condition gives the desired
-- conclusion immediately.
/-- Forgetting the `I^n`-annihilation condition leaves a locally constant finite-type sheaf of
`\Lambda`-modules. -/
theorem isFiniteTypeLocallyConstant_of_isFiniteTypeLocallyConstantIdealPowerQuotientModule
    {I : Ideal Λ} {n : ℕ} {F : Mod}
    (hF : IsFiniteTypeLocallyConstantIdealPowerQuotientModule I n F) :
    IsFiniteTypeLocallyConstantModule F := sorry

-- Proof sketch: apply the distinguished triangles
-- `K ⊗ \underline{I^m/I^(m+1)} → K ⊗ \underline{\Lambda/I^(m+1)} → K ⊗ \underline{\Lambda/I^m}`
-- and use the factorization
-- `K ⊗ \underline{I^m/I^(m+1)} ≅ (K ⊗ \underline{\Lambda/I}) ⊗_{\Lambda/I}^{\mathbf L}
-- \underline{I^m/I^(m+1)}` together with Lemma `21.53.4`. The weak-Serre stability of locally
-- constant finite-type sheaves propagates the property inductively from `n = 1` to all `n ≥ 1`.
/-- Lemma 21.53.5: if the cohomology sheaves of
`K \otimes_\Lambda^{\mathbf L} \underline{\Lambda / I}` are locally constant sheaves of finite
type `\Lambda / I`-modules, then for every `n \geq 1` the cohomology sheaves of
`K \otimes_\Lambda^{\mathbf L} \underline{\Lambda / I^n}` are locally constant sheaves of finite
type `\Lambda / I^n`-modules. -/
theorem derivedTensor_constantIdealPowerQuotient_cohomology_isFiniteTypeLocallyConstant
    [MonoidalCategoryStruct DMod]
    (I : Ideal Λ)
    (K : DMod)
    (hKboundedAbove : ∃ a : ℤ, K.IsLE a)
    (hmodI :
      ∀ i : ℤ,
        IsFiniteTypeLocallyConstantIdealPowerQuotientModule
          I 1
          ((DerivedCategory.homologyFunctor Mod i).obj
            (K ⊗ (single0).obj
              ((constantSheaf J (ModuleCat Λ)).obj
                (ModuleCat.of Λ (Λ ⧸ I)))))) :
    ∀ n : ℕ, 1 ≤ n →
      ∀ i : ℤ,
        IsFiniteTypeLocallyConstantIdealPowerQuotientModule
          I n
          ((DerivedCategory.homologyFunctor Mod i).obj
            (K ⊗ (single0).obj
              ((constantSheaf J (ModuleCat Λ)).obj
                (ModuleCat.of Λ (Λ ⧸ I ^ n))))) := sorry

end

end CategoryTheory.Sheaf
