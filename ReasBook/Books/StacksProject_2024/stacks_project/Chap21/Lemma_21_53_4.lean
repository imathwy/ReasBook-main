import StacksProject_2024.Chap21.SheafModuleDerivedTensor
import StacksProject_2024.Chap13.Aux_13_17_1
import StacksProject_2024.Chap18.Definition_18_43_1_Finite

open CategoryTheory
open CategoryTheory.MonoidalCategory
open DerivedCategory.TStructure
open scoped SheafModuleDerivedTensor

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [((J.W : MorphismProperty (Cᵒᵖ ⥤ ModuleCat.{w} Λ))).IsMonoidal]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [CategoryWithHomology (Sheaf J (ModuleCat.{w} Λ))]
variable [MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))]

local notation "Mod" => Sheaf J (ModuleCat Λ)
local notation "DMod" => DerivedCategory Mod
local notation "Minus" => (t.minus : ObjectProperty DMod)
local notation "FiniteTypeLCoh" =>
  derivedCategoryCohomologyInProperty (finiteTypeLocallyConstantModule J Λ)

/- Domain-style sampling for Lemma 21.53.4:
- primary domain: derived tensor products in `D^-(𝒞, Λ)` and cohomology sheaves of finite-type
  locally constant `Λ`-modules;
- sampled owner declarations:
  `Sheaf.moduleSheafMonoidalCategory`,
  `derivedCategoryCohomologyInProperty`,
  `DerivedCategory.IsLE`,
  `t.minus`,
  `finiteTypeLocallyConstantModule`,
  `IsFiniteTypeLocallyConstantModule`,
  `MonoidalCategoryStruct`;
- best owner abstraction: the main theorem should land directly in the chapter owner
  `derivedCategoryCohomologyInProperty (finiteTypeLocallyConstantModule J Λ)`, with the
  canonical bounded-above owner `Minus := (t.minus : ObjectProperty DMod)` on `K` and `L` and
  the source-facing derived tensor surface `K ⊗^L L`, expressed in this fixed-ring site
  presentation by the canonical monoidal tensor object `K ⊗ L`;
- primitive vs derived: the primitive inputs are the derived objects `K`, `L`, their `D^-`
  membership through `Minus`, and the specialized Chapter 13 cohomology owner `FiniteTypeLCoh`.
  The explicit bounds `K.IsLE a` and `L.IsLE b` are bridge data derived from `Minus` and should
  therefore stay in the companion theorem `tensor_of_isLE`.

Source/core/bridge triage:
- `source-facing`: the tensor-closure statement for finite-type locally constant cohomology on
  `K ⊗^L L`;
- `core/canonical`: `FiniteTypeLCoh`, `Minus`, and the Chapter 21 source-facing tensor owner
  `K ⊗^L L`;
- `bridge/view`: the scoped notation `SheafModuleDerivedTensor` used below for the fixed-ring
  derived tensor product in this presentation, together with the explicit-bound companion
  `tensor_of_isLE`, which exposes
  concrete witnesses `a` and `b` without replacing the owner predicate `Minus` as the main
  theorem surface. -/

/-- Companion form of Lemma 21.53.4 with explicit cohomological upper bounds `a` and `b`. -/
theorem finiteTypeLocallyConstantCohomology_tensor_of_isLE
    {a b : ℤ} {K L : DMod}
    (hK : FiniteTypeLCoh K)
    (hKboundedAbove : K.IsLE a)
    (hL : FiniteTypeLCoh L)
    (hLboundedAbove : L.IsLE b) :
    FiniteTypeLCoh (K ⊗^L L) := by
  sorry

/-- Lemma 21.53.4: if `K, L ∈ D^-(𝒞, Λ)` and all cohomology sheaves of `K` and `L` are locally
constant sheaves of finite-type `Λ`-modules, then every cohomology sheaf of `K ⊗^L L` is locally
constant of finite type. On the theorem surface below the `D^-` hypotheses are expressed by the
canonical owner `Minus := (t.minus : ObjectProperty DMod)`. -/
@[stacks 094H]
theorem finiteTypeLocallyConstantCohomology_tensor
    {K L : DMod}
    (hK : FiniteTypeLCoh K)
    (hKboundedAbove : Minus K)
    (hL : FiniteTypeLCoh L)
    (hLboundedAbove : Minus L)
    : FiniteTypeLCoh (K ⊗^L L) := by
  obtain ⟨a, hKa⟩ : ∃ a : ℤ, K.IsLE a := by
    simpa using hKboundedAbove
  obtain ⟨b, hLb⟩ : ∃ b : ℤ, L.IsLE b := by
    simpa using hLboundedAbove
  exact finiteTypeLocallyConstantCohomology_tensor_of_isLE hK hKa hL hLb

end

end CategoryTheory.Sheaf
