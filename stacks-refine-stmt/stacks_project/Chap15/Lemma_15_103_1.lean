import Mathlib
import stacks_project.Chap04.Definition_4_22_1
import stacks_project.Chap12.Definition_12_31_2
import stacks_project.Chap15.Definition_15_89_1
import stacks_project.Chap15.Definition_15_65_1
import stacks_project.Chap15.Lemma_15_66_1
import stacks_project.Chap15.Lemma_15_101_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)

/- Domain-style sampling for Lemma 15.103.1:
- primary domain: derived `Ext` towers over ideal-power quotient inverse systems of finite
  modules;
- sampled owner declarations:
  `derivedExtModuleFunctor`,
  `idealPowerModuleQuotient`,
  `Functor.ofOpSequence`,
  `IsEssentiallyConstantCofilteredCone`;
- best owner abstraction in the present import closure: the source-facing tower is a sequential
  inverse system in `ModuleCat A` obtained by postcomposing the quotient transitions
  `M / I^(n + 2) M ⟶ M / I^(n + 1) M` with the fixed-degree Ext functor
  `derivedExtModuleFunctor K i`;
- primitive vs. derived:
  primitive data are the ideal `I`, the pseudo-coherent complex `K`, the finite module `M`, the
  fixed degree `i`, and the torsion hypothesis on higher Ext modules;
  derived API is the essentially constant cone and the resulting limit cone on that tower;
- source/core/bridge triage:
  `source-facing`: the two existence theorems below;
  `core/canonical`: `derivedExtModuleFunctor`, `idealPowerModuleQuotient`,
    `AdicCompletion.transitionMap`, `Functor.ofOpSequence`, and the Chapter 4 essentially
    constant-cone owner;
  `bridge/view`: the tower abbreviation `derivedExtIdealPowerQuotientTower`. -/

/-- The `n`th term `Ext^i_A(K, M / I^(n+1)M)` in the ideal-power quotient Ext tower. -/
abbrev derivedExtIdealPowerQuotientStage
    (I : Ideal A) (K : DMod) (M : ModuleCat A) (i : ℤ) (n : ℕ) : ModuleCat A :=
  (derivedExtModuleFunctor K i).obj (ModuleCat.of A (idealPowerModuleQuotient I M n))

/-- The transition morphism
`Ext^i_A(K, M / I^(n+2)M) ⟶ Ext^i_A(K, M / I^(n+1)M)`
in the ideal-power quotient Ext tower. -/
abbrev derivedExtIdealPowerQuotientStep
    (I : Ideal A) (K : DMod) (M : ModuleCat A) (i : ℤ) (n : ℕ) :
    derivedExtIdealPowerQuotientStage I K M i (n + 1) ⟶
      derivedExtIdealPowerQuotientStage I K M i n :=
  (derivedExtModuleFunctor K i).map
    (ModuleCat.ofHom (AdicCompletion.transitionMap I M (Nat.le_succ (n + 1))))
/-- The sequential inverse system `(Ext^i_A(K, M / I^(n+1)M))_n` attached to `K`, `M`, and `I`.
The Lean indexing starts at `n = 0`, corresponding to the textbook quotient `M / IM`. -/
abbrev derivedExtIdealPowerQuotientTower
    (I : Ideal A) (K : DMod) (M : ModuleCat A) (i : ℤ) : SeqMod :=
  Functor.ofOpSequence (derivedExtIdealPowerQuotientStep I K M i)

/-- The hypothesis that all higher Ext modules `Ext^j_A(K, N)` with `j ≥ a` are `I`-power
torsion for finite `A`-modules `N`. -/
def DerivedExtIsIdealPowerTorsionAbove (I : Ideal A) (K : DMod) (a : ℤ) : Prop :=
  ∀ (N : ModuleCat.{u} A), Module.Finite A N → ∀ ⦃j : ℤ⦄, a ≤ j →
    Module.IsIdealPowerTorsion I ((derivedExtModuleFunctor K j).obj N)

-- Proof sketch: for `Ext^i_A(K, M)`, pseudo-coherence makes the group finite, so the torsion
-- hypothesis gives a power of `I` killing it. Apply Lemma `15.102.4` to the finite modules
-- `I^m M` to see that the images of `Ext^i_A(K, I^nM)` and `Ext^(i+1)_A(K, I^nM)` in the long
-- exact sequence of `0 → I^nM → M → M / I^nM → 0` vanish for large `n`. The resulting diagram
-- chase produces an essentially constant cone with vertex `Ext^i_A(K, M)`.
/-- Lemma 15.103.1: let `A` be a Noetherian ring, `I ⊆ A` an ideal, `K ∈ D(A)` a
pseudo-coherent complex, and `a ∈ ℤ`. Assume that for every finite `A`-module `N`, the modules
`Ext^j_A(K, N)` are `I`-power torsion for all `j ≥ a`. Then for every `i ≥ a` and every finite
`A`-module `M`, the inverse system `(Ext^i_A(K, M / I^(n+1)M))_n` is essentially constant with
value `Ext^i_A(K, M)`. The Lean indexing starts at `n = 0`, corresponding to the textbook
quotient `M / IM`. -/
theorem derivedExt_idealPowerQuotientTower_exists_essentiallyConstantCone
    (I : Ideal A) (K : DMod) (hK : K.IsPseudoCoherent) (a : ℤ)
    (hExt : DerivedExtIsIdealPowerTorsionAbove I K a)
    (i : ℤ) (hi : a ≤ i) (M : ModuleCat A) [Module.Finite A M] :
    ∃ c : Cone (derivedExtIdealPowerQuotientTower I K M i),
      c.pt = (derivedExtModuleFunctor K i).obj M ∧
        IsEssentiallyConstantCofilteredCone c := sorry

-- Proof sketch: use the essentially constant cone from
-- `derivedExt_idealPowerQuotientTower_exists_essentiallyConstantCone`; Chapter 4 upgrades an
-- essentially constant cofiltered cone to a genuine `LimitCone`, so the tower admits a limit cone
-- whose vertex is `Ext^i_A(K, M)`.
/-- The ideal-power quotient Ext tower admits a limit cone whose vertex is `Ext^i_A(K, M)` under
the hypotheses of Lemma `15.103.1`. -/
theorem exists_limitCone_derivedExt_idealPowerQuotientTower
    (I : Ideal A) (K : DMod) (hK : K.IsPseudoCoherent) (a : ℤ)
    (hExt : DerivedExtIsIdealPowerTorsionAbove I K a)
    (i : ℤ) (hi : a ≤ i) (M : ModuleCat A) [Module.Finite A M] :
    ∃ c : LimitCone (derivedExtIdealPowerQuotientTower I K M i),
      c.cone.pt = (derivedExtModuleFunctor K i).obj M ∧
        IsEssentiallyConstantCofilteredCone c.cone := sorry

end

end CategoryTheory
