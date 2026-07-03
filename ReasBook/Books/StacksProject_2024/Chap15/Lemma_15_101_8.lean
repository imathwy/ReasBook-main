import Mathlib
import stacks_project.Chap15.Lemma_15_101_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open IadicFiniteModuleSystem

noncomputable section

universe u

attribute [local instance] CategoryTheory.HasExt.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "Q" => IadicFiniteModuleSystem.Category.quotient A

/- Domain-style sampling for Lemma 15.101.8:
- primary domain: `Ext` towers in the quotient category of `I`-adic finite module systems from
  Remark `15.101.6`;
- sampled owner declarations:
  `IadicFiniteModuleSystem`,
  `IadicFiniteModuleSystem.Category`,
  `IadicFiniteModuleSystem.Category.quotient`,
  `IadicFiniteModuleSystem.isIso_iff_hasEventuallyBoundedKernelAndCokernel`,
  `CategoryTheory.IsIsomorphic`;
- best owner abstraction:
  `source-facing`: the two `IadicFiniteModuleSystem` objects
    `extQuotientSystem I M N i` and `extReductionSystem I M N i`;
  `core/canonical`: the quotient-category owner from Remark `15.101.6`, together with the
    object-level proposition `CategoryTheory.IsIsomorphic`;
  `bridge/view`: the stagewise reduction `M / I^n M`, which is only implementation data for the
    reduction-side system and should not remain a second public owner;
- primitive data: the two source-facing Ext systems;
- derived API: the theorem that these systems are isomorphic in the category `\mathcal C`.

This item should therefore keep the systems themselves public, but record the comparison at the
canonical object-isomorphism layer rather than as a chosen concrete isomorphism. -/

/-- The reduction `M_n = M / I^n M`, viewed as a module over `A_n = A / I^n`. This is a private
bridge for the reduction-side system, not a second public owner. -/
private abbrev stagewiseReduction (I : Ideal A) (M : ModuleCat A) (n : ℕ+) :
    ModuleCat (stageRing A I n) :=
  ModuleCat.of (stageRing A I n) (M ⧸ (I ^ (n : ℕ) • (⊤ : Submodule A M)))

/-- The inverse system whose `n`th stage is
`Ext^i_A(M, N) / I^n Ext^i_A(M, N)`, indexed by positive integers `n`. -/
abbrev extQuotientSystem (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M]
    [Module.Finite A N] (i : ℕ) : IadicFiniteModuleSystem A I :=
  fun n ↦ FGModuleCat.of (stageRing A I n)
    (Ext M N i ⧸ (I ^ (n : ℕ) • (⊤ : Submodule A (Ext M N i))))

/-- The inverse system whose `n`th stage is
`Ext^i_{A / I^n}(M / I^n M, N / I^n N)`, indexed by positive integers `n`. -/
abbrev extReductionSystem (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M]
    [Module.Finite A N] (i : ℕ) : IadicFiniteModuleSystem A I :=
  fun n ↦ FGModuleCat.of (stageRing A I n)
    (Ext (stagewiseReduction I M n) (stagewiseReduction I N n) i)

-- Proof sketch: choose a finite presentation `0 → K → A^r → M → 0`, compare the systems
-- `(K / I^n K)_n` and `(Ker(A_n^r → M_n))_n` via Lemma `15.101.1`, and then compare the induced
-- Hom systems using Lemmas `15.101.4` and `15.101.7`. Dimension shifting reduces the higher Ext
-- cases to `i = 0, 1`, where the long exact sequence and a diagram chase produce the required
-- representative with uniformly bounded kernel and cokernel.
/-- Lemma 15.101.8: for every `i ≥ 0`, the system
`(\operatorname{Ext}^i_A(M, N) / I^n \operatorname{Ext}^i_A(M, N))_{n \ge 1}` admits a
representative with eventually bounded kernel and cokernel to the system
`(\operatorname{Ext}^i_{A / I^n}(M / I^n M, N / I^n N))_{n \ge 1}`; equivalently, and here taken
as the canonical public statement, these two objects are isomorphic in the category
`\mathcal C` of Remark `15.101.6`. -/
theorem extQuotientSystem_isomorphic_extReductionSystem
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] [Module.Finite A N] (i : ℕ) :
    IsIsomorphic ((Q I).obj (extQuotientSystem I M N i)) ((Q I).obj (extReductionSystem I M N i)) := by
  sorry

end
