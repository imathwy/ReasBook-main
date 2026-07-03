import Mathlib
import StacksProject_2024.Chap20.Remark_20_36_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "ModX" => SheafOfModules.{u} (RingedSpace.ringCatSheaf X)
local notation "TowerX" => ℕᵒᵖ ⥤ ModX

/-- An `\mathcal O_X`-module is `f`-divisible if multiplication by `f` is an epimorphism. -/
def IsDivisibleByGlobalSection
    (f : StructureSheafGlobalSection X) (ℱ : ModX) : Prop :=
  Epi (globalSectionMul f ℱ)

/-- The transition morphism `\mathcal F_{n + 1} \to \mathcal F_n` in a sequential inverse system
of `\mathcal O_X`-modules. -/
abbrev inverseSystemStep
    (ℱ : TowerX) (n : ℕ) :
    ℱ.obj (op (n + 1)) ⟶ ℱ.obj (op n) :=
  ℱ.map (homOfLE (Nat.le_succ n)).op

/-- The comparison morphism `\mathcal F_n \to \mathcal F_1` for a stage `n ≥ 1` of a sequential
inverse system of `\mathcal O_X`-modules. -/
abbrev inverseSystemToFirst
    (ℱ : TowerX) (n : ℕ) (hn : 1 ≤ n) :
    ℱ.obj (op n) ⟶ ℱ.obj (op 1) :=
  ℱ.map (homOfLE hn).op

/-- Condition (1) from Lemma 20.36.1: for every `n ≥ 1`, multiplication by `f` on
`\mathcal F_{n + 1}` factors through `\mathcal F_{n + 1} \to \mathcal F_n` and gives a short
exact sequence `0 → \mathcal F_n → \mathcal F_{n + 1} → \mathcal F_1 → 0`. -/
def stepShortExactCondition
    (f : StructureSheafGlobalSection X) (ℱ : TowerX) : Prop :=
  ∀ n : ℕ, ∀ _ : 1 ≤ n,
    let π := inverseSystemToFirst ℱ (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    let σ := inverseSystemStep ℱ n
    ∃ (ι : ℱ.obj (op n) ⟶ ℱ.obj (op (n + 1))) (hιπ : ι ≫ π = 0),
      (ShortComplex.mk ι π hιπ).ShortExact ∧
        σ ≫ ι = globalSectionMul f (ℱ.obj (op (n + 1)))

/-- Condition (2) from Lemma 20.36.1: for every `n ≥ 1`, multiplication by `f^n` on
`\mathcal F_{n + 1}` factors through `\mathcal F_{n + 1} \to \mathcal F_1` and gives a short
exact sequence `0 → \mathcal F_1 → \mathcal F_{n + 1} → \mathcal F_n → 0`. -/
def powerShortExactCondition
    (f : StructureSheafGlobalSection X) (ℱ : TowerX) : Prop :=
  ∀ n : ℕ, ∀ _ : 1 ≤ n,
    let π := inverseSystemStep ℱ n
    let σ := inverseSystemToFirst ℱ (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    ∃ (ι : ℱ.obj (op 1) ⟶ ℱ.obj (op (n + 1))) (hιπ : ι ≫ π = 0),
      (ShortComplex.mk ι π hιπ).ShortExact ∧
        σ ≫ ι =
          globalSectionMulPow f (ℱ.obj (op (n + 1))) n

/-- Condition (3) from Lemma 20.36.1: the inverse system is obtained from the kernels
`\mathcal G[f^n]` of powers of multiplication by `f` on an `f`-divisible module `\mathcal G`. -/
def divisibleKernelTowerCondition
    (f : StructureSheafGlobalSection X) (ℱ : TowerX) : Prop :=
  ∃ 𝒢 : ModX,
    IsDivisibleByGlobalSection f 𝒢 ∧
      ∀ n : ℕ, ∀ _ : 1 ≤ n,
        Nonempty (ℱ.obj (op n) ≅ kernel (globalSectionMulPow f 𝒢 n))

-- Proof sketch: starting from an `f`-torsion free module `\mathcal F`, apply the standard short
-- exact sequences `0 → \mathcal F/f\mathcal F → \mathcal F/f^{n + 1}\mathcal F →
-- \mathcal F/f^n\mathcal F → 0`, pass to the colimit model of the quotient tower, and identify
-- the resulting divisible module whose `f^n`-torsion recovers the original stages.
/-- Lemma 20.36.1 (1): if the inverse system is given by quotients
`\mathcal F / f^n \mathcal F` of an `f`-torsion free module, then it is also given by the kernels
`\mathcal G[f^n]` inside an `f`-divisible module `\mathcal G`. -/
theorem torsionFreeQuotientTowerCondition_implies_divisibleKernelTowerCondition
    (f : StructureSheafGlobalSection X) (ℱ : TowerX) :
    torsionFreeQuotientTowerCondition f ℱ →
      divisibleKernelTowerCondition f ℱ := sorry

-- Proof sketch: for `3 → 2`, use the inclusions `\mathcal G[f] \subset \mathcal G[f^{n + 1}]`
-- inside an `f`-divisible module and identify the quotient with `\mathcal G[f^n]`; for `2 → 3`,
-- form the filtered colimit of the tower and show that multiplication by `f` on the colimit is
-- surjective, with kernels equal to the prescribed stages.
/-- Lemma 20.36.1 (2): the inverse system comes from the kernels `\mathcal G[f^n]` of an
`f`-divisible module if and only if the powers `f^n` factor through
`\mathcal F_{n + 1} \to \mathcal F_1` to yield short exact sequences
`0 → \mathcal F_1 → \mathcal F_{n + 1} → \mathcal F_n → 0`. -/
theorem divisibleKernelTowerCondition_iff_powerShortExactCondition
    (f : StructureSheafGlobalSection X) (ℱ : TowerX) :
    divisibleKernelTowerCondition f ℱ ↔
      powerShortExactCondition f ℱ := sorry

-- Proof sketch: in one direction, compose the factorization through `\mathcal F_{n + 1} →
-- \mathcal F_1` with the standard exact sequence from condition (2) to recover the factorization
-- through `\mathcal F_{n + 1} → \mathcal F_n`; in the other direction, iterate the stepwise
-- factorization from condition (1) to identify the factorization of `f^n`.
/-- Lemma 20.36.1 (3): the power-factorization short exact sequences from condition (2) are
equivalent to the stepwise factorization short exact sequences from condition (1). -/
theorem powerShortExactCondition_iff_stepShortExactCondition
    (f : StructureSheafGlobalSection X) (ℱ : TowerX) :
    powerShortExactCondition f ℱ ↔
      stepShortExactCondition f ℱ := sorry

end AlgebraicGeometry.RingedSpace
