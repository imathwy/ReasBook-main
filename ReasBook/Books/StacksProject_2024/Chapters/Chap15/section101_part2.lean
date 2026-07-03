import Mathlib
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Quotient
import Mathlib.Data.PNat.Basic
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_15_101_10 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open IadicFiniteModuleSystem
open MvPowerSeries

universe u

attribute [local instance] CategoryTheory.HasExt.standard

section

/- Domain-style sampling for Example 15.101.10:
- primary domain: commutative algebra of the nodal complete local ring, its `I`-power quotients,
  the induced quotient modules, and the resulting `Ext²` groups in `ModuleCat`;
- sampled owner declarations:
  `MvPowerSeries`,
  `IadicFiniteModuleSystem.stageRing`,
  `ModuleCat.of`,
  `CategoryTheory.Abelian.Ext`;
- best owner abstraction:
  `source-facing`: the nodal ring `A = k[[x,y]] / (xy)`, the ideal `I = (x)`, the module
    `M = N = A / (y)`, and the reduced modules `M_n = N_n = M / I^n M`;
  `core/canonical`: quotient rings via ideals, quotient modules via submodules, the chapter owner
    `stageRing`, and the ambient `Ext`;
  `bridge/view`: the stagewise quotient module over `A_n`, which should be expressed directly from
    `stageRing` rather than via a parallel local stage-ring owner;
- primitive data: the nodal ring, its generators `x, y`, the ideals `(x)` and `(y)`, and the
  quotient module `A / (y)`;
- derived API: the reduced stage modules and the ambient/stagewise `Ext²` groups appearing in the
  counterexample theorem. -/

/-- The two-variable formal power series ring `k[[x,y]]`. -/
abbrev nodalPowerSeriesRing (k : Type u) [Field k] : Type u :=
  MvPowerSeries (Fin 2) k

/-- The nodal relation `xy` inside `k[[x,y]]`. -/
abbrev nodalRelation (k : Type u) [Field k] : nodalPowerSeriesRing k :=
  X (0 : Fin 2) * X (1 : Fin 2)

/-- The nodal complete local ring `A = k[[x,y]] / (xy)`. -/
abbrev nodalRing (k : Type u) [Field k] : Type u :=
  nodalPowerSeriesRing k ⧸
    Ideal.span ({ nodalRelation k } : Set (nodalPowerSeriesRing k))

/-- The image of `x` in the quotient ring `A = k[[x,y]] / (xy)`. -/
abbrev nodalX (k : Type u) [Field k] : nodalRing k :=
  Ideal.Quotient.mk _ (X (0 : Fin 2))

/-- The image of `y` in the quotient ring `A = k[[x,y]] / (xy)`. -/
abbrev nodalY (k : Type u) [Field k] : nodalRing k :=
  Ideal.Quotient.mk _ (X (1 : Fin 2))

/-- The ideal `I = (x)` in the nodal ring `A`. -/
abbrev nodalIdealX (k : Type u) [Field k] : Ideal (nodalRing k) :=
  Ideal.span ({ nodalX k } : Set (nodalRing k))

/-- The ideal `(y)` in the nodal ring `A`. -/
abbrev nodalIdealY (k : Type u) [Field k] : Ideal (nodalRing k) :=
  Ideal.span ({ nodalY k } : Set (nodalRing k))

/-- The module `M = N = A / (y)` used in the counterexample. -/
abbrev nodalQuotientModule (k : Type u) [Field k] : ModuleCat (nodalRing k) :=
  ModuleCat.of (nodalRing k) ((nodalRing k) ⧸ nodalIdealY k)

/-- The reduced stage `M_n = N_n = M / I^n M`, viewed as a module over `A_n = A / I^n`. -/
abbrev nodalStageModule (k : Type u) [Field k] (n : ℕ+) :
    ModuleCat (stageRing (nodalRing k) (nodalIdealX k) n) :=
  ModuleCat.of (stageRing (nodalRing k) (nodalIdealX k) n) <|
    (nodalQuotientModule k) ⧸
      (((nodalIdealX k) ^ (n : ℕ)) • (⊤ : Submodule (nodalRing k) (nodalQuotientModule k)))

variable (k : Type u) [Field k]

-- Proof sketch: compute `Ext^2_A(M, N)` from the periodic free resolution
-- `⋯ → A --y→ A --x→ A --y→ A → M → 0`; when `N = A / (y)`, this gives
-- `Ext^2_A(M, N) = N[y] / xN = N / xN ≃ k`. For each `n > 0`, use the reduced free resolution
-- `⋯ → A_n^⊕2 → A_n → A_n → A_n → M_n → 0` from the text to identify
-- `Ext^2_{A_n}(M_n, N_n)` with `N_n[x^(n - 1)] / xN_n`, and then use the exact sequence
-- `N_n --x→ N_n --x^(n - 1)→ N_n` for `N_n = k[x] / (x^n)` to deduce vanishing.
/-- Example 15.101.10: for the nodal ring `A = k[[x,y]] / (xy)` with `I = (x)` and
`M = N = A / (y)`, the ambient group `Ext^2_A(M, N)` is isomorphic to `k`, while for every
positive integer `n` the reduced group `Ext^2_{A_n}(M_n, N_n)` vanishes, where
`A_n = A / I^n` and `M_n = N_n = M / I^n M`. This is the explicit counterexample showing that the
`I`-power torsion term in Lemma `15.101.8` cannot be ignored. -/
theorem nodal_power_series_ext2_counterexample :
    ∃ e : (Ext (nodalQuotientModule k) (nodalQuotientModule k) 2) ≃ₗ[k] k,
      ∀ n : ℕ+, IsZero (Ext (nodalStageModule k n) (nodalStageModule k n) 2) := sorry

/-- For every positive integer `n`, the reduced group `Ext^2_{A_n}(M_n, N_n)` vanishes in the
nodal counterexample from Example `15.101.10`. -/
theorem nodal_stage_ext2_isZero (n : ℕ+) :
    IsZero (Ext (nodalStageModule k n) (nodalStageModule k n) 2) := by
  rcases nodal_power_series_ext2_counterexample k with ⟨_, hzero⟩
  exact hzero n

end

/-! ### Lemma_15_101_11 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open IadicFiniteModuleSystem
open Opposite

universe u

attribute [local instance] CategoryTheory.HasExt.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {B : Type u} [CommRing B] [IsNoetherianRing B] [Algebra A B]

local notation "SeqModA" => SequentialInverseSystem (ModuleCat A)

/- Domain-style sampling for Lemma 15.101.11:
- primary domain: commutative algebra and homological algebra of `Ext` towers over ideal-power
  quotients and their inverse limits;
- sampled owner declarations:
  `idealPowerModuleQuotient`,
  `IadicFiniteModuleSystem.stageRing`,
  `SeqRingMod`,
  `sequentialRingedModuleEvaluation`;
- best owner abstraction: the quotient-side tower should reuse the chapter owners
  `idealPowerModuleQuotient` and `SequentialInverseSystem (ModuleCat A)` rather than a raw
  quotient type and raw `ℕᵒᵖ ⥤ ModuleCat A` witness; on the reduction side, a strict varying-ring
  representative should be carried by
  `SeqRingMod (fun n ↦ stageRing B ((Ideal.map (algebraMap A B) I)) (Nat.succPNat n)) ...`, with
  the A-module inverse system obtained by the canonical restriction-of-scalars bridge rather than
  by an arbitrary bare `SequentialInverseSystem (ModuleCat A)`;
- primitive data: the ideal `I`, the modules `M` and `N`, the degree `i`, and the stagewise
  quotient and reduction `Ext` objects;
- derived API: the quotient tower `extIdealPowerQuotientTower`, the strict varying-ring owner
  `SeqRingMod ...` for a reduction-side representative, and the A-restricted tower derived from
  that owner.

Source/core/bridge triage:
- `source-facing`: the quotient stages
  `Ext^i_B(M, N) / I^(n+1) Ext^i_B(M, N)` and the reduced stages
  `Ext^i_{B / I^(n+1) B}(M / I^(n+1) M, N / I^(n+1) N)`;
- `core/canonical`: `idealPowerModuleQuotient`, `SeqRingMod`,
  `sequentialRingedModuleEvaluation`, `SequentialInverseSystem (ModuleCat A)`,
  `Functor.ofOpSequence`, `extIdealPowerQuotientTower`, and `limit`;
- `bridge/view`: the A-restricted sequential tower attached to a strict
  `SeqRingMod` representative of the reduced stages. -/

variable (B)

private abbrev extIdealPower (I : Ideal A) (n : ℕ) : Ideal B :=
  (Ideal.map (algebraMap A B) I) ^ (n + 1)

variable {B}

/-- The `n`th quotient stage
`Ext^i_B(M, N) / I^(n+1) Ext^i_B(M, N)`, viewed as an `A`-module. -/
private abbrev extIdealPowerQuotientStage (I : Ideal A) (M N : ModuleCat B) (i n : ℕ) :
    ModuleCat A :=
  (ModuleCat.restrictScalars (algebraMap A B)).obj <|
    ModuleCat.of B (idealPowerModuleQuotient (Ideal.map (algebraMap A B) I) (Ext M N i) n)

/-- The transition morphism
`Ext^i_B(M, N) / I^(n+2) Ext^i_B(M, N) ⟶ Ext^i_B(M, N) / I^(n+1) Ext^i_B(M, N)`. -/
private abbrev extIdealPowerQuotientStep (I : Ideal A) (M N : ModuleCat B) (i n : ℕ) :
    extIdealPowerQuotientStage I M N i (n + 1) ⟶
      extIdealPowerQuotientStage I M N i n :=
  (ModuleCat.restrictScalars (algebraMap A B)).map <|
    ModuleCat.ofHom
      (AdicCompletion.transitionMap (Ideal.map (algebraMap A B) I) (Ext M N i)
        (Nat.le_succ (n + 1)))

/-- The sequential inverse system
`(Ext^i_B(M, N) / I^(n+1) Ext^i_B(M, N))_n`, indexed from `n = 0`. -/
abbrev extIdealPowerQuotientTower (I : Ideal A) (M N : ModuleCat B) (i : ℕ) : SeqModA :=
  Functor.ofOpSequence (extIdealPowerQuotientStep I M N i)

/-- The quotient module `M / I^(n+1) M`, viewed over `B / I^(n+1) B`. -/
private abbrev extIdealPowerQuotientModule (I : Ideal A) (M : ModuleCat B) (n : ℕ) :
    ModuleCat (B ⧸ (extIdealPower B I n : Ideal B)) :=
  ModuleCat.of
    (B ⧸ (extIdealPower B I n : Ideal B))
    (M ⧸ (((extIdealPower B I n : Ideal B)) • (⊤ : Submodule B M)))

/-- The stage `Ext^i_{B / I^(n+1) B}(M / I^(n+1) M, N / I^(n+1) N)` as a module over
`B / I^(n+1) B`. -/
abbrev extIdealPowerReductionStageOverQuotient
    (I : Ideal A) (M N : ModuleCat B) (i n : ℕ) :
    ModuleCat (stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n)) :=
  ModuleCat.of (B ⧸ (extIdealPower B I n : Ideal B))
    (Ext
      (extIdealPowerQuotientModule I M n)
      (extIdealPowerQuotientModule I N n)
      i)

omit [IsNoetherianRing A] in
private theorem extIdealPowerReductionTransition_comp_algebraMap
    (B : Type u) [CommRing B] [IsNoetherianRing B] [Algebra A B]
    (I : Ideal A) (n : ℕ) :
    (Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I) (Nat.le_succ (n + 1))).comp
        (algebraMap A (stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat (n + 1)))) =
      algebraMap A (stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n)) :=
  rfl

/-- Evaluation of a strict reduction-side `SeqRingMod` representative at stage `n`,
followed by restriction of scalars to `A`. -/
private abbrev extIdealPowerReductionTowerEvaluation
    (B : Type u) [CommRing B] [IsNoetherianRing B] [Algebra A B]
    (I : Ideal A) (n : ℕ) :
    SeqRingMod
        (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
        (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I)
          (Nat.le_succ (n + 1))) ⥤
      ModuleCat A :=
  sequentialRingedModuleEvaluation
      (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
      (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I)
        (Nat.le_succ (n + 1))) n ⋙
    ModuleCat.restrictScalars
      (algebraMap A (stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n)))

/-- The successor transition on the A-restricted tower attached to a strict reduction-side
`SeqRingMod` representative. -/
private abbrev extIdealPowerReductionTowerStep
    (B : Type u) [CommRing B] [IsNoetherianRing B] [Algebra A B]
    (I : Ideal A) (n : ℕ) :
    extIdealPowerReductionTowerEvaluation B I (n + 1) ⟶
      extIdealPowerReductionTowerEvaluation B I n :=
  (Functor.whiskerRight
      (sequentialRingedModuleEvaluationStep
        (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
        (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I)
          (Nat.le_succ (n + 1))) n)
      (ModuleCat.restrictScalars
        (algebraMap A (stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat (n + 1)))))) ≫
    Functor.whiskerLeft
      (sequentialRingedModuleEvaluation
        (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
        (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I)
          (Nat.le_succ (n + 1))) n)
      ((ModuleCat.restrictScalarsComp'
        (algebraMap A (stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat (n + 1))))
        (Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I) (Nat.le_succ (n + 1)))
        (algebraMap A (stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n)))
        (extIdealPowerReductionTransition_comp_algebraMap B I n)).inv)

/-- The sequential inverse system of `A`-modules obtained from a strict reduction-side
`SeqRingMod` representative by stagewise restriction of scalars. -/
abbrev extIdealPowerReductionTowerOverA
    (I : Ideal A)
    (T :
      SeqRingMod
        (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
        (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I) (Nat.le_succ (n + 1)))) :
    SeqModA :=
  @Functor.ofOpSequence (ModuleCat A) _
    (fun n ↦ (extIdealPowerReductionTowerEvaluation B I n).obj T)
    (fun n ↦ (extIdealPowerReductionTowerStep B I n).app T)

-- Proof sketch: choose a resolution of the finite `B`-module `M` by finite free `B`-modules.
-- Because `B` and `M` are flat over `A`, reduction modulo `I^(n+1)` stays exact and computes
-- `Ext^i` over `B / I^(n+1) B`. The resulting levelwise identifications of the Hom complexes with
-- the quotients modulo `I^(n+1)` reduce the statement to Lemma `15.101.1 (2)` for the associated
-- homology towers.
/-- Lemma 15.101.11: let `A → B` be a flat homomorphism of Noetherian rings, let `I ⊆ A` be an
ideal, and let `M, N` be `B`-modules with `M` finite over `B` and flat over `A`. Then for every
degree `i`, the inverse limit of the quotients
`Ext^i_B(M, N) / I^(n+1) Ext^i_B(M, N)` is canonically isomorphic to the inverse limit of some
strict compatible varying-ring module system `T` over the quotient-ring tower
`B / I^(n+1)B`, whose stagewise evaluations recover the reduced `Ext` stages
`Ext^i_{B / I^(n+1) B}(M / I^(n+1) M, N / I^(n+1) N)`. The inverse limit on the reduction side is
taken on the induced `A`-module tower `extIdealPowerReductionTowerOverA I T`. Lean starts the
quotient tower at `n = 0`, corresponding to the textbook quotient by `I^1`. -/
theorem exists_extIdealPowerReductionTower_limit_isomorphic_limit_extIdealPowerQuotientTower
    (I : Ideal A) (M N : ModuleCat B) [Module.Finite B M]
    (hBflat : (algebraMap A B).Flat)
    (hMflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj M))
    (i : ℕ) :
    ∃ T :
        SeqRingMod
          (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
          (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I) (Nat.le_succ (n + 1))),
      (∀ n : ℕ,
        IsIsomorphic
          ((sequentialRingedModuleEvaluation
            (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
            (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I)
              (Nat.le_succ (n + 1))) n).obj T)
          (extIdealPowerReductionStageOverQuotient I M N i n)) ∧
        IsIsomorphic
          (limit (extIdealPowerQuotientTower I M N i))
          (limit (extIdealPowerReductionTowerOverA I T)) := by
  sorry

end
