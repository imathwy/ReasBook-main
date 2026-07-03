import Mathlib
import StacksProject_2024.Chap15.Remark_15_101_6

-- Declarations for this item will be appended below by the statement pipeline.

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
