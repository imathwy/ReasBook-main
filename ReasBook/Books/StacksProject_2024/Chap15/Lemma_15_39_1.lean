import Mathlib
import StacksProject_2024.Chap10.Definition_10_160_5
import StacksProject_2024.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped Topology

universe u v w

section

/- Domain-style sampling for Lemma 15.39.1:
- primary domain: adic formal smoothness of coefficient maps into finite-variable formal power
  series rings over fields and Cohen rings.
- sampled owner declarations:
  * `RingHom.formally_smooth_for_adic`,
  * `Algebra.formallySmooth_of_charZero`,
  * `Algebra.formallySmooth_of_isSeparableOver`,
  * `cohenRing_zmodPow_quotient_algebraMap_formallySmooth`.
- best owner abstraction: `RingHom.formally_smooth_for_adic` is the chapter owner for the adic
  lifting property used here, and the project’s canonical owner for “finitely many variables” is
  `MvPowerSeries σ _` with `[Finite σ]`, not the coordinate encoding `Fin n`;
  field-theoretic formal smoothness and the Cohen-ring quotient results are upstream bridge inputs
  rather than separate local owners.
- primitive data: the coefficient field or Cohen ring together with its characteristic
  hypotheses.
- derived API: the three maximal-ideal-adic formal smoothness statements for the corresponding
  multivariable formal power series rings.

Source/core/bridge triage:
- `source-facing`: the three textbook cases in Lemma 15.39.1.
- `core/canonical`: `Algebra.FormallySmooth` and the owner theorem
  `RingHom.formally_smooth_for_adic`.
- `bridge/view`: passage from the coefficient-ring formal smoothness statements to the power-series
  targets.
-/

section CharZeroField

variable {σ : Type v} [Finite σ] (K : Type u) [Field K] [CharZero K]

local notation "P" => MvPowerSeries σ K

-- Proof sketch: first use Proposition `10.158.9` to see that `ℚ → K` is formally smooth for a
-- characteristic-zero field `K`. Then apply the universal property of the finite-variable formal
-- power series ring to lift maps coefficientwise, giving formal smoothness for the maximal-ideal
-- adic topology on `MvPowerSeries σ K`.
/-- Lemma 15.39.1 (1): if `K` is a field of characteristic zero, then the canonical map
`ℚ → K[[x_i]]`, formalized as `algebraMap ℚ (MvPowerSeries σ K)` for a finite variable set `σ`, is
formally
smooth in the `maximalIdeal`-adic topology. -/
theorem rational_to_mvPowerSeries_formally_smooth_for_madic
    : RingHom.formally_smooth_for_adic (algebraMap ℚ P) (maximalIdeal P) := sorry

end CharZeroField

section CharPField

variable {σ : Type v} [Finite σ] (L : Type u) [Field L] {p : ℕ} [Fact p.Prime] [CharP L p]

local instance : Algebra (ZMod p) L := ZMod.algebra L p
local notation "P" => MvPowerSeries σ L

-- Proof sketch: by Proposition `10.158.9`, a field `L` of characteristic `p` is formally smooth
-- over `𝔽_p = ZMod p`. The universal property of the finite-variable formal power series ring then
-- upgrades this coefficientwise lifting property to the maximal-ideal adic topology on
-- `MvPowerSeries σ L`.
/-- Lemma 15.39.1 (2): if `L` is a field of characteristic `p > 0`, then the canonical map
`𝔽_p → L[[x_i]]`, formalized as `algebraMap (ZMod p) (MvPowerSeries σ L)` for a finite variable
set `σ`, is formally smooth in the `maximalIdeal`-adic topology. -/
theorem zmod_to_mvPowerSeries_formally_smooth_for_madic
    : RingHom.formally_smooth_for_adic (algebraMap (ZMod p) P) (maximalIdeal P) := by
  sorry

end CharPField

section CohenRing

variable {σ : Type v} [Finite σ] (Λ : Type u) [CommRing Λ] [IsCohenRing Λ]

local notation "P" => MvPowerSeries σ Λ

-- Proof sketch: choose the prime `p` generating the maximal ideal of the Cohen ring `Λ`. Lemma
-- `10.160.7` gives formal smoothness of the maps `ZMod (p^m) → Λ ⧸ (p^m)` for all `m > 0`, and
-- Lemma `10.160.7` together with Definition `15.37.1` implies `ℤ → Λ` is formally smooth in the
-- `maximalIdeal Λ`-adic topology. The universal property of finite-variable formal power series
-- then yields the corresponding statement for `MvPowerSeries σ Λ`.
/-- Lemma 15.39.1 (3): if `Λ` is a Cohen ring, then the canonical map
`ℤ → Λ[[x_i]]`, formalized as `algebraMap ℤ (MvPowerSeries σ Λ)` for a finite variable set `σ`, is
formally
smooth in the `maximalIdeal`-adic topology. -/
theorem int_to_mvPowerSeries_over_cohenRing_formally_smooth_for_madic
    : RingHom.formally_smooth_for_adic (algebraMap ℤ P) (maximalIdeal P) := sorry

end CohenRing

end
