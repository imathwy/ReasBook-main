import ProbabilityTheory_Klenke_2020.Chap19.Definition_19_17
import ProbabilityTheory_Klenke_2020.Chap19.Theorem_19_15
import Mathlib

open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace ProbabilityTheory

/- `source-facing`: Example 19.18 studies concrete series and parallel electrical networks.
Its primitive data are the edge conductances/resistances of those networks.
`core/canonical`: Chapter 19 already organizes electrical networks around
`electricalCurrent`, `IsElectricalPotential`, and `netFlowOnSet`, with Definition 19.17
identifying effective conductance/resistance as the boundary current and its reciprocal.
`bridge/view`: the declarations below package the concrete path/parallel networks into
conductance families and state the textbook series/parallel formulas directly through that owner
API. -/

section SeriesConnection

variable {k n : ℕ}

/-- The conductance network on the path `0 - 1 - ... - n` whose edge `(i, i + 1)` has
conductance `c i`. -/
def pathConductance {n : ℕ} (c : Fin n → ℝ≥0∞) : Fin (n + 1) → Fin (n + 1) → ℝ≥0∞
  | i, j =>
      if hij : i.1 + 1 = j.1 then
        c ⟨i.1, Nat.lt_of_succ_lt_succ <| by simpa [hij] using j.2⟩
      else if hji : j.1 + 1 = i.1 then
        c ⟨j.1, Nat.lt_of_succ_lt_succ <| by simpa [hji] using i.2⟩
      else
        0

-- Proof sketch: Kirchhoff's rule at the middle vertex of the three-point path gives
-- `c 0 * (u 1 - u 0) = c 1 * (u 2 - u 1)`. For finite positive conductances, substituting the
-- boundary values `u 0 = 0` and `u 2 = 1` yields the conductance-ratio formula without any
-- `toReal` degeneration at `∞`.
/-- Example 19.18 (1): in the three-point series network with finite positive edge conductances
`c 0` and `c 1`, the middle voltage is the conductance ratio `c 1 / (c 0 + c 1)`. -/
theorem threePointSeriesVoltage_eq_conductanceRatio
    {u : Fin 3 → ℝ} {c : Fin 2 → ℝ≥0∞}
    (hu : IsElectricalPotential (pathConductance c) ({0, 2} : Set (Fin 3)) u)
    (hfinite : ∀ i : Fin 2, c i < ∞)
    (hpos : ∀ i : Fin 2, 0 < c i)
    (h0 : u 0 = 0) (h2 : u 2 = 1) :
    u 1 = (c 1).toReal / ((c 0).toReal + (c 1).toReal) := sorry

-- Proof sketch: apply `threePointSeriesVoltage_eq_conductanceRatio` to the path conductance
-- `i ↦ (R i)⁻¹`; positivity of the resistances gives the required finite positive conductances,
-- and the resulting fraction of reciprocals simplifies to the resistance ratio.
/-- Example 19.18 (2): in the same three-point series network with edge resistances `R 0` and
`R 1`, the middle voltage is the resistance ratio `R 0 / (R 0 + R 1)`. -/
theorem threePointSeriesVoltage_eq_resistanceRatio
    {u : Fin 3 → ℝ} {R : Fin 2 → ℝ}
    (hu : IsElectricalPotential
      (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) ({0, 2} : Set (Fin 3)) u)
    (h0 : u 0 = 0) (h2 : u 2 = 1)
    (hR0_pos : 0 < R 0) (hR1_pos : 0 < R 1) :
    u 1 = R 0 / (R 0 + R 1) := sorry

-- Proof sketch: on each edge, the current on the ordered pair `(l + 1, l)` agrees with the
-- terminal boundary current `I₀` from Definition 19.17. Multiplying by `R l` gives the edgewise
-- voltage drop `u (l + 1) - u l`, and the sum telescopes from `0` to `k`.
/-- Example 19.18 (3): in a series connection, if the current on each ordered edge `(l + 1, l)`
agrees with the common terminal current `I₀`, then the voltage drop from `0` to `k` is `I₀`
times the sum of the edge resistances. -/
theorem pathSeriesVoltageDrop_eq_current_mul_sum
    {u : Fin (k + 1) → ℝ} {I₀ : ℝ} {R : Fin k → ℝ}
    (hcurrent :
      ∀ l : Fin k,
        electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u
          l.succ (Fin.castSucc l) = I₀)
    (hR_pos : ∀ l : Fin k, 0 < R l) :
    u (Fin.last k) - u 0 = I₀ * ∑ l : Fin k, R l := sorry
-- Proof sketch: for the unit-voltage electrical potential on the path, Definition 19.17
-- identifies the effective resistance with the reciprocal of the boundary current through the
-- terminal vertex. The voltage-drop identity from the preceding theorem then gives the series
-- sum of resistances.
/-- Example 19.18 (4): for the unit-voltage electrical potential on the path `0 - 1 - ... - n`,
the effective resistance from `0` to `n` is the sum of the edge resistances. -/
theorem pathSeriesEffectiveResistance_eq_sum
    {u : Fin (n + 1) → ℝ} {R : Fin n → ℝ}
    (hu : IsElectricalPotential
      (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) ({0, Fin.last n} : Set (Fin (n + 1))) u)
    (h0 : u 0 = 0) (hn : u (Fin.last n) = 1)
    (hR_pos : ∀ l : Fin n, 0 < R l) :
    (1 /
      netFlowOnSet
        (electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u)
        ({Fin.last n} : Set (Fin (n + 1))) : ℝ) =
      ∑ l : Fin n, R l := sorry

-- Proof sketch: combine `pathSeriesEffectiveResistance_eq_sum` with the elementary splitting of
-- the finite sum of edge resistances at the breakpoint `k`.
/-- Example 19.18 (5) and (6): the effective resistance of a path is the sum of the resistances on
the initial segment and on the tail segment, so series resistances add under a decomposition at
`k`. -/
theorem pathSeriesEffectiveResistance_eq_prefix_add_tail
    (hk : k ≤ n) {u : Fin (n + 1) → ℝ} {R : Fin n → ℝ}
    (hu : IsElectricalPotential
      (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) ({0, Fin.last n} : Set (Fin (n + 1))) u)
    (h0 : u 0 = 0) (hn : u (Fin.last n) = 1)
    (hR_pos : ∀ l : Fin n, 0 < R l) :
    (1 /
      netFlowOnSet
        (electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u)
        ({Fin.last n} : Set (Fin (n + 1))) : ℝ) =
      (∑ l : Fin k, R (Fin.castLE hk l)) +
        ∑ l : Fin (n - k), R (Fin.natAdd_castLEEmb (Nat.sub_le n k) l) := sorry

-- Proof sketch: apply the effective-resistance formula to the initial segment `0 - ... - k` and
-- to the full path `0 - ... - n`, then use the boundary values `u 0 = 0` and `u n = 1` to solve
-- for `u k`.
/-- Example 19.18 (7): for a series chain with boundary values `u 0 = 0` and `u n = 1`, the
voltage at `k` is the ratio of the prefix resistance sum to the total resistance sum. -/
theorem pathSeriesVoltage_eq_resistanceRatio
    (hk : k ≤ n) {u : Fin (n + 1) → ℝ} {R : Fin n → ℝ}
    (hu : IsElectricalPotential
      (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) ({0, Fin.last n} : Set (Fin (n + 1))) u)
    (h0 : u 0 = 0) (hn : u (Fin.last n) = 1)
    (hR_pos : ∀ l : Fin n, 0 < R l) :
    u ⟨k, Nat.lt_succ_of_le hk⟩ =
      (∑ l : Fin k, R (Fin.castLE hk l)) / ∑ l : Fin n, R l := sorry

end SeriesConnection

section ParallelConnection

variable {n : ℕ}

/-- The two-vertex conductance network obtained by putting the wire conductances `C i` in
parallel between the boundary vertices `0` and `1`. -/
def parallelConductance (C : Fin n → ℝ≥0∞) : Fin 2 → Fin 2 → ℝ≥0∞ :=
  fun i j ↦
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then
      ∑ t, C t
    else
      0

-- Proof sketch: on the two-vertex network, the boundary values `u 0 = 0` and `u 1 = 1` directly
-- determine the induced current. For finite positive wire conductances, the total flow through
-- `1` is exactly the sum of those conductances, with no loss from `toReal` at `∞`.
/-- Example 19.18 (8): for parallel wires with finite positive conductances and unit voltage drop,
the effective conductance is the sum of the individual wire conductances. -/
theorem parallelConnectionEffectiveConductance_eq_sum
    {u : Fin 2 → ℝ} {C : Fin n → ℝ≥0∞}
    (h0 : u 0 = 0) (h1 : u 1 = 1)
    (hfinite : ∀ i : Fin n, C i < ∞)
    (hpos : ∀ i : Fin n, 0 < C i) :
    netFlowOnSet (electricalCurrent (parallelConductance C) u) ({1} : Set (Fin 2)) =
      (∑ i, C i).toReal := sorry

-- Proof sketch: apply the conductance formula to the conductance family `i ↦ (R i)⁻¹`; positive
-- resistances give finite positive conductances, and Definition 19.17 identifies effective
-- resistance with the reciprocal of the induced boundary current.
/-- Example 19.18 (9): for parallel wires with unit voltage drop, the effective resistance is the
reciprocal of the sum of the reciprocal wire resistances. -/
theorem parallelConnectionEffectiveResistance_eq_reciprocalSum
    {u : Fin 2 → ℝ} {R : Fin n → ℝ}
    (h0 : u 0 = 0) (h1 : u 1 = 1)
    (hR_pos : ∀ i : Fin n, 0 < R i) :
    (1 /
      netFlowOnSet
        (electricalCurrent (parallelConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u)
        ({1} : Set (Fin 2)) : ℝ) =
      (∑ i, (R i)⁻¹)⁻¹ := sorry

end ParallelConnection

end ProbabilityTheory
