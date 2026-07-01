import Mathlib
import AchimKlenkeLean.Items.Chap06.Definition_6_8
import AchimKlenkeLean.Items.Chap09.Example_9_40

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration

local notation "S" => petersburgPartialSum
local notation "μ" => fairBernoulliMeasure
local notation "ℱ" => petersburgPayoffFiltration

/- Example 11.6 is `source-facing`: it records the almost-sure convergence of the Petersburg gain
process to `1`, its failure to converge in `L¹`, and the resulting failure of uniform
integrability. The `core/canonical` owner layer is split between the Chapter 4 Petersburg limit
API (`petersburgLimit`, `petersburgPartialSum_ae_tendsto_limit`, `petersburgLimit_ae_eq_one`,
`integral_petersburgPartialSum_eq_zero`) and the Chapter 9/Mathlib martingale owner abstraction
(`petersburg_game_gain_process_martingale`, `ℱ.limitProcess`). The only `bridge/view` introduced
here is the almost-sure identification of that canonical `limitProcess` with the constant `1`;
the file does not keep a parallel wrapper around the Petersburg process itself.
-/

-- Proof sketch: use the pathwise identity
-- `one_sub_petersburgGainProcess_eq_prod`; each factor `1 - D_i(ω)` is either `0` or `2`, hence
-- the product is nonnegative and therefore `1 - S_n(ω) ≥ 0`.
/-- Every finite Petersburg gain is pathwise bounded above by `1`, hence also almost surely. -/
theorem petersburg_gain_process_le_one (n : ℕ) (ω : BernoulliSequence) :
    S n ω ≤ 1 := sorry

-- Proof sketch: reuse the Chapter 4 owner theorem `petersburgPartialSum_ae_tendsto_limit`, then
-- intersect with the full-measure event from `petersburgLimit_ae_eq_one`; on that event the
-- `EReal` limit is the finite value `1`, so the convergence upgrades to ordinary real-valued
-- convergence to the constant random variable `1`.
/-- Example 11.6: the Petersburg game gain process from Example 9.40 converges almost surely to
the constant random variable `1`. -/
theorem petersburg_gain_process_ae_tendsto_one :
    ∀ᵐ ω ∂ μ, Tendsto (fun n ↦ S n ω) atTop (nhds 1) :=
  sorry

-- Proof sketch: if the martingale were uniformly integrable, then the owner theorem
-- `Martingale.ae_eq_condExp_limitProcess` would identify each `S_n` with the conditional
-- expectation of the canonical limit process `ℱ.limitProcess S μ`; compare that owner limit with
-- the Chapter 4 almost-sure limit `1` using `petersburg_gain_process_ae_tendsto_one`.
/-- The canonical Chapter 11 limit process of the Petersburg gain martingale is almost surely the
constant random variable `1`. -/
theorem petersburg_gain_process_limitProcess_ae_eq_one :
    limitProcess S ℱ μ =ᵐ[μ] fun _ ↦ (1 : ℝ) := sorry

-- Proof sketch: if `S_n → 1` in mean, then the owner theorem `TendstoInMean.integrableSeq`
-- gives integrability of each `S_n`, `TendstoInMean.integrable` gives integrability of the limit,
-- and `TendstoInMean.tendsto_eLpNorm` recovers the raw `L¹` seminorm convergence. The standard
-- `L¹` continuity of integration would then force the integrals to converge. But `∫ S_n dP = 0`
-- for every `n`, while `∫ 1 dP = 1` on the fair Bernoulli probability space, giving a
-- contradiction.
/-- The almost-sure convergence of the Petersburg gain process does not improve to convergence in
`L¹`. -/
theorem petersburg_gain_process_not_tendstoInMean_to_one :
    ¬ TendstoInMean μ S (fun _ ↦ (1 : ℝ)) := sorry

-- Proof sketch: a uniformly integrable martingale converges in `L¹` to its owner limit process
-- `ℱ.limitProcess S μ`; the bridge theorem `petersburg_gain_process_limitProcess_ae_eq_one`
-- identifies that canonical limit with `1`, contradicting
-- `petersburg_gain_process_not_tendstoInMean_to_one`.
/-- The Petersburg gain process is not uniformly integrable. -/
theorem petersburg_gain_process_not_uniformIntegrable :
    ¬ UniformIntegrable S 1 μ := sorry
