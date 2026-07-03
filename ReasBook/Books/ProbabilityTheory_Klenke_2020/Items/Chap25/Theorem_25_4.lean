import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_2
import ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

section Setup

variable {μ : Measure Ω}

/-- Every predictable simple process is globally square-integrable on `Ω × [0,∞)` for a
probability measure. -/
theorem predictableSimpleProcess_memLp
    {ℱ : TimeFiltration} [IsProbabilityMeasure μ]
    (H : PredictableSimpleProcess ℱ) :
    MemLp (processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞) (processMeasure μ) := sorry

/-- The terminal Brownian elementary integral of a predictable simple process belongs to
`L²(μ)`. -/
theorem brownianElementaryIntegralAtInfinity_memLp
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : PredictableSimpleProcess ℱ) :
    MemLp (brownianElementaryIntegralAtInfinity W H) 2 μ := sorry

private theorem brownianElementaryIntegralAtInfinityL2_congr
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    {H K : PredictableSimpleProcess ℱ}
    {hH : MemLp (processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞) (processMeasure μ)}
    {hK : MemLp (processToTimeSpaceFun (K : Process)) (2 : ℝ≥0∞) (processMeasure μ)}
    (hHK :
      (predictableSimpleProcessToL2 H hH : Lp ℝ 2 (processMeasure μ)) =
        predictableSimpleProcessToL2 K hK) :
    (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H).toLp
        (brownianElementaryIntegralAtInfinity W H) =
      (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted K).toLp
        (brownianElementaryIntegralAtInfinity W K) := sorry

private theorem existsUnique_brownianElementaryIntegralAtInfinityL2
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : predictableSimpleProcessL2 ℱ μ) :
    ∃! I : Lp ℝ 2 μ,
      ∀ K : PredictableSimpleProcess ℱ,
        ∀ hK : MemLp (processToTimeSpaceFun (K : Process)) (2 : ℝ≥0∞) (processMeasure μ),
          (H : Lp ℝ 2 (processMeasure μ)) = predictableSimpleProcessToL2 K hK →
            I =
              (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted K).toLp
                (brownianElementaryIntegralAtInfinity W K) := by
  rcases H.2 with ⟨K, hK, hK_repr⟩
  have hK_repr' : (H : Lp ℝ 2 (processMeasure μ)) = predictableSimpleProcessToL2 K hK := by
    simpa using hK_repr
  refine ⟨(brownianElementaryIntegralAtInfinity_memLp hW hW_adapted K).toLp
      (brownianElementaryIntegralAtInfinity W K), ?_, ?_⟩
  · intro K' hK' hK'_repr
    have hKK' :
        (predictableSimpleProcessToL2 K hK : Lp ℝ 2 (processMeasure μ)) =
          predictableSimpleProcessToL2 K' hK' :=
      hK_repr'.symm.trans hK'_repr
    exact brownianElementaryIntegralAtInfinityL2_congr hW hW_adapted hKK'
  · intro I hI
    exact hI K hK hK_repr'

private noncomputable def brownianElementaryIntegralAtInfinityL2Data
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W) :
    predictableSimpleProcessL2 ℱ μ → Lp ℝ 2 μ :=
  fun H ↦
    Classical.choose <| (existsUnique_brownianElementaryIntegralAtInfinityL2 hW hW_adapted H).exists

private theorem brownianElementaryIntegralAtInfinityL2Data_spec
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : predictableSimpleProcessL2 ℱ μ)
    {K : PredictableSimpleProcess ℱ}
    {hK : MemLp (processToTimeSpaceFun (K : Process)) (2 : ℝ≥0∞) (processMeasure μ)}
    (hHK :
      (H : Lp ℝ 2 (processMeasure μ)) = predictableSimpleProcessToL2 K hK) :
    brownianElementaryIntegralAtInfinityL2Data hW hW_adapted H =
      (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted K).toLp
        (brownianElementaryIntegralAtInfinity W K) :=
  (Classical.choose_spec <|
      (existsUnique_brownianElementaryIntegralAtInfinityL2 hW hW_adapted H).exists)
    K hK hHK

private theorem brownianElementaryIntegralAtInfinityL2_map_add
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H K : predictableSimpleProcessL2 ℱ μ) :
    brownianElementaryIntegralAtInfinityL2Data hW hW_adapted (H + K) =
      brownianElementaryIntegralAtInfinityL2Data hW hW_adapted H +
        brownianElementaryIntegralAtInfinityL2Data hW hW_adapted K := sorry

private theorem brownianElementaryIntegralAtInfinityL2_map_smul
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (a : ℝ) (H : predictableSimpleProcessL2 ℱ μ) :
    brownianElementaryIntegralAtInfinityL2Data hW hW_adapted (a • H) =
      a • brownianElementaryIntegralAtInfinityL2Data hW hW_adapted H := sorry

private theorem brownianElementaryIntegralAtInfinityL2_norm_map
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : predictableSimpleProcessL2 ℱ μ) :
    ‖brownianElementaryIntegralAtInfinityL2Data hW hW_adapted H‖ = ‖H‖ := sorry

/-- The canonical linear isometric `L²` lift of the terminal Brownian elementary integral from
the upstream `L²(μ ⊗ dt)` image `predictableSimpleProcessL2 ℱ μ` of predictable simple
integrands for an `ℱ`-adapted Brownian motion. This is the core/canonical owner for Theorem
25.4(i). -/
noncomputable def brownianElementaryIntegralAtInfinityLinearIsometry
    (ℱ : TimeFiltration) {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W) :
    predictableSimpleProcessL2 ℱ μ →ₗᵢ[ℝ] Lp ℝ 2 μ where
  toLinearMap :=
    { toFun := brownianElementaryIntegralAtInfinityL2Data hW hW_adapted
      map_add' := brownianElementaryIntegralAtInfinityL2_map_add hW hW_adapted
      map_smul' := brownianElementaryIntegralAtInfinityL2_map_smul hW hW_adapted }
  norm_map' := brownianElementaryIntegralAtInfinityL2_norm_map hW hW_adapted

/-- Applying the canonical `L²` linear isometry of Theorem 25.4(i) to a concrete predictable
simple process recovers the `Lp` class of the source-facing terminal Brownian elementary integral
from Definition 25.3. -/
@[simp] theorem brownianElementaryIntegralAtInfinityLinearIsometry_apply
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : PredictableSimpleProcess ℱ) :
    brownianElementaryIntegralAtInfinityLinearIsometry ℱ hW hW_adapted
        (letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
         predictableSimpleProcessToL2 H (predictableSimpleProcess_memLp H)) =
      (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H).toLp
        (brownianElementaryIntegralAtInfinity W H) := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  exact brownianElementaryIntegralAtInfinityL2Data_spec hW hW_adapted
    (predictableSimpleProcessToL2 H (predictableSimpleProcess_memLp H)) rfl

/-- On a concrete predictable simple process, the canonical `L²` linear isometry of Theorem
25.4(i) agrees almost everywhere with the source-facing terminal Brownian elementary integral from
Definition 25.3. -/
theorem brownianElementaryIntegralAtInfinityLinearIsometry_ae_eq
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : PredictableSimpleProcess ℱ) :
    (brownianElementaryIntegralAtInfinityLinearIsometry ℱ hW hW_adapted
      (letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
       predictableSimpleProcessToL2 H (predictableSimpleProcess_memLp H)) : Ω → ℝ) =ᵐ[μ]
        brownianElementaryIntegralAtInfinity W H := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  rw [brownianElementaryIntegralAtInfinityLinearIsometry_apply hW hW_adapted H]
  exact MemLp.coeFn_toLp (brownianElementaryIntegralAtInfinity_memLp hW hW_adapted H)

-- Proof sketch: apply the linear isometry of Theorem 25.4(i) to the canonical `L²(μ ⊗ dt)`
-- class of `H` and rewrite both sides back to the source-facing formulas from Definitions 25.2
-- and 25.3.
/-- Theorem 25.4 (i), source-facing norm identity: the terminal Brownian elementary integral from
Definition 25.3 preserves the textbook `L²(μ ⊗ dt)` norm from Definition 25.2 on predictable
simple processes, provided the Brownian motion is adapted to the filtration of the integrand. -/
theorem brownianElementaryIntegralAtInfinity_norm_eq
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : PredictableSimpleProcess ℱ) :
    eLpNorm (brownianElementaryIntegralAtInfinity W H) 2 μ =
      ENNReal.ofReal
        (letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
         predictableSimpleProcessNorm μ H) := sorry

-- Proof sketch: for a predictable simple integrand `H`, the stopped Brownian elementary integral
-- is the usual Brownian Itô martingale; the Itô isometry gives the uniform `L²` bound, and the
-- Brownian sample-path continuity passes through the finite increment formula defining the
-- integral.
/-- Theorem 25.4 (ii): for every predictable simple process `H`, the stopped Brownian elementary
integral process is a continuous `𝓕`-martingale that is uniformly bounded in `L²(μ)`, provided
the Brownian motion is adapted to `𝓕`. -/
theorem brownianElementaryIntegral_isL2BoundedContinuousMartingale
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : PredictableSimpleProcess ℱ) :
    Martingale (brownianElementaryIntegral W H) ℱ μ ∧
      HasAlmostSurelyContinuousPaths μ (brownianElementaryIntegral W H) ∧
      ∃ C : ℝ≥0, ∀ t : NNReal, eLpNorm (brownianElementaryIntegral W H t) 2 μ ≤ (C : ℝ≥0∞) :=
  sorry

/-- The stopped Brownian elementary integral of a predictable simple process is a martingale. -/
theorem brownianElementaryIntegral_martingale
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : PredictableSimpleProcess ℱ) :
    Martingale (brownianElementaryIntegral W H) ℱ μ :=
  (brownianElementaryIntegral_isL2BoundedContinuousMartingale hW hW_adapted H).1

/-- The stopped Brownian elementary integral of a predictable simple process has almost surely
continuous sample paths. -/
theorem brownianElementaryIntegral_hasAlmostSurelyContinuousPaths
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : PredictableSimpleProcess ℱ) :
    HasAlmostSurelyContinuousPaths μ (brownianElementaryIntegral W H) :=
  (brownianElementaryIntegral_isL2BoundedContinuousMartingale hW hW_adapted H).2.1

/-- The stopped Brownian elementary integral of a predictable simple process is uniformly bounded
in `L²(μ)` over time. -/
theorem brownianElementaryIntegral_l2_bounded
    {ℱ : TimeFiltration} {W : Process}
    (hW : IsBrownianMotion μ W)
    (hW_adapted : Adapted ℱ W)
    (H : PredictableSimpleProcess ℱ) :
    ∃ C : ℝ≥0, ∀ t : NNReal, eLpNorm (brownianElementaryIntegral W H t) 2 μ ≤ (C : ℝ≥0∞) :=
  (brownianElementaryIntegral_isL2BoundedContinuousMartingale hW hW_adapted H).2.2

end Setup

end ProbabilityTheory

end
