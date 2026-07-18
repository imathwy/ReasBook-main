import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

namespace MeasureTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "RealProcess" => NNReal → Ω → ℝ

variable {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}

namespace IsStronglyProgressive

/-- Remark 25.7: every progressively measurable real-valued process is product measurable. -/
-- Proof sketch: for each deterministic horizon `t`, progressive measurability gives measurability
-- of the restriction of `H` to the strip `Set.Iic t × Ω` with respect to `𝓑([0,t]) ⊗ ℱ t`;
-- since `ℱ t ≤ inferInstance`, these restrictions are jointly measurable for the ambient product
-- measurable space, and one patches the stripwise statements over the increasing cover
-- `[0,∞) = ⋃ n, [0,n]`.
theorem measurable_uncurry
    (hH : IsStronglyProgressive ℱ H) :
    Measurable (Function.uncurry H) := sorry

/-- A progressively measurable real-valued process is adapted to the underlying filtration. -/
-- Proof sketch: `IsStronglyProgressive.stronglyAdapted` upgrades `H` to a strongly adapted
-- process, and
-- for real-valued processes strong adaptedness implies ordinary adaptedness.
theorem adapted
    (hH : IsStronglyProgressive ℱ H) :
    Adapted ℱ H :=
  (IsStronglyProgressive.stronglyAdapted hH).adapted

end IsStronglyProgressive

namespace Adapted

/-- An adapted product-measurable real-valued process admits a progressively measurable
modification. -/
-- Proof sketch: use the standard regularization theorem for jointly measurable adapted processes
-- to build a version `H'` whose restriction to every strip `[0,t] × Ω` is measurable for
-- `𝓑([0,t]) ⊗ ℱ t`; by construction `H'` agrees with `H` almost surely at each deterministic time,
-- so `H'` is a progressively measurable modification of `H`.
theorem exists_progMeasurable_modification_of_productMeasurable
    (hH_adapted : Adapted ℱ H)
    (hH_prod : Measurable (Function.uncurry H)) :
    ∃ H' : RealProcess, IsStronglyProgressive ℱ H' ∧ AreModifications μ H H' := sorry

end Adapted

end MeasureTheory
