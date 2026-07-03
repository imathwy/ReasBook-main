import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_23_20 (from Items/Chap23) -/
noncomputable section

namespace ProbabilityTheory

/-- The mean-field energy per particle in the Weiss ferromagnet with external field `h`. -/
def weissMeanFieldEnergy (h m : ℝ) : ℝ :=
  -((m ^ 2) / 2) - h * m

/-- The binary entropy term associated with a magnetization value `m`. -/
def weissEntropy (m : ℝ) : ℝ :=
  -((1 + m) / 2) * Real.log ((1 + m) / 2) -
    ((1 - m) / 2) * Real.log ((1 - m) / 2)

/-- The Weiss free energy per particle at inverse temperature `β` and external field `h`. -/
def weissFreeEnergy (β h m : ℝ) : ℝ :=
  weissMeanFieldEnergy h m - β⁻¹ * weissEntropy m

-- Proof sketch: unfold `weissFreeEnergy`, `weissMeanFieldEnergy`, and `weissEntropy`, then
-- simplify the signs in the entropy contribution.
/-- The Weiss free energy is the mean-field energy plus the inverse-temperature weighted entropy
term written in logarithmic form. -/
theorem weissFreeEnergy_def (β h m : ℝ) :
    weissFreeEnergy β h m =
      -((m ^ 2) / 2) - h * m +
        β⁻¹ * (((1 + m) / 2) * Real.log ((1 + m) / 2) +
          ((1 - m) / 2) * Real.log ((1 - m) / 2)) := sorry

-- Proof sketch: the stationary-point equation is `-m - h + β⁻¹ * Real.artanh m = 0`. Multiply by
-- `β`, rewrite it as `Real.artanh m = β * (m + h)`, then apply `Real.tanh` and use
-- `Real.tanh_artanh hm`; the converse uses `Real.artanh_tanh`.
/-- Example 23.20: for `m ∈ (-1,1)` and positive inverse temperature `β`, the stationary-point
equation for the Weiss free energy is equivalent to the mean-field fixed-point equation
`m = tanh (β (m + h))`. -/
theorem weissFreeEnergy_stationary_iff {β h m : ℝ} (hβ : 0 < β)
    (hm : m ∈ Set.Ioo (-1 : ℝ) 1) :
    (-m - h + β⁻¹ * Real.artanh m = 0) ↔
      m = Real.tanh (β * (m + h)) := sorry

-- Proof sketch: solve the linearized equation `m = β * (m + h)` by rearranging terms to
-- `(β⁻¹ - 1) * m = h` and dividing by `β⁻¹ - 1`.
/-- The linearized Weiss equation gives the Curie-Weiss response formula away from the critical
inverse temperature `β = 1`. -/
theorem weissLinearizedEquation_iff {β h m : ℝ} (hβ : β ≠ 1) :
    m = β * (m + h) ↔ m = h / (β⁻¹ - 1) := sorry

end ProbabilityTheory
