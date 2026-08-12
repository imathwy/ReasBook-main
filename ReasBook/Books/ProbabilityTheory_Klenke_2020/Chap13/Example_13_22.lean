import ProbabilityTheory_Klenke_2020.Chap13.Definition_13_21

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace StieltjesFunction

/-- Translation of a real Stieltjes function by `a`, i.e. `x ↦ F (x + a)`. -/
def translate (F : StieltjesFunction ℝ) (a : ℝ) : StieltjesFunction ℝ :=
  { toFun := fun x ↦ F (x + a)
    mono' := F.mono.comp (monotone_id.add_const a)
    right_continuous' := fun x ↦ by
      have h_add : ContinuousWithinAt (fun y : ℝ ↦ y + a) (Set.Ici x) x :=
        (continuous_add_const a).continuousWithinAt
      have h_mapsTo : Set.MapsTo (fun y : ℝ ↦ y + a) (Set.Ici x) (Set.Ici (x + a)) :=
        fun y hy ↦ by simpa using add_le_add_right hy a
      have h_comp :
          ContinuousWithinAt ((fun y : ℝ ↦ F y) ∘ fun y : ℝ ↦ y + a) (Set.Ici x) x :=
        ContinuousWithinAt.comp (F.right_continuous (x + a)) h_add h_mapsTo
      simpa [Function.comp] using h_comp }

@[simp] theorem translate_apply (F : StieltjesFunction ℝ) (a x : ℝ) :
    F.translate a x = F (x + a) := rfl

/-- Translating a defective distribution function preserves defectiveness. -/
instance instIsDefectiveDistributionFunction_translate (F : StieltjesFunction ℝ)
    [IsDefectiveDistributionFunction F] (a : ℝ) :
    IsDefectiveDistributionFunction (F.translate a) := sorry

/-- Translating a distribution function preserves the distribution-function property. -/
instance instIsDistributionFunction_translate (F : StieltjesFunction ℝ)
    [IsDistributionFunction F] (a : ℝ) :
    IsDistributionFunction (F.translate a) := sorry

end StieltjesFunction

section

/-- The zero Stieltjes function is a defective distribution function. -/
instance : IsDefectiveDistributionFunction (0 : StieltjesFunction ℝ) where
  nonneg _ := by simp
  le_one _ := by simp
  tendsto_atBot_zero := tendsto_const_nhds

variable (F : StieltjesFunction ℝ)

-- Proof sketch: since `F y → 1` as `y → +∞`, compose this with
-- `n ↦ x + n`, which also tends to `+∞`.
/-- Example 13.22 (1): at each fixed `x`, the right-translated values `F(x + n)` converge to
`1`. -/
theorem tendsto_right_shifted_distribution_function_at_point [IsDistributionFunction F] (x : ℝ) :
    Tendsto (fun n : ℕ ↦ F.translate n x) atTop (𝓝 1) := sorry

-- Proof sketch: weak convergence would force the candidate limit to agree with the pointwise
-- limit `1` at every continuity point. Since a defective distribution function must tend to `0`
-- at `-∞`, the constant pointwise limit `1` cannot arise from any admissible weak limit in the
-- sense of Definition 13.21.
/-- Example 13.22 (1): the right-shifted distribution functions do not converge weakly, even to a
defective distribution function, because their pointwise limit is the inadmissible constant
function `1`. -/
theorem right_shifted_distribution_functions_not_weakly_converges_to
    [IsDistributionFunction F] {G : StieltjesFunction ℝ} :
    ¬ distribution_function_weakly_converges_to (fun n ↦ F.translate n) G := sorry

-- Proof sketch: the constant function `1` fails the defining condition `F(x) → 0` as
-- `x → -∞`, so it cannot be a distribution function.
/-- Example 13.22 (2): the constant function `1` is not a distribution function on `ℝ`. -/
theorem constant_one_not_isDistributionFunction :
    ¬ IsDistributionFunction (StieltjesFunction.const ℝ 1) := sorry

-- Proof sketch: the same left-tail obstruction already rules out defectiveness, since a
-- defective distribution function must tend to `0` at `-∞`.
/-- The constant function `1` is not even a defective distribution function on `ℝ`. -/
theorem constant_one_not_isDefectiveDistributionFunction :
    ¬ IsDefectiveDistributionFunction (StieltjesFunction.const ℝ 1) := sorry

-- Proof sketch: since `F y → 0` as `y → -∞`, compose this with
-- `n ↦ x - n`, which tends to `-∞`.
/-- Example 13.22 (3): at each fixed `x`, the left-translated values `F(x - n)` converge to
`0`. -/
theorem tendsto_left_shifted_distribution_function_at_point [IsDistributionFunction F] (x : ℝ) :
    Tendsto (fun n : ℕ ↦ F.translate (-(n : ℝ)) x) atTop (𝓝 0) := sorry

/- Example 13.22 (4): the zero Stieltjes function has right-tail limit `0`; this is the direct
constant-function convergence fact. -/
#check (tendsto_const_nhds : Tendsto (0 : StieltjesFunction ℝ) atTop (𝓝 0))

-- Proof sketch: for fixed `n`, the map `x ↦ x - n` tends to `+∞` as `x → +∞`; composing with
-- `F x → 1` gives the right-tail limit `1` for the shifted function.
/- Example 13.22 (5): every left-translated function `x ↦ F(x - n)` still has right-tail limit
`1`; this is the `tendsto_atTop_one` field of the translated `IsDistributionFunction` instance. -/
section

variable [IsDistributionFunction F] (n : ℕ)

#check (IsDistributionFunction.tendsto_atTop_one :
  Tendsto (F.translate (-(n : ℝ))) atTop (𝓝 1))

end

-- Proof sketch: the left shifts converge pointwise to the zero function, but weak convergence in
-- the sense of Definition 13.21 would force convergence of the endpoint values, equivalently of
-- the total masses. Here each shifted distribution function still has endpoint value `1`, while
-- the zero limit has endpoint value `0`.
/-- Example 13.22 (3)--(5): although the left-shifted distribution functions converge pointwise to
`0`, they do not converge weakly to the zero defective distribution function because the endpoint
condition fails. -/
theorem left_shifted_distribution_functions_not_weakly_converges_to_zero
    [IsDistributionFunction F] :
    ¬ distribution_function_weakly_converges_to
      (fun n ↦ F.translate (-(n : ℝ))) 0 := sorry

end
