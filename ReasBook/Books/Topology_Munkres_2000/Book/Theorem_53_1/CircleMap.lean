module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

public section

open Complex Function Set

namespace Circle

/-- The one-turn parametrization of the unit circle. -/
noncomputable def turnExp : ℝ → Circle :=
  fun x ↦ Circle.exp (2 * Real.pi * x)

/-- Helper for Theorem 53.1: `turnExp` is exponential after angular scaling. -/
theorem turnExp_eq_exp_scale :
    turnExp = fun x ↦ Circle.exp (2 * Real.pi * x) := by
  -- Expose the defining function once for predicate-level transport arguments.
  rfl

/-- The one-turn circle parametrization sends `0` to the basepoint `1 : Circle`. -/
theorem turnExp_zero : turnExp 0 = 1 := by
  simp [turnExp]

/-- The one-turn circle parametrization returns to the basepoint after one turn. -/
theorem turnExp_one : turnExp 1 = 1 := by
  simp [turnExp]

/-- The one-turn circle parametrization sends every integer to the basepoint. -/
theorem turnExp_int (n : ℤ) : turnExp n = 1 := by
  simpa [turnExp] using Circle.exp_two_pi_mul_int n

/-- The one-turn circle exponential has the usual cosine-sine coordinate formula. -/
theorem coe_turnExp (x : ℝ) :
    (turnExp x : ℂ) =
      Real.cos (2 * Real.pi * x) + Real.sin (2 * Real.pi * x) * Complex.I := by
  -- Unfold the parametrization and use the standard complex exponential formula.
  simp [turnExp, Circle.coe_exp, Complex.exp_mul_I]

/-- The one-turn parametrization of the circle is a covering map. -/
theorem isCoveringMap_turnExp : IsCoveringMap turnExp := by
  -- Precompose the exponential covering by the nonzero scaling homeomorphism.
  have hpi : 2 * Real.pi ≠ 0 := by
    positivity
  rw [turnExp_eq_exp_scale]
  simpa [Function.comp_def] using
    Circle.isCoveringMap_exp.comp_homeomorph (Homeomorph.mulLeft₀ (2 * Real.pi) hpi)

/-- The one-turn circle parametrization is surjective. -/
theorem turnExp_surjective : Function.Surjective turnExp := by
  -- Surjectivity is preserved when the exponential is precomposed by this homeomorphism.
  have hpi : 2 * Real.pi ≠ 0 := by
    positivity
  rw [turnExp_eq_exp_scale]
  simpa [Function.comp_def] using
    Circle.exp_surjective.comp (Homeomorph.mulLeft₀ (2 * Real.pi) hpi).surjective

/-- The fiber of the one-turn circle parametrization over `1` consists of the integers. -/
theorem turnExp_eq_one_iff (x : ℝ) :
    turnExp x = 1 ↔ ∃ n : ℤ, x = n := by
  constructor
  · -- Rewrite the exponential fiber equation and cancel the nonzero angular scale.
    intro hx
    rw [turnExp, Circle.exp_eq_one] at hx
    obtain ⟨n, hn⟩ := hx
    refine ⟨n, ?_⟩
    have hpi : 2 * Real.pi ≠ 0 := by
      positivity
    apply mul_left_cancel₀ hpi
    calc
      (2 * Real.pi) * x = n * (2 * Real.pi) := hn
      _ = (2 * Real.pi) * n := mul_comm _ _
  · -- Every integer is sent to the basepoint by one full-turn periodicity.
    rintro ⟨n, rfl⟩
    exact turnExp_int n

/-- Every integer unit interval maps onto the circle under the one-turn parametrization. -/
theorem surjOn_Icc_int_turnExp (n : ℤ) :
    Set.SurjOn turnExp (Set.Icc (n : ℝ) ((n : ℝ) + 1)) Set.univ := by
  -- Scaling converts the exponential's `2π` period into period `1` for `turnExp`.
  have hperiodic : Function.Periodic turnExp 1 := by
    intro x
    unfold turnExp
    calc
      Circle.exp (2 * Real.pi * (x + 1)) =
          Circle.exp (2 * Real.pi * x + 2 * Real.pi) := by
        congr 1
        ring
      _ = Circle.exp (2 * Real.pi * x) := Circle.periodic_exp (2 * Real.pi * x)
  -- A full period has the entire range as its image, and that range is the circle.
  have himage :
      turnExp '' Set.Icc (n : ℝ) ((n : ℝ) + 1) = Set.univ := by
    calc
      turnExp '' Set.Icc (n : ℝ) ((n : ℝ) + 1) = Set.range turnExp :=
        hperiodic.image_Icc one_pos n
      _ = Set.univ := turnExp_surjective.range_eq
  intro y hy
  rw [himage]
  exact hy

end Circle
