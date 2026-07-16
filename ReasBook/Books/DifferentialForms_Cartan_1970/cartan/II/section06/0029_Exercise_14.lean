import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0017_Definition_II_1_extra_10»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0026_Definition_II_1_extra_16»

open scoped unitInterval

-- Declarations for this item will be appended below by the statement pipeline.

namespace Path

/-- Helper for Exercise 14: the homotopy obtained by interpolating two logarithmic lifts and
exponentiating back after translating by the center `a`. -/
noncomputable def interpolated_homotopy_fun (a : ℂ) (w₀ w₁ : C(I, ℂ)) : I × I → ℂ :=
  fun p ↦
    a + Complex.exp
      ((((1 : ℂ) - ((p.1 : ℝ) : ℂ)) * w₀ p.2) + (((p.1 : ℝ) : ℂ) * w₁ p.2))

/-- Helper for Exercise 14: interpolating two logarithmic lifts with the same endpoint jump
preserves that common jump. -/
lemma interpolated_log_lift_endpoint_eq {w₀ w₁ : C(I, ℂ)} (s : I) {Δ : ℂ}
    (hw₀ : w₀ 1 = w₀ 0 + Δ) (hw₁ : w₁ 1 = w₁ 0 + Δ) :
    (((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ 1 + ((s : ℝ) : ℂ) * w₁ 1) =
      (((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ 0 + ((s : ℝ) : ℂ) * w₁ 0) + Δ := by
  -- Expand both endpoint jumps and collect the shared `Δ`.
  rw [hw₀, hw₁]
  ring

/-- Helper for Exercise 14: adding a period whose exponential is `1` does not change the
exponential. -/
lemma exp_add_eq_self_of_exp_eq_one {u Δ : ℂ} (hΔ : Complex.exp Δ = 1) :
    Complex.exp (u + Δ) = Complex.exp u := by
  -- Split off the period and use that its exponential is trivial.
  rw [Complex.exp_add, hΔ, mul_one]

/-- Helper for Exercise 14: the interpolated logarithmic-lift homotopy is continuous. -/
lemma continuous_interpolated_homotopy_fun {a : ℂ} {w₀ w₁ : C(I, ℂ)} :
    Continuous (interpolated_homotopy_fun a w₀ w₁) := by
  -- Continuity is obtained by composing the two lifts with the coordinate projections.
  have hs_real : Continuous fun p : I × I ↦ (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hs : Continuous fun p : I × I ↦ ((p.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hs_real
  have hone_sub : Continuous fun p : I × I ↦ (1 : ℂ) - ((p.1 : ℝ) : ℂ) :=
    continuous_const.sub hs
  have hw₀ : Continuous fun p : I × I ↦ w₀ p.2 :=
    w₀.continuous.comp continuous_snd
  have hw₁ : Continuous fun p : I × I ↦ w₁ p.2 :=
    w₁.continuous.comp continuous_snd
  have hinterp : Continuous fun p : I × I ↦
      (((1 : ℂ) - ((p.1 : ℝ) : ℂ)) * w₀ p.2) + (((p.1 : ℝ) : ℂ) * w₁ p.2) :=
    (hone_sub.mul hw₀).add (hs.mul hw₁)
  -- The final translation by `a` preserves continuity.
  exact continuous_const.add (Complex.continuous_exp.comp hinterp)

/-- Helper for Exercise 14: the interpolated homotopy starts at the first loop. -/
lemma interpolated_homotopy_apply_zero {a z₀ : ℂ} {γ₀ : Path z₀ z₀} {w₀ w₁ : C(I, ℂ)}
    (hw₀exp : ∀ t : I, Complex.exp (w₀ t) = γ₀ t - a) (t : I) :
    interpolated_homotopy_fun a w₀ w₁ (0, t) = γ₀ t := by
  -- At `s = 0`, only the first lift contributes to the interpolation.
  calc
    interpolated_homotopy_fun a w₀ w₁ (0, t) = a + Complex.exp (w₀ t) := by
      simp [interpolated_homotopy_fun]
    _ = a + (γ₀ t - a) := by rw [hw₀exp t]
    _ = γ₀ t := by ring

/-- Helper for Exercise 14: the interpolated homotopy ends at the second loop. -/
lemma interpolated_homotopy_apply_one {a z₁ : ℂ} {γ₁ : Path z₁ z₁} {w₀ w₁ : C(I, ℂ)}
    (hw₁exp : ∀ t : I, Complex.exp (w₁ t) = γ₁ t - a) (t : I) :
    interpolated_homotopy_fun a w₀ w₁ (1, t) = γ₁ t := by
  -- At `s = 1`, only the second lift contributes to the interpolation.
  calc
    interpolated_homotopy_fun a w₀ w₁ (1, t) = a + Complex.exp (w₁ t) := by
      simp [interpolated_homotopy_fun]
    _ = a + (γ₁ t - a) := by rw [hw₁exp t]
    _ = γ₁ t := by ring

/-- Helper for Exercise 14: translating an exponential image by `a` keeps it away from the center
`a`. -/
lemma interpolated_log_lift_avoids_center (a z : ℂ) :
    a + Complex.exp z ∉ ({a} : Set ℂ) := by
  intro hz
  -- Subtract `a` from the singleton equality to contradict `Complex.exp_ne_zero`.
  rw [Set.mem_singleton_iff] at hz
  have hz_eq : Complex.exp z = 0 := by
    apply add_left_cancel (a := a)
    calc
      a + Complex.exp z = a := hz
      _ = a + 0 := by simp
  exact Complex.exp_ne_zero z hz_eq

-- Proof sketch: choose logarithmic lifts `w₀`, `w₁` for the two loops with the same endpoint
-- increment `2 * π * n * I`, linearly interpolate these lifts, and compose with `Complex.exp`
-- after re-centering at `a` to obtain a homotopy through closed loops in `ℂ \ {a}`.
/-- If two closed paths in `ℂ \ {a}` have the same index with respect to `a`, then they are
homotopic through closed paths in `ℂ \ {a}`. -/
theorem closedPathHomotopicIn_compl_singleton_of_sameIndexAt {a z₀ z₁ : ℂ}
    {γ₀ : Path z₀ z₀} {γ₁ : Path z₁ z₁} {n : ℤ} (hγ₀ : γ₀.HasIndexAt a n)
    (hγ₁ : γ₁.HasIndexAt a n) :
    ClosedPathHomotopicIn ({a} : Set ℂ)ᶜ γ₀ γ₁ := by
  -- Unpack the two logarithmic lifts with their common endpoint jump.
  rcases hγ₀ with ⟨w₀, hw₀exp, hw₀jump⟩
  rcases hγ₁ with ⟨w₁, hw₁exp, hw₁jump⟩
  let Δ : ℂ := ((2 * Real.pi : ℂ) * (n : ℂ)) * Complex.I
  have hΔexp : Complex.exp Δ = 1 := by
    -- Normalize the jump to the standard `n * (2πi)` shape.
    rw [show Δ = (n : ℂ) * (2 * Real.pi * Complex.I) by
      dsimp [Δ]
      ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  -- Build the homotopy by linearly interpolating the logarithmic lifts and exponentiating back.
  refine ⟨{ toHomotopy := ?_, prop' := ?_ }⟩
  · refine
      { toFun := interpolated_homotopy_fun a w₀ w₁
        continuous_toFun := ?_
        map_zero_left := ?_
        map_one_left := ?_ }
    · -- The explicit continuous-map lemma avoids re-elaborating the whole expression inline.
      exact continuous_interpolated_homotopy_fun
    · intro t
      -- The left boundary of the homotopy recovers `γ₀`.
      exact interpolated_homotopy_apply_zero hw₀exp t
    · intro t
      -- The right boundary of the homotopy recovers `γ₁`.
      exact interpolated_homotopy_apply_one hw₁exp t
  · intro s
    rw [isClosedPathIn_compl_iff]
    constructor
    · -- Every intermediate loop is closed because the interpolated lift keeps the same jump `Δ`.
      change
        interpolated_homotopy_fun a w₀ w₁ (s, 0) =
          interpolated_homotopy_fun a w₀ w₁ (s, 1)
      change
        a + Complex.exp ((((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ 0) + (((s : ℝ) : ℂ) * w₁ 0)) =
          a + Complex.exp ((((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ 1) + (((s : ℝ) : ℂ) * w₁ 1))
      have hEndpoint :
          (((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ 1 + ((s : ℝ) : ℂ) * w₁ 1) =
            (((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ 0 + ((s : ℝ) : ℂ) * w₁ 0) + Δ :=
        interpolated_log_lift_endpoint_eq s hw₀jump hw₁jump
      -- The shared logarithmic jump exponentiates to `1`, so the endpoints agree.
      have hClosed :
          a + Complex.exp ((((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ 1) + (((s : ℝ) : ℂ) * w₁ 1)) =
            a + Complex.exp ((((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ 0) + (((s : ℝ) : ℂ) * w₁ 0)) := by
        calc
          a + Complex.exp ((((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ 1) + (((s : ℝ) : ℂ) * w₁ 1))
              = a + Complex.exp
                  ((((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ 0 + ((s : ℝ) : ℂ) * w₁ 0) + Δ) := by
                    rw [hEndpoint]
          _ = a + Complex.exp ((((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ 0) + (((s : ℝ) : ℂ) * w₁ 0)) := by
                rw [exp_add_eq_self_of_exp_eq_one hΔexp]
      exact hClosed.symm
    · intro t
      -- Exponentials never vanish, so every intermediate loop stays in `ℂ \ {a}`.
      change
        a + Complex.exp ((((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ t) + (((s : ℝ) : ℂ) * w₁ t)) ∉
          ({a} : Set ℂ)
      exact
        interpolated_log_lift_avoids_center a
          ((((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ t) + (((s : ℝ) : ℂ) * w₁ t))

/-- Exercise 14: if two closed paths in `ℂ \ {0}` have the same index with respect to `0`, then
they are homotopic through closed paths in `ℂ \ {0}`. -/
theorem closedPathHomotopicIn_compl_zero_of_sameIndexAtZero {z₀ z₁ : ℂ} {γ₀ : Path z₀ z₀}
    {γ₁ : Path z₁ z₁} {n : ℤ} (hγ₀ : γ₀.HasIndexAt 0 n) (hγ₁ : γ₁.HasIndexAt 0 n) :
    ClosedPathHomotopicIn ({0} : Set ℂ)ᶜ γ₀ γ₁ := by
  simpa using closedPathHomotopicIn_compl_singleton_of_sameIndexAt hγ₀ hγ₁

end Path
