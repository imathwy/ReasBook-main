module

public import Topology_Munkres_2000.Book.Definition_18_9.SeparateContinuity
public import Mathlib.Topology.Algebra.Ring.Real

public section

namespace SeparateContinuityCounterexample

/-- The real function `F` used to distinguish separate continuity from continuity. -/
@[expose]
noncomputable def map (p : ℝ × ℝ) : ℝ :=
  p.1 * p.2 / (p.1 ^ 2 + p.2 ^ 2)

/-- The value of `map` in coordinates. -/
theorem map_apply (x y : ℝ) :
    map (x, y) = x * y / (x ^ 2 + y ^ 2) := rfl

/-- The textbook piecewise formula for `map`. -/
theorem map_eq_piecewise (x y : ℝ) :
    map (x, y) = if (x, y) = (0, 0) then 0 else x * y / (x ^ 2 + y ^ 2) := by
  split_ifs with h
  · simp_all [map]
  · rfl

/-- The restriction of `map` to the diagonal of `ℝ × ℝ`. -/
@[expose]
noncomputable def diagonal (x : ℝ) : ℝ :=
  map (x, x)

/-- The value of the diagonal restriction at a point. -/
theorem diagonal_apply (x : ℝ) :
    diagonal x = if x = 0 then 0 else (1 / 2 : ℝ) := by
  rw [diagonal, map]
  split_ifs with h
  · simp [h]
  · field_simp
    ring

/-- Helper for Exercise 18.12: a sum of two real squares is nonzero when one
of its inputs is nonzero. -/
private lemma sqAddSq_ne_zero_of_ne_zero {x y : ℝ} (h : x ≠ 0 ∨ y ≠ 0) :
    x ^ 2 + y ^ 2 ≠ 0 := by
  -- The nonzero coordinate contributes a strictly positive square.
  rcases h with hx | hy
  · exact ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg y))
  · exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_ne_zero hy))

/-- Part (1) of Exercise 18.12: The map `map` is continuous in each variable separately. -/
theorem separatelyContinuous : SeparatelyContinuous map := by
  -- Fixing either coordinate reduces `map` to a quotient of continuous functions.
  constructor
  · intro y
    by_cases hy : y = 0
    · subst y
      simpa [map] using (continuous_const : Continuous fun _ : ℝ ↦ (0 : ℝ))
    · exact (continuous_id.mul continuous_const).div
        ((continuous_id.pow 2).add (continuous_const.pow 2))
        (fun x ↦ sqAddSq_ne_zero_of_ne_zero (Or.inr hy))
  · intro x
    by_cases hx : x = 0
    · subst x
      simpa [map] using (continuous_const : Continuous fun _ : ℝ ↦ (0 : ℝ))
    · exact (continuous_const.mul continuous_id).div
        ((continuous_const.pow 2).add (continuous_id.pow 2))
        (fun y ↦ sqAddSq_ne_zero_of_ne_zero (Or.inl hx))

/-- Part (2) of Exercise 18.12: The diagonal restriction is `0` at the origin and `1 / 2`
away from the origin. -/
theorem diagonal_eq :
    diagonal = fun x ↦ if x = 0 then 0 else (1 / 2 : ℝ) := by
  funext x
  exact diagonal_apply x

/-- Helper for Exercise 18.12: the diagonal restriction is composition with
the diagonal embedding of `ℝ` into `ℝ × ℝ`. -/
private lemma diagonal_eq_comp :
    diagonal = map ∘ fun x ↦ (x, x) := by
  -- Unfold the named restriction once, outside the continuity argument.
  rfl

/-- Helper for Exercise 18.12: the diagonal lies below `1 / 4` exactly at the
origin. -/
private lemma diagonal_preimage_Iio_quarter :
    diagonal ⁻¹' Set.Iio (1 / 4 : ℝ) = {0} := by
  -- Use the computed diagonal values to characterize the preimage pointwise.
  ext x
  rw [Set.mem_preimage, Set.mem_Iio, Set.mem_singleton_iff, diagonal_apply]
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx]
    norm_num

/-- Exercise 18.12 (3): The map `map` is not continuous. -/
theorem not_continuous : ¬ Continuous map := by
  -- Continuity of `map` would make its diagonal restriction continuous.
  intro hmap
  have hdiagonal : Continuous diagonal := by
    rw [diagonal_eq_comp]
    exact hmap.comp (continuous_id.prodMk continuous_id)
  -- The open ray below `1 / 4` would then have the non-open singleton preimage.
  have hopen : IsOpen (diagonal ⁻¹' Set.Iio (1 / 4 : ℝ)) :=
    hdiagonal.isOpen_preimage _ isOpen_Iio
  rw [diagonal_preimage_Iio_quarter] at hopen
  exact not_isOpen_singleton 0 hopen

end SeparateContinuityCounterexample
