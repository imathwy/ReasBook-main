import Topology_Munkres_2000.Book.Definition_49_1.Secant
import Mathlib.Algebra.Order.Archimedean.Real.Basic

open Set
open scoped UnitIntervalSecant

namespace UnitIntervalSecant

/-- Definition 49.2. The infimum, over the closed unit interval, of the secant
magnitudes at scale `h`. -/
noncomputable def infMagnitude (f : Icc (0 : ℝ) 1 → ℝ) (h : ℝ) : ℝ :=
  sInf (Set.range (fun x ↦ Δ f (x, h)))

/-- The source notation `Δ_{h} f` for the infimum secant magnitude of `f` at
scale `h`. -/
scoped notation:arg "Δ_{" h "}" f:arg => infMagnitude f h

/-- Helper for Definition 49.2: at a positive displacement at most `1 / 2`,
every secant magnitude is nonnegative. -/
theorem maxMagnitude_nonneg (f : Icc (0 : ℝ) 1 → ℝ)
    (x : Icc (0 : ℝ) 1) (h : ℝ) (hpos : 0 < h) (hle : h ≤ 1 / 2) :
    0 ≤ Δ f (x, h) := by
  -- Route correction: the source hypotheses guarantee an available endpoint,
  -- so the public endpoint formulas avoid unfolding the private branch data.
  have hendpoint := exists_endpoint x hpos hle
  by_cases hplus : x + h ∈ Icc (0 : ℝ) 1
  · by_cases hminus : x - h ∈ Icc (0 : ℝ) 1
    · rw [maxMagnitude_eq_max f x h hplus hminus]
      exact le_trans (abs_nonneg _) (le_max_left _ _)
    · rw [maxMagnitude_eq_right f x h hplus hminus]
      exact abs_nonneg _
  · have hminus : x - h ∈ Icc (0 : ℝ) 1 := hendpoint.resolve_left hplus
    rw [maxMagnitude_eq_left f x h hminus hplus]
    exact abs_nonneg _

/-- Helper for Definition 49.2: the range of the secant-magnitude function is
bounded below at a positive displacement at most `1 / 2`. -/
theorem secantMagnitudeRange_bddBelow (f : Icc (0 : ℝ) 1 → ℝ) (h : ℝ)
    (hpos : 0 < h) (hle : h ≤ 1 / 2) :
    BddBelow (Set.range (fun x ↦ Δ f (x, h))) := by
  -- Zero is a lower bound because every pointwise magnitude is nonnegative.
  refine ⟨0, ?_⟩
  intro z hz
  obtain ⟨x, rfl⟩ := hz
  exact maxMagnitude_nonneg f x h hpos hle

/-- The infimum of the secant magnitudes is at most every pointwise secant
magnitude at a positive displacement at most `1 / 2`. -/
theorem infMagnitude_le (f : Icc (0 : ℝ) 1 → ℝ) (h : ℝ)
    (hpos : 0 < h) (hle : h ≤ 1 / 2) (x : Icc (0 : ℝ) 1) :
    Δ_{h} f ≤ Δ f (x, h) := by
  -- Unfold the infimum once, then use membership of the chosen range value.
  unfold infMagnitude
  exact csInf_le (secantMagnitudeRange_bddBelow f h hpos hle) (Set.mem_range_self x)

/-- A real number bounds the infimum of the secant magnitudes from below
exactly when it bounds every pointwise secant magnitude from below, for a
positive displacement at most `1 / 2`. -/
theorem le_infMagnitude_iff (f : Icc (0 : ℝ) 1 → ℝ) (h : ℝ)
    (hpos : 0 < h) (hle : h ≤ 1 / 2) {α : ℝ} :
    α ≤ Δ_{h} f ↔ ∀ x, α ≤ Δ f (x, h) := by
  -- Translate the universal property of `sInf` from range membership to points.
  unfold infMagnitude
  rw [le_csInf_iff (secantMagnitudeRange_bddBelow f h hpos hle) (Set.range_nonempty _)]
  constructor
  · intro hall x
    exact hall (Δ f (x, h)) (Set.mem_range_self x)
  · intro hall z hz
    obtain ⟨x, rfl⟩ := hz
    exact hall x

/-- The infimum of the secant magnitudes is nonnegative at a positive
displacement at most `1 / 2`. -/
theorem infMagnitude_nonneg (f : Icc (0 : ℝ) 1 → ℝ) (h : ℝ)
    (hpos : 0 < h) (hle : h ≤ 1 / 2) :
    0 ≤ Δ_{h} f := by
  -- Apply the infimum universal property to pointwise nonnegativity.
  rw [le_infMagnitude_iff f h hpos hle]
  intro x
  exact maxMagnitude_nonneg f x h hpos hle

end UnitIntervalSecant

open scoped UnitIntervalSecant

/-
Definition 49.2. Given `0 < h` with `h ≤ 1 / 2`,
`Δ_{h} f` is the infimum of
`Δ f (x, h)` over `x ∈ Set.Icc (0 : ℝ) 1`.
-/
#check fun (f : Set.Icc (0 : ℝ) 1 → ℝ) (h : ℝ) ↦ Δ_{h} f
