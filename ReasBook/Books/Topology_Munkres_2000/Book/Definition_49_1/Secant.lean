import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

open Set

namespace UnitIntervalSecant

/-- The magnitude of the secant slope from `x` to `x + h`, or `0` when the
right endpoint does not lie in the closed unit interval. -/
private noncomputable def rightMagnitude (f : Icc (0 : ℝ) 1 → ℝ)
    (x : Icc (0 : ℝ) 1) (h : ℝ) : ℝ :=
  if hplus : x + h ∈ Icc (0 : ℝ) 1 then
    |(f ⟨x + h, hplus⟩ - f x) / h|
  else
    0

/-- The magnitude of the secant slope from `x` to `x - h`, or `0` when the
left endpoint does not lie in the closed unit interval. -/
private noncomputable def leftMagnitude (f : Icc (0 : ℝ) 1 → ℝ)
    (x : Icc (0 : ℝ) 1) (h : ℝ) : ℝ :=
  if hminus : x - h ∈ Icc (0 : ℝ) 1 then
    |(f ⟨x - h, hminus⟩ - f x) / (-h)|
  else
    0

/-- The magnitude of the larger available secant slope at `x` with
displacement `h`; an unavailable direction contributes `0`. -/
noncomputable def maxMagnitude (f : Icc (0 : ℝ) 1 → ℝ)
    (x : Icc (0 : ℝ) 1) (h : ℝ) : ℝ :=
  max (rightMagnitude f x h) (leftMagnitude f x h)

/-- The source notation `Δ f (x, h)` for the larger available secant-slope
magnitude of `f` at `x` and displacement `h`. -/
scoped notation:arg "Δ" f:arg " (" x ", " h ")" => maxMagnitude f x h

/-- When both secant endpoints are available, `Δ f (x, h)` is the maximum of
the two displayed secant-slope magnitudes. -/
theorem maxMagnitude_eq_max (f : Icc (0 : ℝ) 1 → ℝ)
    (x : Icc (0 : ℝ) 1) (h : ℝ) (hplus : x + h ∈ Icc (0 : ℝ) 1)
    (hminus : x - h ∈ Icc (0 : ℝ) 1) :
    Δ f (x, h) =
      max |(f ⟨x + h, hplus⟩ - f x) / h|
        |(f ⟨x - h, hminus⟩ - f x) / (-h)| := by
  -- Select both available endpoint branches in the defining maximum.
  simp only [maxMagnitude, rightMagnitude, leftMagnitude, dif_pos hplus, dif_pos hminus]

/-- When only the right secant endpoint is available, `Δ f (x, h)` is its
secant-slope magnitude. -/
theorem maxMagnitude_eq_right (f : Icc (0 : ℝ) 1 → ℝ)
    (x : Icc (0 : ℝ) 1) (h : ℝ) (hplus : x + h ∈ Icc (0 : ℝ) 1)
    (hminus : x - h ∉ Icc (0 : ℝ) 1) :
    Δ f (x, h) = |(f ⟨x + h, hplus⟩ - f x) / h| := by
  -- The unavailable left direction contributes zero, below an absolute value.
  simp only [maxMagnitude, rightMagnitude, leftMagnitude, dif_pos hplus, dif_neg hminus,
    max_eq_left, abs_nonneg]

/-- When only the left secant endpoint is available, `Δ f (x, h)` is its
secant-slope magnitude. -/
theorem maxMagnitude_eq_left (f : Icc (0 : ℝ) 1 → ℝ)
    (x : Icc (0 : ℝ) 1) (h : ℝ) (hminus : x - h ∈ Icc (0 : ℝ) 1)
    (hplus : x + h ∉ Icc (0 : ℝ) 1) :
    Δ f (x, h) = |(f ⟨x - h, hminus⟩ - f x) / (-h)| := by
  -- The unavailable right direction contributes zero, below an absolute value.
  simp only [maxMagnitude, rightMagnitude, leftMagnitude, dif_neg hplus, dif_pos hminus,
    max_eq_right, abs_nonneg]

/-- At a positive displacement at most `1 / 2`, every point of the closed unit
interval has at least one available secant endpoint. -/
theorem exists_endpoint (x : Icc (0 : ℝ) 1) {h : ℝ} (hpos : 0 < h)
    (hle : h ≤ 1 / 2) :
    x + h ∈ Icc (0 : ℝ) 1 ∨ x - h ∈ Icc (0 : ℝ) 1 := by
  -- Choose the direction pointing from the nearer half of the interval inward.
  rcases x.property with ⟨hxzero, hxone⟩
  by_cases hxmid : (x : ℝ) ≤ 1 / 2
  · left
    constructor
    · linarith
    · linarith
  · right
    constructor
    · linarith
    · linarith

/-- A lower bound for `Δ f (x, h)` is equivalent to the existence of an available
left or right secant whose slope magnitude has that lower bound. -/
theorem le_maxMagnitude_iff (f : Icc (0 : ℝ) 1 → ℝ) {α : ℝ} (hα : 0 < α)
    (x : Icc (0 : ℝ) 1) (h : ℝ) :
    α ≤ Δ f (x, h) ↔
      (∃ y : Icc (0 : ℝ) 1, y = x + h ∧ α ≤ |(f y - f x) / h|) ∨
      ∃ y : Icc (0 : ℝ) 1, y = x - h ∧ α ≤ |(f y - f x) / (-h)| := by
  -- Split a lower bound on the maximum into the right and left directions.
  rw [maxMagnitude, le_max_iff]
  constructor
  · intro hbound
    rcases hbound with hright | hleft
    · by_cases hplus : x + h ∈ Icc (0 : ℝ) 1
      · left
        refine ⟨⟨x + h, hplus⟩, rfl, ?_⟩
        simpa only [rightMagnitude, dif_pos hplus] using hright
      · have hnonpos : α ≤ 0 := by
          simpa only [rightMagnitude, dif_neg hplus] using hright
        linarith
    · by_cases hminus : x - h ∈ Icc (0 : ℝ) 1
      · right
        refine ⟨⟨x - h, hminus⟩, rfl, ?_⟩
        simpa only [leftMagnitude, dif_pos hminus] using hleft
      · have hnonpos : α ≤ 0 := by
          simpa only [leftMagnitude, dif_neg hminus] using hleft
        linarith
  · intro hwitness
    rcases hwitness with ⟨y, hy, hybound⟩ | ⟨y, hy, hybound⟩
    · left
      have hplus : x + h ∈ Icc (0 : ℝ) 1 := by
        simpa only [← hy] using y.property
      have hycanonical : y = (⟨x + h, hplus⟩ : Icc (0 : ℝ) 1) := by
        apply Subtype.ext
        exact hy
      simpa only [rightMagnitude, dif_pos hplus, hycanonical] using hybound
    · right
      have hminus : x - h ∈ Icc (0 : ℝ) 1 := by
        simpa only [← hy] using y.property
      have hycanonical : y = (⟨x - h, hminus⟩ : Icc (0 : ℝ) 1) := by
        apply Subtype.ext
        exact hy
      simpa only [leftMagnitude, dif_pos hminus, hycanonical] using hybound

end UnitIntervalSecant
