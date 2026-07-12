import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section WhitneyApproximation

universe u v

variable {M : Type u}
variable {Y : Type v} [PseudoMetricSpace Y]

-- Semantic search note: `lean_leansearch` was unavailable in this environment, so the declaration
-- shape was chosen from the source statement and the local Whitney approximation precedent using
-- `dist` for pointwise control.
/-- Definition 6.41-extra-1: if `δ : M → ℝ` is a positive continuous function, then two maps
`F, G : M → Y` are `δ`-close when their pointwise distance is strictly smaller than `δ` at every
point of `M`. The positivity and continuity of `δ` are ambient assumptions rather than fields of
this predicate. -/
def delta_close (δ : M → ℝ) (F G : M → Y) : Prop :=
  ∀ x : M, dist (F x) (G x) < δ x

variable {E : Type v} [NormedAddCommGroup E]

/-- For normed additive-group targets, `delta_close` is the pointwise norm inequality. -/
theorem delta_close_iff {δ : M → ℝ} {F G : M → E} :
    delta_close δ F G ↔ ∀ x : M, ‖F x - G x‖ < δ x := by
  simp [delta_close, dist_eq_norm]

end WhitneyApproximation
