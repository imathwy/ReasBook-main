import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

noncomputable section

/-- The logarithmic `1`-form `z ↦ dz / (z - a)` on the punctured plane. -/
def indexForm (a : ℂ) : ℂ → ℂ →L[ℂ] ℂ :=
  fun z ↦ (1 : ℂ →L[ℂ] ℂ).smulRight ((z - a)⁻¹)

/-- Definition II.1-extra-16: the index of a closed path `γ` with respect to a point `a` of `ℂ`
outside the image of `γ` is the normalized contour integral
`(1 / (2 * π * i)) ∫_γ dz / (z - a)`. -/
def closedPathIndex {z : ℂ} (γ : Path z z) (a : {w : ℂ // w ∉ Set.range γ}) : ℂ :=
  (∫ᶜ w in γ, indexForm a.1 w) / (((2 * Real.pi : ℂ) * Complex.I))

/-- The index is the curve integral of the logarithmic form divided by `2 * π * i`. -/
@[simp]
theorem closedPathIndex_def {z : ℂ} (γ : Path z z) (a : {w : ℂ // w ∉ Set.range γ}) :
    closedPathIndex γ a = (∫ᶜ w in γ, indexForm a.1 w) / (((2 * Real.pi : ℂ) * Complex.I)) := rfl

-- Proof sketch: differentiate the identity `Complex.exp ∘ f = fun t ↦ γ t - a`, rewrite the
-- logarithmic derivative as `f'`, and integrate along the closed path to express the index by the
-- endpoint difference of the logarithm lift.
/-- If `γ(t) - a` admits a continuous logarithm `f` on `[0,1]`, then the index is the normalized
endpoint difference of that logarithm. -/
theorem closedPathIndex_eq_endpoint_log_lift_difference
    {z : ℂ} (γ : Path z z) (a : {w : ℂ // w ∉ Set.range γ}) (f : C(I, ℂ))
    (hf : ∀ t, Complex.exp (f t) = γ t - a.1) :
    closedPathIndex γ a = (f 1 - f 0) / (((2 * Real.pi : ℂ) * Complex.I)) := sorry

namespace Path

/-- The index of a closed path at a point `a` off its image. -/
abbrev closedPathIndexAt {z : ℂ} (γ : Path z z) (a : ℂ) (ha : a ∉ Set.range γ) : ℂ :=
  closedPathIndex γ ⟨a, ha⟩

@[simp]
theorem closedPathIndexAt_def {z : ℂ} (γ : Path z z) (a : ℂ) (ha : a ∉ Set.range γ) :
    γ.closedPathIndexAt a ha = closedPathIndex γ ⟨a, ha⟩ := rfl

/-- A closed complex loop has winding index `n` about `a` if `γ - a` admits a continuous
logarithm whose endpoint jump is `2πni`. -/
def HasIndexAt {z : ℂ} (γ : Path z z) (a : ℂ) (n : ℤ) : Prop :=
  ∃ w : C(I, ℂ), (∀ t : I, Complex.exp (w t) = γ t - a) ∧
    w 1 = w 0 + ((2 * Real.pi : ℂ) * (n : ℂ)) * Complex.I

-- Proof sketch: exponentials never vanish, so `exp (w t) = γ t - a` forces `γ t ≠ a`.
/-- A loop with a winding index about `a` avoids the center `a` pointwise. -/
theorem HasIndexAt.ne_center {z : ℂ} {γ : Path z z} {a : ℂ} {n : ℤ}
    (hγ : γ.HasIndexAt a n) (t : I) :
    γ t ≠ a := sorry

/-- A loop with winding index about `a` avoids `a` on its whole image. -/
theorem HasIndexAt.not_mem_range {z : ℂ} {γ : Path z z} {a : ℂ} {n : ℤ}
    (hγ : γ.HasIndexAt a n) :
    a ∉ Set.range γ := by
  rintro ⟨t, rfl⟩
  exact hγ.ne_center t rfl

-- Proof sketch: apply `closedPathIndex_eq_endpoint_log_lift_difference` to the defining logarithm
-- lift and simplify the endpoint jump by `2 * π * i`.
/-- A logarithmic lift with endpoint jump `2πni` computes the integral index as `n`. -/
theorem HasIndexAt.closedPathIndex_eq {z : ℂ} {γ : Path z z} {a : ℂ} {n : ℤ}
    (hγ : γ.HasIndexAt a n) :
    γ.closedPathIndexAt a hγ.not_mem_range = (n : ℂ) := sorry

end Path

-- Proof sketch: lift `γ - a` through the covering map `Complex.exp`, apply
-- `closedPathIndex_eq_endpoint_log_lift_difference`, and use `Complex.exp_eq_exp_iff_exists_int`
-- together with the closedness of `γ` to show that `f 1 - f 0` is an integral multiple of
-- `2 * π * i`.
/-- The index of a closed path about a point off its image is an integer. -/
theorem closedPathIndex_isInteger
    {z : ℂ} (γ : Path z z) (a : {w : ℂ // w ∉ Set.range γ}) :
    ∃ n : ℤ, closedPathIndex γ a = (n : ℂ) := sorry
