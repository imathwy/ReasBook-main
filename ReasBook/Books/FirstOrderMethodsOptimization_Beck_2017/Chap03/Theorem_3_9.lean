import FirstOrderMethodsinOptimization.Chap03.Definition_3_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} {ι : Type v}
variable [AddCommMonoid E] [Module ℝ E]

/- Theorem 3.9 is a `source-facing` item in the chapter directional-derivative API. The owner
notions are `has_directional_derivative_at` and `directional_derivative` from Definition 3.8. The
active-index collection is auxiliary derived data, so this file keeps it inline in the theorem
statement instead of introducing a parallel public wrapper around the subtype
`{i | f i x = ⨆ j, f j x}`. -/
recall has_directional_derivative_at
recall directional_derivative

-- Proof sketch: for sufficiently small positive steps `t`, the indices that are not active at `x`
-- remain strictly below the active ones because each `f i` has a finite directional derivative at
-- `x` along `d`, hence is directionally continuous there. Thus the difference quotient of the
-- pointwise supremum agrees near `0⁺` with the supremum over the active subfamily, and the limit
-- of a finite supremum is the supremum of the individual directional-derivative limits.
/-- Theorem 3.9: for a finite family of extended-real-valued functions, if every directional
derivative at `x` along `d` exists as a finite real value, then the directional derivative of the
pointwise maximum is the maximum of the directional derivatives over the active indices
`I(x) = {i | fᵢ x = max_j fⱼ x}`. -/
theorem directional_derivative_iSup_eq_iSup_active_indices
    [Finite ι] [Nonempty ι]
    (f : ι → E → EReal) (x d : E)
    (hdir : ∀ i : ι, ∃ ℓ : ℝ, has_directional_derivative_at (f i) x d (ℓ : EReal)) :
    directional_derivative (fun y ↦ ⨆ i : ι, f i y) x d =
      iSup fun i : {i : ι // f i x = ⨆ j : ι, f j x} ↦ directional_derivative (f i) x d :=
  sorry

end
