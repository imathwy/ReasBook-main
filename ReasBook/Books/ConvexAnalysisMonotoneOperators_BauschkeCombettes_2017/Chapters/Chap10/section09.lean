import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_10_9 (from Chap10) -/
universe u

section Normed

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/- Example 10.9 (1): the norm function is sublinear; this is exactly the earlier
`norm_sublinear` from Example 10.4. -/
recall norm_sublinear

end Normed

section NontrivialNormed

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [Nontrivial H]

/- Recall: on a nontrivial real normed space, the norm function is not strictly convex on the
whole space. -/
recall norm_not_strictConvexOn_univ

-- Proof sketch: if the norm admitted a modulus positive away from `0` making it uniformly convex
-- on `Set.univ`, then `UniformConvexOn.strictConvexOn` would imply strict convexity, contradicting
-- `norm_not_strictConvexOn_univ`.
/-- Example 10.9 (2): the norm function is not uniformly convex on the whole space. -/
theorem norm_not_uniformlyConvexOn_univ :
    ¬ ∃ φ : ℝ → ℝ,
      (∀ ⦃r : ℝ⦄, r ≠ 0 → 0 < φ r) ∧ UniformConvexOn (Set.univ : Set H) φ (norm : H → ℝ) := by
  intro h
  rcases h with ⟨φ, hφ, hunif⟩
  exact norm_not_strictConvexOn_univ <| hunif.strictConvexOn fun {r} hr ↦ hφ hr

end NontrivialNormed

section Hilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: mathlib's owner theorem `strongConvexOn_iff_convex` with `β = 2` rewrites strong
-- convexity of `x ↦ ‖x‖^2` on `Set.univ` as convexity of `x ↦ ‖x‖^2 - ‖x‖^2`, namely the
-- constant zero function.
/-- Example 10.9 (3): the squared norm is strongly convex on the whole space with constant `2`. -/
theorem norm_sq_strongConvexOn_univ :
    StrongConvexOn (Set.univ : Set H) (2 : ℝ) (fun x : H ↦ ‖x‖ ^ 2) := by
  rw [strongConvexOn_iff_convex]
  simpa using (convexOn_const 0 convex_univ : ConvexOn ℝ (Set.univ : Set H) (fun _ : H ↦ (0 : ℝ)))

end Hilbert

section NontrivialNormed

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [Nontrivial H]

/- Example 10.9 (4): the squared norm is not positively homogeneous; this is exactly the earlier
`norm_sq_not_positivelyHomogeneous` from Example 10.4. -/
recall norm_sq_not_positivelyHomogeneous

end NontrivialNormed
