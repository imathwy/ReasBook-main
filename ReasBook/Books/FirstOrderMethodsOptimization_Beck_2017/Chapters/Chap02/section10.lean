

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_10 (from Chap02) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

-- Proof sketch: unfold `support_function` and identify the `sSup` of the
-- finite image set `(fun b ↦ (y b : EReal)) '' (s : Set E)` with the nonempty finset supremum
-- `s.sup' hs (fun b ↦ (y b : EReal))` via `Finset.sup'_eq_csSup_image`.
/-- Definition 2.10: if `C` is represented by a nonempty finite set `s`, then the support
function of `C` at `y` is the maximum of the finitely many values `y b` for `b ∈ s`. -/
theorem support_function_finset_eq_sup' (s : Finset E) (hs : s.Nonempty) (y : Module.Dual ℝ E) :
    support_function (s : Set E) y = s.sup' hs (fun b ↦ (y b : EReal)) := by
  rw [support_function_apply, ← Finset.sup'_eq_csSup_image s hs]

end

/-! ### Example_2_10 (from Chap02) -/
open Matrix

noncomputable section

section

/- Example 2.10 is bridge-only: the intrinsic statement is the chapter owner theorem
`support_function_unit_simplex_eq_coordinate_max`, which already identifies the support function
of the unit simplex with the coordinate supremum `⨆ i, (y i : EReal)`. -/
recall support_function_unit_simplex_eq_coordinate_max

variable {n : ℕ} [Nonempty (Fin n)] (y : Fin n → ℝ)

/- For a nonempty finite index type, the coordinate supremum from the owner theorem is the finite
maximum over `Finset.univ`. -/
theorem support_function_unit_simplex_eq_coordinate_sup' :
    support_function (stdSimplex ℝ (Fin n)) (dotProductEquiv ℝ (Fin n) y) =
      Finset.univ.sup' Finset.univ_nonempty (fun i ↦ (y i : EReal)) := by
  simpa [Finset.sup'_univ_eq_ciSup] using support_function_unit_simplex_eq_coordinate_max y

end

/-! ### Theorem_2_10 (from Chap02) -/
-- Proof sketch: the convexity hypothesis makes the effective domain an interval in `ℝ`, hence its
-- interior is again an interval where the finite-valued restriction of `f` is a real-valued convex
-- function and therefore continuous. At an endpoint of the effective domain, use the one-sided
-- monotonicity of secant slopes for convex functions to show that the one-sided limit exists, then
-- combine this with lower semicontinuity to identify that limit with the endpoint value.
/-- Theorem 2.10: a proper closed and convex extended-real-valued function on `ℝ` is continuous on
its effective domain. Here closedness is expressed by `LowerSemicontinuous`, convexity by the
chapter owner predicate `is_convex_function`, and the codomain restriction `(-∞, ∞]` by the
assumption that `f` never takes the value `⊥`. -/
theorem continuousOn_effective_domain_of_lowerSemicontinuous_convex_univariate
    {f : ℝ → EReal} (h_ne_bot : ∀ x, f x ≠ ⊥) (h_closed : LowerSemicontinuous f)
    (h_convex : is_convex_function f) :
    ContinuousOn f (effective_domain f) := sorry
