import FirstOrderMethodsinOptimization.Chap02.Definition_2_9

-- Declarations for this item will be appended below by the statement pipeline.

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
