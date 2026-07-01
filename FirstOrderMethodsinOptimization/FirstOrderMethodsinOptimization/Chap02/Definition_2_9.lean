import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Definition 2.9: the support function of a set `C ⊆ E` is the extended-real-valued function on
the dual space `E* = Module.Dual ℝ E` sending `y` to the supremum of the pairings `y x` for
`x ∈ C`. For nonempty `C`, this realizes the textbook codomain `(-∞, ∞]`. -/
noncomputable def support_function (C : Set E) : Module.Dual ℝ E → EReal :=
  fun y ↦ sSup ((fun x : E ↦ (y x : EReal)) '' C)

-- Proof sketch: unfold `support_function`; the statement is exactly the defining supremum formula
-- for the image of `C` under the pairing map `x ↦ y x`.
/-- Evaluating the support function at `y` gives the supremum of the dual pairings `y x` over
`x ∈ C`. -/
lemma support_function_apply (C : Set E) (y : Module.Dual ℝ E) :
    support_function C y = sSup ((fun x : E ↦ (y x : EReal)) '' C) :=
  rfl

-- Proof sketch: choose `x ∈ C`; then `(y x : EReal)` belongs to the image set whose supremum
-- defines `support_function C y`, so `⊥ < (y x : EReal) ≤ support_function C y`, ruling out
-- the value `⊥`.
/-- For a nonempty set `C`, the support function never takes the value `-∞`. -/
theorem support_function_ne_bot (C : Set E) (hC : C.Nonempty) (y : Module.Dual ℝ E) :
    support_function C y ≠ ⊥ := sorry

-- Proof sketch: unfold `support_function`; the hypothesis says that the defining image set has
-- greatest element `a`, so its supremum is exactly `a`.
/-- If the pairing image `y '' C` has greatest element `a`, then the support function of `C` at
`y` is exactly `a`. -/
theorem support_function_eq_of_isGreatest_image (C : Set E) (y : Module.Dual ℝ E) {a : EReal}
    (hmax : IsGreatest ((fun x : E ↦ (y x : EReal)) '' C) a) :
    support_function C y = a := by
  rw [support_function_apply]
  exact hmax.csSup_eq

end
