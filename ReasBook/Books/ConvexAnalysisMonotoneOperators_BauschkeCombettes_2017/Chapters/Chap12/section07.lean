import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_12_7 (from Chap12) -/
namespace ERealFunction

/-- Example 12.7: for `f(ξ) = ξ` and `g = -f` on `ℝ`, the infimal convolution `f □ g` is
identically `-∞`, so the conclusion of Proposition 12.6(i) can fail without the common-minorant
hypothesis. -/
-- Proof sketch: for fixed `x`, the defining summand is
-- `y + (-(x - y)) = 2y - x`. Taking `y = -n` sends this quantity to `-∞`,
-- so the infimum over all `y` is `⊥` for every `x`.
theorem id_infimalConvolution_neg_id_eq_bot :
    id.toEReal □ (-id).toEReal = (⊥ : ℝ → EReal) := by
  ext x
  rw [infimalConvolution_apply]
  change (⨅ y : ℝ, (id.toEReal y : EReal) + (((-id).toEReal (x - y) : EReal))) = (⊥ : EReal)
  refine (EReal.eq_bot_iff_forall_lt _).2 ?_
  intro r
  let y : ℝ := (x + r - 1) / 2
  refine lt_of_le_of_lt (iInf_le _ y) ?_
  dsimp [y]
  exact_mod_cast (show ((x + r - 1) / 2) - (x - ((x + r - 1) / 2)) < r by linarith)

end ERealFunction
