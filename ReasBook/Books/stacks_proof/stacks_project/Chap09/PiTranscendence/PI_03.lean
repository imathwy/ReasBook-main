import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall tool `lean_leansearch` was unavailable in this environment, so this file uses
-- the direct finite-product statement matching the source text.

/-- Chap09 PiTranscendence/PI 03: if one factor in the finite product
`∏ i, (1 + Complex.exp (a i))` is zero because `Complex.exp (a i₀) = -1`,
then the whole product is zero. -/
theorem prod_one_add_exp_eq_zero_of_exists_exp_eq_neg_one {n : ℕ} (a : Fin n → ℂ)
    (h : ∃ i₀ : Fin n, Complex.exp (a i₀) = -1) :
    ∏ i, (1 + Complex.exp (a i)) = 0 := by
  -- Choose the index whose factor is forced to vanish.
  obtain ⟨i₀, hi₀⟩ := h
  -- A product over `Finset.univ` is zero once the chosen factor is zero.
  refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
  -- The chosen factor is `1 + (-1)`, so it vanishes in `ℂ`.
  rw [hi₀]
  ring
