import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MvPolynomial

section FiniteField

variable (K : Type u) [Field K] [Fintype K]

/-- Remark 1.3.53: the infinitude hypothesis in Proposition 1.3.52 is essential. Over a finite
field `K`, the polynomial `X₀^|K| - X₀` is nonzero but evaluates to `0` at every point of `K`. -/
-- Proof sketch: `eval x (X₀^|K| - X₀) = x 0 ^ |K| - x 0 = 0` by `FiniteField.pow_card`, while
-- nonzeroness follows because the monomials `X₀^|K|` and `X₀` are distinct when `|K| > 1`.
theorem frobenius_difference_nonzero_and_eval_zero :
    (X (0 : Fin 1) ^ Fintype.card K - X 0 : MvPolynomial (Fin 1) K) ≠ 0 ∧
      ∀ x : Fin 1 → K,
        eval x (X (0 : Fin 1) ^ Fintype.card K - X 0 : MvPolynomial (Fin 1) K) = 0 := by
  refine ⟨?_, ?_⟩
  · refine sub_ne_zero.mpr ?_
    intro h
    have h' : (X (0 : Fin 1) ^ Fintype.card K : MvPolynomial (Fin 1) K) = X 0 ^ 1 := by
      simpa using h
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial] at h'
    have hs := MvPolynomial.monomial_left_injective one_ne_zero h'
    have hcard : Fintype.card K = 1 := by
      simpa using congrArg (fun s : Fin 1 →₀ ℕ ↦ s 0) hs
    exact Fintype.one_lt_card.ne' hcard
  · intro x
    simp [FiniteField.pow_card]

end FiniteField

section FiniteField

variable (K : Type u) [Field K] [Finite K]

/-- Over a finite field, evaluation does not embed `MvPolynomial (Fin 1) K` into the polynomial
functions `K → K`. This is the failure of the `MvPolynomial.funext_iff` phenomenon from
Proposition 1.3.52 in finite characteristic. -/
theorem eval_not_injective :
    ¬ Function.Injective (fun P : MvPolynomial (Fin 1) K ↦ fun x : Fin 1 → K ↦ eval x P) := by
  let _ : Fintype K := Fintype.ofFinite K
  intro h_injective
  rcases frobenius_difference_nonzero_and_eval_zero K with ⟨h_nonzero, h_zero⟩
  apply h_nonzero
  apply h_injective
  funext x
  simp [h_zero x]

end FiniteField
