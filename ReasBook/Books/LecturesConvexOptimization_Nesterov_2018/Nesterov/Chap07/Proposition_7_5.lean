import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix

variable {p n : ℕ}

local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ

/- Proposition 7.5 lies in the chapter's Frobenius-Gram / dense arithmetic-cost domain.

Sampled owner-style declarations:
- `Matrix.gram` in mathlib, the canonical Frobenius Gram-matrix owner for a family of
  coefficient matrices;
- `matrix_gram_apply_eq_entrywise_sum` in `Chap07/Definition_7_21`, the Chapter 7 bridge from
  that owner to the textbook Frobenius double sum;
- `linearMatrixGramOperator_toMatrixOrthonormal` in `Chap07/Definition_7_21`, the bridge from the
  source-facing operator `G = L†L` to its Gram matrix;
- `gramMatrix` in `Chap07/Proposition_7_24`, another use of the same canonical Gram owner.

Best owner abstraction:
- source-facing: the preliminary arithmetic-work bound for forming the Frobenius Gram matrix and
  inverting it;
- core/canonical: `Matrix.gram ℝ` on matrix-entry coordinates;
- bridge/view: `matrix_gram_apply_eq_entrywise_sum`.

Primitive data:
- `n`, `p : ℕ`.

Derived API:
- the canonical Frobenius Gram owner `Matrix.gram ℝ`;
- the parameter-only arithmetic-work expression
  `frobeniusGramPreliminaryArithmeticWorkBound n p`;
- its explicit expansion and regime-specific quadratic bound.

Source/core/bridge triage:
- source-facing: the arithmetic complexity statement of Proposition 7.5;
- core/canonical: `Matrix.gram ℝ`;
- bridge/view: the entrywise identity `matrix_gram_apply_eq_entrywise_sum`.

The previous file kept local raw-matrix inner-product scaffolding just to mention the Gram owner.
This refinement deletes that scaffolding and reuses the Chapter 7 Frobenius Gram owner directly,
leaving this file to own only the new arithmetic-work model and its asymptotic consequence.
-/

section

variable (p n)

/- Proposition 7.5 uses the canonical Frobenius Gram-matrix owner. -/
set_option linter.hashCommand false in
#check (Matrix.gram ℝ : (Fin p → Mₙ) → Matrix (Fin p) (Fin p) ℝ)

end

/-- A dimension-only arithmetic upper bound for the preliminary computation that first forms the
Frobenius Gram matrix of a family of coefficient matrices and then computes its inverse. -/
def frobeniusGramPreliminaryArithmeticWorkBound (n p : ℕ) : ℕ :=
  p ^ 2 * n ^ 2 + p ^ 3

/-- Expanding `frobeniusGramPreliminaryArithmeticWorkBound n p` recovers the sum of the
Gram-matrix formation cost `p^2 n^2` and the matrix-inversion cost `p^3`. -/
-- Proof sketch: unfold `frobeniusGramPreliminaryArithmeticWorkBound`.
theorem frobeniusGramPreliminaryArithmeticWorkBound_eq
    (n p : ℕ) :
    frobeniusGramPreliminaryArithmeticWorkBound n p = p ^ 2 * n ^ 2 + p ^ 3 :=
  sorry

-- Proof sketch: use `hpn` to deduce `p < n^2`, hence `p^3 ≤ p^2 n^2`, and then absorb the
-- inversion term into the explicit preliminary-work expression
-- `p^2 n^2 + p^3`.
/-- The preliminary arithmetic-work model is bounded by `2 p^2 n^2` on the admissible regime
`p < n (n + 1) / 2`. -/
theorem frobeniusGramPreliminaryArithmeticWorkBound_le_two_mul
    {n p : ℕ} (hpn : p < n * (n + 1) / 2) :
    frobeniusGramPreliminaryArithmeticWorkBound n p ≤ 2 * (p ^ 2 * n ^ 2) := sorry

-- Proof sketch: take the constant witness `C = 2` and apply the explicit upper bound above.
/-- Proposition 7.5 [Chapter7_2.json:38]: if `A₁, …, Aₚ ∈ ℝ^(n × n)` and `G` is the Frobenius
Gram matrix with entries `G^(i,j) = ⟪Aᵢ, Aⱼ⟫_F`, then under the size condition
`p < n(n + 1) / 2` the preliminary computation modeled by
`frobeniusGramPreliminaryArithmeticWorkBound n p` has total arithmetic work bounded by a constant
multiple of `p^2 n^2`, i.e. of order `O(p^2 n^2)`. -/
theorem frobeniusGramPreliminaryArithmeticWork_has_quadratic_bound
    {n p : ℕ} (hpn : p < n * (n + 1) / 2) :
    ∃ C : ℕ,
      frobeniusGramPreliminaryArithmeticWorkBound n p ≤ C * (p ^ 2 * n ^ 2) := sorry

end
