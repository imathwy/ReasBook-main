import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_20_22 (from Chap20) -/
open scoped Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: swap the coordinates of the graph. This transports monotonicity to `A⁻¹`,
-- and graph inclusion between monotone extensions is preserved by taking inverses, so maximality
-- transfers as well.
/-- Proposition 20.22 (1): the inverse of a maximally monotone set-valued operator is maximally
monotone. -/
theorem Maximal.inverse {A : SetValuedOperator H H}
    (hA : Maximal IsMonotone A) :
    Maximal IsMonotone A⁻¹ := sorry

-- Proof sketch: view `x ↦ {u} + γ • A (x + z)` as the image of `A.graph` under the affine
-- automorphism `(x, a) ↦ (x - z, u + γ • a)` of `H × H`. Positive scaling and translations
-- preserve monotonicity, and the bijective transport of graph inclusion preserves maximality.
/-- Proposition 20.22 (2): for `z, u : H` and `γ ∈ ℝ_{++}`, the affine perturbation
`x ↦ {u} + γ • A (x + z)` of a maximally monotone operator is maximally monotone. -/
theorem Maximal.output_translation_smul_input_translation
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    (z u : H) (γ : Set.Ioi (0 : ℝ)) :
    Maximal IsMonotone (((fun _ : H ↦ u).toSetValuedOperator) + (γ : ℝ) • A.translate (-z)) :=
  sorry

end SetValuedOperator
