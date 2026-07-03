import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_13_35 (from Chap13) -/
open scoped InnerProductSpace
open WithLp

universe u

namespace ERealFunction

noncomputable section

section Autoconjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Proof sketch: expand both sides with `conjugate_apply_pair`, rewrite the transpose by
-- `transpose_apply`, and reindex the supremum on the right by the coordinate swap `Prod.swap`.
/-- Proposition 13.35: on `H × H`, Fenchel conjugation commutes with transpose `ᵀ`. -/
theorem transpose_conjugate (F : H × H → EReal) :
    (F∗)ᵀ = (Fᵀ)∗ := by
  ext ⟨u, x⟩
  simp only [transpose_apply, conjugate_apply_pair]
  exact (Equiv.prodComm H H).iSup_congr fun p ↦ by
    rcases p with ⟨a, b⟩
    simp [add_comm]

end Autoconjugation

end

end ERealFunction
