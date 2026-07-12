import Mathlib.Algebra.Colimit.Module
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open Module.DirectLimit

universe u v

noncomputable section

section

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I] [IsDirectedOrder I]
variable (M : I → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable (μ : ∀ i j, i ≤ j → M i →ₗ[R] M j)
variable [DirectedSystem M (μ · · ·)]

local instance directLimit_zero_decidableEqIndex : DecidableEq I := Classical.decEq I

/-- Lemma 10.8.4: an element of a stage of a directed system of modules maps to zero in the
direct limit if and only if it becomes zero in some later stage. -/
-- Proof sketch: the forward implication is the canonical exactness statement
-- `Module.DirectLimit.of.zero_exact`; the reverse implication uses compatibility of the structure
-- maps with the colimit map via `Module.DirectLimit.of_f`.
@[stacks 00D7]
theorem directLimit_stageMap_eq_zero_iff {i : I} {x : M i} :
    of R I M μ i x = 0 ↔ ∃ (j : I) (hij : i ≤ j), μ i j hij x = 0 := by
  constructor
  · -- The direct-limit exactness criterion gives the eventual vanishing stage.
    intro hx
    exact of.zero_exact hx
  · -- Rewrite the colimit class through the witness stage and then simplify using the zero witness.
    rintro ⟨j, hij, hxj⟩
    have hstage : of R I M μ j (μ i j hij x) = of R I M μ j 0 := by
      exact congrArg (of R I M μ j) hxj
    simpa [of_f] using hstage

end
