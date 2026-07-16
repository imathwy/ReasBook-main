import StacksProject_2024.stacks_project.Chap10.Definition_10_84_1

open scoped DirectSum

universe u v w

section Lemma_10_84_2

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace DirectSumDevissage

/-- The ordinal stages of a dévissage that have a successor stage still inside the dévissage. -/
abbrev successorIndex (D : DirectSumDevissage R M) : Type _ :=
  { α : Ordinal.{w} // α + 1 < D.length }

/-- The quotient attached to a successor step of a direct sum dévissage. -/
abbrev successiveQuotient (D : DirectSumDevissage R M) (α : D.successorIndex) : Type _ :=
  D.stages (α.1 + 1) ⧸ D.predecessorStage α.1

-- Proof sketch: choose complements from `D.stage_succ_isCompl`, identify each successor quotient
-- with its chosen complement using `Submodule.quotientEquivOfIsCompl`, then prove by transfinite
-- induction on `β < D.length` that the partial direct sum over stages below `β` maps isomorphically
-- onto `D.stages β`.
/-- Lemma 10.84.2: a direct sum dévissage yields an `R`-linear equivalence between `M` and the
direct sum of the successive quotients `M_(α + 1) / M_ α`. -/
theorem nonempty_linearEquiv_directSum_successiveQuotients
    (D : DirectSumDevissage R M) :
    Nonempty (M ≃ₗ[R] ⨁ α : D.successorIndex, D.successiveQuotient α) := sorry

end DirectSumDevissage

end Lemma_10_84_2
