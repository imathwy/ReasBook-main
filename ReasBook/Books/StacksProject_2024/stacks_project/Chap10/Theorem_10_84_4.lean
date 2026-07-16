import StacksProject_2024.stacks_project.Chap10.Definition_10_84_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [Ring R]
variable {M P : Type v}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup P] [Module R P]

namespace Module

-- Proof sketch: run the Kaplansky transfinite dévissage on `M` and transport each stage across the
-- split injection `i : P →ₗ[R] M` and retraction `s : M →ₗ[R] P`; the splitting identity
-- `s.comp i = LinearMap.id` makes the induced stages on `P` compatible with the successor
-- complements, so they again form an internal direct-sum decomposition by countably generated
-- submodules.
/-- Theorem 10.84.4: if `M` is an internal direct sum of countably generated `R`-submodules and
`P` is a direct summand of `M`, exhibited by `R`-linear maps `i : P →ₗ[R] M` and
`s : M →ₗ[R] P` with `s.comp i = LinearMap.id`, then `P` is also an internal direct sum of
countably generated `R`-submodules. -/
theorem directSummand_isDirectSumOfCountablyGenerated
    (i : P →ₗ[R] M) (s : M →ₗ[R] P) (hs : s.comp i = LinearMap.id)
    (hM : IsDirectSumOfCountablyGenerated R M) :
    IsDirectSumOfCountablyGenerated R P := sorry

-- Proof sketch: apply Theorem `10.84.4` to the linear equivalence `e`, viewed as split inclusion
-- and retraction data.
/-- A linear equivalence preserves the property of being an internal direct sum of countably
generated submodules. -/
theorem isDirectSumOfCountablyGenerated_of_linearEquiv
    (e : P ≃ₗ[R] M) (hM : IsDirectSumOfCountablyGenerated R M) :
    IsDirectSumOfCountablyGenerated R P := by
  simpa using
    (directSummand_isDirectSumOfCountablyGenerated e.toLinearMap e.symm.toLinearMap
      (by
        ext x
        simp) hM)

-- Proof sketch: a complemented submodule `P ≤ M` carries canonical split inclusion/projection
-- data, so this is the bridge/view specialization of Theorem `10.84.4` to the concrete submodule
-- presentation of a direct summand.
/-- Bridge form of Theorem 10.84.4 for a complemented submodule realization of a direct summand. -/
theorem isDirectSumOfCountablyGenerated_of_isComplemented
    (P : Submodule R M) (hP : IsComplemented P)
    (hM : IsDirectSumOfCountablyGenerated R M) :
    IsDirectSumOfCountablyGenerated R P := by
  rcases hP with ⟨Q, hQ⟩
  simpa using
    (directSummand_isDirectSumOfCountablyGenerated P.subtype
      (P.linearProjOfIsCompl Q hQ) (P.linearProjOfIsCompl_comp_subtype hQ) hM)

end Module

end
