import Mathlib
import LinearRepresentations_Serre_1977.Chap06.Remark_6_6_4_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Algebra

section

variable {R : Type u} [Ring R]

-- Source/core/bridge triage:
-- * source-facing: Proposition 6-6.4-1, specialized to the base ring `ℤ`.
-- * core/canonical owner: the simple adjoin `ℤ[x]`, with mathlib owner theorem
--   `Algebra.finite_adjoin_simple_of_isIntegral`.
-- * bridge/view: `isIntegral_tfae_finite_adjoin_simple`, which packages the textbook three-way
--   equivalence without introducing a parallel local owner.
/- Proposition 6-6.4-1: for `x` in a ring, the following are equivalent: `x` is integral over
`ℤ`; the simple subring `ℤ[x]` is finitely generated as a `ℤ`-module; and `ℤ[x]` is contained in
a finitely generated `ℤ`-submodule of the ambient ring. In the current API, this is the
integer-base specialization of the general theorem
`isIntegral_tfae_finite_adjoin_simple`. -/
#check
  (isIntegral_tfae_finite_adjoin_simple ℤ :
    ∀ x : R,
      [IsIntegral ℤ x,
        Module.Finite ℤ ℤ[x],
        ∃ M : Submodule ℤ R,
          Module.Finite ℤ M ∧ ℤ[x].toSubmodule ≤ M].TFAE)

end
