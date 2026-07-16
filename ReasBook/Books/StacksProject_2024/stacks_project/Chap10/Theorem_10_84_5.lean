import StacksProject_2024.stacks_project.Chap10.Theorem_10_84_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {P : Type v}
variable [Ring R] [AddCommGroup P] [Module R P] [Module.Projective R P]

/-- A submodule is countably generated projective if, as an `R`-module, it is both countably
generated and projective. -/
class Submodule.IsCountablyGeneratedProjective (A : Submodule R P) : Prop where
  countablyGenerated : Module.CountablyGenerated R A
  projective : Module.Projective R A

-- Proof sketch: realize `P` as a direct summand of a free `R`-module. Decompose the free module
-- as the internal direct sum of its rank-one free summands, which are countably generated and
-- projective, then apply the direct-summand result from Theorem `10.84.4` and observe that each
-- resulting summand remains projective.
/-- Theorem 10.84.5: if `P` is a projective `R`-module, then `P` is an internal direct sum of
countably generated projective `R`-submodules. -/
theorem projective_isDirectSumOfCountablyGeneratedProjective :
    ∃ (ι : Type w) (_ : DecidableEq ι) (A : ι → Submodule R P),
      DirectSum.IsInternal A ∧ ∀ i, Submodule.IsCountablyGeneratedProjective (A i) := sorry

end
