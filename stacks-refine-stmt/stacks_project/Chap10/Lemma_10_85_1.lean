import stacks_project.Chap10.Theorem_10_84_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [Ring R]

/- Domain triage:
* primary domain: projective modules and countable generation;
* sampled owner declarations:
  `Module.CountablyGenerated`,
  `Theorem_10_84_5.projective_isDirectSumOfCountablyGeneratedProjective`,
  and the direct-sum free-module instance `Module.Free.dfinsupp`;
* owner abstraction: `Module.Projective R P` with the derived predicate
  `Module.CountablyGenerated R P`;
* layer: `source-facing`, since the lemma states a chapter-level reduction criterion for when all
  projective modules are free. -/

-- Proof sketch: the forward implication is immediate. For the converse, apply Theorem `10.84.5`
-- to write any projective `R`-module as an internal direct sum of countably generated projective
-- submodules; by hypothesis each summand is free, and an internal direct sum of free modules is
-- free.
/-- Lemma 10.85.1: every projective `R`-module is free if and only if every countably generated
projective `R`-module is free. -/
theorem allProjectiveModulesFree_iff_allCountablyGeneratedProjectiveModulesFree :
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.Projective R P],
      Module.Free R P) ↔
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.Projective R P],
      Module.CountablyGenerated R P → Module.Free R P) := sorry

end
