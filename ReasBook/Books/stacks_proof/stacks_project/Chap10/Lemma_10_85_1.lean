import StacksProject_2024.Chap10.Theorem_10_84_5
import Mathlib.Tactic.StacksAttribute

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
@[stacks 0590]
theorem allProjectiveModulesFree_iff_allCountablyGeneratedProjectiveModulesFree :
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.Projective R P],
      Module.Free R P) ↔
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.Projective R P],
      Module.CountablyGenerated R P → Module.Free R P) := by
  constructor
  · intro h P _ _ _ _
    -- The forward implication is immediate: a stronger freeness statement already covers the
    -- countably generated projective case.
    exact h P
  · intro h P _ _ _
    classical
    -- Decompose the projective module into countably generated projective summands using
    -- Theorem 10.84.5.
    rcases (projective_isDirectSumOfCountablyGeneratedProjective.{u, v, max u v}
        (R := R) (P := P)) with ⟨ι, _, A, hA, hcountproj⟩
    have hfreeA : ∀ i, Module.Free R (A i) := by
      intro i
      -- Each summand is free by the converse hypothesis, since Theorem 10.84.5 packages both
      -- projectivity and countable generation for that summand.
      letI : Module.Projective R (A i) := (hcountproj i).projective
      exact h (A i) (hcountproj i).countablyGenerated
    letI : ∀ i, Module.Free R (A i) := hfreeA
    -- Collect bases from the free summands along the internal direct-sum decomposition to obtain
    -- a basis of the whole module.
    exact Module.Free.of_basis <|
      hA.collectedBasis fun i ↦ Module.Free.chooseBasis R (A i)

end
