import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain-style sampling for this file:
-- * primary domain: permutation-group orbits for orbital fixing in a symmetric binary MILP
-- * sampled owner abstractions:
--   - mathlib's canonical orbit owner `MulAction.orbit`
--   - mathlib's canonical transitivity consequence `MulAction.orbit_eq_univ`
--   - mathlib's characterization theorem `MulAction.isPretransitive_iff_orbit_eq_univ`
--   - Chapter 9.5 Exercise 9.21's recall-only pattern for permutation-action facts already owned
--     upstream
-- * source/core/bridge triage:
--   - Example 9.14 is a `bridge/view` use of the canonical permutation-action owner
--   - `MulAction.orbit` is the `core/canonical` owner
--   - the source-facing membership consequence is used by orbital fixing
-- * primitive data: the index type `Fin n`, a chosen variable index `i`, and the full symmetric
--   group action
-- * derived API: the full-orbit fact `orbit_eq_univ` and its point-membership consequence

open MulAction

section Example_9_14

variable (n : ℕ) (i : Fin n)

/- Example 9.14 is the permutation-action specialization of the canonical theorem
`MulAction.orbit_eq_univ`: the full symmetric group on `Fin n` acts pretransitively, so every
orbit is all of `Fin n`. -/
recall MulAction.orbit_eq_univ
#check (orbit (Equiv.Perm (Fin n)) i : Set (Fin n))
#synth MulAction.IsPretransitive (Equiv.Perm (Fin n)) (Fin n)

/-- Example 9.14. Under the full symmetric-group action, the orbit of any variable index is all
of `Fin n`. -/
theorem example_9_14_orbit_eq_univ (i : Fin n) :
    orbit (Equiv.Perm (Fin n)) i = Set.univ :=
  MulAction.orbit_eq_univ (Equiv.Perm (Fin n)) i

/-- Example 9.14. Any two variable indices lie in the same permutation orbit under the full
symmetric-group action. -/
theorem example_9_14_mem_orbit (i j : Fin n) :
    j ∈ orbit (Equiv.Perm (Fin n)) i := by
  simp [example_9_14_orbit_eq_univ]

end Example_9_14
