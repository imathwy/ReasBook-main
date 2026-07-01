import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

section

variable (F : Type u) [Field F]

/- Domain triage:
- primary domain: algebraically closed fields, expressed through polynomial factorization and root
  existence criteria;
- sampled owner declarations: `IsAlgClosed`, `IsAlgClosed.exists_root`,
  `IsAlgClosed.of_exists_root`, and `IsAlgClosed.degree_eq_one_of_irreducible`;
- core/canonical owner abstraction: `IsAlgClosed F`;
- layer: `source-facing`, since Lemma 9.10.2 is genuinely a list of equivalent textbook
  characterizations rather than a bare recall item;
- primitive data: only the field `F`;
- derived API: the irreducible-linear, nonconstant-root, and nonconstant-splitting criteria below.

The textbook clause “every polynomial splits” is already exactly the owner notion `IsAlgClosed F`,
so this file keeps the owner directly in the main `List.TFAE` statement instead of introducing a
parallel local wrapper for that clause.
-/

/-- A field is algebraically closed iff every irreducible polynomial over it is linear. -/
theorem isAlgClosed_iff_forall_irreducible_degree_eq_one :
    IsAlgClosed F ↔ ∀ (p : F[X]) (_ : Irreducible p), p.degree = 1 := by
  refine ⟨fun _ p hp ↦ IsAlgClosed.degree_eq_one_of_irreducible F hp, fun h ↦ ?_⟩
  exact IsAlgClosed.of_exists_root F fun p _ hp ↦ exists_root_of_degree_eq_one (h p hp)

/-- A field is algebraically closed iff every nonconstant polynomial over it has a root. -/
theorem isAlgClosed_iff_forall_nonconstant_exists_root :
    IsAlgClosed F ↔ ∀ (p : F[X]) (_ : p.natDegree ≠ 0), ∃ x : F, IsRoot p x := by
  refine ⟨?_, ?_⟩
  · intro _ p hp
    exact IsAlgClosed.exists_root p (degree_ne_of_natDegree_ne hp)
  · intro h
    exact IsAlgClosed.of_exists_root F fun p _ hp ↦ h p hp.natDegree_pos.ne'

/-- A field is algebraically closed iff every nonconstant polynomial over it splits. -/
theorem isAlgClosed_iff_forall_nonconstant_splits :
    IsAlgClosed F ↔ ∀ (p : F[X]) (_ : p.natDegree ≠ 0), p.Splits := by
  refine ⟨fun _ p _ ↦ IsAlgClosed.splits p, ?_⟩
  intro h
  refine (isAlgClosed_iff_forall_nonconstant_exists_root F).2 fun p hp ↦ ?_
  exact (h p hp).exists_eval_eq_zero (degree_ne_of_natDegree_ne hp)

/-- Lemma 9.10.2: for a field `F`, the following are equivalent: `F` is algebraically closed,
every irreducible polynomial over `F` is linear, every nonconstant polynomial over `F` has a
root, and every nonconstant polynomial over `F` splits as a product of linear factors. -/
theorem isAlgClosed_tfae :
    List.TFAE [
      IsAlgClosed F,
      ∀ (p : F[X]) (_ : Irreducible p), p.degree = 1,
      ∀ (p : F[X]) (_ : p.natDegree ≠ 0), ∃ x : F, IsRoot p x,
      ∀ (p : F[X]) (_ : p.natDegree ≠ 0), p.Splits
    ] := by
  tfae_have 1 ↔ 2 := isAlgClosed_iff_forall_irreducible_degree_eq_one F
  tfae_have 1 ↔ 3 := isAlgClosed_iff_forall_nonconstant_exists_root F
  tfae_have 1 ↔ 4 := isAlgClosed_iff_forall_nonconstant_splits F
  tfae_finish

end
