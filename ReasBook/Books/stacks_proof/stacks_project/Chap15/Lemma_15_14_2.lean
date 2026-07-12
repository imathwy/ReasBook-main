import StacksProject_2024.Chap15.Definition_15_14_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling for Lemma 15.14.2:
- primary domain: commutative algebra of absolutely integrally closed rings and root-existence for
  monic polynomials;
- sampled owner declarations:
  `IsAbsolutelyIntegrallyClosed`,
  `IsAbsolutelyIntegrallyClosed.exists_root`,
  `IsAbsolutelyIntegrallyClosed.of_exists_root`,
  `Polynomial.Splits.exists_eval_eq_zero`;
- best owner abstraction: the chapter owner `IsAbsolutelyIntegrallyClosed A`;
- primitive data: only the owner predicate `IsAbsolutelyIntegrallyClosed A`, whose primitive field
  is splitting of monic polynomials;
- derived API: the root-existence criterion for monic polynomials of nonzero degree.

Source/core/bridge triage:
- `source-facing`: the iff statement `absolutely_integrally_closed_iff_forall_monic_has_root`;
- `core/canonical`: `IsAbsolutelyIntegrallyClosed`;
- `bridge/view`: the forward and backward implications provided canonically by
  `IsAbsolutelyIntegrallyClosed.exists_root` and `IsAbsolutelyIntegrallyClosed.of_exists_root`.

This file therefore keeps the textbook iff statement, but only as a thin source-facing bridge over
the owner-level API from `Definition_15_14_1`.
-/

/-- Lemma 15.14.2: a ring is absolutely integrally closed if and only if every monic polynomial
over `A` of nonzero degree has a root in `A`. -/
@[stacks 0DCM]
theorem absolutely_integrally_closed_iff_forall_monic_has_root :
    IsAbsolutelyIntegrallyClosed A ↔
      ∀ (f : A[X]) (_ : f.Monic) (_ : f.degree ≠ 0), ∃ a : A, f.IsRoot a := by
  refine ⟨?_, IsAbsolutelyIntegrallyClosed.of_exists_root⟩
  intro hA f hf hdeg
  let _ : IsAbsolutelyIntegrallyClosed A := hA
  exact IsAbsolutelyIntegrallyClosed.exists_root f hf hdeg

end
