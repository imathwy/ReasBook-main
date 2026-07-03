import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/- Domain triage:
- `source-facing`: the textbook definition says a simple `R`-module has no nontrivial submodules.
- `core/canonical`: mathlib owns this notion as `IsSimpleModule R M`.
- `bridge/view`: the final theorem restates the owner class in the source wording
  `Nontrivial M ∧ ∀ N, N = ⊥ ∨ N = ⊤`.
- Primitive data vs derived API: there is no extra source-defined data here; the owner notion is
  primitive, and the source-text characterization is derived from `isSimpleModule_iff`.
-/

/- Definition 10.52.9: for an `R`-module `M`, the canonical mathlib notion of a simple module is
`IsSimpleModule R M`, expressing that `M` has no nontrivial submodules. -/
#check IsSimpleModule R M

/- Companion recall: the canonical structural form of simplicity is that the lattice
`Submodule R M` is a simple order. -/
recall isSimpleModule_iff

-- This is the source-text reformulation of `isSimpleModule_iff`, reduced to the standard
-- order-theoretic characterization `isSimpleOrder_iff` and the canonical equivalence
-- `Submodule.nontrivial_iff`.
/-- A module is simple exactly when it is nontrivial and every submodule is either `⊥` or `⊤`. -/
theorem isSimpleModule_iff_nontrivial_and_submodule_eq_bot_or_eq_top :
    IsSimpleModule R M ↔ Nontrivial M ∧ ∀ N : Submodule R M, N = ⊥ ∨ N = ⊤ := by
  rw [isSimpleModule_iff, isSimpleOrder_iff, Submodule.nontrivial_iff]
