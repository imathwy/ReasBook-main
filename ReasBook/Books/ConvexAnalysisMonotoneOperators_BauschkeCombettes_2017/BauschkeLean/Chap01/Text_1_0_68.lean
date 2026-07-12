import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
Text 1.0.68: a subset of a topological space, and hence in particular of a Hausdorff space, is
called a `G_δ` set when it is a countable intersection of open sets, formalized by the canonical
predicate `IsGδ`.
-/
recall IsGδ {X : Type u} [TopologicalSpace X] (s : Set X) : Prop

/- Companion recall: a set is `G_δ` exactly when it can be written as the intersection of a
sequence of open sets. -/
recall isGδ_iff_eq_iInter_nat {X : Type u} [TopologicalSpace X] {s : Set X} :
    IsGδ s ↔ ∃ (f : ℕ → Set X), (∀ n, IsOpen (f n)) ∧ s = ⋂ n, f n
