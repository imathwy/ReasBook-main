import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finite.Card

-- Semantic recall: the Euler characteristic of a finite graph is the number of
-- vertices minus the number of edges.

universe u

namespace SimpleGraph

/-- Definition 4.4.1. For a finite graph `X`, the Euler characteristic of `X` is the number of
vertices minus the number of edges:
`χ(X) = Nat.card V - Nat.card X.edgeSet`. -/
noncomputable def eulerCharacteristic {V : Type u} (X : SimpleGraph V) [Finite V] : ℤ :=
  (Nat.card V : ℤ) - Nat.card X.edgeSet

@[inherit_doc eulerCharacteristic]
scoped notation "χ(" X ")" => eulerCharacteristic X

open scoped SimpleGraph

/-- The Euler characteristic of a finite graph is `Nat.card V - Nat.card X.edgeSet`. -/
@[simp] theorem eulerCharacteristic_def {V : Type u} (X : SimpleGraph V) [Finite V] :
    χ(X) = (Nat.card V : ℤ) - Nat.card X.edgeSet :=
  rfl

end SimpleGraph
