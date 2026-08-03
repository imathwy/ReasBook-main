module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.SetTheory.Cardinal.Defs

public section

universe u

namespace Set

/-- A subset separates a topological space when its complement is not preconnected. -/
def Separates {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  ¬ PreconnectedSpace (Aᶜ : Set X)

/-- A subset separates a topological space exactly when its complement subtype
is not preconnected. -/
theorem separates_iff {X : Type u} [TopologicalSpace X] {A : Set X} :
    A.Separates ↔ ¬ PreconnectedSpace (Aᶜ : Set X) := by
  -- Unfolding `Separates` makes both sides of the equivalence identical.
  rfl

/-- A subset separates a topological space into `n` components when its
complement has exactly `n` connected components. -/
def SeparatesInto {X : Type u} [TopologicalSpace X] (A : Set X) (n : ℕ) : Prop :=
  Cardinal.mk (ConnectedComponents (Aᶜ : Set X)) = n

/-- A subset separates a topological space into `n` components exactly when
its complement has that many connected components. -/
theorem separatesInto_iff {X : Type u} [TopologicalSpace X] {A : Set X} {n : ℕ} :
    A.SeparatesInto n ↔ Cardinal.mk (ConnectedComponents (Aᶜ : Set X)) = n := by
  -- Unfolding `SeparatesInto` makes both sides of the equivalence identical.
  rfl

end Set
