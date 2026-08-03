module

public import Mathlib.Topology.UniformSpace.Cauchy

public section

universe u

/-- The set of Cauchy sequences in a uniform space. -/
def cauchySequences (X : Type u) [UniformSpace X] : Set (ℕ → X) :=
  {x | CauchySeq x}

/-- `X̃` is the set of Cauchy sequences in `X`. -/
postfix:max "̃" => cauchySequences

/-- Membership in `X̃` is the `CauchySeq` predicate. -/
theorem mem_cauchySequences {X : Type u} [UniformSpace X] {x : ℕ → X} :
    x ∈ X̃ ↔ CauchySeq x := Iff.rfl
