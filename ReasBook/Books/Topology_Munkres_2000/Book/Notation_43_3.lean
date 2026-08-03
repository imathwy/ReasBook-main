module

public import Topology_Munkres_2000.Book.Notation_43_3.CauchySequences

public section

universe u

variable {X : Type u} [UniformSpace X]

/- Notation 43.3: `X̃` denotes the set of all Cauchy sequences in `X`. -/
#check (X̃ : Set (ℕ → X))
#check mem_cauchySequences
