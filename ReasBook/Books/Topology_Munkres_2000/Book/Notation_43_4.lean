module

public import Topology_Munkres_2000.Book.Notation_43_4.Quotient

public section

universe u

variable {X : Type u} [PseudoMetricSpace X]

/- Notation 43.4: `⟦x⟧` denotes the equivalence class `[x]`, and
`CauchySequences.Quotient X` denotes the type `Y` of all such classes. -/
#check CauchySequences.Quotient
#check (⟦·⟧ : X̃ → CauchySequences.Quotient X)

end
