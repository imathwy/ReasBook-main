module

public import Topology_Munkres_2000.Book.Definition_77_1.Proper
import all Topology_Munkres_2000.Book.Definition_77_1.Proper

public section

universe u

namespace PolygonWord

/-- Definition 77.2 (torus type): A proper polygon word has torus type when each occurring
label appears once with each sign. -/
def TorusType {α : Type u} (word : PolygonWord α) : Prop :=
  ∀ c ∈ ({word} : LabellingScheme α).labels,
    ∃ rest : Multiset (α × Bool),
      (word.1 : Multiset (α × Bool)) = (c, true) ::ₘ (c, false) ::ₘ rest ∧
        ∀ b : Bool, (c, b) ∉ rest

/-- Definition 77.2 (projective type): A proper polygon word has projective type when it does
not have torus type. -/
def ProjectiveType {α : Type u} (word : PolygonWord α) : Prop :=
  ({word} : LabellingScheme α).Proper ∧ ¬ word.TorusType


end PolygonWord
