module

public import Topology_Munkres_2000.Book.Definition_74_4.Scheme
public import Mathlib.Data.Multiset.Bind

public section

universe u

namespace LabellingScheme

/-- Helper for Definition 77.1: the unsigned label occurrences in a labelling scheme. -/
def labels {α : Type u} (scheme : LabellingScheme α) : Multiset α :=
  scheme.bind (fun word ↦ word.1.map Prod.fst)

/- Definition 77.1: A labelling scheme is proper when every label appearing in it
occurs exactly twice, independently of its orientation sign. -/
/-- Definition 77.1: A labelling scheme is proper when every occurring unsigned label
appears exactly twice. -/
def Proper {α : Type u} (scheme : LabellingScheme α) : Prop :=
  ∀ c ∈ scheme.labels,
    ∃ rest : Multiset α, scheme.labels = c ::ₘ c ::ₘ rest ∧ c ∉ rest


end LabellingScheme
