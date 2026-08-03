module

public import Topology_Munkres_2000.Book.Definition_74_3.Pasting
public import Mathlib.GroupTheory.PresentedGroup

public section

namespace CyclicPolygon.EdgePasting

universe v

variable {n : ℕ} {poly : CyclicPolygon n} {S : Type v}

/-- The labels that actually occur among the edges of `pasting`. -/
abbrev UsedLabel (pasting : poly.EdgePasting S) :=
  {label : S // label ∈ Set.range pasting.label}

/-- The cyclic boundary word of `pasting`, with each label paired with its orientation sign. -/
def boundaryWord (pasting : poly.EdgePasting S) : List (pasting.UsedLabel × Bool) :=
  List.ofFn fun i : Fin n ↦
    (⟨pasting.label i, Set.mem_range_self i⟩, pasting.sign i)

/-- The boundary word has one entry for each cyclic edge. -/
theorem boundaryWord_length (pasting : poly.EdgePasting S) :
    pasting.boundaryWord.length = n := sorry

/-- The entry of the boundary word at edge `i` is its used label and orientation. -/
theorem boundaryWord_get (pasting : poly.EdgePasting S) (i : Fin n) :
    pasting.boundaryWord.get (Fin.cast pasting.boundaryWord_length.symm i) =
      (⟨pasting.label i, Set.mem_range_self i⟩, pasting.sign i) := sorry

/-- The free-group relator represented by the signed cyclic boundary word. -/
def relator (pasting : poly.EdgePasting S) : FreeGroup pasting.UsedLabel :=
  FreeGroup.mk pasting.boundaryWord

/-- The relator is the free-group word obtained from `pasting.boundaryWord`. -/
theorem relator_def (pasting : poly.EdgePasting S) :
    pasting.relator = FreeGroup.mk pasting.boundaryWord := sorry


end CyclicPolygon.EdgePasting
