module

public import Topology_Munkres_2000.Book.Definition_29_2.Compactification
public import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

universe u

namespace Compactification

/-- The Stone–Čech compactification of a completely regular space. -/
def stoneCech (X : Type u) [TopologicalSpace X] [T35Space X] : Compactification X :=
  Compactification.of (StoneCech X) stoneCechUnit isDenseEmbedding_stoneCechUnit

/-- The embedding stored by the Stone–Čech compactification is `stoneCechUnit`. -/
theorem stoneCech_apply (X : Type u) [TopologicalSpace X] [T35Space X] (x : X) :
    stoneCech X x = stoneCechUnit x := by
  -- The compactification constructor retains its supplied embedding.
  exact of_apply (StoneCech X) stoneCechUnit isDenseEmbedding_stoneCechUnit x


end Compactification
