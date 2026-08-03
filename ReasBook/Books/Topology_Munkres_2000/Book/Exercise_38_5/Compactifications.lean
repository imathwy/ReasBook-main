module

public import Topology_Munkres_2000.Book.Definition_38_1.Equivalence
public import Topology_Munkres_2000.Book.Exercise_38_5.Instances
public import Topology_Munkres_2000.Book.Proposition_38_1.StoneCech
public import Mathlib.Topology.Compactification.OnePoint.Basic

public section

namespace OpenOmegaOne

/-- The canonical one-point compactification of the open first-uncountable ordinal. -/
@[expose]
def onePointCompactification : Compactification OpenOmegaOne :=
  Compactification.of (OnePoint OpenOmegaOne) (fun x ↦ (x : OnePoint OpenOmegaOne))
    OnePoint.isDenseEmbedding_coe

/-- The canonical Stone–Čech compactification of the open first-uncountable ordinal. -/
abbrev stoneCechCompactification : Compactification OpenOmegaOne :=
  Compactification.stoneCech OpenOmegaOne

/-- The embedding into the one-point compactification is the canonical coercion. -/
theorem onePointCompactification_apply (x : OpenOmegaOne) :
    onePointCompactification x = (x : OnePoint OpenOmegaOne) := by
  -- The generic compactification constructor retains its supplied embedding.
  exact Compactification.of_apply (OnePoint OpenOmegaOne) _ OnePoint.isDenseEmbedding_coe x

/-- The embedding of `OpenOmegaOne` into its Stone–Čech compactification is `stoneCechUnit`. -/
theorem stoneCechCompactification_apply (x : OpenOmegaOne) :
    stoneCechCompactification x = stoneCechUnit x :=
  Compactification.stoneCech_apply OpenOmegaOne x


end OpenOmegaOne

end
