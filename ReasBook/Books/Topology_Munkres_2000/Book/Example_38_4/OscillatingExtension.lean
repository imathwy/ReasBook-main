module

public import Topology_Munkres_2000.Book.Example_38_3

@[expose] public section

namespace TopologistsSineCurve

/-- The continuous second coordinate of the canonical inclusion of the sine-curve
compactification into its ambient square. -/
noncomputable def oscillatingExtension : ContinuousMap compactification ℝ where
  toFun y := (InducedCompactification.inclusion squareEmbedding y).2.1
  continuous_toFun := by
    -- Project the continuous ambient inclusion onto the square's second real coordinate.
    exact (continuous_subtype_val.comp continuous_snd).comp
      (InducedCompactification.isEmbedding_inclusion squareEmbedding).continuous

/-- The oscillating extension is evaluated by the second ambient coordinate. -/
@[simp]
theorem oscillatingExtension_eq (y : compactification) :
    oscillatingExtension y = (InducedCompactification.inclusion squareEmbedding y).2.1 :=
  rfl


end TopologistsSineCurve

end
