module

public import Topology_Munkres_2000.Book.Example_53_6.Polar
import Topology_Munkres_2000.Book.Example_53_1
import Topology_Munkres_2000.Book.Theorem_53_3.Product

public section

namespace Complex

/-- Example 53.6. The polar-coordinate map from the open upper half-plane to the
punctured complex plane is a surjective covering map. -/
theorem isCoveringMap_polarTurn :
    IsCoveringMap polarTurn ∧ Function.Surjective polarTurn := by
  constructor
  · -- Form the product covering and transport it across the polar homeomorphism.
    simpa only [polarTurn] using
      (Circle.isCoveringMap_turnExp.prodMap isCoveringMap_id.1).homeomorph_comp polarHomeomorph
  · -- Product surjectivity followed by the homeomorphism reaches every punctured-plane point.
    simpa only [polarTurn] using
      polarHomeomorph.surjective.comp
        (Circle.turnExp_surjective.prodMap Function.surjective_id)

end Complex
