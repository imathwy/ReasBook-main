import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Module

/-- Definition 10.90.1 (1): an `R`-module is coherent if it is finitely generated and every
finitely generated submodule is finitely presented over `R`. -/
class Coherent (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M] : Prop
    extends Module.Finite R M where
  finitePresentation_submodule :
    ∀ (N : Submodule R M), Module.Finite R N → Module.FinitePresentation R N

end Module

/-- Definition 10.90.1 (2): a commutative ring is coherent if it is coherent as a module over
itself. -/
class IsCoherentRing (R : Type u) [CommRing R] : Prop extends Module.Coherent R R
