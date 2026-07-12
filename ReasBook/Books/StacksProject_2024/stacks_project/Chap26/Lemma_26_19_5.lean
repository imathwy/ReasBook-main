import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

-- Semantic recall: the source-facing statement is the Stacks-tagged bridge to the canonical
-- instance chain from `IsClosedImmersion f` to `QuasiCompact f`.
/- Lemma 26.19.5: a closed immersion of schemes is quasi-compact. -/
@[stacks 01QT]
theorem closedImmersion_quasiCompact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    QuasiCompact f :=
  inferInstance

end AlgebraicGeometry
