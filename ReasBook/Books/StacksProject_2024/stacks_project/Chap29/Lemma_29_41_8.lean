import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry

-- Semantic recall: the source-facing statement is the Stacks-tagged bridge to the canonical
-- instance chain from `UniversallyClosed f` to `QuasiCompact f`.

/- Lemma 29.41.8: a universally closed morphism of schemes is quasi-compact. -/
@[stacks 04XU]
theorem universallyClosed_quasiCompact
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f] :
    QuasiCompact f :=
  inferInstance

end AlgebraicGeometry
