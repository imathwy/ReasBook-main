import Mathlib.AlgebraicGeometry.Morphisms.Flat

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: mathlib already exports the exact scheme-morphism theorem
-- `AlgebraicGeometry.Flat.generalizingMap`. This file keeps the Stacks item as a thin
-- source-facing bridge to that canonical owner.

/- Lemma 29.25.9: if `f : X ⟶ S` is a flat morphism of schemes, then generalizations lift along
`f`. Equivalently, the underlying map of topological spaces of a flat morphism of schemes is a
generalizing map in the sense of Topology, Definition 5.19.4. -/
@[stacks 04PV]
theorem Flat.generalizingMap_base
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] :
    GeneralizingMap f.base :=
  by simpa using (Flat.generalizingMap f)

end AlgebraicGeometry
