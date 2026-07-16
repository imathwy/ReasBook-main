import StacksProject_2024.stacks_project.Chap34.Definition_34_8_4
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

variable (T : Scheme) [IsAffine T]

/- Semantic recall for Definition 34.8.1:
- `source-facing`: a standard ph covering of an affine scheme is given by a proper surjective map
  together with a finite affine open cover of its source;
- `core/canonical`: the Chapter 34 owner `StandardPhCovering T`;
- `bridge/view`: the companion specification theorem `StandardPhCovering.source_spec`.

This item is therefore a pure Chapter 34 recall, not a place for a second constructor-shaped
wrapper such as `standardPhCovering`. -/

/- Definition 34.8.1: for an affine scheme `T`, a standard ph covering of `T` is the Chapter 34
owner `StandardPhCovering T`, whose data is a proper surjective morphism to `T` together with a
finite affine open cover of its source. -/
recall StandardPhCovering

/- Companion recall: the defining source-facing fields of a standard ph covering are exposed by
`StandardPhCovering.source_spec`. -/
recall StandardPhCovering.source_spec

end AlgebraicGeometry
