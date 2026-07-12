import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found the exact canonical mathlib instance
-- `AlgebraicGeometry.instIsAffineOfFiniteOfDiscreteTopologyCarrierCarrierCommRingCat`.

/- Lemma 26.11.8: a scheme whose underlying topological space is finite and discrete is affine.
In mathlib this is the canonical instance
`AlgebraicGeometry.instIsAffineOfFiniteOfDiscreteTopologyCarrierCarrierCommRingCat`. -/
recall AlgebraicGeometry.instIsAffineOfFiniteOfDiscreteTopologyCarrierCarrierCommRingCat

section

variable (X : Scheme) [Finite X] [DiscreteTopology X]

#check (inferInstance : IsAffine X)

end
