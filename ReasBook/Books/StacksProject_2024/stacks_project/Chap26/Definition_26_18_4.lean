import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S)

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-fiber owners
-- `Scheme.Hom.fiber`, `Scheme.Hom.fiberι`, `Scheme.Hom.fiberOverSpecResidueField`, and
-- `Scheme.Hom.fiberToSpecResidueField`; local Chapter 29/31 precedent already uses this API.

/- Definition 26.18.4: for a morphism of schemes `f : X ⟶ S` and a point `s : S`, the
scheme-theoretic fibre `X_s` is the canonical pullback owner `Scheme.Hom.fiber`, written in
downstream-facing form as `f.fiber s`, i.e. the fiber product `Spec (κ(s)) ×_S X`. -/
recall Scheme.Hom.fiber
#check f.fiber s

/- Companion recall: the two canonical projections from the fibre product are the map
`f.fiberι s : f.fiber s ⟶ X` and the structure morphism
`f.fiberToSpecResidueField s : f.fiber s ⟶ Spec (S.residueField s)`;
equivalently, the latter is recorded by the over-object
`f.fiberOverSpecResidueField s`. -/
recall Scheme.Hom.fiberι
recall Scheme.Hom.fiberOverSpecResidueField
recall Scheme.Hom.fiberToSpecResidueField
#check f.fiberι s
#check f.fiberOverSpecResidueField s
#check f.fiberToSpecResidueField s

end AlgebraicGeometry
