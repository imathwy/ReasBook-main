import Mathlib
import StacksProject_2024.Chap29.Definition_29_30_1
import StacksProject_2024.Chap29.Definition_29_29_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ)

/- Semantic recall / analogue check:
- local project precedent records the scheme-level syntomic owner as `Syntomic f` in
  `Chap29/Definition_29_30_1.lean`;
- Chapter 29 already defines the exact relative-dimension owner
  `Scheme.Hom.RelativeDimension f d` in `Chap29/Definition_29_29_1.lean`;
- the source definition is therefore a source-facing conjunction of these two canonical owners,
  rather than a parallel exact-dimension wrapper built from pointwise fibre-dimension equalities or
  a new proposition class.
-/

/- Definition 29.30.15: a morphism of schemes `f : X ⟶ S` is syntomic of relative dimension `d`
if `f` is syntomic and every nonempty fibre is equidimensional of topological Krull dimension
`d`; equivalently, the source-facing condition is exactly the conjunction below. -/
#check (Syntomic f ∧ Scheme.Hom.RelativeDimension f d : Prop)

/-- A morphism that is syntomic and of relative dimension `d` is, in particular, syntomic. -/
theorem syntomic_of_syntomic_and_relativeDimension
    (h : Syntomic f ∧ Scheme.Hom.RelativeDimension f d) : Syntomic f :=
  h.1

/-- A morphism that is syntomic and of relative dimension `d` is, in particular, of relative
dimension `d`. -/
theorem relativeDimension_of_syntomic_and_relativeDimension
    (h : Syntomic f ∧ Scheme.Hom.RelativeDimension f d) : Scheme.Hom.RelativeDimension f d :=
  h.2

/-- A morphism that is syntomic and of relative dimension `d` is locally of finite type through
its relative-dimension hypothesis. -/
theorem locallyOfFiniteType_of_syntomic_and_relativeDimension
    (h : Syntomic f ∧ Scheme.Hom.RelativeDimension f d) : LocallyOfFiniteType f := by
  let _ : Scheme.Hom.RelativeDimension f d := h.2
  exact Scheme.Hom.locallyOfFiniteType_of_relativeDimension f d

end AlgebraicGeometry
