import Mathlib
import StacksProject_2024.Chap29.Lemma_29_35_12

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical scheme-morphism owners `Flat`,
  `LocallyOfFinitePresentation`, `Etale`, and the ring-level finite-separable criterion.
- Local Chapter 29 precedent records the source fibre hypothesis directly through
  `SchemeAsDisjointUnionOfSpecFiniteSeparable` applied to `f.fiberToSpecResidueField s`.
-/

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- Lemma 29.36.8: if a morphism of schemes is flat, locally of finite presentation, and every
fibre is a disjoint union of spectra of finite separable extensions of the corresponding residue
field, then it is étale. -/
@[stacks 02GM]
theorem etale_of_flat_locallyOfFinitePresentation_of_fiber_schemeAsDisjointUnionOfSpecFiniteSeparable
    (hflat : Flat f) (hfp : LocallyOfFinitePresentation f)
    (hfiber : f.FibersAreDisjointUnionOfSpecFiniteSeparable) :
    Etale f := sorry

end AlgebraicGeometry
