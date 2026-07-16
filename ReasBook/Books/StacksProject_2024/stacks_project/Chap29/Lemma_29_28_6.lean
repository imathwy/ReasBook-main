import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_28_4

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

namespace Scheme.Hom

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical topological owner `IsRetrocompact` together with the
  scheme-side compact-open API, while local Chapter 29 precedent in `Lemma_29_28_4` already fixes
  `fiberDimensionLELocus` as the source-faithful owner for the locus `U_n`.
-/

variable {X S : Scheme.{u}}

/-- Lemma 29.28.6: for a locally finitely presented morphism `f : X ⟶ S`, the open locus
`U_n = {x ∈ X | dim_x X_{f(x)} ≤ n}` from Lemma 29.28.4 is retrocompact in `X`. -/
@[stacks 02G0]
theorem isRetrocompact_fiberDimensionLELocus (f : X ⟶ S) [LocallyOfFinitePresentation f] (n : ℕ) :
    IsRetrocompact (f.fiberDimensionLELocus n) := sorry

end Scheme.Hom

end AlgebraicGeometry
