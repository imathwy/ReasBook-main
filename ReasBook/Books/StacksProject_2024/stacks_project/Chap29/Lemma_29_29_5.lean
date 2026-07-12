import Mathlib
import StacksProject_2024.Chap29.Definition_29_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/- Semantic recall / verified owner check:
- `lean_leansearch` surfaced the scheme-side owners `Scheme.Hom.QuasiFiniteAt`,
  `LocallyQuasiFinite`, and `Scheme.Hom.fiber`;
- local Chapter 29 precedent records the local fibre dimension as
  `Scheme.Hom.fiberDimensionAt` and relative dimension as `Scheme.Hom.RelativeDimension`.
-/

/-- Lemma 29.29.5 (1): for a locally finite type morphism of schemes `f : X ⟶ S` and a point
`x : X`, `f` is quasi-finite at `x` if and only if the fibre `X_{f x}` has local dimension zero
at `x`. -/
@[stacks 0397]
theorem quasiFiniteAt_iff_fiberDimensionAt_eq_zero [LocallyOfFiniteType f] (x : X) :
    f.QuasiFiniteAt x ↔ f.fiberDimensionAt x = (0 : WithBot ℕ∞) := sorry

/-- Lemma 29.29.5 (2): for a locally finite type morphism of schemes, local quasi-finiteness is
equivalent to having relative dimension zero. -/
@[stacks 0397]
theorem locallyQuasiFinite_iff_relativeDimension_zero [LocallyOfFiniteType f] :
    LocallyQuasiFinite f ↔ RelativeDimension f 0 := sorry

end Scheme.Hom
end AlgebraicGeometry
