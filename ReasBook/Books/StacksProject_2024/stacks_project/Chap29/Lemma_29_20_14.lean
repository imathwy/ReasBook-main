import Mathlib
import StacksProject_2024.Chap29.Definition_29_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical scheme owners `Scheme.Hom.fiber`,
  `Scheme.Hom.QuasiFiniteAt`, and `LocallyQuasiFinite`.
- Local Chapter 29 precedent records the source phrase "of finite type" through
  `Scheme.Hom.FiniteType`, and represents points of a fiber either by `f.asFiber x` or by the
  topological equation `f x = s`. This item is stated as finiteness of the corresponding subset
  of source points.
-/

/-- Lemma 29.20.14: if `f : X ⟶ S` is a morphism of schemes of finite type and `s : S`, then
there are only finitely many points of `X` lying over `s` at which `f` is quasi-finite. -/
@[stacks 0AAY]
theorem finiteQuasiFiniteAtPointsOver
    {X S : Scheme.{u}} (f : X ⟶ S) [FiniteType f] (s : S) :
    ({x : X | f x = s ∧ f.QuasiFiniteAt x} : Set X).Finite := sorry

end Scheme.Hom
end AlgebraicGeometry
