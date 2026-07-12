import Mathlib.AlgebraicGeometry.PullbackCarrier

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

-- Canonical source-facing owner: `Scheme.Pullback.exists_preimage_pullback` in the pullback-carrier
-- API gives the exact existence statement for points of the scheme pullback.

/-- Lemma 29.9.3: for morphisms `f : X ⟶ S` and `g : Y ⟶ S`, a point of the fiber product
`pullback f g` mapping to prescribed points `x : X` and `y : Y` under the projections exists if
and only if `x` and `y` have the same image in `S`. -/
@[stacks 0495]
theorem exists_pullback_point_iff
    (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y) :
    (∃ z : pullback f g, pullback.fst f g z = x ∧ pullback.snd f g z = y) ↔
      f x = g y := by
  constructor
  · rintro ⟨z, hzx, hzy⟩
    rw [← hzx, ← hzy]
    exact congrFun (pullback.condition f g) z
  · exact Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y

end AlgebraicGeometry
