import Mathlib
import cartan.II.section05.«0008_Proposition_3_1»

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set
open scoped Interval

section

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {a a' b b' : ℝ}

/-- The local witness at `p` for a primitive along `δ` on the rectangle: on some neighborhood of
`p` in the rectangle, the function agrees with the pullback of a primitive of `ω` defined on an
open neighborhood of `δ p` contained in `D`. -/
def HasLocalPrimitiveFollowingOnRectangleAt
    (ω : E → E →L[ℝ] F) (D : Set E)
    (δ : C([[(a, a'), (b, b')]], E)) (f : C([[(a, a'), (b, b')]], F))
    (p : [[(a, a'), (b, b')]]) : Prop :=
  ∃ s : Set ([[(a, a'), (b, b')]]), IsOpen s ∧ p ∈ s ∧
    ∃ U : Set E, IsOpen U ∧ δ p ∈ U ∧ U ⊆ D ∧ MapsTo δ s U ∧
      ∃ primitive : E → F,
        IsPrimitiveOn U ω primitive ∧
          EqOn f (primitive ∘ δ) s

/-- Definition II.1-extra-11: a continuous function on the closed rectangle with opposite corners
`(a, a')` and `(b, b')` is a primitive of `ω` following `δ` when this local primitive condition
holds at every point of the rectangle. -/
def IsPrimitiveFollowingOnRectangle
    (ω : E → E →L[ℝ] F) (D : Set E)
    (δ : C([[(a, a'), (b, b')]], E)) (f : C([[(a, a'), (b, b')]], F)) : Prop :=
  ∀ p : [[(a, a'), (b, b')]],
    HasLocalPrimitiveFollowingOnRectangleAt ω D δ f p

/-- Near each point of the rectangle, the function agrees with the pullback of a local primitive
of `ω` on a neighborhood of the corresponding image point contained in `D`. -/
theorem IsPrimitiveFollowingOnRectangle.local_primitive
    {ω : E → E →L[ℝ] F} {D : Set E} {a a' b b' : ℝ}
    {δ : C([[(a, a'), (b, b')]], E)} {f : C([[(a, a'), (b, b')]], F)}
    (hf : IsPrimitiveFollowingOnRectangle ω D δ f) (p : [[(a, a'), (b, b')]]) :
    HasLocalPrimitiveFollowingOnRectangleAt ω D δ f p :=
  hf p

-- Proof sketch: the local witness provides an open neighborhood `U` of `δ p` contained in `D`.
/-- A local primitive witness on the rectangle forces the corresponding image point to lie in the
ambient domain `D`. -/
theorem HasLocalPrimitiveFollowingOnRectangleAt.mem_domain
    {ω : E → E →L[ℝ] F} {D : Set E} {a a' b b' : ℝ}
    {δ : C([[(a, a'), (b, b')]], E)} {f : C([[(a, a'), (b, b')]], F)}
    {p : [[(a, a'), (b, b')]]} (hp : HasLocalPrimitiveFollowingOnRectangleAt ω D δ f p) :
    δ p ∈ D := by
  rcases hp with ⟨_, _, _, U, _, hδU, hUD, _, _, _, _⟩
  exact hUD hδU

-- Proof sketch: apply `HasLocalPrimitiveFollowingOnRectangleAt.mem_domain` to the local witness
-- given by `hf` at `p`.
/-- A primitive following `δ` on the rectangle is evaluated only at image points lying in the
ambient domain `D`. -/
theorem IsPrimitiveFollowingOnRectangle.mem_domain
    {ω : E → E →L[ℝ] F} {D : Set E} {a a' b b' : ℝ}
    {δ : C([[(a, a'), (b, b')]], E)} {f : C([[(a, a'), (b, b')]], F)}
    (hf : IsPrimitiveFollowingOnRectangle ω D δ f) (p : [[(a, a'), (b, b')]]) :
    δ p ∈ D :=
  (hf.local_primitive p).mem_domain

end
