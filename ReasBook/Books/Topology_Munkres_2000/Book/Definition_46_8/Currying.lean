module

public import Mathlib.Topology.ContinuousMap.Basic

public section

universe u v w

namespace ContinuousMap

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- Packages the continuous `X`-slices of a function `X × Z → Y` as a
`Z`-indexed family of continuous maps. -/
@[expose]
def curryRight (f : X × Z → Y) (h_slice : ∀ z, Continuous (fun x ↦ f (x, z))) :
    Z → C(X, Y) :=
  fun z ↦ ⟨fun x ↦ f (x, z), h_slice z⟩

/-- Evaluating `curryRight f h_slice z` at `x` gives `f (x, z)`. -/
@[simp]
theorem curryRight_apply (f : X × Z → Y)
    (h_slice : ∀ z, Continuous (fun x ↦ f (x, z))) (z : Z) (x : X) :
    curryRight f h_slice z x = f (x, z) := rfl

/-- Evaluates a `Z`-indexed family of continuous maps in product order `X × Z`. -/
@[expose]
def uncurryRight (F : Z → C(X, Y)) : X × Z → Y :=
  fun p ↦ F p.2 p.1

/-- Evaluating `uncurryRight F` at `(x, z)` gives `F z x`. -/
@[simp]
theorem uncurryRight_apply (F : Z → C(X, Y)) (x : X) (z : Z) :
    uncurryRight F (x, z) = F z x := rfl

/-- Every `X`-slice of `uncurryRight F` is continuous. -/
theorem continuous_uncurryRight_slice (F : Z → C(X, Y)) (z : Z) :
    Continuous (fun x ↦ uncurryRight F (x, z)) :=
  (F z).continuous

/-- Uncurrying the family of continuous slices recovers the original function. -/
theorem uncurryRight_curryRight (f : X × Z → Y)
    (h_slice : ∀ z, Continuous (fun x ↦ f (x, z))) :
    uncurryRight (curryRight f h_slice) = f := by
  funext p
  exact curryRight_apply f h_slice p.2 p.1

/-- Currying the evaluation of a continuous-map-valued family recovers that family. -/
theorem curryRight_uncurryRight (F : Z → C(X, Y)) :
    curryRight (uncurryRight F) (continuous_uncurryRight_slice F) = F := by
  funext z
  ext x
  exact uncurryRight_apply F x z

/-- The source's correspondence between functions with continuous `X`-slices and
`Z`-indexed families of continuous maps. -/
def curryRightEquiv :
    {f : X × Z → Y // ∀ z, Continuous (fun x ↦ f (x, z))} ≃ (Z → C(X, Y)) where
  toFun f := curryRight f f.property
  invFun F := ⟨uncurryRight F, continuous_uncurryRight_slice F⟩
  left_inv f := by
    rcases f with ⟨f, h_slice⟩
    ext p
    exact congrFun (uncurryRight_curryRight f h_slice) p
  right_inv := curryRight_uncurryRight

end ContinuousMap
