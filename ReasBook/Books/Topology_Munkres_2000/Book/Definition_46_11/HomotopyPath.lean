module

public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Path

public section

universe u v

open unitInterval

namespace ContinuousMap

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f₀ f₁ : C(X, Y)}

namespace Homotopy

/-- A homotopy determines a path in the compact-open function space. -/
def toPath (F : Homotopy f₀ f₁) : Path f₀ f₁ :=
  ⟨F.curry, F.curry_zero, F.curry_one⟩

/-- The path associated to a homotopy evaluates to the homotopy itself. -/
@[simp]
theorem toPath_apply (F : Homotopy f₀ f₁) (t : I) (x : X) : F.toPath t x = F (t, x) :=
  F.curry_apply t x

end Homotopy

end ContinuousMap

namespace Path

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f₀ f₁ : C(X, Y)}

/-- A path in the compact-open function space determines a homotopy when the source is locally
compact. -/
def toHomotopy [LocallyCompactSpace X] (γ : Path f₀ f₁) : ContinuousMap.Homotopy f₀ f₁ where
  toContinuousMap := ContinuousMap.uncurry γ.toContinuousMap
  map_zero_left x := by simp
  map_one_left x := by simp

/-- The homotopy associated to a path evaluates to the path itself. -/
@[simp]
theorem toHomotopy_apply [LocallyCompactSpace X] (γ : Path f₀ f₁) (t : I) (x : X) :
    γ.toHomotopy (t, x) = γ t x :=
  ContinuousMap.uncurry_apply γ.toContinuousMap (t, x)

end Path

namespace ContinuousMap

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f₀ f₁ : C(X, Y)}

/-- For a locally compact source, homotopies from `f₀` to `f₁` are equivalent to paths from `f₀` to
`f₁` in the compact-open function space `C(X, Y)`. -/
def homotopyEquivPath [LocallyCompactSpace X] : Homotopy f₀ f₁ ≃ Path f₀ f₁ where
  toFun := Homotopy.toPath
  invFun := Path.toHomotopy
  left_inv F := by ext ⟨t, x⟩; rfl
  right_inv γ := by ext t x; rfl

end ContinuousMap
