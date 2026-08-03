module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

@[expose] public section

universe u

namespace FundamentalGroup

/-- The fundamental group with multiplication in left-to-right path order. -/
abbrev LeftToRight (X : Type u) [TopologicalSpace X] (x₀ : X) :=
  (FundamentalGroup X x₀)ᵐᵒᵖ

/-- Munkres's notation for the fundamental group, with multiplication in
left-to-right path order. -/
notation "π₁(" X ", " x₀ ")" => LeftToRight X x₀

namespace LeftToRight

variable {X : Type u} [TopologicalSpace X] {x₀ : X}

/-- Regard a left-to-right fundamental-group element as a path-homotopy class. -/
abbrev toPath (p : π₁(X, x₀)) : Path.Homotopic.Quotient x₀ x₀ :=
  FundamentalGroup.toPath p.unop

/-- Regard a path-homotopy class as an element of the left-to-right fundamental group. -/
abbrev fromPath (p : Path.Homotopic.Quotient x₀ x₀) : π₁(X, x₀) :=
  .op (FundamentalGroup.fromPath p)

/-- The identity is represented by the constant loop. -/
theorem one_def : toPath (1 : π₁(X, x₀)) = .refl x₀ := rfl

/-- Multiplication first traverses `p`, then traverses `q`. -/
theorem mul_def (p q : π₁(X, x₀)) :
    toPath (p * q) = (toPath p).trans (toPath q) := rfl

/-- Inversion is represented by path reversal. -/
theorem inv_def (p : π₁(X, x₀)) : toPath p⁻¹ = (toPath p).symm := rfl

@[simp] theorem toPath_fromPath (p : Path.Homotopic.Quotient x₀ x₀) :
    toPath (fromPath p) = p := rfl

@[simp] theorem fromPath_toPath (p : π₁(X, x₀)) :
    fromPath (toPath p) = p := rfl

end LeftToRight

end FundamentalGroup
