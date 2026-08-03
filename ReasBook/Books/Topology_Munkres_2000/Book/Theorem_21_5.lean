module

import Mathlib.Topology.Algebra.Ring.Real

universe u

/- Theorem 21.5 (1): If `f g : X → ℝ` are continuous, then their sum is
continuous. -/
#check (Continuous.add :
  ∀ {X : Type u} [TopologicalSpace X] {f g : X → ℝ},
    Continuous f → Continuous g → Continuous (f + g))

/- Theorem 21.5 (2): If `f g : X → ℝ` are continuous, then their difference is
continuous. -/
#check (Continuous.sub :
  ∀ {X : Type u} [TopologicalSpace X] {f g : X → ℝ},
    Continuous f → Continuous g → Continuous (f - g))

/- Theorem 21.5 (3): If `f g : X → ℝ` are continuous, then their product is
continuous. -/
#check (Continuous.mul :
  ∀ {X : Type u} [TopologicalSpace X] {f g : X → ℝ},
    Continuous f → Continuous g → Continuous (f * g))

/- Theorem 21.5 (4): If `f g : X → ℝ` are continuous and `g` is nowhere zero,
then their quotient is continuous. -/
#check (Continuous.div :
  ∀ {X : Type u} [TopologicalSpace X] {f g : X → ℝ},
    Continuous f → Continuous g → (∀ x, g x ≠ 0) → Continuous (f / g))
