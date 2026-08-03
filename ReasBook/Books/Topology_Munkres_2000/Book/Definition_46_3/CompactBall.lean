module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

public section

noncomputable section

open Set

universe u v

namespace Metric

variable {X : Type u} {Y : Type v} [PseudoMetricSpace Y]

/-- The supremum of the pointwise distances between two functions on a set. -/
def supDistOn (C : Set X) (f g : X → Y) : ℝ :=
  sSup ((fun x ↦ dist (f x) (g x)) '' C)

/-- The supremum distance is the supremum of the image of the pointwise distance function. -/
theorem supDistOn_eq_sSup (C : Set X) (f g : X → Y) :
    supDistOn C f g = sSup ((fun x ↦ dist (f x) (g x)) '' C) := by
  -- Expose the defining supremum for order-theoretic comparisons.
  rfl

/-- The textbook compact-convergence ball on `C`. The boundedness clause records that the
displayed real supremum exists, rather than using the default value of `sSup` on an
unbounded set. -/
def uniformBallOn (C : Set X) (f : X → Y) (ε : ℝ) : Set (X → Y) :=
  {g | BddAbove ((fun x ↦ dist (f x) (g x)) '' C) ∧ supDistOn C f g < ε}

/-- Membership in a uniform ball on a set is boundedness of the pointwise-distance image
together with the strict supremum-distance bound. -/
theorem mem_uniformBallOn {C : Set X} {f g : X → Y} {ε : ℝ} :
    g ∈ uniformBallOn C f ε ↔
      BddAbove ((fun x ↦ dist (f x) (g x)) '' C) ∧ supDistOn C f g < ε := by
  rfl

/-- The difference between the radius of a uniform ball and the supremum distance of one
of its members from the center is positive. -/
theorem uniformBallOn_radius_pos {C : Set X} {f g : X → Y} {ε : ℝ}
    (hg : g ∈ uniformBallOn C f ε) :
    0 < ε - supDistOn C f g := by
  exact sub_pos.mpr hg.2

end Metric

/- Textbook notation `B_C(f, ε)` for the uniform ball on `C`. -/
namespace CompactConvergence

scoped syntax:max (name := uniformBallOnNotation)
  "B_[" term "](" term ", " term ")" : term
scoped macro_rules
  | `(B_[$C]($f, $ε)) => `(Metric.uniformBallOn $C $f $ε)

end CompactConvergence
