import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped NNReal Topology

section HolderAt

variable {X : Type u} {Y : Type v} [PseudoMetricSpace X] [PseudoMetricSpace Y]
variable {γ : Set.Ioc (0 : ℝ≥0) 1} {f : X → Y} {x : X}

/-- Definition 21.2 (1): a map is Hölder-continuous of order `γ ∈ (0,1]` at the point `r` if
there are a radius `ε > 0` and a finite Hölder constant `C` such that nearby points satisfy the
textbook inequality `dist (φ r) (φ s) ≤ C * dist r s ^ γ`. -/
def HolderContinuousAt (γ : Set.Ioc (0 : ℝ≥0) 1) (f : X → Y) (x : X) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ≥0, ∀ y : X, dist y x < ε →
    dist (f x) (f y) ≤ C * dist x y ^ (γ : ℝ)

/-- A Hölder-continuous map at a point admits a positive-radius neighborhood and a finite Hölder
constant controlling the oscillation from the center point. -/
theorem HolderContinuousAt.exists_dist_le_mul_rpow (hf : HolderContinuousAt γ f x) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ≥0, ∀ y : X, dist y x < ε →
      dist (f x) (f y) ≤ C * dist x y ^ (γ : ℝ) :=
  hf

end HolderAt

section LocalHolder

variable {X : Type u} {Y : Type v} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- A map is locally Hölder of exponent `r` if every point has a neighborhood on which it is
Hölder with exponent `r` and some local Hölder constant. -/
def LocallyHolderWith (r : ℝ≥0) (f : X → Y) : Prop :=
  ∀ x : X, ∃ s : Set X, s ∈ 𝓝 x ∧ ∃ C : ℝ≥0, HolderOnWith C r f s

-- Proof sketch: use the whole space as the neighborhood of each point and keep the same Hölder
-- constant.
/-- A globally Hölder map is locally Hölder with the same exponent. -/
theorem HolderWith.locallyHolderWith
    {C r : ℝ≥0} {f : X → Y} (hf : HolderWith C r f) :
    LocallyHolderWith r f := sorry

end LocalHolder

section MetricLocalHolder

variable {X : Type u} {Y : Type v} [MetricSpace X] [PseudoMetricSpace Y]

/- Definition 21.2 (2): local Hölder continuity is the canonical owner predicate
`LocallyHolderWith`. -/
#check LocallyHolderWith

/-- In a metric space, a locally Hölder map admits a Hölder estimate on some open ball around each
point. -/
theorem LocallyHolderWith.exists_holderOnWith_ball {r : ℝ≥0} {f : X → Y}
    (hf : LocallyHolderWith r f) (x : X) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ≥0, HolderOnWith C r f (Metric.ball x ε) := sorry

end MetricLocalHolder

section GlobalHolder

variable {X : Type u} {Y : Type v} [PseudoMetricSpace X] [PseudoMetricSpace Y]
variable (γ : Set.Ioc (0 : ℝ≥0) 1) (f : X → Y)

/- Definition 21.2 (3): global Hölder continuity of order `γ` is the existence of a
`HolderWith` constant. -/
#check (∃ C : ℝ≥0, HolderWith C γ f)

end GlobalHolder
