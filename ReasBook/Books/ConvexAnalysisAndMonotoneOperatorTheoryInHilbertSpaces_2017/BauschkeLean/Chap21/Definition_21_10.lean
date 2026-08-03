import BauschkeLean.Chap01.Text_1_0_9

universe u v

namespace SetValuedOperator

variable {X : Type u} {Y : Type v} [PseudoMetricSpace X] [Bornology Y]

/-- Definition 21.10: a set-valued operator is locally bounded at `x` when some metric ball
around `x` has bounded image under `A`. -/
def IsLocallyBoundedAt (A : SetValuedOperator X Y) (x : X) : Prop :=
  -- This is the pointwise textbook notion: a positive-radius ball around `x` has bounded image.
  ∃ ε > 0, Bornology.IsBounded (A.image (Metric.ball x ε))

/-- Helper for Definition 21.10: a set-valued operator is locally bounded everywhere when it is
locally bounded at each point of its domain. -/
abbrev IsLocallyBounded (A : SetValuedOperator X Y) : Prop :=
  -- The global notion is the pointwise condition evaluated at every source point.
  ∀ x, A.IsLocallyBoundedAt x

end SetValuedOperator
