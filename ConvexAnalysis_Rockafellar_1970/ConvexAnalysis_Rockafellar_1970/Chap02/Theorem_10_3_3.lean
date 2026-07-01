import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_10_3_2

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

variable {X : Type u} {Y : Type v}
variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

namespace LipschitzOnWith

-- Proof sketch: unpack the owner witness and apply the fixed-constant owner theorem
-- `LipschitzOnWith.uniformContinuousOn`.
/-- Canonical owner theorem for Definition 10.3.2: if `f` has a nonnegative
`LipschitzOnWith` witness on `S`, then `f` is uniformly continuous on `S`. -/
theorem uniformContinuousOn_of_exists
    {f : X → Y} {S : Set X} (hf : ∃ α : NNReal, LipschitzOnWith α f S) :
    UniformContinuousOn f S := by
  rcases hf with ⟨α, hα⟩
  exact hα.uniformContinuousOn

-- Proof sketch: use the canonical emetric bridge
-- `LipschitzOnWith.exists_iff_forall_edist_le_mul` to package the pointwise
-- extended-metric inequality as an existential `LipschitzOnWith` witness.
/-- Canonical emetric bridge for Theorem 10.3.3: if `f` satisfies a pointwise Lipschitz
bound on `S` for some nonnegative constant in extended-metric form, then `f` is uniformly
continuous on `S`. -/
theorem uniformContinuousOn_of_exists_forall_edist_le_mul
    {f : X → Y} {S : Set X}
    (hf : ∃ α : NNReal, ∀ x ∈ S, ∀ y ∈ S, edist (f x) (f y) ≤ α * edist x y) :
    UniformContinuousOn f S := by
  exact uniformContinuousOn_of_exists <|
    (LipschitzOnWith.exists_iff_forall_edist_le_mul).2 hf

end LipschitzOnWith

end

section

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-
Source/core/bridge triage:
- `source-facing`: the source-facing Lipschitz witness is the metric inequality
  `dist (f x) (f y) ≤ α * dist x y` on `S`.
- `core/canonical`: the source-facing owner data is the existential fixed-constant owner
  `∃ α, LipschitzOnWith α f S`; bridges to pointwise inequalities live at the emetric/metric
  layers.
- `bridge/view`: `LipschitzOnWith.exists_iff_forall_dist_le_mul` is the metric
  specialization
  bridge; norm formulas are further thin specializations.
- Primitive data vs derived API: this item introduces no new owner object and no new primitive
  data; it consumes the source-facing hypothesis and derives uniform continuity
  through the canonical owner theorem.

Domain-style sampling used here:
- `LipschitzOnWith`;
- `LipschitzOnWith.exists_iff_forall_edist_le_mul`;
- `LipschitzOnWith.exists_iff_forall_dist_le_mul`;
- `LipschitzOnWith.uniformContinuousOn`;
- `UniformContinuousOn`.
-/

/- The canonical fixed-constant owner theorem behind Theorem 10.3.3. -/
recall LipschitzOnWith.uniformContinuousOn

namespace LipschitzOnWith

-- Proof sketch: use the canonical metric bridge
-- `LipschitzOnWith.exists_iff_forall_dist_le_mul` to package the pointwise metric
-- inequality as an existential `LipschitzOnWith` witness.
/-- Canonical metric bridge for Theorem 10.3.3: if `f` satisfies a pointwise Lipschitz
bound on `S` for some nonnegative constant, then `f` is uniformly continuous on `S`. -/
theorem uniformContinuousOn_of_exists_forall_dist_le_mul {f : X → Y} {S : Set X}
    (hf : ∃ α : NNReal, ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) ≤ α * dist x y) :
    UniformContinuousOn f S := by
  exact uniformContinuousOn_of_exists <|
    (LipschitzOnWith.exists_iff_forall_dist_le_mul).2 hf

end LipschitzOnWith

end

section

variable {X Y : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]

namespace LipschitzOnWith

-- Proof sketch: this is the normed-group specialization of the canonical metric theorem
-- `uniformContinuousOn_of_exists_forall_dist_le_mul`.
/-- Normed-group specialization of Theorem 10.3.3: if
`‖f x - f y‖ ≤ α ‖x - y‖` on `S` for some nonnegative `α`, then `f` is uniformly continuous
on `S`. -/
theorem uniformContinuousOn_of_exists_forall_norm_sub_le {f : X → Y} {S : Set X}
    (hf : ∃ α : NNReal, ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ α * ‖x - y‖) :
    UniformContinuousOn f S := by
  exact uniformContinuousOn_of_exists_forall_dist_le_mul <|
    by simpa [dist_eq_norm] using hf

end LipschitzOnWith

end
