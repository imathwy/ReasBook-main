import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {X Y : Type*}

/-
Source/core/bridge triage:
- `source-facing`: Definition 10.3.2 is the setwise property that some nonnegative constant makes
  `f` Lipschitz on `S`.
- `core/canonical`: the primitive owner in mathlib is `LipschitzOnWith α f S` with fixed `α`.
- `bridge/view`: the canonical metric bridge is `lipschitzOnWith_iff_dist_le_mul`; the textbook
  norm inequality is a thin normed-group specialization.
- Primitive data vs derived API: fixed-constant `LipschitzOnWith` is primitive; Definition 10.3.2
  is expressed directly as its existential witness form.
- Domain-style sampling: `LipschitzOnWith`, `lipschitzOnWith_iff_dist_le_mul`, `dist_eq_norm`.
- Layer target: keep the public statement at the canonical owner layer
  `∃ α : NNReal, LipschitzOnWith α f S`, with bridge theorems as reformulations only.
-/

/- The canonical fixed-constant owner behind Definition 10.3.2. -/
recall LipschitzOnWith

namespace LipschitzOnWith

section Core

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-- Canonical owner form of Definition 10.3.2:
`f` is Lipschitzian relative to `S` iff it has some nonnegative `LipschitzOnWith` witness
on `S`. -/
theorem exists_iff_forall_edist_le_mul
    {f : X → Y} {S : Set X} :
    (∃ α : NNReal, LipschitzOnWith α f S) ↔
      ∃ α : NNReal, ∀ x ∈ S, ∀ y ∈ S, edist (f x) (f y) ≤ α * edist x y := by
  simp [LipschitzOnWith]

end Core

section Metric

variable [PseudoMetricSpace X] [PseudoMetricSpace Y]

-- Proof sketch: unfold each `LipschitzOnWith` witness with `lipschitzOnWith_iff_dist_le_mul`.
/-- Canonical metric bridge for Definition 10.3.2: `f` is Lipschitz on `S` iff there exists
a nonnegative constant giving the pointwise metric inequality on `S`. -/
theorem exists_iff_forall_dist_le_mul
    {f : X → Y} {S : Set X} :
    (∃ α : NNReal, LipschitzOnWith α f S) ↔
      ∃ α : NNReal, ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) ≤ α * dist x y := by
  simp [lipschitzOnWith_iff_dist_le_mul]

end Metric

section Normed

variable [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]

-- Proof sketch: specialize the metric bridge and rewrite distances by norms.
/-- Normed-group specialization of the canonical metric bridge: `f` is Lipschitz on `S` iff
there is a nonnegative constant bounding `‖f x - f y‖` by `α * ‖x - y‖` on `S`. -/
theorem exists_iff_forall_norm_sub_le
    {f : X → Y} {S : Set X} :
    (∃ α : NNReal, LipschitzOnWith α f S) ↔
      ∃ α : NNReal, ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ α * ‖x - y‖ := by
  simpa [dist_eq_norm] using
    (exists_iff_forall_dist_le_mul :
      (∃ α : NNReal, LipschitzOnWith α f S) ↔
        ∃ α : NNReal, ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) ≤ α * dist x y)

end Normed

end LipschitzOnWith

end
