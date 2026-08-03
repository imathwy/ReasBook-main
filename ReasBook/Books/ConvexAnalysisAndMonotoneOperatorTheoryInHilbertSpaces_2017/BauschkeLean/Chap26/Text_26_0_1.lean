import Mathlib
import BauschkeLean.Chap01.Text_1_0_11

open scoped Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [AddGroup H]

-- Semantic recall: `lean_leansearch` did not surface a monotone-operator-specific owner for the
-- paired primal/dual inclusion solution sets, so this file uses the Chapter 1 zero-set and
-- inverse owners directly.

/- Source/core/bridge triage:
- `source-facing`: Text 26.0.1 introduces the primal and dual inclusion problems for a pair
  `(A, B)` of set-valued operators on a Hilbert space.
- `core/canonical`: the owner declarations are `SetValuedOperator.zeros`,
  `SetValuedOperator.inverse`, and the pointwise set operations on operator values.
- `bridge/view`: the reusable downstream surface is therefore the pair of source-facing solution
  sets, together with membership lemmas exposing the two inclusions. -/

/-- Text 26.0.1 (1): for set-valued operators `A, B : H → 2^H`, the primal solution set `𝓟`
consists of the points `x : H` solving the monotone inclusion `0 ∈ A x + B x`, i.e.
`𝓟 = zer (A + B)`. -/
def primal_inclusion_solution_set (A B : SetValuedOperator H H) : Set H :=
  (A + B).zeros

/-- Membership in `primal_inclusion_solution_set A B` is exactly the primal inclusion
`0 ∈ A x + B x`. -/
@[simp] theorem mem_primal_inclusion_solution_set
    (A B : SetValuedOperator H H) (x : H) :
    x ∈ primal_inclusion_solution_set A B ↔ (0 : H) ∈ A x + B x := Iff.rfl

/-- Text 26.0.1 (2): for set-valued operators `A, B : H → 2^H`, the dual solution set `𝓓`
consists of the points `u : H` solving the dual inclusion
`0 ∈ -A⁻¹(-u) + B⁻¹u`. -/
def dual_inclusion_solution_set (A B : SetValuedOperator H H) : Set H :=
  (fun u ↦ (-(A⁻¹ (-u)) : Set H) + B⁻¹ u).zeros

/-- Membership in `dual_inclusion_solution_set A B` is exactly the dual inclusion
`0 ∈ -A⁻¹(-u) + B⁻¹u`. -/
@[simp] theorem mem_dual_inclusion_solution_set
    (A B : SetValuedOperator H H) (u : H) :
    u ∈ dual_inclusion_solution_set A B ↔
      (0 : H) ∈ (-(A⁻¹ (-u)) : Set H) + B⁻¹ u := Iff.rfl

end SetValuedOperator
