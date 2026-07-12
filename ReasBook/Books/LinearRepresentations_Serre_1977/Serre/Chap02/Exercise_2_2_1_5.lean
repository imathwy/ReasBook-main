import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Representation

section

variable {k : Type*} {G : Type u} {X : Type v} [Field k] [Monoid G] [MulAction G X] [Finite X]

/-
Source/core/bridge triage:
* source-facing: the value of the permutation character at `s`.
* core/canonical owners: `Representation.ofMulAction`, `Representation.character`, and
  `MulAction.fixedBy`.
* bridge/view: in the delta-function basis of `X →₀ k`, the diagonal entry indexed by `x` is `1`
  exactly when `s • x = x`, so the trace counts the fixed basis vectors.
-/
-- Proof sketch: in the delta-function basis of `X →₀ k`, the diagonal entry indexed by `x` is `1`
-- exactly when `s • x = x`, so the trace counts the fixed points of the endomorphism `x ↦ s • x`.
/-- Exercise 2-2.1-5: for the permutation representation attached to a finite `G`-set `X`, the
character at `s` is the number of elements of `X` fixed by `s`. -/
@[simp]
theorem ofMulAction_character_eq_ncard_fixedBy (s : G) :
    (ofMulAction k G X).character s = ↑(MulAction.fixedBy X s).ncard := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  calc
    (ofMulAction k G X).character s
      = Matrix.trace
          (LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
            ((ofMulAction k G X) s)) := by
          rw [character, LinearMap.trace_eq_matrix_trace k Finsupp.basisSingleOne]
    _ = ∑ x : X, if s • x = x then 1 else 0 := by
          simp [Matrix.trace, LinearMap.toMatrix_apply, ofMulAction_single,
            Finsupp.single_apply]
    _ = ↑((Finset.univ.filter fun x : X ↦ s • x = x).card) := by
          simp
    _ = ↑((MulAction.fixedBy X s).toFinset.card) := by
          congr
          ext x
          simp [MulAction.mem_fixedBy]
    _ = ↑(MulAction.fixedBy X s).ncard := by
          rw [← Set.ncard_eq_toFinset_card']

end

end Representation
