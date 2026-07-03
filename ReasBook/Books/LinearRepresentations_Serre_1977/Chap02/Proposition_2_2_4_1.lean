import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Classical.propDecidable

universe u

namespace Representation

/-
Source/core/bridge triage:
* source-facing: the explicit values of the regular character.
* core/canonical owners: `leftRegular`, `MulAction.fixedBy`, and
  `ofMulAction_character_eq_ncard_fixedBy`.
* bridge/view: compute the fixed-point set of the left regular action inside the proof; the
  character formula is then immediate from the canonical permutation-character theorem.
-/

section

variable {k : Type*} [Field k]
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- Helper for Proposition 2-2.4-1: for the permutation representation attached to a finite
`G`-set `X`, the character at `s` is the number of elements of `X` fixed by `s`. -/
@[simp]
lemma of_mulAction_character_eq_ncard_fixedBy {X : Type v} [MulAction G X] [Finite X] (s : G) :
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

omit [Finite G] in
/-- Helper for Proposition 2-2.4-1: a nonidentity element has no fixed points in the left regular
action of `G` on itself. -/
lemma leftRegular_fixedBy_eq_empty_of_ne_one {s : G} (hs : s ≠ 1) :
    MulAction.fixedBy G s = ∅ := by
  -- A fixed point for left multiplication would force `s = 1` by right cancellation.
  rw [Set.eq_empty_iff_forall_notMem]
  intro g hg
  have hmul : s * g = g := by
    simpa [MulAction.mem_fixedBy] using hg
  have hs' : s = 1 := by
    rwa [mul_eq_right] at hmul
  exact hs hs'

omit [Finite G] in
/-- Helper for Proposition 2-2.4-1: the fixed-point set of left multiplication is all of `G` at
the identity and empty otherwise. -/
lemma leftRegular_fixedBy_eq_ite (s : G) :
    MulAction.fixedBy G s = if s = 1 then Set.univ else ∅ := by
  -- Split on whether the acting element is the identity and use the fixed-point computation.
  by_cases hs : s = 1
  · simp [hs, MulAction.fixedBy_one_eq_univ]
  · simp [hs, leftRegular_fixedBy_eq_empty_of_ne_one hs]

/-- Helper for Proposition 2-2.4-1: the fixed-point set of left multiplication has cardinality
`|G|` at the identity and cardinality `0` otherwise. -/
@[simp]
lemma leftRegular_fixedBy_ncard (s : G) :
    (MulAction.fixedBy G s).ncard = if s = 1 then Nat.card G else 0 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  -- Rewrite the fixed-point set into the identity/nonidentity dichotomy before counting.
  rw [leftRegular_fixedBy_eq_ite]
  -- Each branch now has an immediate finite-cardinality computation.
  by_cases hs : s = 1 <;> simp [hs]

-- Proof sketch: specialize the canonical permutation-character formula
-- `ofMulAction_character_eq_ncard_fixedBy` to the left regular action of `G` on itself and
-- compute the fixed-point set by cancellation in `G`.
/-- Proposition 2-2.4-1: the regular character `r_G` takes the value `|G|` at the identity and `0`
away from the identity. -/
theorem leftRegular_character_eq_ite (s : G) :
    (leftRegular k G).character s = if s = 1 then ↑(Nat.card G) else 0 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  -- Rewrite the regular character as a permutation character counting fixed points.
  rw [of_mulAction_character_eq_ncard_fixedBy, leftRegular_fixedBy_ncard]
  -- The counting helper returns a natural-valued `if`, so only the scalar coercion remains.
  by_cases hs : s = 1 <;> simp [hs]

-- Specialize the main `if`-formula at the identity element.
@[simp] theorem leftRegular_character_one :
    (leftRegular k G).character (1 : G) = ↑(Nat.card G) := by
  -- The identity case is exactly the `then` branch of the main character formula.
  rw [leftRegular_character_eq_ite]
  simp

-- Specialize the main `if`-formula away from the identity element.
theorem leftRegular_character_eq_zero_of_ne_one {s : G} (hs : s ≠ 1) :
    (leftRegular k G).character s = 0 := by
  -- Off the identity, the character is the `else` branch of the same formula.
  rw [leftRegular_character_eq_ite]
  simp [hs]

end

end Representation
