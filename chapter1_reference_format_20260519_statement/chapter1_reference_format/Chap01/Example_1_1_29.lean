import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Equiv

variable (n : ℕ)

/- Example 1.1.29 (1): the multiplicative set `{1, -1}` of integers is the canonical unit group
`ℤˣ`, and this group is commutative. -/
#check (inferInstance : CommGroup ℤˣ)

/- Example 1.1.29 (2): the units of `ℤ` are exactly `1` and `-1`, identifying `ℤˣ` with the
textbook set `{±1}`. -/
#check (Int.units_eq_one_or : ∀ u : ℤˣ, u = 1 ∨ u = -1)

/- Example 1.1.29 (3): the symmetric group `S_n` is the permutation type `Perm (Fin n)`. -/
#check (Perm (Fin n))

/- Example 1.1.29 (4): the group law on `S_n` is the canonical group structure on `Perm (Fin n)`,
given by composition of permutations. -/
#check (inferInstance : Group (Perm (Fin n)))

-- Proof sketch: for `n > 2`, pick the adjacent transpositions swapping `0` with `1` and `1` with
-- `2`; evaluating their composites at `0` shows the two orders give different permutations.
/-- Example 1.1.29: for `n > 2`, the symmetric group `S_n` is noncommutative. -/
theorem symmetric_group_exists_noncommuting_pair (hn : 2 < n) :
    ∃ σ τ : Perm (Fin n), σ * τ ≠ τ * σ := by
  let i0 : Fin n := ⟨0, lt_trans (by decide) hn⟩
  let i1 : Fin n := ⟨1, lt_trans (by decide) hn⟩
  let i2 : Fin n := ⟨2, hn⟩
  refine ⟨swap i0 i1, swap i1 i2, ?_⟩
  intro h
  have h0 := congrArg (fun π : Perm (Fin n) ↦ π i0) h
  simp [Equiv.swap_apply_def, i0, i1, i2] at h0

/- Example 1.1.29 (6): a transposition is the canonical predicate `Perm.IsSwap`. -/
#check (Perm.IsSwap : Perm (Fin n) → Prop)

/- Example 1.1.29 (7): a `k`-cycle is modeled by the canonical cycle predicate `Perm.IsCycle`,
with `k` recovered canonically from the order, equivalently the cardinality of the support. -/
#check Perm.IsCycle.orderOf

/- Example 1.1.29 (8): every permutation of `S_n` can be expressed as a product of
transpositions. -/
#check Perm.truncSwapFactors

/- Example 1.1.29 (9): the sign is the canonical homomorphism `Perm.sign : S_n → {±1}`. -/
#check (Perm.sign : Perm (Fin n) →* ℤˣ)

/- Example 1.1.29 (10): on `Fin n`, the sign is given by the usual product over the pairs
`i < j`. -/
#check Perm.sign_eq_prod_prod_Iio

/- Example 1.1.29 (11): every transposition has sign `-1`, via the owner-level theorem on
`Perm.IsSwap`. -/
#check Perm.IsSwap.sign_eq

/- Example 1.1.29 (12): the sign is multiplicative, so it is a group homomorphism on `S_n`. -/
#check Perm.sign_mul

/- Example 1.1.29 (13): the alternating group `A_n` is the canonical subgroup
`alternatingGroup (Fin n)` of `S_n`. -/
#check (alternatingGroup (Fin n))

/- Example 1.1.29 (14): a permutation belongs to `A_n` exactly when its sign is `1`. -/
#check Perm.mem_alternatingGroup
