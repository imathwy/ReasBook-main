import Mathlib
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap20.Definition_20_1
import BauschkeLean.Chap25.Definition_25_29
import BauschkeLean.Chap25.Definition_25_39

open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace ContinuousLinearMap

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Source/core/bridge triage:
-- * `source-facing`: Example 25.40 is the identity relating the Chapter 25 parallel composition
--   by the sum map to the Chapter 25 parallel sum.
-- * `core/canonical`: the owner declarations already live upstream as `A × B`, `A □ B`, and
--   `L ▷ A`.
-- * `bridge/view`: the only extra input here is the canonical adjoint of the sum map
--   `fst + snd`, namely the diagonal map `u ↦ (u, u)`.
/-- Helper for Example 25.40: the adjoint of the sum map on the `ℓ²` product is the diagonal map
`u ↦ (u, u)`, written as `inl + inr`. -/
lemma sum_map_adjoint_eq_diagonal :
    (fst ℝ H H + snd ℝ H H).adjoint =
      inl ℝ H H + inr ℝ H H := by
  -- Identify the adjoint by checking the defining inner-product relation on arbitrary vectors.
  symm
  refine (eq_adjoint_iff (inl ℝ H H + inr ℝ H H) (fst ℝ H H + snd ℝ H H)).2 ?_
  intro x y
  -- On the raw-product `ℓ²` structure, the left side is the diagonal pair `(x, x)` and the
  -- right side is the sum `y.1 + y.2`.
  change ⟪((inl ℝ H H + inr ℝ H H) x), y⟫_ℝ = ⟪x, (fst ℝ H H + snd ℝ H H) y⟫_ℝ
  simpa only [add_apply, inl_apply, inr_apply, Prod.mk_add_mk, add_zero, zero_add, coe_fst',
    coe_snd', inner_add_right] using
    (show ⟪(x, x), y⟫_ℝ = ⟪x, y.1⟫_ℝ + ⟪x, y.2⟫_ℝ by
      rfl)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Example 25.40: diagonal membership in the product operator is equivalent to the
two componentwise memberships. -/
lemma diag_mem_prod_iff
    (A B : SetValuedOperator H H) (p : H × H) (u : H) :
    (u, u) ∈ (A × B) p ↔ u ∈ A p.1 ∧ u ∈ B p.2 := by
  -- Unfold the product operator only far enough to read off the two component conditions.
  change (u, u) ∈ (A × B) p ↔ (u, u).1 ∈ A p.1 ∧ (u, u).2 ∈ B p.2
  exact SetValuedOperator.mem_prod_iff A B p (u, u)

/-- Helper for Example 25.40: membership in the parallel composition by the sum map is equivalent
to a decomposition `x = y + z` where `u` lies in both component operator values. -/
lemma parallelComposition_prod_mem_iff
    (A B : SetValuedOperator H H) (x u : H) :
    u ∈ ((fst ℝ H H + snd ℝ H H) ▷ (A × B)) x ↔
      ∃ y z : H, y + z = x ∧ u ∈ A y ∧ u ∈ B z := by
  -- Rewrite the parallel composition using the textbook witness form from Definition 25.39.
  rw [mem_parallelComposition_iff]
  constructor
  · rintro ⟨p, hp, hu⟩
    -- Replace the adjoint by the diagonal map and split product membership componentwise.
    have hp' : p.1 + p.2 = x := by
      simpa only [add_apply, coe_fst', coe_snd'] using hp
    have hu_diag : (u, u) ∈ (A × B) p := by
      simpa only [sum_map_adjoint_eq_diagonal, add_apply, inl_apply, inr_apply, Prod.mk_add_mk,
        add_zero, zero_add] using hu
    have hu_components : u ∈ A p.1 ∧ u ∈ B p.2 :=
      (diag_mem_prod_iff A B p u).1 hu_diag
    exact ⟨p.1, p.2, hp', hu_components.1, hu_components.2⟩
  · rintro ⟨y, z, hsum, huA, huB⟩
    -- Package the two component memberships back into product membership on the diagonal.
    have hu_diag : (u, u) ∈ (A × B) (y, z) :=
      (diag_mem_prod_iff A B (y, z) u).2 ⟨huA, huB⟩
    refine ⟨(y, z), ?_, ?_⟩
    · simpa only [add_apply, coe_fst', coe_snd'] using hsum
    · simpa only [sum_map_adjoint_eq_diagonal, add_apply, inl_apply, inr_apply, Prod.mk_add_mk,
        add_zero, zero_add] using hu_diag

/-- Example 25.40: on the explicit Chapter 9 raw-product `ℓ²` Hilbert structure on `H × H`, the
parallel composition of the componentwise product operator `(x, y) ↦ A x × B y` by the sum map
`(x, y) ↦ x + y` is the parallel sum `A □ B`. -/
theorem parallelComposition_prod_eq_parallelSum
    (A B : SetValuedOperator H H) :
    (fst ℝ H H + snd ℝ H H) ▷ (A × B) = A □ B := by
  ext x u
  -- Compare both operators pointwise by translating them into the same witness data.
  rw [parallelComposition_prod_mem_iff, SetValuedOperator.mem_parallelSum_iff]
  change (∃ y z : H, y + z = x ∧ u ∈ A y ∧ u ∈ B z) ↔ x ∈ A⁻¹ u + B⁻¹ u
  constructor
  · rintro ⟨y, z, hsum, huA, huB⟩
    -- Convert the component memberships into inverse memberships and then into set addition.
    have hy : y ∈ A⁻¹ u := (SetValuedOperator.mem_inverse_iff A u y).2 huA
    have hz : z ∈ B⁻¹ u := (SetValuedOperator.mem_inverse_iff B u z).2 huB
    exact Set.mem_add.2 ⟨y, hy, z, hz, hsum⟩
  · intro hx
    -- Unpack a set-sum witness and translate inverse membership back to the original operators.
    rcases Set.mem_add.1 hx with ⟨y, hy, z, hz, hsum⟩
    have huA : u ∈ A y := (SetValuedOperator.mem_inverse_iff A u y).1 hy
    have huB : u ∈ B z := (SetValuedOperator.mem_inverse_iff B u z).1 hz
    exact ⟨y, z, hsum, huA, huB⟩

end ContinuousLinearMap
