import BauschkeLean.Chap01.Text_1_0_9
import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap25.Definition_25_29
import BauschkeLean.Chap25.Proposition_25_30

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Domain-style sampling:
-- * `source-facing`: the Chapter 25 parallel sum `□`.
-- * `core/canonical`: the set-valued-operator owners `comp`, `inverse`, and pointwise addition.
-- * `bridge/view`: the canonical singleton-valued operator attached to the underlying function of
--   the linear map `B`, written in object-prefix form as `(B : H → H).toSetValuedOperator`.
-- Semantic recall note: `lean_leansearch` did not surface a canonical owner for this identity.
-- The source proof block for equation `(25.33)` works in a real Hilbert space, so this item keeps
-- the textbook ambient even though the operator identity itself is written through Chapter 25's
-- canonical `□`, `comp`, and singleton-valued-function owners.

/-- Helper for Proposition 25.31: membership in the parallel sum with the singleton-valued
operator attached to `B` is equivalent to the source-facing witness condition
`∃ y, u ∈ A y ∧ u = B (x - y)`. -/
private theorem mem_parallelSum_linearMap_iff_exists_mem
    (A : SetValuedOperator H H) (B : H →ₗ[ℝ] H) (x u : H) :
    u ∈ (A □ (B : H → H).toSetValuedOperator) x ↔
      ∃ y : H, u ∈ A y ∧ u = B (x - y) := by
  constructor
  · intro hu
    -- Normalize parallel-sum membership with Proposition 25.30, then collapse the singleton
    -- witness contributed by the function-valued operator of `B`.
    rcases
        (mem_parallelSum_iff_exists_mem_inverse A ((B : H → H).toSetValuedOperator) x u).1 hu with
      ⟨y, hy, hz⟩
    refine ⟨y, (SetValuedOperator.mem_inverse_iff A u y).1 hy, ?_⟩
    have hz' : u ∈ ((B : H → H).toSetValuedOperator) (x - y) :=
      (SetValuedOperator.mem_inverse_iff ((B : H → H).toSetValuedOperator) u (x - y)).1 hz
    simpa [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] using hz'
  · rintro ⟨y, hy, hz⟩
    -- Repackage the same witness `y` back into the inverse-membership form of Proposition 25.30.
    refine (mem_parallelSum_iff_exists_mem_inverse A ((B : H → H).toSetValuedOperator) x u).2 ?_
    refine ⟨y, (SetValuedOperator.mem_inverse_iff A u y).2 hy, ?_⟩
    refine (SetValuedOperator.mem_inverse_iff ((B : H → H).toSetValuedOperator) u (x - y)).2 ?_
    simpa [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] using hz

/-- Helper for Proposition 25.31: the composed right-hand side reduces to choosing a witness
`y` with `u ∈ A y` and `B x ∈ (A + B) y`. -/
private theorem mem_comp_inverse_add_linearMap_iff_exists_mem
    (A : SetValuedOperator H H) (B : H →ₗ[ℝ] H) (x u : H) :
    u ∈ ((A.comp ((A + (B : H → H).toSetValuedOperator)⁻¹)).comp
        ((B : H → H).toSetValuedOperator)) x ↔
      ∃ y : H, u ∈ A y ∧ B x ∈ (A + (B : H → H).toSetValuedOperator) y := by
  -- Unfold the outer composition first; the singleton-valued operator fixes the intermediate
  -- point to `B x`.
  rw [SetValuedOperator.mem_comp]
  simp only [Function.toSetValuedOperator_apply, Set.mem_singleton_iff, exists_eq_left]
  -- Unfold the remaining composition so the inverse-membership witness appears explicitly.
  rw [SetValuedOperator.mem_comp]
  constructor
  · rintro ⟨y, hy, hu⟩
    exact ⟨y, hu, (SetValuedOperator.mem_inverse_iff
      (A + (B : H → H).toSetValuedOperator) (B x) y).1 hy⟩
  · rintro ⟨y, hy, hu⟩
    exact ⟨y, (SetValuedOperator.mem_inverse_iff
      (A + (B : H → H).toSetValuedOperator) (B x) y).2 hu, hy⟩

/-- Helper for Proposition 25.31: once `u ∈ A y` is fixed and `A` is at most single-valued,
membership of `B x` in `(A + B) y` is equivalent to the equality `B x = u + B y`. -/
private theorem mem_add_linearMapOperator_iff
    (A : SetValuedOperator H H) (B : H →ₗ[ℝ] H) (hA : A.IsAtMostSingleValued)
    {x y u : H} (hu : u ∈ A y) :
    B x ∈ (A + (B : H → H).toSetValuedOperator) y ↔ B x = u + B y := by
  constructor
  · intro hx
    -- Expand sum-membership, then collapse the `A y` witness by `hA` and the `B y` witness by
    -- singleton simplification.
    rcases Set.mem_add.1 hx with ⟨a, ha, b, hb, hab⟩
    have ha' : a = u := (hA y) ha hu
    have hb' : b = B y := by
      simpa [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] using hb
    calc
      B x = a + b := hab.symm
      _ = u + b := by rw [ha']
      _ = u + B y := by rw [hb']
  · intro hx
    -- Build the sum witness directly from the chosen value `u ∈ A y` and the singleton value
    -- `B y` contributed by the linear map.
    refine Set.mem_add.2 ⟨u, hu, B y, ?_, hx.symm⟩
    simp [Function.toSetValuedOperator_apply]

/-- Helper for Proposition 25.31: the additive normal form `B x = u + B y` is equivalent to the
source-facing subtraction form `u = B (x - y)`. -/
private theorem linearMap_eq_add_iff_eq_sub
    (B : H →ₗ[ℝ] H) (x y u : H) :
    B x = u + B y ↔ u = B (x - y) := by
  constructor
  · intro hx
    -- Move `B y` to the other side, then rewrite the difference through linearity.
    have hsub : u = B x - B y := by
      rw [eq_sub_iff_add_eq]
      simpa using hx.symm
    simpa [B.map_sub] using hsub
  · intro hx
    -- Rewrite the subtraction image back to `B x - B y` and convert it to the sum form.
    have hsub : u = B x - B y := by
      simpa [B.map_sub] using hx
    rw [eq_sub_iff_add_eq] at hsub
    exact hsub.symm

/-- Proposition 25.31: if `A` is at most single-valued and `B` is linear, then
`A □ B = A(A + B)⁻¹B`, represented here by the canonical singleton-valued operator associated
with the underlying function of `B`. This is equation `(25.33)`. -/
theorem parallelSum_eq_comp_inverse_add_comp_of_isAtMostSingleValued
    (A : SetValuedOperator H H) (B : H →ₗ[ℝ] H) (hA : A.IsAtMostSingleValued) :
    A □ (B : H → H).toSetValuedOperator =
      (A.comp ((A + (B : H → H).toSetValuedOperator)⁻¹)).comp
        ((B : H → H).toSetValuedOperator) := by
  ext x u
  -- Normalize the left-hand side and the right-hand side to the same witness parameter `y`.
  rw [mem_parallelSum_linearMap_iff_exists_mem, mem_comp_inverse_add_linearMap_iff_exists_mem]
  constructor
  · rintro ⟨y, hy, hyu⟩
    -- Convert the source-facing subtraction form into the sum-membership condition needed on the
    -- composed right-hand side.
    refine ⟨y, hy, ?_⟩
    exact (mem_add_linearMapOperator_iff A B hA hy).2
      ((linearMap_eq_add_iff_eq_sub B x y u).2 hyu)
  · rintro ⟨y, hy, hyBx⟩
    -- Collapse the right-hand side sum-membership back to `B x = u + B y`, then rewrite it as
    -- `u = B (x - y)` to recover the source-facing left-hand side normal form.
    refine ⟨y, hy, ?_⟩
    exact (linearMap_eq_add_iff_eq_sub B x y u).1
      ((mem_add_linearMapOperator_iff A B hA hy).1 hyBx)

end SetValuedOperator
