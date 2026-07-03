

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_3_7 (from Chap01) -/
universe u

variable {R : Type*}
variable [DivisionSemiring R] [PartialOrder R] [AddLeftStrictMono R]
  [PosMulReflectLT R]
variable {E : Type u}
variable [AddCommMonoid E] [Module R E]
local instance : PosMulStrictMono R := PosMulReflectLT.toPosMulStrictMono R

open scoped Pointwise
open scoped Rockafellar

section

/-
Source/core/bridge triage:
- `source-facing`: Theorem 3.7 states that the inverse addition `C₁ #[R] C₂` of two convex
  subsets is convex.
- `core/canonical`: the owner abstraction is the predicate `Convex R` on subsets of the ambient
  module.
- `bridge/view`: the inverse addition itself is already the source-facing owner operation
  `inverseAddition`; once Text 3.6.1 is kept source-faithful with strict coefficients, the
  canonical proof route is the direct strict-convexity criterion `convex_iff_forall_pos`
  together with `Set.mem_inverseAddition_primitive_iff` and the pointwise scalar-action API.
- Primitive data vs derived API: the sets `C₁` and `C₂` and their convexity hypotheses are
  primitive; the conclusion is the derived convexity of the existing operation `inverseAddition`.
- Domain-style sampling: this item is guided by the owner declaration `inverseAddition` from
  Text 3.6.1, the primitive membership theorem
  `Set.mem_inverseAddition_primitive_iff`, mathlib's strict
  convexity criterion `convex_iff_forall_pos`, and the standard pointwise-set API
  `Set.mem_smul_set`.
- Layer target: `source-facing`; the theorem keeps the strict source-facing owner
  `inverseAddition` and proves convexity directly by recombining the two strict witnesses inside
  each convex input set.
-/

/-- Theorem 3.7: if `C₁` and `C₂` are convex subsets, then their inverse addition
`C₁ #[R] C₂` is convex. -/
-- Proof sketch: use `convex_iff_forall_pos` and the primitive owner form
-- `Set.mem_inverseAddition_primitive_iff`. A point of `C₁ #[R] C₂` has strict positive
-- coefficients
-- `t₁,t₂` summing to `1`. For a strict convex combination `a • x + b • y`, recombine first and
-- second coefficients separately:
-- `u₁ = a * tx₁ + b * ty₁`, `u₂ = a * tx₂ + b * ty₂`. Then `u₁ + u₂ = 1`, and each component is
-- normalized inside `C₁` and `C₂` using convexity.
theorem Convex.inverseAddition {C₁ C₂ : Set E}
    (hC₁ : Convex R C₁) (hC₂ : Convex R C₂) :
    Convex R (C₁ #[R] C₂) := by
  refine convex_iff_forall_pos.2 ?_
  intro x hx y hy a b ha hb hab
  rcases (Set.mem_inverseAddition_primitive_iff C₁ C₂ x).1 hx with
    ⟨tx₁, tx₂, htx₁, htx₂, htxsum, hx⟩
  rcases (Set.mem_inverseAddition_primitive_iff C₁ C₂ y).1 hy with
    ⟨ty₁, ty₂, hty₁, hty₂, htysum, hy⟩
  rcases hx with ⟨hx₁, hx₂⟩
  rcases hy with ⟨hy₁, hy₂⟩
  rcases Set.mem_smul_set.mp hx₁ with ⟨x₁, hx₁C, hx₁eq⟩
  rcases Set.mem_smul_set.mp hx₂ with ⟨x₂, hx₂C, hx₂eq⟩
  rcases Set.mem_smul_set.mp hy₁ with ⟨y₁, hy₁C, hy₁eq⟩
  rcases Set.mem_smul_set.mp hy₂ with ⟨y₂, hy₂C, hy₂eq⟩
  let t₁ : R := a * tx₁ + b * ty₁
  let t₂ : R := a * tx₂ + b * ty₂
  have ht₁_pos : 0 < t₁ := by
    dsimp [t₁]
    exact add_pos (mul_pos ha htx₁) (mul_pos hb hty₁)
  have ht₂_pos : 0 < t₂ := by
    dsimp [t₂]
    exact add_pos (mul_pos ha htx₂) (mul_pos hb hty₂)
  have htsum : t₁ + t₂ = 1 := by
    calc
      t₁ + t₂ = (a * tx₁ + b * ty₁) + (a * tx₂ + b * ty₂) := by rfl
      _ = (a * tx₁ + a * tx₂) + (b * ty₁ + b * ty₂) := by
        simp [add_left_comm, add_assoc]
      _ = a * (tx₁ + tx₂) + b * (ty₁ + ty₂) := by
        rw [← mul_add, ← mul_add]
      _ = a * 1 + b * 1 := by rw [htxsum, htysum]
      _ = 1 := by simpa [mul_one] using hab
  refine (Set.mem_inverseAddition_primitive_iff C₁ C₂ _).2 ⟨t₁, t₂, ht₁_pos, ht₂_pos, htsum, ?_⟩
  constructor
  · let α₁ : R := t₁⁻¹ * (a * tx₁)
    let β₁ : R := t₁⁻¹ * (b * ty₁)
    have hα₁_nonneg : 0 ≤ α₁ := (mul_pos (inv_pos.mpr ht₁_pos) (mul_pos ha htx₁)).le
    have hβ₁_nonneg : 0 ≤ β₁ := (mul_pos (inv_pos.mpr ht₁_pos) (mul_pos hb hty₁)).le
    have hα₁β₁ : α₁ + β₁ = 1 := by
      calc
        α₁ + β₁ = t₁⁻¹ * (a * tx₁) + t₁⁻¹ * (b * ty₁) := by
          rfl
        _ = t₁⁻¹ * (a * tx₁ + b * ty₁) := by rw [mul_add]
        _ = t₁⁻¹ * t₁ := by rw [show a * tx₁ + b * ty₁ = t₁ by rfl]
        _ = 1 := inv_mul_cancel₀ (ne_of_gt ht₁_pos)
    have hα₁_coeff : t₁ * α₁ = a * tx₁ := by
      calc
        t₁ * α₁ = t₁ * (t₁⁻¹ * (a * tx₁)) := by rfl
        _ = (t₁ * t₁⁻¹) * (a * tx₁) := by rw [mul_assoc]
        _ = a * tx₁ := by rw [mul_inv_cancel₀ (ne_of_gt ht₁_pos), one_mul]
    have hβ₁_coeff : t₁ * β₁ = b * ty₁ := by
      calc
        t₁ * β₁ = t₁ * (t₁⁻¹ * (b * ty₁)) := by rfl
        _ = (t₁ * t₁⁻¹) * (b * ty₁) := by rw [mul_assoc]
        _ = b * ty₁ := by rw [mul_inv_cancel₀ (ne_of_gt ht₁_pos), one_mul]
    have hmem₁ : α₁ • x₁ + β₁ • y₁ ∈ C₁ :=
      hC₁ hx₁C hy₁C hα₁_nonneg hβ₁_nonneg hα₁β₁
    refine Set.mem_smul_set.mpr ⟨α₁ • x₁ + β₁ • y₁, hmem₁, ?_⟩
    calc
      t₁ • (α₁ • x₁ + β₁ • y₁) = (t₁ * α₁) • x₁ + (t₁ * β₁) • y₁ := by
        rw [smul_add, smul_smul, smul_smul]
      _ = (a * tx₁) • x₁ + (b * ty₁) • y₁ := by
        rw [hα₁_coeff, hβ₁_coeff]
      _ = a • x + b • y := by
        calc
          (a * tx₁) • x₁ + (b * ty₁) • y₁ = a • (tx₁ • x₁) + b • (ty₁ • y₁) := by
            rw [smul_smul, smul_smul]
          _ = a • x + b • y := by rw [hx₁eq, hy₁eq]
  · let α₂ : R := t₂⁻¹ * (a * tx₂)
    let β₂ : R := t₂⁻¹ * (b * ty₂)
    have hα₂_nonneg : 0 ≤ α₂ := (mul_pos (inv_pos.mpr ht₂_pos) (mul_pos ha htx₂)).le
    have hβ₂_nonneg : 0 ≤ β₂ := (mul_pos (inv_pos.mpr ht₂_pos) (mul_pos hb hty₂)).le
    have hα₂β₂ : α₂ + β₂ = 1 := by
      calc
        α₂ + β₂ = t₂⁻¹ * (a * tx₂) + t₂⁻¹ * (b * ty₂) := by
          rfl
        _ = t₂⁻¹ * (a * tx₂ + b * ty₂) := by rw [mul_add]
        _ = t₂⁻¹ * t₂ := by rw [show a * tx₂ + b * ty₂ = t₂ by rfl]
        _ = 1 := inv_mul_cancel₀ (ne_of_gt ht₂_pos)
    have hα₂_coeff : t₂ * α₂ = a * tx₂ := by
      calc
        t₂ * α₂ = t₂ * (t₂⁻¹ * (a * tx₂)) := by rfl
        _ = (t₂ * t₂⁻¹) * (a * tx₂) := by rw [mul_assoc]
        _ = a * tx₂ := by rw [mul_inv_cancel₀ (ne_of_gt ht₂_pos), one_mul]
    have hβ₂_coeff : t₂ * β₂ = b * ty₂ := by
      calc
        t₂ * β₂ = t₂ * (t₂⁻¹ * (b * ty₂)) := by rfl
        _ = (t₂ * t₂⁻¹) * (b * ty₂) := by rw [mul_assoc]
        _ = b * ty₂ := by rw [mul_inv_cancel₀ (ne_of_gt ht₂_pos), one_mul]
    have hmem₂ : α₂ • x₂ + β₂ • y₂ ∈ C₂ :=
      hC₂ hx₂C hy₂C hα₂_nonneg hβ₂_nonneg hα₂β₂
    refine Set.mem_smul_set.mpr ⟨α₂ • x₂ + β₂ • y₂, hmem₂, ?_⟩
    calc
      t₂ • (α₂ • x₂ + β₂ • y₂) = (t₂ * α₂) • x₂ + (t₂ * β₂) • y₂ := by
        rw [smul_add, smul_smul, smul_smul]
      _ = (a * tx₂) • x₂ + (b * ty₂) • y₂ := by
        rw [hα₂_coeff, hβ₂_coeff]
      _ = a • x + b • y := by
        calc
          (a * tx₂) • x₂ + (b * ty₂) • y₂ = a • (tx₂ • x₂) + b • (ty₂ • y₂) := by
            rw [smul_smul, smul_smul]
          _ = a • x + b • y := by rw [hx₂eq, hy₂eq]

/-- Theorem 3.7: if `C₁` and `C₂` are convex subsets, then their inverse addition
`C₁ #[R] C₂` is convex. -/
theorem convex_inverseAddition {C₁ C₂ : Set E} (hC₁ : Convex R C₁) (hC₂ : Convex R C₂) :
    Convex R (C₁ #[R] C₂) :=
  hC₁.inverseAddition hC₂

end
