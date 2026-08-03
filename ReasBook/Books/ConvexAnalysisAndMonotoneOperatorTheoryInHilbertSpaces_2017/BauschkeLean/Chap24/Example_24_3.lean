import BauschkeLean.Chap24.Example_24_2

-- Semantic recall note: `lean_leansearch` surfaced only generic adjoint/self-composition lemmas,
-- so this item follows the local quadratic-affine owner from `Chap24/Example_24_2.lean` together
-- with the project's canonical `Γ₀(H)` / `Prox[f, hf]` surface.

open scoped BigOperators InnerProductSpace

universe u v w

namespace ERealFunction

noncomputable section

section HilbertFamilies

variable {I : Type v} [Fintype I]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {K : I → Type w}
variable [∀ i, NormedAddCommGroup (K i)]
variable [∀ i, InnerProductSpace ℝ (K i)]
variable [∀ i, CompleteSpace (K i)]

/-- The weighted least-squares functional from Example 24.3,
`x ↦ (1 / 2) ∑ i, λᵢ ‖Lᵢ x - rᵢ‖²`. -/
def example_24_3_function (lam : I → Set.Ioi (0 : ℝ))
    (L : ∀ i, H →L[ℝ] K i) (r : ∀ i, K i) : H → Set.Ioi (⊥ : EReal) :=
  (fun x ↦ (1 / 2 : ℝ) * ∑ i, (lam i : ℝ) * ‖L i x - r i‖ ^ 2).toEReal

omit [CompleteSpace H] [∀ i, CompleteSpace (K i)] in
/-- Coercing the weighted least-squares owner back to `EReal` recovers its defining real
expression. -/
@[simp] theorem example_24_3_function_apply
    (lam : I → Set.Ioi (0 : ℝ)) (L : ∀ i, H →L[ℝ] K i) (r : ∀ i, K i) (x : H) :
    (example_24_3_function lam L r x : EReal) =
      (((1 / 2 : ℝ) * ∑ i, (lam i : ℝ) * ‖L i x - r i‖ ^ 2 : ℝ) : EReal) := by
  simp [example_24_3_function]

omit [CompleteSpace H] [∀ i, CompleteSpace (K i)] in
/-- The real-valued representative of Example 24.3 is exactly its defining weighted least-squares
expression. -/
@[simp] theorem example_24_3_function_toReal
    (lam : I → Set.Ioi (0 : ℝ)) (L : ∀ i, H →L[ℝ] K i) (r : ∀ i, K i) (x : H) :
    (example_24_3_function lam L r x : EReal).toReal =
      (1 / 2 : ℝ) * ∑ i, (lam i : ℝ) * ‖L i x - r i‖ ^ 2 := by
  simpa using
    (EReal.toReal_coe ((1 / 2 : ℝ) * ∑ i, (lam i : ℝ) * ‖L i x - r i‖ ^ 2))

/-- The positive self-adjoint operator `∑ i, λᵢ Lᵢ* Lᵢ` appearing in Example 24.3. -/
def example_24_3_linear_part (lam : I → Set.Ioi (0 : ℝ))
    (L : ∀ i, H →L[ℝ] K i) : H →L[ℝ] H :=
  ∑ i, (lam i : ℝ) • ((L i).adjoint.comp (L i))

/-- Helper for Example 24.3: the quadratic form of the weighted normal operator is the weighted
sum of squared norms `‖Lᵢ x‖²`. -/
theorem example_24_3_linear_part_inner_eq_sum_norm_sq
    (lam : I → Set.Ioi (0 : ℝ)) (L : ∀ i, H →L[ℝ] K i) (x : H) :
    ⟪example_24_3_linear_part lam L x, x⟫_ℝ = ∑ i, (lam i : ℝ) * ‖L i x‖ ^ 2 := by
  -- Expand the weighted sum and rewrite each Gram term as a squared norm.
  calc
    ⟪example_24_3_linear_part lam L x, x⟫_ℝ
        = ∑ i, ⟪((lam i : ℝ) • ((L i).adjoint.comp (L i)) x), x⟫_ℝ := by
            simp [example_24_3_linear_part, sum_inner]
    _ = ∑ i, (lam i : ℝ) * ⟪((L i).adjoint.comp (L i)) x, x⟫_ℝ := by
          simp [real_inner_smul_left]
    _ = ∑ i, (lam i : ℝ) * ‖L i x‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [show ⟪((L i).adjoint.comp (L i) x), x⟫_ℝ = ‖L i x‖ ^ 2 by
            simpa [ContinuousLinearMap.comp_apply] using
              ((L i).apply_norm_sq_eq_inner_adjoint_left x).symm]

/-- The weighted normal operator from Example 24.3 is self-adjoint. -/
theorem example_24_3_linear_part_isSelfAdjoint
    (lam : I → Set.Ioi (0 : ℝ)) (L : ∀ i, H →L[ℝ] K i) :
    IsSelfAdjoint (example_24_3_linear_part lam L) := by
  -- Each summand `λᵢ Lᵢ†Lᵢ` is symmetric, so the whole weighted sum is symmetric.
  refine LinearMap.IsSymmetric.isSelfAdjoint ?_
  intro x y
  calc
    ⟪example_24_3_linear_part lam L x, y⟫_ℝ
        = ∑ i, ⟪(lam i : ℝ) • ((L i).adjoint ((L i) x)), y⟫_ℝ := by
            simp [example_24_3_linear_part, sum_inner]
    _ = ∑ i, (lam i : ℝ) * ⟪L i x, L i y⟫_ℝ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          calc
            ⟪(lam i : ℝ) • ((L i).adjoint ((L i) x)), y⟫_ℝ
                = (lam i : ℝ) * ⟪(L i).adjoint ((L i) x), y⟫_ℝ := by
                    rw [real_inner_smul_left]
            _ = (lam i : ℝ) * ⟪L i x, L i y⟫_ℝ := by
                  rw [ContinuousLinearMap.adjoint_inner_left]
    _ = ∑ i, (lam i : ℝ) * ⟪L i y, L i x⟫_ℝ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [real_inner_comm]
    _ = ∑ i, ⟪x, (lam i : ℝ) • ((L i).adjoint ((L i) y))⟫_ℝ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          calc
            (lam i : ℝ) * ⟪L i y, L i x⟫_ℝ
                = (lam i : ℝ) * ⟪L i x, L i y⟫_ℝ := by
                    rw [real_inner_comm]
            _ = (lam i : ℝ) * ⟪x, (L i).adjoint ((L i) y)⟫_ℝ := by
                  rw [ContinuousLinearMap.adjoint_inner_right]
            _ = ⟪x, (lam i : ℝ) • ((L i).adjoint ((L i) y))⟫_ℝ := by
                  rw [real_inner_smul_right]
    _ = ⟪x, example_24_3_linear_part lam L y⟫_ℝ := by
          symm
          simpa [example_24_3_linear_part] using
            (inner_sum
              (s := Finset.univ)
              (f := fun i ↦ (lam i : ℝ) • ((L i).adjoint ((L i) y)))
              x)

/-- The weighted normal operator from Example 24.3 is monotone. -/
theorem example_24_3_linear_part_isMonotone
    (lam : I → Set.Ioi (0 : ℝ)) (L : ∀ i, H →L[ℝ] K i) :
    (example_24_3_linear_part lam L).toLinearMap.IsMonotone := by
  intro x
  -- The quadratic form is a sum of nonnegative weighted squared norms.
  have hsum_nonneg : 0 ≤ ∑ i, (lam i : ℝ) * ‖L i x‖ ^ 2 := by
    refine Finset.sum_nonneg ?_
    intro i hi
    have hlam : 0 ≤ (lam i : ℝ) := (lam i).2.le
    have hnorm : 0 ≤ ‖L i x‖ ^ 2 := by
      nlinarith [norm_nonneg (L i x)]
    exact mul_nonneg hlam hnorm
  simpa [example_24_3_linear_part_inner_eq_sum_norm_sq lam L x] using hsum_nonneg

/-- The linear term `- ∑ i, λᵢ Lᵢ* rᵢ` appearing in Example 24.3. -/
def example_24_3_linear_term (lam : I → Set.Ioi (0 : ℝ))
    (L : ∀ i, H →L[ℝ] K i) (r : ∀ i, K i) : H :=
  -∑ i, (lam i : ℝ) • ((L i).adjoint (r i))

/-- The constant term `∑ i, λᵢ ‖rᵢ‖² / 2` appearing in Example 24.3. -/
def example_24_3_constant_term (lam : I → Set.Ioi (0 : ℝ))
    (r : ∀ i, K i) : ℝ :=
  ∑ i, (lam i : ℝ) * ‖r i‖ ^ 2 / 2

/-- Rewriting the weighted least-squares functional in the quadratic-affine form used in
Example 24.2. -/
theorem example_24_3_function_eq_example_24_2_function
    (lam : I → Set.Ioi (0 : ℝ)) (L : ∀ i, H →L[ℝ] K i) (r : ∀ i, K i) :
    example_24_3_function lam L r =
      example_24_2_function
        (example_24_3_linear_part lam L)
        (example_24_3_linear_term lam L r)
        (example_24_3_constant_term lam r) := by
  ext x
  -- Rewrite the quadratic term as the weighted sum of `‖Lᵢ x‖²`.
  have hquad :
      ⟪example_24_3_linear_part lam L x, x⟫_ℝ =
        ∑ i, (lam i : ℝ) * ‖L i x‖ ^ 2 :=
    example_24_3_linear_part_inner_eq_sum_norm_sq lam L x
  -- Rewrite the affine term through the adjoint identity `⟪x, Lᵢ† rᵢ⟫ = ⟪Lᵢ x, rᵢ⟫`.
  have hlin :
      ⟪x, example_24_3_linear_term lam L r⟫_ℝ =
        -∑ i, (lam i : ℝ) * ⟪L i x, r i⟫_ℝ := by
    calc
      ⟪x, example_24_3_linear_term lam L r⟫_ℝ
          = ⟪x, -∑ i, (lam i : ℝ) • ((L i).adjoint (r i))⟫_ℝ := rfl
      _ = -∑ i, (lam i : ℝ) * ⟪x, (L i).adjoint (r i)⟫_ℝ := by
            rw [inner_neg_right, inner_sum]
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [real_inner_smul_right]
      _ = -∑ i, (lam i : ℝ) * ⟪L i x, r i⟫_ℝ := by
            refine congrArg Neg.neg ?_
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [ContinuousLinearMap.adjoint_inner_right]
  -- Expand each squared norm and regroup the finite sums into the Example 24.2 owner.
  change
    (((1 / 2 : ℝ) * ∑ i, (lam i : ℝ) * ‖L i x - r i‖ ^ 2 : ℝ) : EReal) =
      (((1 / 2 : ℝ) * ⟪example_24_3_linear_part lam L x, x⟫_ℝ
          + ⟪x, example_24_3_linear_term lam L r⟫_ℝ
          + example_24_3_constant_term lam r : ℝ) : EReal)
  congr 1
  rw [hquad, hlin, example_24_3_constant_term]
  calc
    (1 / 2 : ℝ) * ∑ i, (lam i : ℝ) * ‖L i x - r i‖ ^ 2
        = ∑ i, ((1 / 2 : ℝ) * ((lam i : ℝ) * ‖L i x‖ ^ 2)
            - (lam i : ℝ) * ⟪L i x, r i⟫_ℝ
            + (lam i : ℝ) * ‖r i‖ ^ 2 / 2) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [norm_sub_sq_real]
              ring
    _ = (1 / 2 : ℝ) * ∑ i, (lam i : ℝ) * ‖L i x‖ ^ 2
          + -∑ i, (lam i : ℝ) * ⟪L i x, r i⟫_ℝ
          + ∑ i, (lam i : ℝ) * ‖r i‖ ^ 2 / 2 := by
            rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
              ← Finset.sum_add_distrib]
            simp [sub_eq_add_neg, add_comm]

/-- Example 24.3 (1): for a finite family of Hilbert spaces `Kᵢ`, vectors `rᵢ ∈ Kᵢ`,
bounded linear maps `Lᵢ : H → Kᵢ`, and positive weights `λᵢ`, the weighted least-squares
functional `x ↦ (1 / 2) ∑ i, λᵢ ‖Lᵢ x - rᵢ‖²` belongs to `Γ₀(H)`. -/
theorem example_24_3_function_mem_gammaZero
    (lam : I → Set.Ioi (0 : ℝ)) (L : ∀ i, H →L[ℝ] K i) (r : ∀ i, K i) :
    example_24_3_function lam L r ∈ Γ₀(H) := by
  rw [example_24_3_function_eq_example_24_2_function]
  exact
    example_24_2_function_mem_gammaZero
      (example_24_3_linear_part lam L)
      (example_24_3_linear_part_isSelfAdjoint lam L)
      (example_24_3_linear_part_isMonotone lam L)
      (example_24_3_linear_term lam L r)
      (example_24_3_constant_term lam r)

/-- A point is proximal for Example 24.3 exactly when it satisfies the weighted normal-equation
resolvent formula. -/
theorem isProxPoint_example_24_3_function_iff_eq_inverse_add_weighted_adjoint
    (lam : I → Set.Ioi (0 : ℝ)) (L : ∀ i, H →L[ℝ] K i) (r : ∀ i, K i) {x p : H} :
    IsProxPoint (example_24_3_function lam L r) x p ↔
      p = (((1 : H →L[ℝ] H) + example_24_3_linear_part lam L).inverse)
        (x + ∑ i, (lam i : ℝ) • ((L i).adjoint (r i))) := by
  rw [example_24_3_function_eq_example_24_2_function]
  simpa [example_24_3_linear_term, sub_eq_add_neg, add_comm] using
    (isProxPoint_example_24_2_function_iff_eq_inverse_sub
      (example_24_3_linear_part lam L)
      (example_24_3_linear_part_isSelfAdjoint lam L)
      (example_24_3_linear_part_isMonotone lam L)
      (example_24_3_linear_term lam L r)
      (example_24_3_constant_term lam r))

/-- Any chosen proximity operator for the weighted least-squares owner agrees with the weighted
normal-equation resolvent. -/
theorem proximityOperator_example_24_3_function_eq_inverse_add_weighted_adjoint
    (lam : I → Set.Ioi (0 : ℝ)) (L : ∀ i, H →L[ℝ] K i) (r : ∀ i, K i)
    (hprox : HasUniqueProxPoint (example_24_3_function lam L r)) (x : H) :
    proximityOperator (example_24_3_function lam L r) hprox x =
      (((1 : H →L[ℝ] H) + example_24_3_linear_part lam L).inverse)
        (x + ∑ i, (lam i : ℝ) • ((L i).adjoint (r i))) := by
  rw [← isProxPoint_example_24_3_function_iff_eq_inverse_add_weighted_adjoint lam L r]
  exact proximityOperator_isProxPoint (example_24_3_function lam L r) hprox x

/-- Example 24.3 (2): the proximity operator of the weighted least-squares functional is
`(Id + ∑ i, λᵢ Lᵢ* Lᵢ)⁻¹ (x + ∑ i, λᵢ Lᵢ* rᵢ)`. -/
theorem prox_example_24_3_function_eq_inverse_add_weighted_adjoint
    (lam : I → Set.Ioi (0 : ℝ)) (L : ∀ i, H →L[ℝ] K i) (r : ∀ i, K i) (x : H) :
    Prox[example_24_3_function lam L r, example_24_3_function_mem_gammaZero lam L r] x =
      (((1 : H →L[ℝ] H) + example_24_3_linear_part lam L).inverse)
        (x + ∑ i, (lam i : ℝ) • ((L i).adjoint (r i))) := by
  simpa using
    proximityOperator_example_24_3_function_eq_inverse_add_weighted_adjoint
      lam L r
      (hasUniqueProxPoint_of_mem_gammaZero
        (example_24_3_function lam L r)
        (example_24_3_function_mem_gammaZero lam L r))
      x

end HilbertFamilies

end

end ERealFunction
