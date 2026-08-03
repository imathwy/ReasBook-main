import BauschkeLean.Chap14.Corollary_14_8
import BauschkeLean.Chap24.Proposition_24_56

open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

noncomputable section

section QuadraticPerspectiveFormula

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

-- Semantic recall/domain sampling: the owner abstraction here is the Chapter 9 closed
-- perspective specialized to `halfSquaredNorm`, and the proximal-map owner is the Chapter 24
-- `closedPerspective` API from Proposition 24.56. The explicit quadratic formula `(24.112)` is
-- therefore a source-facing bridge, not a second owner.

/- Source/core/bridge triage:
- `source-facing`: Example 24.57 studies the proximal map of the quadratic perspective `(24.112)`
  and the depressed cubic `(24.115)`.
- `core/canonical`: the owner declarations are `closedPerspective`, `halfSquaredNorm`, and the
  Chapter 24 scaled-proximal formulas from Proposition 24.56.
- `bridge/view`: the following branch lemmas identify the canonical owner with the source-facing
  formula `(24.112)` without introducing a second public evaluator. -/

private theorem halfSquaredNorm_recession_zero :
    (recessionFunction (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))
      halfSquaredNorm_mem_gammaZero.2.nonempty (0 : H) : EReal) = 0 := by
  rw [recessionFunction_apply]
  have himage :
      ((fun y : H ↦
          (halfSquaredNorm (y + 0) : EReal) - (halfSquaredNorm y : EReal)) ''
        effectiveDomain (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))) =
        ({0} : Set EReal) := by
    ext a
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy_top : (halfSquaredNorm y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
      have hy_bot : (halfSquaredNorm y : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (halfSquaredNorm y : EReal) from (halfSquaredNorm y).2)
      simpa using EReal.sub_self hy_top hy_bot
    · intro ha
      have hdom :
          (effectiveDomain (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))).Nonempty :=
        halfSquaredNorm_mem_gammaZero.2.nonempty
      rcases hdom with ⟨y, hy⟩
      rw [Set.mem_singleton_iff] at ha
      subst a
      have hy_top : (halfSquaredNorm y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
      have hy_bot : (halfSquaredNorm y : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (halfSquaredNorm y : EReal) from (halfSquaredNorm y).2)
      exact ⟨y, hy, by simpa using EReal.sub_self hy_top hy_bot⟩
  change sSup
      (((fun y : H ↦
          (halfSquaredNorm (y + 0) : EReal) - (halfSquaredNorm y : EReal)) ''
        effectiveDomain (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)))) = 0
  rw [himage]
  simp

private theorem halfSquaredNorm_recession_eq_top_of_ne_zero
    {x : H} (hx : x ≠ 0) :
    (recessionFunction (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))
      halfSquaredNorm_mem_gammaZero.2.nonempty x : EReal) = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro r
  have hnorm_sq_pos : 0 < ‖x‖ ^ (2 : ℕ) := by
    have hnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    positivity
  let t : ℝ := |r| / (‖x‖ ^ (2 : ℕ)) + 1
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have hy :
      t • x ∈ effectiveDomain (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) := by
    rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
    exact EReal.coe_lt_top _
  have hle :
      ((halfSquaredNorm (t • x + x) : EReal) - (halfSquaredNorm (t • x) : EReal)) ≤
        (recessionFunction (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))
          halfSquaredNorm_mem_gammaZero.2.nonempty x : EReal) := by
    rw [recessionFunction_apply]
    exact (isLUB_sSup _).1 ⟨t • x, hy, rfl⟩
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have ht_one_nonneg : 0 ≤ t + 1 := by positivity
  have htx : t • x + x = (t + 1) • x := by
    simpa using (add_smul t 1 x).symm
  have hreal :
      (‖(t + 1) • x‖ ^ (2 : ℕ) / 2 : ℝ) - ‖t • x‖ ^ (2 : ℕ) / 2 =
        (t + 1 / 2) * ‖x‖ ^ (2 : ℕ) := by
    rw [norm_smul, Real.norm_of_nonneg ht_one_nonneg, norm_smul, Real.norm_of_nonneg ht_nonneg]
    ring
  have hincrement :
      ((halfSquaredNorm (t • x + x) : EReal) - (halfSquaredNorm (t • x) : EReal)) =
        (((t + 1 / 2) * ‖x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    rw [htx, halfSquaredNorm_apply, halfSquaredNorm_apply, ← EReal.coe_sub]
    exact congrArg (fun s : ℝ ↦ (s : EReal)) hreal
  have hgt : r < (t + 1 / 2) * ‖x‖ ^ (2 : ℕ) := by
    have hrewrite : (t + 1 / 2) * ‖x‖ ^ (2 : ℕ) = |r| + (3 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) := by
      dsimp [t]
      field_simp [hnorm_sq_pos.ne']
      ring
    rw [hrewrite]
    have hr_abs : r ≤ |r| := le_abs_self r
    nlinarith [hnorm_sq_pos]
  have hgt' : (r : EReal) < (((t + 1 / 2) * ‖x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    exact_mod_cast hgt
  have hle' :
      ((((t + 1 / 2) * ‖x‖ ^ (2 : ℕ) : ℝ) : EReal)) ≤
        (recessionFunction (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))
          halfSquaredNorm_mem_gammaZero.2.nonempty x : EReal) := by
    have hle'' := hle
    rwa [hincrement] at hle''
  exact lt_of_lt_of_le hgt' hle'

/-- On the positive-height branch, the closed perspective of `halfSquaredNorm` is the quadratic
quotient from `(24.112)`. -/
theorem closedPerspective_halfSquaredNorm_apply_of_pos
    (ξ : ℝ) (x : H) (hξ : 0 < ξ) :
    (closedPerspective halfSquaredNorm halfSquaredNorm_mem_gammaZero.2.nonempty (ξ, x) : EReal) =
      (((‖x‖ ^ (2 : ℕ) / (2 * ξ) : ℝ) : EReal)) := by
  rw [closedPerspective_coe]
  rw [closedPerspectiveEReal_apply_of_ne_zero
    halfSquaredNorm halfSquaredNorm_mem_gammaZero.2.nonempty hξ.ne']
  rw [perspective_apply_of_pos _ hξ, halfSquaredNorm_apply]
  have hnorm_smul : ‖ξ⁻¹ • x‖ = ξ⁻¹ * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hξ.le)]
  have hreal :
      ξ * (‖ξ⁻¹ • x‖ ^ (2 : ℕ) / 2) = ‖x‖ ^ (2 : ℕ) / (2 * ξ) := by
    rw [hnorm_smul]
    field_simp [hξ.ne']
  exact_mod_cast hreal

/-- At the origin, the closed perspective of `halfSquaredNorm` is `0`. -/
theorem closedPerspective_halfSquaredNorm_apply_zero_zero :
    (closedPerspective halfSquaredNorm halfSquaredNorm_mem_gammaZero.2.nonempty (0, (0 : H)) :
      EReal) = 0 := by
  rw [closedPerspective_coe, closedPerspectiveEReal_apply_zero, halfSquaredNorm_recession_zero]

/-- On the zero-height slice away from the origin, the closed perspective of `halfSquaredNorm`
is `+∞`. -/
theorem closedPerspective_halfSquaredNorm_apply_zero_of_ne_zero
    (x : H) (hx : x ≠ 0) :
    (closedPerspective halfSquaredNorm halfSquaredNorm_mem_gammaZero.2.nonempty (0, x) : EReal) =
      ⊤ := by
  rw [closedPerspective_coe, closedPerspectiveEReal_apply_zero]
  exact halfSquaredNorm_recession_eq_top_of_ne_zero hx

/-- On negative heights, the closed perspective of `halfSquaredNorm` is `+∞`. -/
theorem closedPerspective_halfSquaredNorm_apply_of_neg
    (ξ : ℝ) (x : H) (hξ : ξ < 0) :
    (closedPerspective halfSquaredNorm halfSquaredNorm_mem_gammaZero.2.nonempty (ξ, x) : EReal) =
      ⊤ := by
  rw [closedPerspective_coe]
  rw [closedPerspectiveEReal_apply_of_ne_zero
    halfSquaredNorm halfSquaredNorm_mem_gammaZero.2.nonempty (ne_of_lt hξ)]
  simp [perspective, le_of_lt hξ]

end QuadraticPerspectiveFormula

section QuadraticPerspectiveExample

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [local instance] scalar_prod_pseudoMetricSpace_l2
attribute [local instance] scalar_prod_normedAddCommGroup_l2
attribute [local instance] scalar_prod_normedSpace_l2
attribute [local instance] scalar_prod_completeSpace_l2
attribute [local instance] scalar_prod_innerProductSpace_l2

/-- Example 24.57 (1): if `2 γ ξ + ‖x‖² ≤ 0`, then the proximal point of the quadratic
perspective `(24.112)` at `(ξ, x)` is `(0, 0)`. -/
theorem scaledProx_quadraticPerspective_eq_zero_of_two_mul_fst_add_norm_sq_nonpos
    (γ : PosReal) (ξ : ℝ) (x : H)
    (htest : 2 * (γ : ℝ) * ξ + ‖x‖ ^ (2 : ℕ) ≤ 0) :
    Prox[γ, closedPerspective halfSquaredNorm halfSquaredNorm_mem_gammaZero.2.nonempty,
      closedPerspective_mem_gammaZero halfSquaredNorm halfSquaredNorm_mem_gammaZero] (ξ, x) =
      (0, 0) := sorry

/-- Example 24.57 (2): on the positive zero-vector slice, the proximal point of the quadratic
perspective `(24.112)` is `(ξ, 0)`. -/
theorem scaledProx_quadraticPerspective_eq_self_of_zero_lt_fst_and_snd_eq_zero
    (γ : PosReal) (ξ : ℝ)
    (hξ : 0 < ξ) :
    Prox[γ, closedPerspective halfSquaredNorm halfSquaredNorm_mem_gammaZero.2.nonempty,
      closedPerspective_mem_gammaZero halfSquaredNorm halfSquaredNorm_mem_gammaZero]
      (ξ, (0 : H)) =
      (ξ, 0) := sorry

/-- Example 24.57 (3): if `0 < 2 γ ξ + ‖x‖²`, if `x ≠ 0`, and if `p` solves the
Proposition 24.56 inclusion `(24.113)`, then the unique positive solution of the depressed
cubic `(24.115)` is `‖p‖`. -/
theorem existsUnique_quadraticPerspective_cubicRoot_of_two_mul_fst_add_norm_sq_pos
    (γ : PosReal) (ξ : ℝ) (x : H)
    (htest : 0 < 2 * (γ : ℝ) * ξ + ‖x‖ ^ (2 : ℕ))
    (hx : x ≠ 0) {p : H}
    (hp :
      x - (γ : ℝ) • p ∈
        ((((ξ : EReal) + ((γ : ℝ) : EReal) * (halfSquaredNorm p : EReal)).toReal) •
          (∂ halfSquaredNorm) p)) :
    ∃! s : Set.Ioi (0 : ℝ),
      ((s : ℝ) ^ (3 : ℕ)) + (2 * (ξ + (γ : ℝ)) / (γ : ℝ)) * (s : ℝ) -
          2 * ‖x‖ / (γ : ℝ) = 0 ∧
        (s : ℝ) = ‖p‖ := sorry

/-- Example 24.57 (4): if `0 < 2 γ ξ + ‖x‖²` and if `s` is a positive solution of `(24.115)`,
then the proximal point of the quadratic perspective `(24.112)` is the pair displayed in
`(24.116)`. -/
theorem scaledProx_quadraticPerspective_eq_pair_of_unique_cubicRoot
    (γ : PosReal) (ξ : ℝ) (x : H)
    (htest : 0 < 2 * (γ : ℝ) * ξ + ‖x‖ ^ (2 : ℕ))
    (s : Set.Ioi (0 : ℝ))
    (hs :
      ((s : ℝ) ^ (3 : ℕ)) + (2 * (ξ + (γ : ℝ)) / (γ : ℝ)) * (s : ℝ) -
          2 * ‖x‖ / (γ : ℝ) = 0) :
    Prox[γ, closedPerspective halfSquaredNorm halfSquaredNorm_mem_gammaZero.2.nonempty,
      closedPerspective_mem_gammaZero halfSquaredNorm halfSquaredNorm_mem_gammaZero] (ξ, x) =
      (ξ + (γ : ℝ) * (s : ℝ) ^ (2 : ℕ) / 2,
        (1 - (γ : ℝ) * (s : ℝ) / ‖x‖) • x) := sorry

end QuadraticPerspectiveExample

end

end ERealFunction
