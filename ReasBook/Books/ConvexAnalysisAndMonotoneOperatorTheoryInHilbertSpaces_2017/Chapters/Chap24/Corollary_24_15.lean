import BauschkeLean.Chap24.Proposition_24_14

open scoped InnerProductSpace

universe u

namespace ERealFunction

section NormSqPosReal

variable {H : Type u} [NormedAddCommGroup H]

/-- Helper for Corollary 24.15: a nonzero vector has strictly positive squared norm. -/
private theorem sq_norm_pos_of_ne_zero (u : H) (hu : u ≠ 0) :
    0 < ‖u‖ ^ 2 := by
  exact pow_pos (norm_pos_iff.mpr hu) 2

/-- The positive scalar parameter `‖u‖²` used in Corollary 24.15. -/
def normSqPosReal (u : H) (hu : u ≠ 0) : PosReal :=
  ⟨‖u‖ ^ 2, sq_norm_pos_of_ne_zero u hu⟩

/-- The underlying real number of `normSqPosReal u hu` is `‖u‖²`. -/
@[simp] theorem normSqPosReal_coe (u : H) (hu : u ≠ 0) :
    ((normSqPosReal u hu : PosReal) : ℝ) = ‖u‖ ^ 2 := rfl

end NormSqPosReal

section BasicProperties

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Semantic recall/local precedent: `lean_leansearch` only surfaced generic inner-product and
-- linear-map composition lemmas, so this item stays on the local Chapter 24 owners `Γ₀(H)` and
-- `Prox[...]`, specialized to the rank-one map `innerSL ℝ u` from Proposition 24.14.

/-- Helper for Corollary 24.15: the adjoint of `innerSL ℝ u` sends `t` to `t • u`. -/
private theorem adjoint_innerSL_apply_eq_smul (u : H) (t : ℝ) :
    (innerSL ℝ u).adjoint t = t • u := by
  -- Evaluate mathlib's operator identity for `adjoint (innerSL ℝ u)` at the scalar `t`.
  simpa [ContinuousLinearMap.toSpanSingleton_apply] using
    congrArg (fun T : ℝ →L[ℝ] H ↦ T t) (ContinuousLinearMap.adjoint_innerSL_apply (𝕜 := ℝ) u)

/-- Helper for Corollary 24.15: the inner-product functional `innerSL ℝ u` satisfies the
scalar-adjoint hypothesis from Proposition 24.14 with factor `‖u‖²`. -/
private theorem innerSL_comp_adjoint_eq_smul_id_of_ne_zero (u : H) (hu : u ≠ 0) :
    (innerSL ℝ u).comp (innerSL ℝ u).adjoint =
      (normSqPosReal u hu : ℝ) • (1 : ℝ →L[ℝ] ℝ) := by
  -- Compare both maps at `1`, since an `ℝ`-linear endomorphism of `ℝ` is determined there.
  ext
  -- The adjoint evaluation reduces the composite to `⟪u, 1 • u⟫_ℝ = ‖u‖²`.
  simp only [ContinuousLinearMap.comp_apply, adjoint_innerSL_apply_eq_smul,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
    real_inner_smul_right, real_inner_self_eq_norm_sq, normSqPosReal_coe]
  simp [smul_eq_mul]

/-- Helper for Corollary 24.15: if `φ ∈ Γ₀(ℝ)` and `u ≠ 0`, then the pullback
`φ ∘ (innerSL ℝ u)` belongs to `Γ₀(H)`. -/
theorem comp_innerSL_mem_gammaZero_of_ne_zero
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ)) (u : H) (hu : u ≠ 0) :
    φ ∘ innerSL ℝ u ∈ Γ₀(H) := by
  -- Specialize Proposition 24.14 to the rank-one map `innerSL ℝ u`.
  exact comp_continuousLinearMap_mem_gammaZero_of_comp_adjoint_eq_smul_id
    φ (innerSL ℝ u) (normSqPosReal u hu) hφ
    (innerSL_comp_adjoint_eq_smul_id_of_ne_zero u hu)

/-- Corollary 24.15: if `u ≠ 0`, `φ ∈ Γ₀(ℝ)`, and `g = φ ∘ (innerSL ℝ u)`, then
`Prox_g x = x + ((Prox_{‖u‖² φ} ⟪x, u⟫_ℝ - ⟪x, u⟫_ℝ) / ‖u‖²) • u`. -/
theorem prox_comp_innerSL_eq_add_div_normSq_smul_of_ne_zero
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (u : H) (hu : u ≠ 0) (x : H) :
    Prox[φ ∘ innerSL ℝ u, comp_innerSL_mem_gammaZero_of_ne_zero φ hφ u hu] x =
      x + ((Prox[normSqPosReal u hu, φ, hφ] ⟪x, u⟫_ℝ - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u := by
  -- Apply Proposition 24.14 on the canonical surface `L = innerSL ℝ u`.
  have hprox :=
    prox_comp_continuousLinearMap_eq_add_inv_smul_adjoint_sub_of_comp_adjoint_eq_smul_id
      (f := φ) (L := innerSL ℝ u) (μ := normSqPosReal u hu) hφ
      (innerSL_comp_adjoint_eq_smul_id_of_ne_zero u hu) x
  -- Route correction: postpone the symmetry rewrite `⟪u, x⟫_ℝ = ⟪x, u⟫_ℝ` until the final step.
  simpa [adjoint_innerSL_apply_eq_smul, normSqPosReal_coe, div_eq_inv_mul, smul_smul,
    innerSL_apply_apply, real_inner_comm] using hprox

end BasicProperties

end ERealFunction
