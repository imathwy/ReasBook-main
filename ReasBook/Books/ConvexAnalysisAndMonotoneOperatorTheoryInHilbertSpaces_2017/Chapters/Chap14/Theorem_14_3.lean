import Mathlib
import BauschkeLean.Chap12.Remark_12_24
import BauschkeLean.Chap13.GammaZeroConjugate
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Corollary_16_30
import BauschkeLean.Chap16.Proposition_16_44
import BauschkeLean.Chap16.Proposition_16_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

section MoreauDecomposition

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Theorem 14 3: source-facing notation for the scaled proximity operator of `f*`. -/
noncomputable def scaled_gammaZero_proximity_operator
    (γ : PosReal) (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) : H → H :=
  scaledProximityOperator (f∗[hf]) (gammaZeroConjugate_mem_gammaZero hf) γ

notation "Prox⋆[" γ ", " f ", " hf "]" =>
  scaled_gammaZero_proximity_operator γ f hf

/-- Helper for Theorem 14 3: the reciprocal-parameter conjugate proximal point is the scaled
residual of the primal proximal point. -/
theorem conjugate_scaledProx_eq_inv_smul_sub_scaledProx
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) (x : H) :
    Prox⋆[(γ⁻¹ : PosReal), f, hf] ((γ : ℝ)⁻¹ • x) =
      (γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x) := by
  let p := Prox[γ, f, hf] x
  let pStar := (γ : ℝ)⁻¹ • (x - p)
  have hprox :
      x - p ∈ (∂ ((γ • f : H → Set.Ioi (⊥ : EReal)))) p := by
    -- Read the scaled proximal point as a subgradient inclusion for `γ • f`.
    simpa [p, scaledProximityOperator] using
      (eq_proximityOperator_iff_sub_mem_subdifferential
        (f := (γ • f : H → Set.Ioi (⊥ : EReal)))
        (hf := smul_mem_gammaZero f hf γ)
        (x := x)
        (p := p)).1 rfl
  have hsub :
      pStar ∈ (∂ f) p := by
    -- Undo the positive scalar on the subdifferential side.
    rw [subdifferential_posReal_smul_eq_smul (f := f) (γ := γ)] at hprox
    change x - p ∈ (γ : ℝ) • ((∂ f) p) at hprox
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] at hprox
    simpa [pStar, smul_smul, mul_inv_cancel₀ γ.2.ne'] using hprox
  have hconj :
      p ∈ (∂ (f∗[hf])) pStar := by
    -- Transport the primal subgradient to the conjugate side.
    rw [← inverse_subdifferential_eq_subdifferential_gammaZeroConjugate (f := f) hf]
    rw [SetValuedOperator.mem_inverse_iff]
    exact hsub
  have hscaledConj :
      (γ : ℝ)⁻¹ • p ∈ (∂ (((γ⁻¹ : PosReal) • (f∗[hf]) : H → Set.Ioi (⊥ : EReal)))) pStar := by
    -- Scale the conjugate subgradient by the reciprocal parameter.
    rw [subdifferential_posReal_smul_eq_smul (f := f∗[hf]) (γ := (γ⁻¹ : PosReal))]
    change (γ : ℝ)⁻¹ • p ∈ ((γ : ℝ)⁻¹) • ((∂ (f∗[hf])) pStar)
    exact Set.smul_mem_smul_set hconj
  have hpStar :
      pStar = Prox⋆[(γ⁻¹ : PosReal), f, hf] ((γ : ℝ)⁻¹ • x) := by
    -- The conjugate-side residual identity characterizes the reciprocal scaled proximal point.
    apply (eq_proximityOperator_iff_sub_mem_subdifferential
      (f := (((γ⁻¹ : PosReal) • (f∗[hf]) : H → Set.Ioi (⊥ : EReal))))
      (hf := smul_mem_gammaZero (f∗[hf]) (gammaZeroConjugate_mem_gammaZero hf) (γ⁻¹ : PosReal))
      (x := (γ : ℝ)⁻¹ • x)
      (p := pStar)).2
    simpa [p, pStar, sub_eq_add_neg, smul_sub, smul_smul, inv_mul_cancel₀ γ.2.ne',
      add_assoc, add_left_comm, add_comm] using hscaledConj
  exact hpStar.symm

/-- Helper for Theorem 14 3: the primal and reciprocal-dual scaled proximal points satisfy the
Fenchel--Young equality. -/
theorem fenchel_young_eq_of_scaled_prox_pair
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) (x : H) :
    (f (Prox[γ, f, hf] x) : EReal) +
        f.asEReal∗ (Prox⋆[(γ⁻¹ : PosReal), f, hf] ((γ : ℝ)⁻¹ • x)) =
      ((⟪Prox[γ, f, hf] x, Prox⋆[(γ⁻¹ : PosReal), f, hf] ((γ : ℝ)⁻¹ • x)⟫_ℝ : ℝ) : EReal) := by
  let p := Prox[γ, f, hf] x
  let pStar := Prox⋆[(γ⁻¹ : PosReal), f, hf] ((γ : ℝ)⁻¹ • x)
  have hprox :
      x - p ∈ (∂ ((γ • f : H → Set.Ioi (⊥ : EReal)))) p := by
    -- The primal scaled proximal point is characterized by a scaled subgradient inclusion.
    simpa [p, scaledProximityOperator] using
      (eq_proximityOperator_iff_sub_mem_subdifferential
        (f := (γ • f : H → Set.Ioi (⊥ : EReal)))
        (hf := smul_mem_gammaZero f hf γ)
        (x := x)
        (p := p)).1 rfl
  have hpStar :
      pStar = (γ : ℝ)⁻¹ • (x - p) := by
    simpa [p, pStar] using
      (conjugate_scaledProx_eq_inv_smul_sub_scaledProx
        (f := f) (hf := hf) (γ := γ) x)
  have hsub :
      pStar ∈ (∂ f) p := by
    -- After undoing the positive scalar, the dual point is an honest subgradient of `f` at `p`.
    rw [subdifferential_posReal_smul_eq_smul (f := f) (γ := γ)] at hprox
    change x - p ∈ (γ : ℝ) • ((∂ f) p) at hprox
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] at hprox
    simpa [hpStar, smul_smul, mul_inv_cancel₀ γ.2.ne'] using hprox
  simpa [p, pStar] using
    (mem_subdifferential_iff_fenchel_young_eq (f := f) p pStar).1 hsub

-- Proof sketch: combine Proposition 14.1 with Example 13.6 and apply the reciprocal-parameter
-- form of Moreau regularization to `f*`.
/-- Theorem 14 3 (1): for `f ∈ Γ₀(H)` and `γ ∈ ℝ_{++}`, equation `(14.3)` states that the
quadratic kernel `γ⁻¹ q` is the sum of the `γ`-Moreau envelope of `f` and the
`γ⁻¹`-Moreau envelope of `f*` composed with `γ⁻¹ Id`. -/
theorem moreauQuadraticKernel_eq_moreauEnvelope_add_conjugateMoreauEnvelope
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    (moreauQuadraticKernel γ).asEReal =
      {}^[γ] f + ({}^[(γ⁻¹ : PosReal)] (f.asEReal∗)) ∘
        fun x ↦ (γ : ℝ)⁻¹ • x := by
  funext x
  let p := Prox[γ, f, hf] x
  let pStar := Prox⋆[(γ⁻¹ : PosReal), f, hf] ((γ : ℝ)⁻¹ • x)
  have hpStar :
      pStar = (γ : ℝ)⁻¹ • (x - p) := by
    simpa [p, pStar] using
      (conjugate_scaledProx_eq_inv_smul_sub_scaledProx
        (f := f) (hf := hf) (γ := γ) x)
  have hres :
      (γ : ℝ) • pStar = x - p := by
    rw [hpStar, smul_smul, mul_inv_cancel₀ γ.2.ne', one_smul]
  have hdual_res :
      (γ : ℝ)⁻¹ • x - pStar = (γ : ℝ)⁻¹ • p := by
    rw [hpStar]
    simp [sub_eq_add_neg]
  have hmoreau :
      ({}^[γ] f) x =
        (f p : EReal) +
          ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
    simpa [p] using
      moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero
        (f := f) (hf := hf) (γ := γ) x
  have hmoreauStar :
      ({}^[(γ⁻¹ : PosReal)] (f.asEReal∗)) ((γ : ℝ)⁻¹ • x) =
        (f∗[hf] pStar : EReal) +
          ((((‖(γ : ℝ)⁻¹ • x - pStar‖ ^ 2) /
              (2 * (((γ⁻¹ : PosReal) : ℝ))) : ℝ) : EReal)) := by
    simpa [pStar, gammaZeroConjugate_apply] using
      moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero
        (f := f∗[hf]) (hf := gammaZeroConjugate_mem_gammaZero hf)
        (γ := (γ⁻¹ : PosReal)) ((γ : ℝ)⁻¹ • x)
  have hquad1 :
      ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) =
        ((((γ : ℝ) / 2 * ‖pStar‖ ^ 2 : ℝ) : EReal)) := by
    have hreal :
        ‖x - p‖ ^ 2 / (2 * (γ : ℝ)) = (γ : ℝ) / 2 * ‖pStar‖ ^ 2 := by
      rw [← hres, norm_smul, Real.norm_of_nonneg γ.2.le]
      field_simp [γ.2.ne']
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
  have hquad2 :
      ((((‖(γ : ℝ)⁻¹ • x - pStar‖ ^ 2) /
          (2 * (((γ⁻¹ : PosReal) : ℝ))) : ℝ) : EReal)) =
        ((((‖p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
    have hreal :
        ‖(γ : ℝ)⁻¹ • x - pStar‖ ^ 2 / (2 * (((γ⁻¹ : PosReal) : ℝ))) =
          ‖p‖ ^ 2 / (2 * (γ : ℝ)) := by
      have hγ0 : (γ : ℝ) ≠ 0 := γ.2.ne'
      rw [hdual_res, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr γ.2), pow_two]
      field_simp [hγ0]
      calc
        ‖p‖ ^ 2 = ‖p‖ ^ 2 * 1 := by ring
        _ = ‖p‖ ^ 2 * ((γ : ℝ) * (γ : ℝ)⁻¹) := by
              rw [mul_inv_cancel₀ hγ0]
        _ = (γ : ℝ) * ‖p‖ ^ 2 * (γ : ℝ)⁻¹ := by
              rw [← mul_assoc, mul_comm (‖p‖ ^ 2) (γ : ℝ)]
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
  have hdecomp :
      x = p + (γ : ℝ) • pStar := by
    calc
      x = p + (x - p) := by abel_nf
      _ = p + (γ : ℝ) • pStar := by rw [← hres]
  have hnorm :
      ‖x‖ ^ 2 = ‖p‖ ^ 2 + 2 * (γ : ℝ) * ⟪p, pStar⟫_ℝ + (γ : ℝ) ^ 2 * ‖pStar‖ ^ 2 := by
    calc
      ‖x‖ ^ 2 = ‖p + (γ : ℝ) • pStar‖ ^ 2 := by rw [hdecomp]
      _ = ‖p‖ ^ 2 + 2 * ⟪p, (γ : ℝ) • pStar⟫_ℝ + ‖(γ : ℝ) • pStar‖ ^ 2 := by
            simpa using norm_add_sq_real p ((γ : ℝ) • pStar)
      _ = ‖p‖ ^ 2 + 2 * (γ : ℝ) * ⟪p, pStar⟫_ℝ + (γ : ℝ) ^ 2 * ‖pStar‖ ^ 2 := by
            rw [real_inner_smul_right, norm_smul, Real.norm_of_nonneg γ.2.le]
            ring
  have hfinal :
      ((((‖x‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) =
        (((⟪p, pStar⟫_ℝ + (γ : ℝ) / 2 * ‖pStar‖ ^ 2 +
            ‖p‖ ^ 2 / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
    have hreal :
        ‖x‖ ^ 2 / (2 * (γ : ℝ)) =
          ⟪p, pStar⟫_ℝ + (γ : ℝ) / 2 * ‖pStar‖ ^ 2 +
            ‖p‖ ^ 2 / (2 * (γ : ℝ)) := by
      field_simp [γ.2.ne'] at hnorm ⊢
      nlinarith [hnorm]
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
  have hsum :
      ({}^[γ] f) x + ({}^[(γ⁻¹ : PosReal)] (f.asEReal∗)) ((γ : ℝ)⁻¹ • x) =
        (((⟪p, pStar⟫_ℝ + (γ : ℝ) / 2 * ‖pStar‖ ^ 2 +
            ‖p‖ ^ 2 / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
    let qStar : EReal := ((((γ : ℝ) / 2 * ‖pStar‖ ^ 2 : ℝ) : EReal))
    let qPrimal : EReal := ((((‖p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal))
    have hfy :
        (f p : EReal) + f.asEReal∗ pStar = ((⟪p, pStar⟫_ℝ : ℝ) : EReal) := by
      simpa [p, pStar] using
        fenchel_young_eq_of_scaled_prox_pair (f := f) (hf := hf) (γ := γ) (x := x)
    have hsum' := congrArg (fun t : EReal ↦ qStar + (t + qPrimal)) hfy
    rw [hmoreau, hmoreauStar, gammaZeroConjugate_apply, hquad1, hquad2]
    simpa [qStar, qPrimal, add_assoc, add_left_comm, add_comm] using hsum'
  calc
    (moreauQuadraticKernel γ).asEReal x = ((((‖x‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
      change (moreauQuadraticKernel γ x : EReal) = ((((‖x‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal))
      rw [moreauQuadraticKernel_apply]
      congr 1
      ring
    _ = (((⟪p, pStar⟫_ℝ + (γ : ℝ) / 2 * ‖pStar‖ ^ 2 +
            ‖p‖ ^ 2 / (2 * (γ : ℝ)) : ℝ) : EReal)) := hfinal
    _ = ({}^[γ] f) x + ({}^[(γ⁻¹ : PosReal)] (f.asEReal∗)) ((γ : ℝ)⁻¹ • x) := hsum.symm

-- Proof sketch: differentiate the identity from clause `(1)` with Proposition 12.30, then rewrite
-- the two gradients in terms of `Prox_{γ f}` and `Prox_{f^* / γ}`.
/-- Clause (2) of Theorem 14 3: Moreau's decomposition gives the operator identity
`Id = Prox_{γ f} + γ Prox_{f^* / γ} ∘ γ⁻¹ Id`. -/
theorem id_eq_scaledProximityOperator_add_scaledProximityOperator_conjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    id =
      Prox[γ, f, hf] +
        (γ : ℝ) •
          (Prox⋆[(γ⁻¹ : PosReal), f, hf] ∘
            fun x ↦ (γ : ℝ)⁻¹ • x) := by
  funext x
  let p := Prox[γ, f, hf] x
  have hproxStar :=
    conjugate_scaledProx_eq_inv_smul_sub_scaledProx (f := f) (hf := hf) (γ := γ) x
  have hres :
      (γ : ℝ) • (Prox⋆[(γ⁻¹ : PosReal), f, hf] ((γ : ℝ)⁻¹ • x)) = x - p := by
    rw [hproxStar]
    simp [p, smul_smul, mul_inv_cancel₀ γ.2.ne']
  calc
    id x = x := rfl
    _ = p + (γ : ℝ) • (Prox⋆[(γ⁻¹ : PosReal), f, hf] ((γ : ℝ)⁻¹ • x)) := by
          rw [hres]
          abel_nf
    _ =
        (Prox[γ, f, hf] +
          (γ : ℝ) •
            (Prox⋆[(γ⁻¹ : PosReal), f, hf] ∘ fun y ↦ (γ : ℝ)⁻¹ • y)) x := by
          rfl

-- Proof sketch: apply Proposition 12.26 to points `p` and `pStar` satisfying
-- `p = Prox_{γ f} x` and `pStar = Prox_{f^* / γ} (γ⁻¹ x)`, then use Fenchel--Young equality for
-- the pair `(p, pStar)`.
/-- Clause (3) of Theorem 14 3: if `p = Prox_{γ f} x` and
`p* = Prox_{f^* / γ} (x / γ)`, then equation `(14.4)` gives
`f p + f^*(p*) = ⟪p, p*⟫`. -/
theorem proxValue_add_conjugateProxValue_eq_inner
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) (x p pStar : H)
    (hp : p = Prox[γ, f, hf] x)
    (hpStar : pStar = Prox⋆[(γ⁻¹ : PosReal), f, hf] ((γ : ℝ)⁻¹ • x)) :
    (f p : EReal) + f.asEReal∗ pStar =
      ((⟪p, pStar⟫_ℝ : ℝ) : EReal) := by
  rw [hp, hpStar]
  simpa using
    fenchel_young_eq_of_scaled_prox_pair (f := f) (hf := hf) (γ := γ) (x := x)

end MoreauDecomposition

end ERealFunction
