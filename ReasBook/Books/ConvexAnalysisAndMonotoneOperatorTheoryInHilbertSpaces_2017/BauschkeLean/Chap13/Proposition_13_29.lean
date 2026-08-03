import BauschkeLean.Chap10.Proposition_10_8
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap12.Definition_12_20_Core
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Proposition_13_13
import BauschkeLean.Chap13.Proposition_13_16
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap13.Proposition_13_19
import BauschkeLean.Chap13.Proposition_13_23

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace translate

universe u

namespace ERealFunction

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal)) (γ : Set.Ioi (0 : ℝ))

/-- Helper for Proposition 13 29: if an extended-real-valued function is not identically `⊤`,
then its Fenchel conjugate never takes the value `⊥`. -/
private theorem conjugate_ne_bot_of_exists_ne_top
    {g : H → EReal} (hg : ∃ x : H, g x ≠ ⊤) (u : H) :
    g∗ u ≠ ⊥ := by
  rcases hg with ⟨x, hx⟩
  -- Evaluate the defining supremum at a point where the affine defect is not `⊥`.
  have hterm : (((⟪x, u⟫_ℝ : ℝ) : EReal) - g x) ≠ ⊥ := by
    cases hgx : g x with
    | bot =>
        simp
    | top =>
        exact (hx hgx).elim
    | coe r =>
        simpa using (EReal.coe_ne_bot (⟪x, u⟫_ℝ - r))
  intro hconj
  apply hterm
  exact le_bot_iff.mp <| hconj ▸ by
    rw [conjugate_apply]
    exact le_iSup (fun y : H ↦ ((⟪y, u⟫_ℝ : ℝ) : EReal) - g y) x

/-- Helper for Proposition 13 29: expanding the quadratic at `u + x` separates the base-point
quadratic, the mixed inner-product term, and the quadratic of `x`. -/
private theorem halfSquaredNorm_add_eq_halfSquaredNorm_add_inner_add_halfSquaredNorm
    (u x : H) :
    halfSquaredNorm.asEReal (u + x) =
      halfSquaredNorm.asEReal u + (((⟪x, u⟫_ℝ : ℝ) : EReal) + halfSquaredNorm.asEReal x) := by
  have hu :
      halfSquaredNorm.asEReal u = ((((‖u‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal)) := by
    simpa using (halfSquaredNorm_apply (H := H) u)
  have hx :
      halfSquaredNorm.asEReal x = ((((‖x‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal)) := by
    simpa using (halfSquaredNorm_apply (H := H) x)
  have hux :
      halfSquaredNorm.asEReal (u + x) = ((((‖u + x‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal)) := by
    simpa using (halfSquaredNorm_apply (H := H) (u + x))
  -- Rewrite the quadratic values in real coordinates, then expand `‖u + x‖²`.
  rw [hux, hu, hx, ← EReal.coe_add]
  congr 1
  have hreal :
      ‖u + x‖ ^ (2 : ℕ) / 2 =
        ‖u‖ ^ (2 : ℕ) / 2 + (⟪x, u⟫_ℝ + ‖x‖ ^ (2 : ℕ) / 2) := by
    rw [norm_add_sq_real]
    rw [real_inner_comm]
    ring
  simpa [add_assoc, add_left_comm, add_comm] using hreal

/-- Helper for Proposition 13 29: adding a finite real shift commutes with an indexed infimum in
`EReal`. -/
private theorem iInf_add_real_const
    {ι : Sort*} (Φ : ι → EReal) (c : ℝ) :
    (⨅ i, Φ i + ((c : ℝ) : EReal)) = (⨅ i, Φ i) + ((c : ℝ) : EReal) := by
  have hright :
      (⨅ i, Φ i) + ((c : ℝ) : EReal) ≤ (⨅ i, Φ i + ((c : ℝ) : EReal)) := by
    refine le_iInf fun i ↦ ?_
    exact add_le_add (iInf_le Φ i) le_rfl
  have hleft_sub :
      (⨅ i, Φ i + ((c : ℝ) : EReal)) - ((c : ℝ) : EReal) ≤ (⨅ i, Φ i) := by
    refine le_iInf fun i ↦ ?_
    exact (EReal.sub_le_iff_le_add
      (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))).2
      (iInf_le (fun i ↦ Φ i + ((c : ℝ) : EReal)) i)
  have hleft :
      (⨅ i, Φ i + ((c : ℝ) : EReal)) ≤ (⨅ i, Φ i) + ((c : ℝ) : EReal) := by
    exact (EReal.sub_le_iff_le_add
      (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))).1 hleft_sub
  exact le_antisymm hleft hright

/-- Helper for Proposition 13 29: subtracting a pointwise supremum from a finite real scalar is
the indexed infimum of the corresponding affine defects. -/
private theorem ereal_realCast_sub_iSup_eq_iInf_sub
    {ι : Sort*} (a : ℝ) (φ : ι → EReal) :
    ((a : EReal) - ⨆ i, φ i) = ⨅ i, ((a : EReal) - φ i) := by
  -- Rewrite subtraction as addition with negation and dualize the supremum through `neg`.
  calc
    ((a : EReal) - ⨆ i, φ i) = ((a : EReal) + -(⨆ i, φ i)) := by
      rw [sub_eq_add_neg]
    _ = ((a : EReal) + ⨅ i, -φ i) := by
      congr 1
      exact OrderIso.map_iSup EReal.negOrderIso φ
    _ = (⨅ i, -φ i) + ((a : EReal)) := by
      rw [add_comm]
    _ = ⨅ i, (-φ i) + ((a : EReal)) := by
      symm
      simpa using iInf_add_real_const (Φ := fun i ↦ -φ i) a
    _ = ⨅ i, ((a : EReal) - φ i) := by
      refine iInf_congr fun i ↦ ?_
      simp [sub_eq_add_neg, add_comm]

/-- Helper for Proposition 13 29: the source decomposition
`γ q - f* = inf_x (γ q - (⟪·,x⟫ - f x))`. -/
private theorem smul_halfSquaredNorm_sub_conjugate_eq_iInf_affine_shifts
    :
    (fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v) =
      ⨅ x : H, fun v : H ↦
        ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v -
          (((⟪v, x⟫_ℝ : ℝ) : EReal) - f.asEReal x) := by
  ext v
  simp only [iInf_apply]
  change ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v =
    ⨅ x : H, (((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v -
      ((((⟪v, x⟫_ℝ : ℝ) : EReal) - f.asEReal x)))
  have hquad :
      ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v =
        ((((γ : ℝ) * (‖v‖ ^ (2 : ℕ) / 2) : ℝ) : EReal)) := by
    rw [Function.asEReal_apply, halfSquaredNorm_apply]
    simp
  have hiInf_quad :
      (⨅ x : H, (((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v -
        ((((⟪v, x⟫_ℝ : ℝ) : EReal) - f.asEReal x)))) =
      ⨅ x : H, ((((γ : ℝ) * (‖v‖ ^ (2 : ℕ) / 2) : ℝ) : EReal) -
        ((((⟪v, x⟫_ℝ : ℝ) : EReal) - f.asEReal x))) := by
    refine iInf_congr fun x ↦ ?_
    rw [hquad]
  -- Expand the conjugate at `v`, then transport the finite quadratic term through the supremum.
  rw [conjugate_apply]
  calc
    ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v -
        ⨆ x : H, (((⟪x, v⟫_ℝ : ℝ) : EReal) - f.asEReal x) =
      ((((γ : ℝ) * (‖v‖ ^ (2 : ℕ) / 2) : ℝ) : EReal) -
        ⨆ x : H, (((⟪x, v⟫_ℝ : ℝ) : EReal) - f.asEReal x)) := by
          rw [hquad]
    _ =
      ⨅ x : H,
        ((((γ : ℝ) * (‖v‖ ^ (2 : ℕ) / 2) : ℝ) : EReal) -
          ((((⟪x, v⟫_ℝ : ℝ) : EReal) - f.asEReal x))) := by
            simpa using
              ereal_realCast_sub_iSup_eq_iInf_sub
                (a := (γ : ℝ) * (‖v‖ ^ (2 : ℕ) / 2))
                (φ := fun x : H ↦ (((⟪x, v⟫_ℝ : ℝ) : EReal) - f.asEReal x))
    _ = ⨅ x : H, ((((γ : ℝ) * (‖v‖ ^ (2 : ℕ) / 2) : ℝ) : EReal) -
          ((((⟪v, x⟫_ℝ : ℝ) : EReal) - f.asEReal x))) := by
            refine iInf_congr fun x ↦ ?_
            congr 1
            rw [real_inner_comm]
    _ = ⨅ x : H, (((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v -
          ((((⟪v, x⟫_ℝ : ℝ) : EReal) - f.asEReal x))) := by
            exact hiInf_quad.symm

/-- Helper for Proposition 13 29: the conjugate of a pointwise infimum is the pointwise supremum
of the conjugates. This is the local copy needed because the standalone Proposition 13.28 file is
not dependency-clean yet. -/
private theorem conjugate_iInf_eq_iSup_conjugate_local
    {I : Type*} (F : I → H → EReal) :
    (⨅ i : I, F i)∗ = ⨆ i : I, (F i)∗ := by
  apply le_antisymm
  · have hconj : (⨆ i : I, (F i)∗)∗ ≤ ⨅ i : I, (F i)∗∗ := by
      -- Conjugating the pointwise bound `(F i)∗ ≤ ⨆ j, (F j)∗` reverses the inequality.
      refine le_iInf fun i ↦ ?_
      exact conjugate_antitone (le_iSup (fun j : I ↦ (F j)∗) i)
    have hle : (⨆ i : I, (F i)∗)∗ ≤ ⨅ i : I, F i := by
      exact hconj.trans <| iInf_mono fun i ↦ biconjugate_le (F i)
    -- Conjugate back once more and remove the outer biconjugation by Proposition 13.16.
    exact (conjugate_antitone hle).trans <| biconjugate_le (⨆ i : I, (F i)∗)
  · refine iSup_le fun i ↦ ?_
    exact conjugate_antitone (iInf_le F i)

/-- Helper for Proposition 13 29: after conjugating `γ q`, multiplying by `γ` recovers the
canonical quadratic kernel. -/
private theorem smul_conjugate_smul_halfSquaredNorm
    (w : H) :
    ((γ : ℝ) : EReal) *
        (((fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v)∗ w)) =
      halfSquaredNorm.asEReal w := by
  have hconj :
      ((fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v)∗ w) =
        ((γ : ℝ) : EReal) * (halfSquaredNorm.asEReal)∗ (((γ : ℝ)⁻¹) • w) := by
    -- Proposition 13.23 identifies the conjugate of the scaled quadratic at the inverse homothety.
    simpa using
      congrFun
        (conjugate_pos_smul (f := (halfSquaredNorm (H := H)).asEReal) γ)
        w
  have hscale :
      ((γ : ℝ) : EReal) *
          (((γ : ℝ) : EReal) * halfSquaredNorm.asEReal (((γ : ℝ)⁻¹) • w)) =
        halfSquaredNorm.asEReal w := by
    have hγ : (0 : ℝ) < (γ : ℝ) := γ.2
    -- Normalize the rescaled quadratic in real coordinates and cancel the two factors of `γ`.
    rw [Function.asEReal_apply, halfSquaredNorm_apply, Function.asEReal_apply, halfSquaredNorm_apply,
      ← EReal.coe_mul, ← EReal.coe_mul]
    congr 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hγ)]
    field_simp [ne_of_gt hγ]
  -- Rewrite by the positive-scaling conjugation rule and collapse the quadratic kernel.
  calc
    ((γ : ℝ) : EReal) * (((fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v)∗ w)) =
      ((γ : ℝ) : EReal) *
        (((γ : ℝ) : EReal) * (halfSquaredNorm.asEReal)∗ (((γ : ℝ)⁻¹) • w)) := by
          rw [hconj]
    _ = ((γ : ℝ) : EReal) *
          (((γ : ℝ) : EReal) * halfSquaredNorm.asEReal (((γ : ℝ)⁻¹) • w)) := by
            rw [← half_squared_norm_self_conjugate (H := H)]
    _ = halfSquaredNorm.asEReal w := hscale

/-- Helper for Proposition 13 29: in the finite-`a` branch, the quadratic-affine summand is
exactly the `γ q + ⟪·,-x⟫ + const` input needed by Proposition 13.23. -/
private theorem quadratic_affine_shift_eq_translate_add_inner_const
    (x : H) (a : Set.Ioi (⊥ : EReal)) (ha_top : (a : EReal) ≠ ⊤) :
    (fun v : H ↦
      ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v -
        (((⟪v, x⟫_ℝ : ℝ) : EReal) - (a : EReal))) =
      ((τ (0 : H) (fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v)) +
        (fun v : H ↦ ((⟪v, -x⟫_ℝ : ℝ) : EReal)) +
        fun _ : H ↦ (((a : EReal).toReal : ℝ) : EReal)) := by
  funext v
  have ha_bot : (a : EReal) ≠ ⊥ := ne_of_gt a.2
  have hcoe : ((((a : EReal).toReal : ℝ) : EReal)) = (a : EReal) :=
    EReal.coe_toReal ha_top ha_bot
  have hneg : -((((⟪v, x⟫_ℝ : ℝ) : EReal) + -(a : EReal))) =
      -(((⟪v, x⟫_ℝ : ℝ) : EReal)) + (a : EReal) := by
    -- Convert the finite `EReal` correction back to a real identity so the affine defect
    -- becomes a plain additive rearrangement.
    rw [← hcoe]
    change (((-(⟪v, x⟫_ℝ + -(a : EReal).toReal) : ℝ) : EReal)) =
      (((-⟪v, x⟫_ℝ + (a : EReal).toReal : ℝ) : EReal))
    congr 1
    ring
  have hinner : -(((⟪v, x⟫_ℝ : ℝ) : EReal)) = (((⟪v, -x⟫_ℝ : ℝ) : EReal)) := by
    simpa [inner_neg_right]
  -- Rewrite the defect into the translate-plus-inner-plus-constant shape from the source proof.
  simp only [Pi.add_apply, translate_apply]
  rw [show v - 0 = v by simp, hcoe]
  rw [sub_eq_add_neg, sub_eq_add_neg, hneg, hinner]
  simp [add_assoc]

/-- Helper for Proposition 13 29: after the translate-conjugation rewrite, scaling the quadratic
conjugate minus a finite constant collapses to the textbook kernel `q - γ a`. -/
private theorem scaled_quadratic_conjugate_sub_finite_const
    (w : H) (a : Set.Ioi (⊥ : EReal)) (ha_top : (a : EReal) ≠ ⊤) :
    ((γ : ℝ) : EReal) *
        ((((fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v)∗ w) -
          ((((a : EReal).toReal : ℝ) : EReal)))) =
      halfSquaredNorm.asEReal w - ((γ : ℝ) : EReal) * (a : EReal) := by
  have hγ_nonneg : (0 : EReal) ≤ ((γ : ℝ) : EReal) := by
    exact_mod_cast γ.2.le
  have hγ_ne_top : ((γ : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top (γ : ℝ)
  have ha_bot : (a : EReal) ≠ ⊥ := ne_of_gt a.2
  have hcoe : ((((a : EReal).toReal : ℝ) : EReal)) = (a : EReal) :=
    EReal.coe_toReal ha_top ha_bot
  -- Collapse the scaled quadratic first, then distribute the positive scalar across the
  -- finite constant and rewrite it back to `a`.
  calc
    ((γ : ℝ) : EReal) *
        ((((fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v)∗ w) -
          ((((a : EReal).toReal : ℝ) : EReal)))) =
      ((γ : ℝ) : EReal) *
        (((fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v)∗ w) +
          -((((a : EReal).toReal : ℝ) : EReal))) := by
            rw [sub_eq_add_neg]
    _ =
      ((γ : ℝ) : EReal) *
          (((fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v)∗ w)) +
        ((γ : ℝ) : EReal) * (-((((a : EReal).toReal : ℝ) : EReal))) := by
          rw [EReal.left_distrib_of_nonneg_of_ne_top hγ_nonneg hγ_ne_top]
    _ =
      halfSquaredNorm.asEReal w +
        ((γ : ℝ) : EReal) * (-((((a : EReal).toReal : ℝ) : EReal))) := by
          rw [smul_conjugate_smul_halfSquaredNorm (γ := γ) w]
    _ =
      halfSquaredNorm.asEReal w +
        -(((γ : ℝ) : EReal) * ((((a : EReal).toReal : ℝ) : EReal))) := by
          rw [mul_neg]
    _ =
      halfSquaredNorm.asEReal w +
        -(((γ : ℝ) : EReal) * (a : EReal)) := by
          rw [hcoe]
    _ = halfSquaredNorm.asEReal w - ((γ : ℝ) : EReal) * (a : EReal) := by
          rw [sub_eq_add_neg]

/-- Helper for Proposition 13 29: the conjugate of each quadratic-affine summand is the
translated quadratic defect from the source proof. -/
private theorem smul_conjugate_halfSquaredNorm_sub_inner_add_const
    (x u : H) (a : Set.Ioi (⊥ : EReal)) :
    ((γ : ℝ) : EReal) *
        ((fun v : H ↦
            ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v -
              (((⟪v, x⟫_ℝ : ℝ) : EReal) - (a : EReal)))∗ u) =
      halfSquaredNorm.asEReal (u + x) - ((γ : ℝ) : EReal) * (a : EReal) := by
  by_cases htop : (a : EReal) = ⊤
  · -- When `a = ⊤`, the primal summand is constantly `⊤`, so its conjugate is constantly `⊥`.
    have hsummand :
        (fun v : H ↦
            ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v -
              (((⟪v, x⟫_ℝ : ℝ) : EReal) - (a : EReal))) =
          fun _ : H ↦ (⊤ : EReal) := by
      funext v
      rw [htop, EReal.sub_top]
      have hne : ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v ≠ ⊥ := by
        rw [Function.asEReal_apply, halfSquaredNorm_apply, ← EReal.coe_mul]
        exact EReal.coe_ne_bot _
      rw [EReal.sub_bot hne]
    rw [hsummand]
    have hconj_top : ((fun _ : H ↦ (⊤ : EReal))∗) = (fun _ : H ↦ (⊥ : EReal)) := by
      funext z
      rw [conjugate_apply]
      apply le_antisymm
      · refine iSup_le fun y ↦ ?_
        simp
      · exact bot_le
    rw [hconj_top, htop]
    have hγpos : (0 : EReal) < (((γ : ℝ) : EReal)) := by
      exact_mod_cast γ.2
    rw [EReal.mul_bot_of_pos hγpos, EReal.mul_top_of_pos hγpos, EReal.sub_top]
  · -- Route correction: isolate the finite branch before applying the translate-conjugation rule.
    rw [quadratic_affine_shift_eq_translate_add_inner_const (γ := γ) x a htop]
    rw [congrFun
      (conjugate_translate_add_inner_add_const
        (f := fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v)
        (y := (0 : H)) (v := -x) (β := (a : EReal).toReal)) u]
    simp only [Pi.add_apply, translate_apply]
    -- Collapse the translated scaled quadratic and normalize the finite `EReal` constant.
    simpa [sub_eq_add_neg, add_assoc] using
      scaled_quadratic_conjugate_sub_finite_const (γ := γ) (w := u + x) a htop

/-- Helper for Proposition 13 29: the translated quadratic summand splits into the base quadratic
plus the affine defect defining the conjugate of `γ f - q`. -/
private theorem quadratic_shift_minus_scaled_value_eq_affine_defect_add_base
    (u x : H) :
    halfSquaredNorm.asEReal (u + x) - (((γ : ℝ) : EReal) * f.asEReal x) =
      halfSquaredNorm.asEReal u +
        ((((⟪x, u⟫_ℝ : ℝ) : EReal) -
          ((((γ : ℝ) : EReal) * f.asEReal x) - halfSquaredNorm.asEReal x))) := by
  by_cases htop : f.asEReal x = ⊤
  · have hγpos : (0 : EReal) < (((γ : ℝ) : EReal)) := by
      exact_mod_cast γ.2
    have hq_top : halfSquaredNorm.asEReal x ≠ ⊤ := by
      rw [Function.asEReal_apply, halfSquaredNorm_apply]
      exact EReal.coe_ne_top _
    -- In the `⊤` branch both sides collapse to `⊥` after one subtraction by `⊤`.
    rw [htop, EReal.mul_top_of_pos hγpos, EReal.sub_top]
    rw [EReal.top_sub hq_top, EReal.sub_top]
    simp
  · -- In the finite branch, reduce the `EReal` statement to the corresponding real identity.
    cases hfx : f.asEReal x with
    | bot =>
        exact False.elim ((ne_of_gt (f x).2) hfx)
    | top =>
        exact False.elim (htop hfx)
    | coe a =>
        rw [halfSquaredNorm_add_eq_halfSquaredNorm_add_inner_add_halfSquaredNorm (H := H) u x]
        rw [Function.asEReal_apply, halfSquaredNorm_apply, Function.asEReal_apply,
          halfSquaredNorm_apply, ← EReal.coe_mul]
        -- After rewriting each finite term as a real scalar, the statement is just ring algebra.
        rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_add]
        exact congrArg (fun t : ℝ ↦ (t : EReal)) <| by ring

/-- Helper for Proposition 13 29: if an `EReal`-valued function lies in `Γ(H)` and never takes
the value `⊥`, then its real representative is convex on its finite domain. -/
private theorem convexOn_dom_toReal_of_mem_gamma_of_ne_bot
    {g : H → EReal} (hg : g ∈ gamma H) (hbot : ∀ x, g x ≠ ⊥) :
    _root_.ConvexOn ℝ (dom g) (fun x ↦ (g x).toReal) := by
  by_cases hdom : (dom g).Nonempty
  · have hproper : IsProper g := ⟨hbot, hdom⟩
    have hΓ0 : properIoi g hproper ∈ Γ₀(H) :=
      properIoi_mem_gammaZero_of_mem_gamma hproper hg
    -- Package `g` as a `Γ₀(H)` owner, then use the existing effective-domain bridge.
    simpa [effectiveDomain, dom] using hΓ0.2.toReal_convexOn_effectiveDomain
  · rw [Set.not_nonempty_iff_eq_empty] at hdom
    refine ⟨by simpa [hdom] using (convex_empty : Convex ℝ (∅ : Set H)), ?_⟩
    intro x hx
    exact False.elim (by simpa [hdom] using hx)

-- Proof sketch: apply Proposition 13.28 to the infimum presentation of `γ q - f*`, use the
-- positive-scaling conjugation rule from Proposition 13.23, and simplify the resulting quadratic
-- terms to obtain formula (13.22).
/-- Proposition 13.29 (1): for a proper `]-∞,+∞]`-valued function `f` and `γ > 0`, the Fenchel
conjugate of `γ f - q` equals `γ (γ q - f*)* - q`, where `q(x) = ‖x‖² / 2`. -/
theorem conjugate_smul_sub_halfSquaredNorm_eq
    (hproper : IsProper f.asEReal)
    :
    (fun x : H ↦ ((γ : ℝ) : EReal) * f.asEReal x - halfSquaredNorm.asEReal x)∗ =
      fun u : H ↦
        ((γ : ℝ) : EReal) *
            ((fun v : H ↦
                ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v)∗ u) -
          halfSquaredNorm.asEReal u := by
  let φ : H → EReal :=
    fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v
  let ψ : H → EReal :=
    fun x : H ↦ ((γ : ℝ) : EReal) * f.asEReal x - halfSquaredNorm.asEReal x
  ext u
  have hscaled :
      ((γ : ℝ) : EReal) * (φ∗ u) = halfSquaredNorm.asEReal u + ψ∗ u := by
    -- Follow the source proof: rewrite `φ` as the infimum of quadratic-affine shifts, conjugate
    -- termwise, then normalize each summand to `q(u)` plus the affine defect for `ψ`.
    calc
      ((γ : ℝ) : EReal) * (φ∗ u) =
          ((γ : ℝ) : EReal) *
            ((⨆ x : H,
                ((fun v : H ↦
                    ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v -
                      (((⟪v, x⟫_ℝ : ℝ) : EReal) - f.asEReal x))∗ u))) := by
            rw [show φ =
              (⨅ x : H, fun v : H ↦
                ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v -
                  (((⟪v, x⟫_ℝ : ℝ) : EReal) - f.asEReal x)) by
                simpa [φ] using
                  smul_halfSquaredNorm_sub_conjugate_eq_iInf_affine_shifts
                    (f := f) (γ := γ)]
            rw [conjugate_iInf_eq_iSup_conjugate_local, iSup_apply]
      _ =
          ⨆ x : H,
            ((γ : ℝ) : EReal) *
              ((fun v : H ↦
                  ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v -
                    (((⟪v, x⟫_ℝ : ℝ) : EReal) - f.asEReal x))∗ u) := by
            simpa using
              ereal_mul_iSup_of_pos
                (α := γ)
                (φ := fun x : H ↦
                  ((fun v : H ↦
                      ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v -
                        (((⟪v, x⟫_ℝ : ℝ) : EReal) - f.asEReal x))∗ u))
      _ = ⨆ x : H, halfSquaredNorm.asEReal (u + x) - ((γ : ℝ) : EReal) * f.asEReal x := by
            refine iSup_congr fun x ↦ ?_
            simpa using
              smul_conjugate_halfSquaredNorm_sub_inner_add_const
                (γ := γ) x u (f x)
      _ =
          ⨆ x : H,
            halfSquaredNorm.asEReal u +
              ((((⟪x, u⟫_ℝ : ℝ) : EReal) -
                ((((γ : ℝ) : EReal) * f.asEReal x) - halfSquaredNorm.asEReal x))) := by
            refine iSup_congr fun x ↦ ?_
            simpa using
              quadratic_shift_minus_scaled_value_eq_affine_defect_add_base
                (f := f) (γ := γ) u x
      _ =
          ⨆ x : H,
            ((((⟪x, u⟫_ℝ : ℝ) : EReal) -
              ((((γ : ℝ) : EReal) * f.asEReal x) - halfSquaredNorm.asEReal x))) +
              ((((‖u‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal)) := by
            refine iSup_congr fun x ↦ ?_
            rw [Function.asEReal_apply, halfSquaredNorm_apply, add_comm]
      _ =
          (⨆ x : H,
            (((⟪x, u⟫_ℝ : ℝ) : EReal) -
              ((((γ : ℝ) : EReal) * f.asEReal x) - halfSquaredNorm.asEReal x))) +
            ((((‖u‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal)) := by
            simpa using
              ereal_iSup_add_of_real_shift
                (r := ‖u‖ ^ (2 : ℕ) / 2)
                (φ := fun x : H ↦
                  (((⟪x, u⟫_ℝ : ℝ) : EReal) -
                    ((((γ : ℝ) : EReal) * f.asEReal x) - halfSquaredNorm.asEReal x)))
      _ = ψ∗ u + ((((‖u‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal)) := by
            rw [conjugate_apply]
      _ = ((((‖u‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal)) + ψ∗ u := by
            rw [add_comm]
      _ = halfSquaredNorm.asEReal u + ψ∗ u := by
            rw [Function.asEReal_apply, halfSquaredNorm_apply]
  -- Cancel the finite quadratic term from the source identity `γ φ* = q + ψ*`.
  have hscaled' :
      ψ∗ u + ((((‖u‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal)) = ((γ : ℝ) : EReal) * (φ∗ u) := by
    calc
      ψ∗ u + ((((‖u‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal)) = ψ∗ u + halfSquaredNorm.asEReal u := by
        rw [Function.asEReal_apply, halfSquaredNorm_apply]
      _ = halfSquaredNorm.asEReal u + ψ∗ u := by
        rw [add_comm]
      _ = ((γ : ℝ) : EReal) * (φ∗ u) := hscaled.symm
  calc
    ψ∗ u =
        ψ∗ u + ((((‖u‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal)) -
          ((((‖u‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal)) := by
      simpa using
        (EReal.add_sub_cancel_right (a := ψ∗ u) (b := ‖u‖ ^ (2 : ℕ) / 2)).symm
    _ =
        ((γ : ℝ) : EReal) * (φ∗ u) -
          ((((‖u‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal)) := by
      rw [hscaled']
    _ = ((γ : ℝ) : EReal) * (φ∗ u) - halfSquaredNorm.asEReal u := by
      rw [Function.asEReal_apply, halfSquaredNorm_apply]
    _ =
        ((γ : ℝ) : EReal) *
            ((fun v : H ↦
                ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v)∗ u) -
          halfSquaredNorm.asEReal u := by
            rfl

-- Route correction: the old properness helper was false. The packaged conjugate only needs a
-- witness that `γ q - f*` is not identically `⊤`, and evaluating at `0` provides that witness.
/-- Helper for Proposition 13 29: the quadratic-conjugate gap `γ q - f*` is not identically
`⊤`, because its value at `0` is `-f*(0)` and properness of `f` rules out `f*(0) = ⊥`. -/
theorem smul_halfSquaredNorm_sub_conjugate_exists_ne_top
    (hproper : IsProper f.asEReal)
    :
    ∃ v : H,
      ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v ≠ ⊤ := by
  refine ⟨0, ?_⟩
  have hconj0 : f.asEReal∗ (0 : H) ≠ ⊥ := conjugate_ne_bot_of_isProper hproper 0
  -- At the origin the quadratic term vanishes, so the gap is just `-f*(0)`.
  have hquad0 : halfSquaredNorm.asEReal (0 : H) = 0 := by
    simp [Function.asEReal_apply]
  rw [hquad0, mul_zero, zero_sub]
  intro htop
  exact hconj0 (EReal.neg_eq_top_iff.mp htop)

/-- Helper for Proposition 13 29: the conjugate of `γ f - q` never takes the value `⊥`. -/
private theorem smul_sub_halfSquaredNorm_conjugate_ne_bot
    (hproper : IsProper f.asEReal) (u : H) :
    ((fun x : H ↦ ((γ : ℝ) : EReal) * f.asEReal x - halfSquaredNorm.asEReal x)∗ u) ≠ ⊥ := by
  rcases hproper.2 with ⟨x, hx⟩
  have hxtop : f.asEReal x ≠ ⊤ := (mem_dom_iff_ne_top _ _).1 hx
  have hψx_top :
      ((fun y : H ↦ ((γ : ℝ) : EReal) * f.asEReal y - halfSquaredNorm.asEReal y) x) ≠ ⊤ := by
    cases hfx : f.asEReal x with
    | bot =>
        exact False.elim ((ne_of_gt (f x).2) hfx)
    | top =>
        exact False.elim (hxtop hfx)
    | coe r =>
        have hhalf : ((2 : ℝ)⁻¹ * ‖x‖ ^ (2 : ℕ)) = ‖x‖ ^ (2 : ℕ) / 2 := by
          ring
        have hψx :
            ((fun y : H ↦ ((γ : ℝ) : EReal) * f.asEReal y - halfSquaredNorm.asEReal y) x) =
              ((((γ : ℝ) * r - ‖x‖ ^ (2 : ℕ) / 2 : ℝ) : EReal)) := by
          simpa [Function.asEReal_apply, halfSquaredNorm_apply, hfx, hhalf, ← EReal.coe_mul,
            ← EReal.coe_sub]
        rw [hψx]
        exact EReal.coe_ne_top _
  exact conjugate_ne_bot_of_exists_ne_top
    (g := fun x : H ↦ ((γ : ℝ) : EReal) * f.asEReal x - halfSquaredNorm.asEReal x)
    ⟨x, hψx_top⟩ u

/-- Helper for Proposition 13 29: on the effective domain of `(γ q - f*)*`, the defect against
`γ⁻¹ q` is exactly `γ⁻¹ (γ f - q)*`. -/
private theorem conjugate_gap_defect_eq_inv_smul_conjugate_tail
    (hproper : IsProper f.asEReal) {u : H}
    (hu :
      u ∈ dom ((fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v)∗)) :
    u ∈ dom ((fun x : H ↦ ((γ : ℝ) : EReal) * f.asEReal x - halfSquaredNorm.asEReal x)∗) ∧
      (((fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v)∗ u).toReal -
          ((γ : ℝ)⁻¹ / 2) * ‖u‖ ^ (2 : ℕ)) =
        (γ : ℝ)⁻¹ *
          (((fun x : H ↦ ((γ : ℝ) : EReal) * f.asEReal x - halfSquaredNorm.asEReal x)∗ u).toReal) := by
  let φ : H → EReal :=
    fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v
  let ψ : H → EReal :=
    fun x : H ↦ ((γ : ℝ) : EReal) * f.asEReal x - halfSquaredNorm.asEReal x
  have hφ_bot : φ∗ u ≠ ⊥ := by
    exact conjugate_ne_bot_of_exists_ne_top
      (smul_halfSquaredNorm_sub_conjugate_exists_ne_top (f := f) (γ := γ) hproper) u
  have hφ_top : φ∗ u ≠ ⊤ := (mem_dom_iff_ne_top _ _).1 hu
  have hEq :
      ψ∗ u = ((γ : ℝ) : EReal) * (φ∗ u) - halfSquaredNorm.asEReal u := by
    simpa [φ, ψ] using
      congrFun (conjugate_smul_sub_halfSquaredNorm_eq (f := f) (γ := γ) hproper) u
  cases hφa : φ∗ u with
  | bot =>
      exact False.elim (hφ_bot hφa)
  | top =>
      exact False.elim (hφ_top hφa)
  | coe a =>
      have hψa :
          ψ∗ u = ((((γ : ℝ) * a - ‖u‖ ^ (2 : ℕ) / 2 : ℝ) : EReal)) := by
        rw [hEq, hφa, Function.asEReal_apply, halfSquaredNorm_apply, ← EReal.coe_mul,
          ← EReal.coe_sub]
      have hψ_dom : u ∈ dom ψ∗ := by
        rw [mem_dom_iff_ne_top, hψa]
        exact EReal.coe_ne_top _
      refine ⟨by simpa [ψ] using hψ_dom, ?_⟩
      -- With both conjugate values finite, the defect identity becomes a real cancellation.
      change a - ((γ : ℝ)⁻¹ / 2) * ‖u‖ ^ (2 : ℕ) = (γ : ℝ)⁻¹ * (ψ∗ u).toReal
      rw [hψa]
      simp only [EReal.toReal_coe]
      have hγ0 : (γ : ℝ) ≠ 0 := ne_of_gt γ.2
      field_simp [hγ0]

/-- The canonical `]-∞,+∞]`-valued representative of the conjugate `(γ q - f*)*`, where
`q(x) = ‖x‖² / 2`. -/
noncomputable abbrev conjugateSmulHalfSquaredNormSubConjugate
    (hproper : IsProper f.asEReal) : H → Set.Ioi (⊥ : EReal) :=
  fun u ↦
    ⟨((fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v)∗ u),
      bot_lt_iff_ne_bot.mpr
        (conjugate_ne_bot_of_exists_ne_top
          (smul_halfSquaredNorm_sub_conjugate_exists_ne_top f γ hproper) u)⟩

/-- Coercing `conjugateSmulHalfSquaredNormSubConjugate f γ hproper` back to `EReal` recovers the
canonical conjugate `(γ q - f*)*`. -/
@[simp] theorem conjugateSmulHalfSquaredNormSubConjugate_apply
    (hproper : IsProper f.asEReal) (u : H) :
    (conjugateSmulHalfSquaredNormSubConjugate f γ hproper u : EReal) =
      ((fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v)∗ u) :=
  rfl

-- Semantic recall: `lean_leansearch` confirmed mathlib's owner theorem
-- `strongConvexOn_iff_convex`; the Chapter 10 bridge
-- `StrongConvexOn.toStronglyConvex_effectiveDomain` adds the nonempty-effective-domain premise
-- needed to package an effective-domain result back into `StronglyConvex`.
-- Proof sketch: rewrite `(γ q - f*)*` as `γ⁻¹ q` plus the convex function
-- `γ⁻¹ (γ f - q)*` using Proposition 13.29 (1), then apply Proposition 10.8 in its
-- effective-domain owner form.
/-- Proposition 13.29 (2): source-faithful owner form. The finite representative of
`(γ q - f*)*` is `γ⁻¹`-strongly convex on its effective domain, where `q(x) = ‖x‖² / 2`. -/
theorem strongConvexOn_conjugateSmulHalfSquaredNormSubConjugate
    (hproper : IsProper f.asEReal) :
    StrongConvexOn
      (dom ((fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v)∗))
      ((γ : ℝ)⁻¹)
    (fun u ↦
        ((fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v)∗ u).toReal) :=
  by
    let φ : H → EReal :=
      fun v : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal v - f.asEReal∗ v
    let ψ : H → EReal :=
      fun x : H ↦ ((γ : ℝ) : EReal) * f.asEReal x - halfSquaredNorm.asEReal x
    have hφ_ne_bot : ∀ u : H, φ∗ u ≠ ⊥ := by
      intro u
      exact conjugate_ne_bot_of_exists_ne_top
        (smul_halfSquaredNorm_sub_conjugate_exists_ne_top (f := f) (γ := γ) hproper) u
    have hψ_ne_bot : ∀ u : H, ψ∗ u ≠ ⊥ := by
      intro u
      simpa [ψ] using smul_sub_halfSquaredNorm_conjugate_ne_bot (f := f) (γ := γ) hproper u
    have hψ_convex :
        _root_.ConvexOn ℝ (dom ψ∗) (fun u ↦ (ψ∗ u).toReal) := by
      -- Proposition 13.13 supplies `ψ∗ ∈ Γ(H)`, and the previous helper removes the `⊥` branch.
      simpa [ψ] using
        convexOn_dom_toReal_of_mem_gamma_of_ne_bot
          (H := H) (g := ψ∗) (conjugate_mem_gamma (f := ψ)) hψ_ne_bot
    have hdom_eq : dom φ∗ = dom ψ∗ := by
      ext u
      rw [mem_dom_iff_ne_top, mem_dom_iff_ne_top]
      constructor
      · intro hu
        exact (mem_dom_iff_ne_top _ _).1 <|
          (conjugate_gap_defect_eq_inv_smul_conjugate_tail
            (f := f) (γ := γ) hproper (u := u) ((mem_dom_iff_ne_top _ _).2 hu)).1
      · intro hu
        have hψtop : ψ∗ u ≠ ⊤ := hu
        refine fun hφtop ↦ ?_
        have hEq :
            ψ∗ u = ((γ : ℝ) : EReal) * (φ∗ u) - halfSquaredNorm.asEReal u := by
          simpa [φ, ψ] using
            congrFun
              (conjugate_smul_sub_halfSquaredNorm_eq (f := f) (γ := γ) hproper) u
        have : ψ∗ u = ⊤ := by
          have hγpos : (0 : EReal) < (((γ : ℝ) : EReal)) := by
            exact_mod_cast γ.2
          rw [hEq, hφtop, Function.asEReal_apply, halfSquaredNorm_apply]
          rw [EReal.mul_top_of_pos hγpos]
          simpa using (EReal.top_sub_coe ((‖u‖ ^ (2 : ℕ)) / 2))
        exact hψtop this
    have hψ_scaled :
        _root_.ConvexOn ℝ (dom φ∗) (fun u ↦ (γ : ℝ)⁻¹ * (ψ∗ u).toReal) := by
      rw [hdom_eq]
      simpa [smul_eq_mul] using
        (ConvexOn.smul
          (s := dom ψ∗) (f := fun u ↦ (ψ∗ u).toReal) (c := (γ : ℝ)⁻¹)
          (show 0 ≤ (γ : ℝ)⁻¹ by exact le_of_lt (inv_pos.mpr γ.2)) hψ_convex)
    -- Rewrite strong convexity into convexity of the defect, then identify that defect with the
    -- scaled convex tail using the owner-form equality from the previous helper.
    rw [strongConvexOn_iff_convex]
    refine hψ_scaled.congr ?_
    intro u hu
    simpa [φ, ψ] using
      (conjugate_gap_defect_eq_inv_smul_conjugate_tail
        (f := f) (γ := γ) hproper (u := u) hu).2.symm

-- Proof sketch: once the canonical representative of `(γ q - f*)*` is known to have nonempty
-- effective domain, apply the Chapter 10 bridge
-- `StrongConvexOn.toStronglyConvex_effectiveDomain` to the previous theorem.
/-- Bridge form of Proposition 13.29 (2): if the canonical representative of `(γ q - f*)*` has
nonempty effective domain, then it is `γ⁻¹`-strongly convex. -/
theorem stronglyConvex_conjugateSmulHalfSquaredNormSubConjugate
    (hproper : IsProper f.asEReal)
    (hdom : (effectiveDomain (conjugateSmulHalfSquaredNormSubConjugate f γ hproper)).Nonempty) :
    StronglyConvex
      (conjugateSmulHalfSquaredNormSubConjugate f γ hproper)
      ((γ : ℝ)⁻¹) :=
  by
    -- Rewrite the packaged representative back to the raw conjugate and apply Proposition 10.8.
    refine StrongConvexOn.toStronglyConvex_effectiveDomain ?_ (inv_pos.mpr γ.2) hdom
    simpa [effectiveDomain, dom, conjugateSmulHalfSquaredNormSubConjugate_apply] using
      strongConvexOn_conjugateSmulHalfSquaredNormSubConjugate
        (f := f) (γ := γ) hproper

end

end ERealFunction
