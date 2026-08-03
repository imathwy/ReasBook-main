import Mathlib
import BauschkeLean.Chap07.Exercise_7_1
import BauschkeLean.Chap08.Proposition_8_25
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap09.Proposition_9_42
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Proposition_13_15

-- Declarations for this item will be appended below by the statement pipeline.

open Set

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [local instance] scalar_prod_pseudoMetricSpace_l2
attribute [local instance] scalar_prod_normedAddCommGroup_l2
attribute [local instance] scalar_prod_normedSpace_l2
attribute [local instance] scalar_prod_innerProductSpace_l2

/-- The set `C = {(μ, u) | μ + φ^*(u) ≤ 0}` appearing in the canonical conjugate of the
perspective of `φ`. -/
def perspectiveConjugateSet
    (φ : H → Set.Ioi (⊥ : EReal)) : Set (ℝ × H) :=
  {p | (p.1 : EReal) + (φ.asEReal∗ p.2) ≤ 0}

/- Membership in `perspectiveConjugateSet φ` is the scalar inequality
`μ + φ^*(u) ≤ 0`. -/
-- Proof sketch: unfold `perspectiveConjugateSet`.
@[simp] theorem mem_perspectiveConjugateSet
    (φ : H → Set.Ioi (⊥ : EReal)) {μ : ℝ} {u : H} :
    (μ, u) ∈ perspectiveConjugateSet φ ↔
      ((μ : EReal) + (φ.asEReal∗ u) ≤ 0) := by
  -- The defining set was introduced exactly with this scalar inequality.
  rfl

/- Evaluating the canonical conjugate of the perspective on `ℝ × H` rewrites it as the supremum
of the affine functionals coming from the product pairing `(μ, u) · (ξ, x) = μξ + ⟪u, x⟫`. -/
@[simp] theorem conjugate_perspective_apply
    (φ : H → Set.Ioi (⊥ : EReal)) (p : ℝ × H) :
    (perspective φ.asEReal)∗ p =
      sSup (Set.range fun q : ℝ × H ↦
        (((p.1 * q.1 + ⟪p.2, q.2⟫_ℝ : ℝ) : EReal) -
          perspective φ.asEReal q)) :=
by
  -- Rewrite the indexed supremum from `conjugate_apply` as an `sSup` over its range.
  rw [conjugate_apply, ← sSup_range]
  -- The product Hilbert pairing is exactly `μξ + ⟪u, x⟫` after swapping the real factors.
  congr with q
  congr 1
  change (((q.1 * p.1 + ⟪q.2, p.2⟫_ℝ : ℝ) : EReal)) =
      (((p.1 * q.1 + ⟪p.2, q.2⟫_ℝ : ℝ) : EReal))
  rw [mul_comm, real_inner_comm]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Example 13 9: the finite-value domain of `φ` matches the ordinary domain of
`φ.asEReal`. -/
lemma effectiveDomain_iff_mem_dom_asEReal
    (φ : H → Set.Ioi (⊥ : EReal)) (x : H) :
    x ∈ effectiveDomain φ ↔ x ∈ dom φ.asEReal := by
  -- For subtype-valued functions, being finite is exactly the same as avoiding the value `⊤`
  -- after coercion to `EReal`.
  rw [mem_effectiveDomain_iff, mem_dom_iff_ne_top, Function.asEReal_apply]
  exact lt_top_iff_ne_top

/-- Helper for Example 13 9: after reindexing a positive perspective slice by `x = ξ • z`, the
resulting affine defect factors out the positive scalar `ξ`. -/
lemma positive_height_affine_defect_eq_scaled
    (φ : H → Set.Ioi (⊥ : EReal)) (μ ξ : ℝ) (u z : H) (hξ : 0 < ξ) :
    (((μ * ξ + ⟪u, ξ • z⟫_ℝ : ℝ) : EReal) - perspective φ.asEReal (ξ, ξ • z)) =
      ((ξ : EReal) * ((((μ + ⟪u, z⟫_ℝ : ℝ) : EReal) - φ.asEReal z))) :=
by
  -- Route correction: isolate the positive-height perspective formula before distributing the
  -- scalar through the affine defect.
  rw [perspective_apply_of_pos _ hξ]
  have hcancel : ξ⁻¹ • (ξ • z) = z := by
    simpa [smul_smul] using inv_smul_smul₀ (show ξ ≠ 0 by exact ne_of_gt hξ) z
  rw [hcancel]
  have hinner : ⟪u, ξ • z⟫_ℝ = ξ * ⟪u, z⟫_ℝ := by
    simpa using real_inner_smul_right u z ξ
  rw [hinner]
  have hpair :
      (((μ * ξ + ξ * ⟪u, z⟫_ℝ : ℝ) : EReal)) =
        ((ξ : EReal) * (((μ + ⟪u, z⟫_ℝ : ℝ) : EReal))) := by
    exact_mod_cast (show μ * ξ + ξ * ⟪u, z⟫_ℝ = ξ * (μ + ⟪u, z⟫_ℝ) by ring)
  -- Split on whether `φ z` is finite or `⊤`; this avoids relying on nonexistent distributivity on
  -- all of `EReal`.
  cases hφz : φ.asEReal z with
  | bot =>
      exfalso
      exact (ne_of_gt (φ z).2) hφz
  | top =>
      rw [hpair]
      rw [EReal.coe_mul_top_of_pos hξ, EReal.sub_top, EReal.sub_top,
        EReal.coe_mul_bot_of_pos hξ]
  | coe r =>
      rw [hpair]
      -- Once `φ z` is finite, both sides are casts of the same real distributivity identity.
      exact_mod_cast (show ξ * (μ + ⟪u, z⟫_ℝ) - ξ * r = ξ * ((μ + ⟪u, z⟫_ℝ) - r) by ring)

/-- Helper for Example 13 9: adding a real constant to the pairing adds the same constant to the
corresponding affine defect. -/
lemma affine_defect_add_const
    (φ : H → Set.Ioi (⊥ : EReal)) (μ : ℝ) (u z : H) :
    (((μ + ⟪u, z⟫_ℝ : ℝ) : EReal) - φ.asEReal z) =
      (μ : EReal) + ((((⟪u, z⟫_ℝ : ℝ) : EReal) - φ.asEReal z)) :=
by
  -- Reassociate the subtraction as addition by `-φ z`, then peel off the real constant `μ`.
  rw [sub_eq_add_neg, sub_eq_add_neg, EReal.coe_add, add_assoc]

/-- Helper for Example 13 9: a finite real shift commutes with the supremum of the canonical
affine-defect range. -/
lemma sSup_range_affine_defect_add_real
    (φ : H → Set.Ioi (⊥ : EReal)) (μ : ℝ) (u : H) :
    sSup (Set.range fun z : H ↦
      (μ : EReal) + ((((⟪z, u⟫_ℝ : ℝ) : EReal) - φ.asEReal z))) =
      (μ : EReal) + sSup (Set.range fun z : H ↦
        ((((⟪z, u⟫_ℝ : ℝ) : EReal) - φ.asEReal z))) := by
  -- Rewrite the set supremum as an indexed supremum so the finite real shift can move through it.
  rw [sSup_range, sSup_range]
  have hright :
      (μ : EReal) + (⨆ z : H, (((⟪z, u⟫_ℝ : ℝ) : EReal) - φ.asEReal z)) ≤
        ⨆ z : H, (μ : EReal) + ((((⟪z, u⟫_ℝ : ℝ) : EReal) - φ.asEReal z)) := by
    have hsub :
        (⨆ z : H, (((⟪z, u⟫_ℝ : ℝ) : EReal) - φ.asEReal z)) ≤
          (⨆ z : H, (μ : EReal) + ((((⟪z, u⟫_ℝ : ℝ) : EReal) - φ.asEReal z))) - (μ : EReal) := by
      refine iSup_le fun z ↦ ?_
      have hle :
          (((⟪z, u⟫_ℝ : ℝ) : EReal) - φ.asEReal z) + (μ : EReal) ≤
            ⨆ z : H, (μ : EReal) + ((((⟪z, u⟫_ℝ : ℝ) : EReal) - φ.asEReal z)) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (le_iSup
            (fun z : H ↦ (μ : EReal) + ((((⟪z, u⟫_ℝ : ℝ) : EReal) - φ.asEReal z))) z)
      exact (EReal.le_sub_iff_add_le
        (Or.inl (EReal.coe_ne_bot μ))
        (Or.inl (EReal.coe_ne_top μ))).2 hle
    simpa [add_comm, add_left_comm, add_assoc] using
      (EReal.le_sub_iff_add_le
        (Or.inl (EReal.coe_ne_bot μ))
        (Or.inl (EReal.coe_ne_top μ))).1 hsub
  have hleft :
      (⨆ z : H, (μ : EReal) + ((((⟪z, u⟫_ℝ : ℝ) : EReal) - φ.asEReal z))) ≤
        (μ : EReal) + (⨆ z : H, (((⟪z, u⟫_ℝ : ℝ) : EReal) - φ.asEReal z)) := by
    refine iSup_le fun z ↦ ?_
    exact add_le_add le_rfl (le_iSup (fun z : H ↦ (((⟪z, u⟫_ℝ : ℝ) : EReal) - φ.asEReal z)) z)
  exact le_antisymm hleft hright

/-- Helper for Example 13 9: reindexing the positive-height slice by `x = ξ • z` turns the affine
defect range into the scaled defect range over `z`. -/
lemma positive_slice_range_eq_scaled_defect_range
    (φ : H → Set.Ioi (⊥ : EReal)) (μ ξ : ℝ) (u : H) (hξ : 0 < ξ) :
    Set.range (fun x : H ↦
      (((μ * ξ + ⟪u, x⟫_ℝ : ℝ) : EReal) - perspective φ.asEReal (ξ, x))) =
      Set.range (fun z : H ↦
        ((ξ : EReal) * ((((μ + ⟪u, z⟫_ℝ : ℝ) : EReal) - φ.asEReal z)))) := by
  ext r
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨ξ⁻¹ • x, ?_⟩
    -- Normalize the witness `ξ⁻¹ • x` directly; `simp` collapses the residual scalar transport.
    have hx : ξ • (ξ⁻¹ • x) = x := by
      simpa [smul_smul] using smul_inv_smul₀ hξ.ne' x
    simpa [hx] using
      (positive_height_affine_defect_eq_scaled φ μ ξ u (ξ⁻¹ • x) hξ).symm
  · rintro ⟨z, rfl⟩
    refine ⟨ξ • z, ?_⟩
    -- The forward direction is the same identity read from right to left.
    simpa using
      positive_height_affine_defect_eq_scaled φ μ ξ u z hξ

/-- Helper for Example 13 9: the supremum over a positive perspective slice is exactly the
positive scalar multiple of `μ + φ^*(u)`. -/
lemma positive_perspective_slice_sup_eq_scaled_conjugate_term
    (φ : H → Set.Ioi (⊥ : EReal)) (μ : ℝ) (u : H) (ξ : Set.Ioi (0 : ℝ)) :
    sSup (Set.range fun x : H ↦
      ((((μ * (ξ : ℝ) + ⟪u, x⟫_ℝ : ℝ) : EReal) - perspective φ.asEReal ((ξ : ℝ), x)))) =
      ((ξ : ℝ) : EReal) * ((μ : EReal) + φ.asEReal∗ u) :=
by
  -- Route correction: first reindex the positive-height slice, then pull out the positive scalar,
  -- and only then identify the remaining affine-defect supremum with the conjugate.
  rw [positive_slice_range_eq_scaled_defect_range φ μ (ξ : ℝ) u ξ.2]
  have hscaled_range :
      Set.range (fun z : H ↦
        (((ξ : ℝ) : EReal) * ((((μ + ⟪u, z⟫_ℝ : ℝ) : EReal) - φ.asEReal z))) ) =
        (fun t : EReal ↦ (((ξ : ℝ) : EReal) * t)) ''
          Set.range (fun z : H ↦
            ((((μ + ⟪u, z⟫_ℝ : ℝ) : EReal) - φ.asEReal z)) ) := by
    -- This is only a repackaging of the same range as the image of multiplication by `ξ`.
    ext r
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, ⟨z, rfl⟩, rfl⟩
    · rintro ⟨t, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
  rw [hscaled_range, ereal_pos_mul_sSup _ ξ.2]
  have hdefect_range :
      Set.range (fun z : H ↦
        ((((μ + ⟪u, z⟫_ℝ : ℝ) : EReal) - φ.asEReal z))) =
        Set.range (fun z : H ↦
          (μ : EReal) + ((((⟪z, u⟫_ℝ : ℝ) : EReal) - φ.asEReal z))) := by
    -- Rewrite each term into the canonical `conjugate_apply` shape `⟪z,u⟫ - φ z`.
    ext r
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨z, ?_⟩
      dsimp
      calc
        (μ : EReal) + ((((⟪z, u⟫_ℝ : ℝ) : EReal) - φ.asEReal z))
            = (μ : EReal) + ((((⟪u, z⟫_ℝ : ℝ) : EReal) - φ.asEReal z)) := by
              rw [real_inner_comm]
        _ = (((μ + ⟪u, z⟫_ℝ : ℝ) : EReal) - φ.asEReal z) := by
              symm
              exact affine_defect_add_const φ μ u z
    · rintro ⟨z, rfl⟩
      refine ⟨z, ?_⟩
      dsimp
      calc
        ((((μ + ⟪u, z⟫_ℝ : ℝ) : EReal) - φ.asEReal z))
            = (μ : EReal) + ((((⟪u, z⟫_ℝ : ℝ) : EReal) - φ.asEReal z)) :=
              affine_defect_add_const φ μ u z
        _ = (μ : EReal) + ((((⟪z, u⟫_ℝ : ℝ) : EReal) - φ.asEReal z)) := by
              rw [real_inner_comm]
  -- The shift lemma isolates `μ`, and the remaining supremum is exactly `φ^*(u)`.
  rw [congrArg sSup hdefect_range, sSup_range_affine_defect_add_real]
  rw [conjugate_apply, ← sSup_range]

/-- Helper for Example 13 9: evaluating the conjugate of the perspective at `(μ, u)` reduces to
the one-dimensional positive-ray supremum in the coefficient
`(μ : EReal) + φ.asEReal∗ u`. -/
lemma conjugate_perspective_apply_eq_sSup_pos_mul
    (φ : H → Set.Ioi (⊥ : EReal)) (μ : ℝ) (u : H) :
    (perspective φ.asEReal)∗ (μ, u) =
      sSup (Set.range fun ξ : Set.Ioi (0 : ℝ) ↦
        ((ξ : ℝ) : EReal) * ((μ : EReal) + φ.asEReal∗ u)) := by
  -- Route correction: reduce the product-space supremum to positive-height slices first, then
  -- identify each positive slice with the scaled conjugate term from the source computation.
  rw [conjugate_perspective_apply]
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨⟨ξ, x⟩, rfl⟩
    by_cases hξ : 0 < ξ
    · -- A point on a positive slice is bounded by the supremum of that slice.
      let ξpos : Set.Ioi (0 : ℝ) := ⟨ξ, hξ⟩
      have hslice :
          ((((μ * ξ + ⟪u, x⟫_ℝ : ℝ) : EReal) - perspective φ.asEReal (ξ, x))) ≤
            sSup (Set.range fun y : H ↦
              ((((μ * (ξpos : ℝ) + ⟪u, y⟫_ℝ : ℝ) : EReal) -
                perspective φ.asEReal ((ξpos : ℝ), y)))) := by
        exact le_sSup ⟨x, rfl⟩
      rw [positive_perspective_slice_sup_eq_scaled_conjugate_term φ μ u ξpos] at hslice
      exact hslice.trans <| le_sSup ⟨ξpos, rfl⟩
    · -- Nonpositive heights contribute `⊥`, so they do not affect the supremum.
      change ((((μ * ξ + ⟪u, x⟫_ℝ : ℝ) : EReal) - perspective φ.asEReal (ξ, x))) ≤
        sSup (Set.range fun ξ : Set.Ioi (0 : ℝ) ↦
          ((ξ : ℝ) : EReal) * ((μ : EReal) + φ.asEReal∗ u))
      rw [perspective_apply_of_nonpos _ (le_of_not_gt hξ), EReal.sub_top]
      exact bot_le
  · refine sSup_le ?_
    rintro _ ⟨ξ, rfl⟩
    -- Each positive slice sits inside the full product-space range.
    change ((ξ : ℝ) : EReal) * ((μ : EReal) + φ.asEReal∗ u) ≤
      sSup (Set.range fun q : ℝ × H ↦
        (((μ * q.1 + ⟪u, q.2⟫_ℝ : ℝ) : EReal) - perspective φ.asEReal q))
    rw [← positive_perspective_slice_sup_eq_scaled_conjugate_term φ μ u ξ]
    refine sSup_le ?_
    rintro _ ⟨x, rfl⟩
    exact le_sSup ⟨((ξ : ℝ), x), rfl⟩

/-- Helper for Example 13 9: if the coefficient `a` is strictly negative and not `⊥`, then the
positive-ray supremum `sup_{ξ>0} ξ a` is `0`. -/
lemma sSup_pos_mul_eq_zero_of_neg
    (a : EReal) (ha_ne_bot : a ≠ ⊥) (ha_neg : a < 0) :
    sSup (Set.range fun ξ : Set.Ioi (0 : ℝ) ↦ ((ξ : ℝ) : EReal) * a) = 0 :=
by
  -- Route correction: the source closes the negative branch on the one-dimensional ray itself, so
  -- we reduce to the finite real case and identify `0` as the least upper bound directly.
  cases a with
  | bot =>
      exact (ha_ne_bot rfl).elim
  | top =>
      exact (not_lt_of_ge le_top ha_neg).elim
  | coe r =>
      have hr_neg : r < 0 := by
        exact_mod_cast ha_neg
      refine sSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_
      · intro y hy
        rcases hy with ⟨ξ, rfl⟩
        -- Every positive multiple of a negative real coefficient stays below `0`.
        have hmul_nonpos : (ξ : ℝ) * r ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos ξ.2.le hr_neg.le
        simpa [EReal.coe_mul] using (show (((ξ : ℝ) * r : ℝ) : EReal) ≤ (0 : EReal) by
          exact_mod_cast hmul_nonpos)
      · intro z hz
        cases z with
        | bot =>
            let onePos : Set.Ioi (0 : ℝ) := ⟨1, by simp⟩
            refine ⟨(((onePos : ℝ) : EReal) * (r : EReal)), ?_, ?_⟩
            · exact ⟨onePos, rfl⟩
            · simp [onePos]
        | top =>
            exact (not_lt_of_ge le_top hz).elim
        | coe y =>
            have hy_neg : y < 0 := by
              exact_mod_cast hz
            let t : ℝ := y / r / 2
            have ht : 0 < t := by
              dsimp [t]
              have hdiv_pos : 0 < y / r := div_pos_of_neg_of_neg hy_neg hr_neg
              positivity
            have hy_lt_scaled : y < t * r := by
              have hhalf : y < y / 2 := by
                linarith
              have hmul : t * r = y / 2 := by
                dsimp [t]
                field_simp [hr_neg.ne]
              rw [hmul]
              exact hhalf
            let tpos : Set.Ioi (0 : ℝ) := ⟨t, ht⟩
            refine ⟨(((tpos : ℝ) : EReal) * (r : EReal)), ?_, ?_⟩
            · exact ⟨tpos, rfl⟩
            · simpa [tpos, EReal.coe_mul] using
                (show ((y : ℝ) : EReal) < (((t * r : ℝ) : EReal)) by
                  exact_mod_cast hy_lt_scaled)

/-- Helper for Example 13 9: if the coefficient `a` is strictly positive, then the positive-ray
supremum `sup_{ξ>0} ξ a` is `⊤`. -/
lemma sSup_pos_mul_eq_top_of_pos
    (a : EReal) (ha_pos : 0 < a) :
    sSup (Set.range fun ξ : Set.Ioi (0 : ℝ) ↦ ((ξ : ℝ) : EReal) * a) = ⊤ :=
by
  cases a with
  | bot =>
      exact (not_lt_of_ge bot_le ha_pos).elim
  | top =>
      -- Every real lower bound is beaten already by the positive multiplier `ξ = 1`.
      rw [EReal.eq_top_iff_forall_lt]
      intro y
      let onePos : Set.Ioi (0 : ℝ) := ⟨1, by simp⟩
      have hmem :
          (((onePos : ℝ) : EReal) * (⊤ : EReal)) ∈
            Set.range fun ξ : Set.Ioi (0 : ℝ) ↦ ((ξ : ℝ) : EReal) * (⊤ : EReal) :=
        ⟨onePos, rfl⟩
      have hone_top : (((onePos : ℝ) : EReal) * (⊤ : EReal)) = ⊤ := by
        simpa using (EReal.coe_mul_top_of_pos onePos.2)
      have hy_lt : (y : EReal) < (((onePos : ℝ) : EReal) * (⊤ : EReal)) := by
        rw [hone_top]
        exact EReal.coe_lt_top y
      exact lt_of_lt_of_le hy_lt (le_sSup hmem)
  | coe r =>
      have hr_pos : 0 < r := by
        exact_mod_cast ha_pos
      -- For a finite positive coefficient, scale far enough along the ray to exceed any target
      -- real level.
      rw [EReal.eq_top_iff_forall_lt]
      intro y
      let t : ℝ := |y| / r + 1
      have ht : 0 < t := by
        dsimp [t]
        positivity
      have hmul : t * r = |y| + r := by
        dsimp [t]
        field_simp [hr_pos.ne']
      have hy_lt : y < t * r := by
        rw [hmul]
        have hy_abs : y ≤ |y| := le_abs_self y
        linarith
      let tpos : Set.Ioi (0 : ℝ) := ⟨t, ht⟩
      have hmem :
          (((tpos : ℝ) : EReal) * (r : EReal)) ∈
            Set.range fun ξ : Set.Ioi (0 : ℝ) ↦ ((ξ : ℝ) : EReal) * (r : EReal) :=
        ⟨tpos, rfl⟩
      calc
        (y : EReal) < (((tpos : ℝ) : EReal) * (r : EReal)) := by
          simpa [tpos, EReal.coe_mul] using
            (show (y : EReal) < (((t * r : ℝ) : EReal)) by
              exact_mod_cast hy_lt)
        _ ≤ sSup (Set.range fun ξ : Set.Ioi (0 : ℝ) ↦ ((ξ : ℝ) : EReal) * (r : EReal)) := by
          exact le_sSup hmem

-- Proof sketch: expand the Fenchel conjugate of the perspective on `ℝ × H`, then separate the
-- supremum over the positive scalar variable `ξ`. The inner supremum is exactly `φ^*(u)`, so the
-- remaining one-dimensional supremum is exactly the textbook indicator of
-- `perspectiveConjugateSet φ`. For `φ : H → Set.Ioi (⊥ : EReal)`, the only remaining properness
-- content is that the effective domain is nonempty.
/-- Example 13 9: if `φ` attains at least one finite value, then the Fenchel conjugate of the
perspective is the textbook indicator `ι[C]` of the set `C = {(μ, u) | μ + φ^*(u) ≤ 0}`. -/
theorem conjugate_perspective_eq_indicator_perspectiveConjugateSet
    (φ : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain φ).Nonempty) :
    (perspective φ.asEReal)∗ =
      (ι[perspectiveConjugateSet φ]).asEReal :=
by
  funext p
  rcases p with ⟨μ, u⟩
  let a : EReal := (μ : EReal) + φ.asEReal∗ u
  have hproper : IsProper φ.asEReal := by
    refine ⟨?_, ?_⟩
    · intro x
      exact ne_of_gt (φ x).2
    · rcases hdom with ⟨x, hx⟩
      exact ⟨x, (effectiveDomain_iff_mem_dom_asEReal φ x).1 hx⟩
  have ha_ne_bot : a ≠ ⊥ := by
    -- Properness gives `φ^*(u) ≠ ⊥`, and adding a real cannot create `⊥`.
    refine (EReal.add_ne_bot_iff.2 ?_)
    constructor
    · exact EReal.coe_ne_bot μ
    · exact conjugate_ne_bot_of_isProper hproper u
  -- Evaluate the conjugate through the positive-ray supremum, then split on the indicator set.
  rw [conjugate_perspective_apply_eq_sSup_pos_mul]
  by_cases hmem : (μ, u) ∈ perspectiveConjugateSet φ
  · have ha_le_zero : a ≤ 0 := by
      simpa [a] using (mem_perspectiveConjugateSet (φ := φ) (μ := μ) (u := u)).1 hmem
    by_cases hzero : a = 0
    · have ha_zero : ((μ : EReal) + φ.asEReal∗ u) = 0 := by
        simpa [a] using hzero
      have ha_zero' :
          (↑μ + ⨆ x : H, (((⟪x, u⟫_ℝ : ℝ) : EReal) - φ.asEReal x)) = 0 := by
        simpa [conjugate_apply] using ha_zero
      simp [Function.asEReal_apply, indicator_apply, hmem, ha_zero']
    · have ha_neg : a < 0 := lt_of_le_of_ne ha_le_zero hzero
      simpa [Function.asEReal_apply, indicator_apply, hmem] using
        sSup_pos_mul_eq_zero_of_neg a ha_ne_bot ha_neg
  · have ha_pos : 0 < a := by
      refine lt_of_not_ge ?_
      intro ha_le_zero
      apply hmem
      exact (mem_perspectiveConjugateSet (φ := φ) (μ := μ) (u := u)).2 <| by
        simpa [a] using ha_le_zero
    simpa [Function.asEReal_apply, indicator_apply, hmem] using
      sSup_pos_mul_eq_top_of_pos a ha_pos

/-- Helper for Example 13 9: if the effective domain is empty, then the perspective is
identically `⊤`. -/
lemma perspective_eq_top_of_effectiveDomain_eq_empty
    (φ : H → Set.Ioi (⊥ : EReal)) (hempty : effectiveDomain φ = ∅) :
    perspective φ.asEReal = fun _ : ℝ × H ↦ (⊤ : EReal) := by
  funext p
  rcases p with ⟨ξ, x⟩
  by_cases hξ : 0 < ξ
  · -- Positive-height values reduce to `ξ * φ (ξ⁻¹ • x)`, and emptiness of the effective domain
    -- forces that underlying value to be `⊤`.
    rw [perspective_apply_of_pos _ hξ]
    have htop : (φ (ξ⁻¹ • x) : EReal) = ⊤ := by
      by_contra hfinite
      have hxdom : ξ⁻¹ • x ∈ effectiveDomain φ := by
        exact mem_effectiveDomain_iff.mpr (lt_top_iff_ne_top.mpr hfinite)
      rw [hempty] at hxdom
      exact hxdom
    rw [Function.asEReal_apply, htop]
    exact EReal.coe_mul_top_of_pos hξ
  · -- Nonpositive heights lie on the `+∞` branch of the perspective by definition.
    rw [perspective_apply_of_nonpos _ (le_of_not_gt hξ)]

-- Proof sketch: if `φ` has empty effective domain, then `φ ≡ ⊤`; the perspective is identically
-- `⊤`, and its conjugate collapses to `⊥`.
/-- In the empty-domain degenerate case of Example 13.9, the perspective conjugate is identically
`⊥`. -/
theorem conjugate_perspective_eq_bot_of_effectiveDomain_eq_empty
    (φ : H → Set.Ioi (⊥ : EReal)) (hempty : effectiveDomain φ = ∅) :
    (perspective φ.asEReal)∗ = fun _ : ℝ × H ↦ (⊥ : EReal) := by
  -- Route correction: collapse the perspective itself to the constant `⊤` function first, then
  -- compute the conjugate pointwise from the defining supremum.
  have hpersp : perspective φ.asEReal = fun _ : ℝ × H ↦ (⊤ : EReal) :=
    perspective_eq_top_of_effectiveDomain_eq_empty φ hempty
  ext p
  -- Every affine defect is `-∞` because subtracting `⊤` kills the expression pointwise.
  rw [conjugate_apply, hpersp]
  simp

end

end ERealFunction
