import Mathlib
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace translate

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 13 23: multiplying the affine defect by a positive scalar is the same
as scaling the function value and evaluating the dual variable at the inverse homothety. -/
lemma pos_smul_affine_defect
    (α : Set.Ioi (0 : ℝ)) (x u : H) (a : EReal) :
    ((α : ℝ) : EReal) * ((((⟪x, ((α : ℝ)⁻¹) • u⟫_ℝ : ℝ) : EReal) - a)) =
      (((⟪x, u⟫_ℝ : ℝ) : EReal) - ((α : ℝ) : EReal) * a) := by
  let αR : ℝ := α
  let αE : EReal := (αR : EReal)
  have hα0 : αR ≠ 0 := α.2.ne'
  have hαE_pos : 0 < αE := EReal.coe_pos.mpr α.2
  by_cases htop : a = ⊤
  · -- For `a = ⊤`, both affine defects collapse to `⊥`.
    subst htop
    simp [αR, αE, EReal.mul_bot_of_pos, EReal.mul_top_of_pos, hαE_pos]
  by_cases hbot : a = ⊥
  · -- For `a = ⊥`, both affine defects collapse to `⊤`.
    subst hbot
    simp [αR, αE, EReal.mul_bot_of_pos, EReal.mul_top_of_pos, hαE_pos, EReal.sub_bot]
  have hcoe : ((a.toReal : ℝ) : EReal) = a := EReal.coe_toReal htop hbot
  have hreal :
      αR * (⟪x, αR⁻¹ • u⟫_ℝ - a.toReal) =
        ⟪x, u⟫_ℝ - αR * a.toReal := by
    -- In the finite branch, the `EReal` statement reduces to the corresponding real identity.
    rw [real_inner_smul_right]
    calc
      αR * (αR⁻¹ * ⟪x, u⟫_ℝ - a.toReal) =
          αR * (αR⁻¹ * ⟪x, u⟫_ℝ) - αR * a.toReal := by ring
      _ = (αR * αR⁻¹) * ⟪x, u⟫_ℝ - αR * a.toReal := by ring
      _ = ⟪x, u⟫_ℝ - αR * a.toReal := by
        rw [mul_inv_cancel₀ hα0, one_mul]
  -- Transport the finite real identity back to `EReal`.
  rw [← hcoe]
  simpa [αR, αE] using congrArg (fun t : ℝ ↦ (t : EReal)) hreal

/-- Helper for Proposition 13 23: after translating by `y`, the affine defect splits into the
residual defect at `u - v` plus the finite correction `⟪y,u⟫ - ⟪y,v⟫ - β`. -/
lemma translate_inner_const_affine_defect
    (a : EReal) (y v u z : H) (β : ℝ) :
    (((⟪z + y, u⟫_ℝ : ℝ) : EReal) -
        (a + ((⟪z + y, v⟫_ℝ : ℝ) : EReal) + ((β : ℝ) : EReal))) =
      ((((⟪z, u - v⟫_ℝ : ℝ) : EReal) - a) +
        (((⟪y, u⟫_ℝ : ℝ) : EReal) - ((⟪y, v⟫_ℝ : ℝ) : EReal) - ((β : ℝ) : EReal))) := by
  by_cases htop : a = ⊤
  · -- If `a = ⊤`, both sides are `⊥`.
    subst htop
    simp
  by_cases hbot : a = ⊥
  · -- If `a = ⊥`, both sides are `⊤`.
    subst hbot
    have hshift_ne_bot :
        (((⟪y, u⟫_ℝ : ℝ) : EReal) - ((⟪y, v⟫_ℝ : ℝ) : EReal) - ((β : ℝ) : EReal)) ≠ ⊥ := by
      rw [← EReal.coe_sub, ← EReal.coe_sub]
      exact EReal.coe_ne_bot _
    simp [EReal.sub_bot, hshift_ne_bot, EReal.top_add_of_ne_bot]
  have hcoe : ((a.toReal : ℝ) : EReal) = a := EReal.coe_toReal htop hbot
  have hreal :
      ⟪z + y, u⟫_ℝ - (a.toReal + ⟪z + y, v⟫_ℝ + β) =
        (⟪z, u - v⟫_ℝ - a.toReal) + (⟪y, u⟫_ℝ - ⟪y, v⟫_ℝ - β) := by
    -- Expand the translated pairing and regroup the finite correction terms.
    rw [inner_add_left, inner_add_left, inner_sub_right]
    ring
  -- Reduce the `EReal` statement to the finite real identity.
  rw [← hcoe]
  calc
    (((⟪z + y, u⟫_ℝ : ℝ) : EReal) -
        (((a.toReal : ℝ) : EReal) + ((⟪z + y, v⟫_ℝ : ℝ) : EReal) + ((β : ℝ) : EReal))) =
          (((⟪z + y, u⟫_ℝ - (a.toReal + ⟪z + y, v⟫_ℝ + β) : ℝ) : EReal)) := by
            rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_sub]
    _ = ((((⟪z, u - v⟫_ℝ - a.toReal) + (⟪y, u⟫_ℝ - ⟪y, v⟫_ℝ - β) : ℝ) : EReal)) := by
          exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
    _ = (((((⟪z, u - v⟫_ℝ : ℝ) : EReal) - (((a.toReal : ℝ) : EReal))) +
        (((⟪y, u⟫_ℝ : ℝ) : EReal) - ((⟪y, v⟫_ℝ : ℝ) : EReal) - ((β : ℝ) : EReal)))) := by
          rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add]

/-- Helper for Proposition 13 23: multiplying by a positive real scalar commutes with `iSup` in
`EReal`. -/
lemma ereal_inv_mul_cancel_of_pos
    (α : Set.Ioi (0 : ℝ)) (a : EReal) :
    (((((α : ℝ) : EReal)⁻¹) * (((α : ℝ) : EReal))) * a) = a := by
  have hcancel : (((α : ℝ) : EReal)⁻¹) * (((α : ℝ) : EReal)) = 1 := by
    -- Rewrite the finite `EReal` coefficient back to `ℝ`, cancel there, and recast.
    rw [← EReal.coe_inv, ← EReal.coe_mul, inv_mul_cancel₀ α.2.ne', EReal.coe_one]
  rw [hcancel, one_mul]

/-- Helper for Proposition 13 23: a positive finite scalar cancels with its inverse on the left in
`EReal`. -/
lemma ereal_mul_inv_cancel_of_pos
    (α : Set.Ioi (0 : ℝ)) (a : EReal) :
    ((((α : ℝ) : EReal) * ((((α : ℝ) : EReal)⁻¹) * a)) = a) := by
  have hcancel : (((α : ℝ) : EReal) * (((α : ℝ) : EReal)⁻¹)) = 1 := by
    -- Rewrite the finite `EReal` coefficient back to `ℝ`, cancel there, and recast.
    rw [← EReal.coe_inv, ← EReal.coe_mul, mul_inv_cancel₀ α.2.ne', EReal.coe_one]
  rw [← mul_assoc, hcancel, one_mul]

/-- Helper for Proposition 13 23: multiplying by a positive real scalar commutes with `iSup` in
`EReal`. -/
lemma ereal_mul_iSup_of_pos
    {ι : Sort*} (α : Set.Ioi (0 : ℝ)) (φ : ι → EReal) :
    ((α : ℝ) : EReal) * (⨆ i, φ i) =
      ⨆ i, ((α : ℝ) : EReal) * φ i := by
  let αE : EReal := ((α : ℝ) : EReal)
  have hαE_nonneg : 0 ≤ αE := le_of_lt (EReal.coe_pos.mpr α.2)
  have hαEinv_nonneg : 0 ≤ αE⁻¹ := EReal.inv_nonneg_of_nonneg hαE_nonneg
  have hmono_mul : Monotone (fun t : EReal ↦ αE * t) := by
    intro a b hab
    exact mul_le_mul_of_nonneg_left hab hαE_nonneg
  have hmono_inv : Monotone (fun t : EReal ↦ αE⁻¹ * t) := by
    intro a b hab
    exact mul_le_mul_of_nonneg_left hab hαEinv_nonneg
  have hright :
      (⨆ i, αE * φ i) ≤ αE * (⨆ i, φ i) := by
    simpa [αE] using (hmono_mul.le_map_iSup (s := φ))
  have hinv :
      (⨆ i, φ i) ≤ αE⁻¹ * (⨆ i, αE * φ i) := by
    calc
      (⨆ i, φ i) = ⨆ i, αE⁻¹ * (αE * φ i) := by
        refine iSup_congr fun i => ?_
        simpa [αE, mul_assoc] using (ereal_inv_mul_cancel_of_pos α (φ i)).symm
      _ ≤ αE⁻¹ * (⨆ i, αE * φ i) := by
        simpa using (hmono_inv.le_map_iSup (s := fun i : ι ↦ αE * φ i))
  have hleft_aux :
      αE * (⨆ i, φ i) ≤ αE * (αE⁻¹ * (⨆ i, αE * φ i)) := by
    exact mul_le_mul_of_nonneg_left hinv hαE_nonneg
  have hleft :
      αE * (⨆ i, φ i) ≤ ⨆ i, αE * φ i := by
    simpa [αE, mul_assoc, ereal_mul_inv_cancel_of_pos] using hleft_aux
  exact le_antisymm hleft hright

/-- Helper for Proposition 13 23: adding a finite real shift commutes with `iSup` in `EReal`. -/
lemma ereal_iSup_add_of_real_shift
    {ι : Sort*} (r : ℝ) (φ : ι → EReal) :
    (⨆ i, φ i + ((r : ℝ) : EReal)) =
      (⨆ i, φ i) + ((r : ℝ) : EReal) := by
  -- First push the real shift through the supremum by monotonicity.
  have hright :
      (⨆ i, φ i) + ((r : ℝ) : EReal) ≤
        (⨆ i, φ i + ((r : ℝ) : EReal)) := by
    -- Each shifted term already appears below the shifted supremum.
    have hsub :
        (⨆ i, φ i) ≤ (⨆ i, φ i + ((r : ℝ) : EReal)) - ((r : ℝ) : EReal) := by
      refine iSup_le fun i ↦ ?_
      exact (EReal.le_sub_iff_add_le
        (Or.inl (EReal.coe_ne_bot r))
        (Or.inl (EReal.coe_ne_top r))).2 (le_iSup (fun i ↦ φ i + ((r : ℝ) : EReal)) i)
    exact (EReal.le_sub_iff_add_le
      (Or.inl (EReal.coe_ne_bot r))
      (Or.inl (EReal.coe_ne_top r))).1 hsub
  have hleft :
      (⨆ i, φ i + ((r : ℝ) : EReal)) ≤
        (⨆ i, φ i) + ((r : ℝ) : EReal) := by
    refine iSup_le fun i ↦ ?_
    exact add_le_add (le_iSup φ i) le_rfl
  exact le_antisymm hleft hright

-- Proof sketch: expand `conjugate`, pull the positive scalar `α` out of the supremum, and rewrite
-- `⟪x, u⟫ - α f x` as `α * (⟪x, α⁻¹ • u⟫ - f x)`.
/-- Proposition 13 23: clause (i). Scaling an extended-real-valued function by a positive
scalar sends its conjugate to the same scalar multiple of the conjugate evaluated at the inversely
scaled dual variable. -/
theorem conjugate_pos_smul
    (f : H → EReal) (α : Set.Ioi (0 : ℝ)) :
    (fun x : H ↦ ((α : ℝ) : EReal) * f x)∗ =
      fun u : H ↦ ((α : ℝ) : EReal) * f∗ (((α : ℝ)⁻¹) • u) :=
by
  let αR : ℝ := α
  let αE : EReal := (αR : EReal)
  have hαE_pos : 0 < αE := EReal.coe_pos.mpr α.2
  ext u
  -- Rewrite each affine defect into a positive scalar times the rescaled defect.
  rw [conjugate_apply, conjugate_apply]
  calc
    (⨆ x : H, (((⟪x, u⟫_ℝ : ℝ) : EReal) - αE * f x)) =
        ⨆ x : H, αE * ((((⟪x, αR⁻¹ • u⟫_ℝ : ℝ) : EReal) - f x)) := by
          refine iSup_congr fun x ↦ ?_
          simpa [αR, αE] using (pos_smul_affine_defect α x u (f x)).symm
    _ = αE * (⨆ x : H, (((⟪x, αR⁻¹ • u⟫_ℝ : ℝ) : EReal) - f x)) := by
          -- Transport the positive scalar through the supremum by monotonicity on both sides.
          symm
          simpa [αE] using ereal_mul_iSup_of_pos α
            (fun x : H ↦ (((⟪x, αR⁻¹ • u⟫_ℝ : ℝ) : EReal) - f x))

/-- Helper for Proposition 13 23: reindexing by the homothety `x = α • z` identifies the
rescaled conjugate evaluation with the original conjugate. -/
lemma conjugate_precompose_inv_smul_apply
    (f : H → EReal) (α : Set.Ioi (0 : ℝ)) (u : H) :
    (fun x : H ↦ f (((α : ℝ)⁻¹) • x))∗ (((α : ℝ)⁻¹) • u) = f∗ u := by
  let αR : ℝ := α
  have hα0 : αR ≠ 0 := α.2.ne'
  -- Reindex the defining supremum by the bijective homothety `z ↦ α • z`.
  rw [conjugate_apply, conjugate_apply]
  have hsurj : Function.Surjective (fun z : H ↦ αR • z) := by
    intro x
    refine ⟨αR⁻¹ • x, ?_⟩
    simpa [αR] using smul_inv_smul₀ hα0 x
  exact (hsurj.iSup_congr (fun z : H ↦ αR • z) fun z => by
    -- The homothety cancels in both the pairing and the function argument.
    have hpair : ⟪αR • z, αR⁻¹ • u⟫_ℝ = ⟪z, u⟫_ℝ := by
      rw [real_inner_smul_left, real_inner_smul_right]
      calc
        αR * (αR⁻¹ * ⟪z, u⟫_ℝ) = (αR * αR⁻¹) * ⟪z, u⟫_ℝ := by ring
        _ = ⟪z, u⟫_ℝ := by rw [mul_inv_cancel₀ hα0, one_mul]
    rw [hpair, inv_smul_smul₀ hα0]
  ).symm

-- Proof sketch: combine clause (i) with the change of variables `x = α • z` in the defining
-- supremum, or equivalently precompose by the inverse homothety and absorb the scaling into the
-- dual pairing.
/-- Proposition 13.23 (2): clause (ii). The conjugate of the positively scaled precomposition
`x ↦ α f(α⁻¹ • x)` is the positive scalar multiple `α f*`. -/
theorem conjugate_pos_smul_precompose_inv_smul
    (f : H → EReal) (α : Set.Ioi (0 : ℝ)) :
    (fun x : H ↦ ((α : ℝ) : EReal) * f (((α : ℝ)⁻¹) • x))∗ =
      fun u : H ↦ ((α : ℝ) : EReal) * f∗ u :=
by
  ext u
  -- First use clause (i), then close with the homothety reindexing helper.
  calc
    (fun x : H ↦ ((α : ℝ) : EReal) * f (((α : ℝ)⁻¹) • x))∗ u =
        ((α : ℝ) : EReal) * (fun x : H ↦ f (((α : ℝ)⁻¹) • x))∗ (((α : ℝ)⁻¹) • u) := by
          simpa using congrFun (conjugate_pos_smul (fun x : H ↦ f (((α : ℝ)⁻¹) • x)) α) u
    _ = ((α : ℝ) : EReal) * f∗ u := by
          rw [conjugate_precompose_inv_smul_apply f α u]

-- Proof sketch: translate the supremum by `x = z + y`, separate the linear and constant terms,
-- and identify the remaining supremum with `τ v (f∗)`.
/-- Proposition 13.23 (3): clause (iii). Translating `f` by `y`, adding the linear functional
`x ↦ ⟪x, v⟫`, and shifting by a real constant translates the conjugate by `v` and adds the dual
affine correction. -/
theorem conjugate_translate_add_inner_add_const
    (f : H → EReal) (y v : H) (β : ℝ) :
    ((τ y f) + (fun x : H ↦ ((⟪x, v⟫_ℝ : ℝ) : EReal)) + fun _ : H ↦ ((β : ℝ) : EReal))∗ =
      τ v (f∗) + fun u : H ↦
        ((⟪y, u⟫_ℝ : ℝ) : EReal) - ((⟪y, v⟫_ℝ : ℝ) : EReal) - ((β : ℝ) : EReal) :=
by
  ext u
  let r : ℝ := ⟪y, u⟫_ℝ - ⟪y, v⟫_ℝ - β
  -- Route correction: `EReal` has no additive `OrderIso.addRight`, so move the finite correction
  -- through `iSup` using monotonicity plus subtraction by the same real shift.
  simp only [conjugate_apply, Pi.add_apply, translate_apply]
  calc
    (⨆ x : H, (((⟪x, u⟫_ℝ : ℝ) : EReal) -
        (f (x - y) + ((⟪x, v⟫_ℝ : ℝ) : EReal) + ((β : ℝ) : EReal)))) =
        ⨆ z : H, (((⟪z + y, u⟫_ℝ : ℝ) : EReal) -
          (f z + ((⟪z + y, v⟫_ℝ : ℝ) : EReal) + ((β : ℝ) : EReal))) := by
          -- Reindex the supremum by the translation `x = z + y`.
          exact ((Equiv.addRight y).surjective.iSup_congr (Equiv.addRight y) fun z => by
            simp [sub_eq_add_neg, add_assoc]
          ).symm
    _ = ⨆ z : H, ((((⟪z, u - v⟫_ℝ : ℝ) : EReal) - f z) + ((r : ℝ) : EReal)) := by
          -- Split the translated affine defect into the residual conjugate defect plus a constant.
          refine iSup_congr fun z => ?_
          simpa [r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            translate_inner_const_affine_defect (a := f z) y v u z β
    _ = (⨆ z : H, (((⟪z, u - v⟫_ℝ : ℝ) : EReal) - f z)) + ((r : ℝ) : EReal) := by
          -- Pull the finite real correction through `iSup`.
          simpa [r] using ereal_iSup_add_of_real_shift r
            (fun z : H ↦ (((⟪z, u - v⟫_ℝ : ℝ) : EReal) - f z))
    _ = τ v (f∗) u + ((r : ℝ) : EReal) := by
          rw [translate_apply, conjugate_apply]
    _ = (τ v (f∗) + fun _ : H ↦ ((r : ℝ) : EReal)) u := by
          simp
    _ = (τ v (f∗) + fun _ : H ↦
          ((⟪y, u⟫_ℝ : ℝ) : EReal) - ((⟪y, v⟫_ℝ : ℝ) : EReal) - ((β : ℝ) : EReal)) u := by
          simp [r]

section

variable [CompleteSpace H]

-- Proof sketch: rewrite the conjugate of `f ∘ e` by the substitution `x = e.symm z`, then move
-- the operator through the inner product via the adjoint identity and identify the remaining
-- supremum with `conjugate f`.
/-- Proposition 13.23 (4): clause (iv). Precomposing with a continuous linear equivalence sends the
conjugate to precomposition with the adjoint of the inverse operator. -/
theorem conjugate_comp_continuousLinearEquiv
    (f : H → EReal) (e : H ≃L[ℝ] H) :
    (f ∘ e)∗ = f∗ ∘ (e.symm : H →L[ℝ] H).adjoint := by
  ext u
  -- Reindex the defining supremum by `z = e x`.
  simp only [Function.comp_apply, conjugate_apply]
  calc
    ⨆ x : H, (((⟪x, u⟫_ℝ : ℝ) : EReal) - f (e x)) =
        ⨆ z : H, (((⟪e.symm z, u⟫_ℝ : ℝ) : EReal) - f z) := by
          exact e.surjective.iSup_congr e fun x => by simp
    _ = ⨆ z : H, (((⟪z, (e.symm : H →L[ℝ] H).adjoint u⟫_ℝ : ℝ) : EReal) - f z) := by
          -- Move the inverse operator across the pairing through the adjoint identity.
          refine iSup_congr fun z => ?_
          have hpair :
              ⟪e.symm z, u⟫_ℝ = ⟪z, (e.symm : H →L[ℝ] H).adjoint u⟫_ℝ := by
            simpa using
              (ContinuousLinearMap.adjoint_inner_right (A := (e.symm : H →L[ℝ] H)) z u).symm
          rw [hpair]

end

-- Proof sketch: substitute `x = -z` in the defining supremum and use
-- `⟪-z, u⟫ = ⟪z, -u⟫` to rewrite the affine defects.
/-- Proposition 13.23 (5): clause (v). Reflecting `f` through the origin commutes with Fenchel
conjugation. -/
theorem conjugate_precompose_neg
    (f : H → EReal) :
    (fᵛ)∗ = (f∗)ᵛ := by
  ext u
  -- Reindex the supremum by the involution `z = -x`.
  simp only [ERealFunction.reverse_apply, conjugate_apply]
  calc
    ⨆ x : H, (((⟪x, u⟫_ℝ : ℝ) : EReal) - f (-x)) =
        ⨆ z : H, (((⟪-z, u⟫_ℝ : ℝ) : EReal) - f z) := by
          exact (Equiv.neg H).surjective.iSup_congr (Equiv.neg H) fun x => by simp
    _ = ⨆ z : H, (((⟪z, -u⟫_ℝ : ℝ) : EReal) - f z) := by
          -- Reflection on the primal variable becomes reflection on the dual variable.
          refine iSup_congr fun z => ?_
          simp

section

variable [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Proposition 13 23: if every finite point of `f` lies in `V`, then any ambient point
outside `V` contributes the value `⊥` to the affine defect defining `f*`. -/
lemma affine_defect_eq_bot_of_not_mem_of_dom_subset
    (f : H → EReal) (V : ClosedSubmodule ℝ H) (hdom : dom f ⊆ (V : Set H)) (u x : H)
    (hxV : x ∉ (V : Set H)) :
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) = ⊥ := by
  have hxtop : f x = ⊤ := by
    by_contra htop
    have hxdom : x ∈ dom f := by
      rw [mem_dom_iff_ne_top]
      exact htop
    exact hxV (hdom hxdom)
  -- Outside `V`, the domain condition forces `f x = +∞`, so the defect is `-∞`.
  simp [hxtop]

-- Proof sketch: because `dom f ⊆ V`, the defining supremum for `conjugate f u` may be restricted
-- to points of `V`; on `V`, the inner product with `u` only depends on the orthogonal projection of
-- `u` to `V`.
/-- Proposition 13.23 (6): clause (vi), first equality. If the effective domain of `f` lies in a
closed subspace `V`, then the conjugate of the restriction `f|_V` composed with the orthogonal
projection onto `V` recovers `f*`. -/
theorem conjugate_restrict_comp_orthogonalProjection_of_dom_subset
    (f : H → EReal) (V : ClosedSubmodule ℝ H) (hdom : dom f ⊆ (V : Set H)) :
    (fun x : (V : Submodule ℝ H) ↦ f x)∗ ∘ V.orthogonalProjection = f∗ := by
  ext u
  -- Compare the two defining suprema termwise, using `hdom` to kill points outside `V`.
  rw [Function.comp_apply, conjugate_apply, conjugate_apply]
  apply le_antisymm
  · refine iSup_le fun x => ?_
    have hinner :
        (((⟪x, V.orthogonalProjection u⟫_ℝ : ℝ) : EReal) - f x) =
          (((⟪(x : H), u⟫_ℝ : ℝ) : EReal) - f x) := by
      exact congrArg (fun r : ℝ => ((r : EReal) - f x))
        (Submodule.inner_orthogonalProjection_eq_of_mem_left
          (K := (V : Submodule ℝ H)) x u)
    rw [hinner]
    exact le_iSup (fun y : H ↦ (((⟪y, u⟫_ℝ : ℝ) : EReal) - f y)) x
  · refine iSup_le fun x => ?_
    by_cases hxV : x ∈ (V : Set H)
    · let xV : (V : Submodule ℝ H) := ⟨x, hxV⟩
      have hproj :
          ⟪x, V.orthogonalProjection u⟫_ℝ = ⟪x, u⟫_ℝ := by
        change ⟪xV, (V : Submodule ℝ H).orthogonalProjection u⟫_ℝ = ⟪(xV : H), u⟫_ℝ
        exact Submodule.inner_orthogonalProjection_eq_of_mem_left
          (K := (V : Submodule ℝ H)) xV u
      have hinner :
          (((⟪xV, V.orthogonalProjection u⟫_ℝ : ℝ) : EReal) - f xV) =
            (((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) := by
        change (((⟪(xV : H), V.orthogonalProjection u⟫_ℝ : ℝ) : EReal) - f (xV : H)) =
          (((⟪x, u⟫_ℝ : ℝ) : EReal) - f x)
        exact congrArg (fun r : ℝ => ((r : EReal) - f x)) hproj
      calc
        (((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) =
            (((⟪xV, V.orthogonalProjection u⟫_ℝ : ℝ) : EReal) - f xV) := hinner.symm
        _ ≤ ⨆ y : (V : Submodule ℝ H),
              (((⟪y, V.orthogonalProjection u⟫_ℝ : ℝ) : EReal) - f y) :=
            le_iSup (fun y : (V : Submodule ℝ H) ↦
              (((⟪y, V.orthogonalProjection u⟫_ℝ : ℝ) : EReal) - f y)) xV
    · rw [affine_defect_eq_bot_of_not_mem_of_dom_subset f V hdom u x hxV]
      exact bot_le

-- Proof sketch: once clause (vi), first equality identifies `conjugate f` with the restriction
-- conjugate evaluated on orthogonal projections, apply that identity to `V.starProjection u`.
/-- Proposition 13.23 (7): clause (vi), second equality. If the effective domain of `f` lies in a
closed subspace `V`, then `f*` is invariant under orthogonal projection onto `V`. -/
theorem conjugate_eq_conjugate_comp_starProjection_of_dom_subset
    (f : H → EReal) (V : ClosedSubmodule ℝ H) (hdom : dom f ⊆ (V : Set H)) :
    f∗ = f∗ ∘ V.starProjection := by
  ext u
  have hrestrict :
      ((fun x : (V : Submodule ℝ H) ↦ f x)∗) (V.orthogonalProjection u) = f∗ u := by
    simpa [Function.comp] using
      congrFun (conjugate_restrict_comp_orthogonalProjection_of_dom_subset f V hdom) u
  have hrestrict_proj :
      ((fun x : (V : Submodule ℝ H) ↦ f x)∗) (V.orthogonalProjection (V.starProjection u)) =
        f∗ (V.starProjection u) := by
    simpa [Function.comp] using
      congrFun (conjugate_restrict_comp_orthogonalProjection_of_dom_subset f V hdom)
        (V.starProjection u)
  have hproj : V.orthogonalProjection (V.starProjection u) = V.orthogonalProjection u := by
    simpa using
      (Submodule.orthogonalProjection_mem_subspace_eq_self (V.orthogonalProjection u))
  calc
    f∗ u = ((fun x : (V : Submodule ℝ H) ↦ f x)∗) (V.orthogonalProjection u) :=
      hrestrict.symm
    _ = ((fun x : (V : Submodule ℝ H) ↦ f x)∗) (V.orthogonalProjection (V.starProjection u)) := by
      rw [hproj]
    _ = f∗ (V.starProjection u) := hrestrict_proj

end

end Conjugation

end ERealFunction
