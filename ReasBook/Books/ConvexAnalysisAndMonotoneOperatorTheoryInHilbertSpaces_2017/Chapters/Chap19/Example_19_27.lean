import BauschkeLean.Chap19.Proposition_19_25

noncomputable section

open Set
open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

attribute [local instance] Classical.propDecidable

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance]
  ERealFunction.prod_pseudoMetricSpace_l2
  ERealFunction.prod_normedAddCommGroup_l2
  ERealFunction.prod_normedSpace_l2
  ERealFunction.prod_innerProductSpace_l2

section

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Example 19.27: the translated residual map `x ↦ x - z`. -/
private abbrev translatedConstraintMap (z : H) : H → H := fun x : H ↦ x - z

/-- Helper for Example 19.27: the shifted inner objective `x ↦ f x + ⟪x - z, u⟫`. -/
private abbrev shiftedInnerObjective
    (f : H → Set.Ioi (⊥ : EReal)) (z u : H) : H → EReal :=
  fun x : H ↦ (f x : EReal) + (⟪x - z, u⟫_ℝ : EReal)

/-- Helper for Example 19.27: the unshifted inner objective `x ↦ f x + ⟪x, u⟫`. -/
private abbrev unshiftedInnerObjective
    (f : H → Set.Ioi (⊥ : EReal)) (u : H) : H → EReal :=
  fun x : H ↦ (f x : EReal) + (⟪x, u⟫_ℝ : EReal)

/-- Helper for Example 19.27: the translated-cone perturbation `F` obtained by specializing the
inequality-constraint perturbation to the constraint map `x ↦ x - z`; the companion
theorems below record clauses `(i)` through `(iv)` and the corrected saddle-point
specialization underlying clause `(v)`. -/
abbrev translatedConePerturbation
    (f : H → Set.Ioi (⊥ : EReal))
    (z : H)
    (K : Set H) :
    H × H → Set.Ioi (⊥ : EReal) :=
  inequalityConstraintPerturbation f (translatedConstraintMap z) K

variable (f : H → Set.Ioi (⊥ : EReal)) (z : H) (K : Set H)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for the translated-cone specialization: the feasibility hypothesis
`z ∈ effectiveDomain f - K` supplies
both a nonempty cone witness and a nonempty feasible slice for `R x = x - z`. -/
private theorem translatedConeFeasibilityData
    (hz : z ∈ effectiveDomain f - K) :
    K.Nonempty ∧ (K ∩ translatedConstraintMap z '' effectiveDomain f).Nonempty := by
  -- Extract a single feasible decomposition `z = x₀ - k₀` and reuse it for both side conditions.
  rcases Set.mem_sub.mp hz with ⟨x0, hx0, k0, hk0, hz_eq⟩
  have hx0_sub : x0 - z = k0 := by
    calc
      x0 - z = x0 - (x0 - k0) := by rw [hz_eq]
      _ = k0 := by abel
  refine ⟨⟨k0, hk0⟩, ?_⟩
  refine ⟨k0, hk0, ?_⟩
  exact ⟨x0, hx0, hx0_sub⟩

/-- Helper for the translated-cone specialization: membership in the translated feasible fiber
rewrites to membership
in the translated cone slice `(z - y) +ᵥ K`. -/
private theorem mem_translatedConeFiber_iff
    (x y : H) :
    x - z + y ∈ K ↔ x ∈ (z - y) +ᵥ K := by
  constructor
  · intro hxy
    -- Use the residual `x - z + y` itself as the witness in the translated cone.
    refine ⟨x - z + y, hxy, ?_⟩
    simp [vadd_eq_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · rintro ⟨k, hk, hkx⟩
    -- Expanding the translated witness shows the residual is exactly the chosen cone element.
    have hkx' : x = z - y + k := by
      simpa [vadd_eq_add] using hkx.symm
    rw [hkx']
    have hres : (z - y + k) - z + y = k := by
      abel
    rwa [hres]

/-- Helper for the translated-cone specialization: the zero perturbation slice of the translated
fiber is `z +ᵥ K`. -/
private theorem mem_translatedCone_iff
    (x : H) :
    x - z ∈ K ↔ x ∈ z +ᵥ K := by
  -- Specialize the translated-fiber rewrite to `y = 0`.
  simpa using (mem_translatedConeFiber_iff z K x (0 : H))

/-- Helper for the translated-cone specialization: the translation map `x ↦ x - z` has zero
Jensen defect, so it is
convex with respect to every closed cone containing `0`. -/
private theorem translatedConstraintMap_isConvexWithRespectTo
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_cone : IsCone K) :
    (translatedConstraintMap z).IsConvexWithRespectTo ℝ K := by
  -- The translation map is affine, so every strict Jensen defect is exactly `0`.
  intro x y α hα
  have hzero : (0 : H) ∈ K := by
    exact Set.zero_mem_of_nonempty_of_isClosed_of_isCone hK_nonempty hK_closed hK_cone
  have hline :
      translatedConstraintMap z (α • x + (1 - α) • y) =
        α • translatedConstraintMap z x + (1 - α) • translatedConstraintMap z y := by
    have hone : α + (1 - α) = (1 : ℝ) := by
      ring
    calc
      translatedConstraintMap z (α • x + (1 - α) • y) = α • x + (1 - α) • y - z := by
        rfl
      _ = α • (x - z) + (1 - α) • (y - z) := by
        calc
          α • x + (1 - α) • y - z =
              α • x + (1 - α) • y - ((α + (1 - α)) • z) := by
                congr 1
                symm
                rw [hone, one_smul]
          _ = α • (x - z) + (1 - α) • (y - z) := by
                rw [add_smul, smul_sub, smul_sub]
                abel
  have hdefect :
      translatedConstraintMap z (α • x + (1 - α) • y) -
          α • translatedConstraintMap z x -
          (1 - α) • translatedConstraintMap z y =
        0 := by
    rw [hline]
    abel
  simpa [hdefect] using hzero

/-- Helper for Example 19.27: the generic feasibility slice
`effectiveDomain f ∩ {x | x - z ∈ K}` is exactly the translated cone slice
`(z +ᵥ K) ∩ effectiveDomain f`. -/
private theorem translatedFeasibleSetMembership_iff
    (x : H) :
    x ∈ effectiveDomain f ∩ {x | x - z ∈ K} ↔ x ∈ (z +ᵥ K) ∩ effectiveDomain f := by
  constructor
  · intro hx
    -- Rewrite the residual constraint `x - z ∈ K` as membership in the translated cone.
    have hxK : x - z ∈ K := by
      simpa [Set.mem_setOf_eq] using hx.2
    have htranslated : x ∈ z +ᵥ K := (mem_translatedCone_iff z K x).1 hxK
    exact ⟨htranslated, hx.1⟩
  · intro hx
    -- The translated-cone witness recovers the generic residual constraint.
    have hxK : x - z ∈ K := (mem_translatedCone_iff z K x).2 hx.1
    refine ⟨hx.2, ?_⟩
    simpa [Set.mem_setOf_eq] using hxK

/-- Helper for the translated-cone specialization: translating the first inner-product variable
subtracts the constant
`⟪z, u⟫`, viewed in `EReal`. -/
private theorem inner_sub_left_asEReal
    (x u : H) :
    ((⟪x - z, u⟫_ℝ : ℝ) : EReal) =
      ((⟪x, u⟫_ℝ : ℝ) : EReal) + (((-⟪z, u⟫_ℝ : ℝ) : EReal)) := by
  -- First rewrite the real inner product, then coerce the identity to `EReal`.
  have hreal : ⟪x - z, u⟫_ℝ = ⟪x, u⟫_ℝ - ⟪z, u⟫_ℝ := by
    rw [inner_sub_left]
  exact
    congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal))
      (by simpa [sub_eq_add_neg] using hreal)

/-- Helper for the translated-cone specialization: adding the same finite real constant to an
`EReal` objective does
not change its global minimizers. -/
private theorem mem_argmin_addRealConst_iff
    (φ : H → EReal) (r : ℝ) (xbar : H) :
    xbar ∈ Argmin (fun x : H ↦ φ x + ((r : ℝ) : EReal)) ↔ xbar ∈ Argmin φ := by
  rw [mem_argmin_iff, mem_argmin_iff, isMinOn_univ_iff, isMinOn_univ_iff]
  constructor
  · intro hx y
    -- Cancel the same finite real shift from both sides of the minimizer inequality.
    have hxy : φ xbar + ((r : ℝ) : EReal) ≤ φ y + ((r : ℝ) : EReal) := hx y
    have hcancel : φ xbar ≤ (φ y + ((r : ℝ) : EReal)) - ((r : ℝ) : EReal) := by
      exact
        (EReal.le_sub_iff_add_le
          (Or.inl (EReal.coe_ne_bot r))
          (Or.inl (EReal.coe_ne_top r))).2 hxy
    simpa [EReal.add_sub_cancel_right] using hcancel
  · intro hx y
    -- Reinsert the same finite real shift on both sides.
    exact add_le_add (hx y) le_rfl

/-- Helper for the translated-cone specialization: the shifted and unshifted inner objectives
have the same argmin
set because they differ by the constant `-⟪z, u⟫`. -/
private theorem mem_argmin_shiftedInner_iff
    (u xbar : H) :
    xbar ∈ Argmin (shiftedInnerObjective f z u) ↔
      xbar ∈ Argmin (unshiftedInnerObjective f u) := by
  have hfun :
      shiftedInnerObjective f z u =
        fun x : H ↦ unshiftedInnerObjective f u x + (((-⟪z, u⟫_ℝ : ℝ) : EReal)) := by
    -- Rewrite the translated inner product once and isolate the constant term.
    funext x
    simp only [shiftedInnerObjective, unshiftedInnerObjective]
    rw [inner_sub_left_asEReal z x u]
    simp [add_left_comm, add_comm]
  rw [hfun]
  simpa using
    (mem_argmin_addRealConst_iff
      (unshiftedInnerObjective f u)
      (-⟪z, u⟫_ℝ) xbar)

/-- Helper for Example 19.27: once the translated complementary-slackness identity
`⟪x̄ - z, u⟫ = 0` is known, shifted-objective minimality upgrades to the exact
`sInf` identity required by Proposition 19.25. -/
private theorem eq_sInf_of_mem_argmin_shiftedInner_and_inner_eq_zero
    {u xbar : H}
    (hargmin_shifted : xbar ∈ Argmin (shiftedInnerObjective f z u))
    (hinner_zero : ⟪xbar - z, u⟫_ℝ = 0) :
    (f xbar : EReal) = sInf (Set.range (shiftedInnerObjective f z u)) := by
  -- Rewrite the shifted argmin equality and then remove the zero inner-product term.
  have hsInf_shifted :
      (f xbar : EReal) + (⟪xbar - z, u⟫_ℝ : EReal) =
        sInf (Set.range (shiftedInnerObjective f z u)) :=
    mem_argmin_iff_eq_sInf.mp hargmin_shifted
  calc
    (f xbar : EReal) = (f xbar : EReal) + (⟪xbar - z, u⟫_ℝ : EReal) := by
      simp [hinner_zero]
    _ = sInf (Set.range (shiftedInnerObjective f z u)) := hsInf_shifted

private theorem translatedDualBranch_eq_conjugateNeg_add_inner
    (u : H) :
    (⨆ x : H, -((⟪x - z, u⟫_ℝ : ℝ) : EReal) - (f x : EReal)) =
      f.asEReal∗ (-u) + (⟪z, u⟫_ℝ : EReal) := by
  have hbase :
      (⨆ x : H, -((⟪x, u⟫_ℝ : ℝ) : EReal) - (f x : EReal)) =
        f.asEReal∗ (-u) := by
    -- Evaluate the translate-plus-inner conjugation formula at `0`.
    simpa [Function.asEReal_apply, translate_apply, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm] using
      congrFun
        (conjugate_translate_add_inner_add_const
          (f := f.asEReal) (y := (0 : H)) (v := u) (β := 0))
        (0 : H)
  calc
    (⨆ x : H, -((⟪x - z, u⟫_ℝ : ℝ) : EReal) - (f x : EReal)) =
        (⨆ x : H, (-((⟪x, u⟫_ℝ : ℝ) : EReal) - (f x : EReal)) + (⟪z, u⟫_ℝ : EReal)) := by
          -- Rewrite each term as the unshifted affine defect plus the constant `⟪z, u⟫`.
          refine iSup_congr fun x ↦ ?_
          have hneg_inner :
              -((⟪x - z, u⟫_ℝ : ℝ) : EReal) =
                -((⟪x, u⟫_ℝ : ℝ) : EReal) + (⟪z, u⟫_ℝ : EReal) := by
            exact
              congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal))
                (by
                  rw [inner_sub_left]
                  ring)
          rw [hneg_inner]
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = (⨆ x : H, -((⟪x, u⟫_ℝ : ℝ) : EReal) - (f x : EReal)) + (⟪z, u⟫_ℝ : EReal) := by
          -- Pull the finite real shift through the supremum.
          simpa using
            ereal_iSup_add_of_real_shift (⟪z, u⟫_ℝ)
              (fun x : H ↦ -((⟪x, u⟫_ℝ : ℝ) : EReal) - (f x : EReal))
    _ = f.asEReal∗ (-u) + (⟪z, u⟫_ℝ : EReal) := by
          rw [hbase]

/-- The clause `(v)` optimality system for the translated-cone specialization. -/
structure TranslatedConePerturbationOptimalitySystem
    (f : H → Set.Ioi (⊥ : EReal))
    (z : H)
    (K : Set H)
    (xbar ubar : H) : Prop where
  mem_translatedFeasibleSet : xbar ∈ (z +ᵥ K) ∩ effectiveDomain f
  mem_polarCone : ubar ∈ Kᵒ⊖
  inner_eq_inner : ⟪xbar, ubar⟫_ℝ = ⟪z, ubar⟫_ℝ
  mem_argmin :
    xbar ∈ Argmin (unshiftedInnerObjective f ubar)

/-- Helper for Example 19.27: a saddle point of the translated-cone Lagrangian satisfies the
displayed optimality system from clause `(19.66)`. -/
private theorem translatedConeOptimalitySystem_of_isSaddlePointOn
    (hf : f ∈ Γ₀(H))
    (hK_closed : IsClosed K)
    (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hz : z ∈ effectiveDomain f - K)
    {xbar ubar : H}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set H)
        (ℒ[translatedConePerturbation f z K]) xbar ubar) :
    TranslatedConePerturbationOptimalitySystem f z K xbar ubar := by
  obtain ⟨hK_nonempty, hfeas⟩ := translatedConeFeasibilityData f z K hz
  have hR_cont : Continuous (translatedConstraintMap z) := continuous_id.sub continuous_const
  have hR_convex :
      (translatedConstraintMap z).IsConvexWithRespectTo ℝ K :=
    translatedConstraintMap_isConvexWithRespectTo
      (z := z) (K := K) hK_nonempty hK_closed hK_cone
  have hsaddle_generic :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set H)
        (ℒ[inequalityConstraintPerturbation f (translatedConstraintMap z) K]) xbar ubar := by
    simpa [translatedConePerturbation] using hsaddle
  -- Specialize Proposition 19.25 to the translated constraint map `R x = x - z`.
  obtain ⟨hxbar_generic, hubar, _⟩ :=
    (isSaddlePointOn_lagrangian_inequalityConstraintPerturbation_iff
      f (translatedConstraintMap z) K
      hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas
      xbar ubar).mp hsaddle_generic
  have hinner_zero :
      ⟪xbar - z, ubar⟫_ℝ = 0 := by
    obtain ⟨hinner_zero, _⟩ :=
      inner_eq_zero_and_mem_argmin_perturbationPrimalObjective_of_isSaddlePointOn_lagrangian_inequalityConstraintPerturbation
        f (translatedConstraintMap z) K
        hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas hsaddle_generic
    simpa [translatedConstraintMap] using hinner_zero
  have hargmin_shifted :
      xbar ∈ Argmin (shiftedInnerObjective f z ubar) := by
    simpa [shiftedInnerObjective, translatedConstraintMap] using
      (mem_argmin_of_isSaddlePointOn_lagrangian_inequalityConstraintPerturbation
        f (translatedConstraintMap z) K
        hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas hsaddle_generic)
  refine
    { mem_translatedFeasibleSet := ?_
      mem_polarCone := hubar
      inner_eq_inner := ?_
      mem_argmin := ?_ }
  · -- Rewrite the generic residual constraint as membership in `z +ᵥ K`.
    exact (translatedFeasibleSetMembership_iff f z K xbar).1 hxbar_generic
  · -- Convert `⟪xbar - z, ubar⟫ = 0` into the displayed equality `⟪xbar, ubar⟫ = ⟪z, ubar⟫`.
    have hinner_sub : ⟪xbar - z, ubar⟫_ℝ = ⟪xbar, ubar⟫_ℝ - ⟪z, ubar⟫_ℝ := by
      simp [inner_sub_left]
    linarith
  · -- The shifted and displayed objectives differ only by the constant `-⟪z, ubar⟫`.
    exact (mem_argmin_shiftedInner_iff f z ubar xbar).1 hargmin_shifted

/-- Helper for Example 19.27: the displayed optimality system from clause `(19.66)` yields a
saddle point of the translated-cone Lagrangian. -/
private theorem isSaddlePointOn_of_translatedConeOptimalitySystem
    (hf : f ∈ Γ₀(H))
    (hK_closed : IsClosed K)
    (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hz : z ∈ effectiveDomain f - K)
    {xbar ubar : H}
    (hopt : TranslatedConePerturbationOptimalitySystem f z K xbar ubar) :
    IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set H)
      (ℒ[translatedConePerturbation f z K]) xbar ubar := by
  obtain ⟨hK_nonempty, hfeas⟩ := translatedConeFeasibilityData f z K hz
  have hR_cont : Continuous (translatedConstraintMap z) := continuous_id.sub continuous_const
  have hR_convex :
      (translatedConstraintMap z).IsConvexWithRespectTo ℝ K :=
    translatedConstraintMap_isConvexWithRespectTo
      (z := z) (K := K) hK_nonempty hK_closed hK_cone
  have hxbar_generic :
      xbar ∈ effectiveDomain f ∩ {x | x - z ∈ K} :=
    (translatedFeasibleSetMembership_iff f z K xbar).2 hopt.mem_translatedFeasibleSet
  have hinner_zero : ⟪xbar - z, ubar⟫_ℝ = 0 := by
    -- Rewrite the displayed complementary-slackness identity back to translated coordinates.
    have hinner_sub : ⟪xbar - z, ubar⟫_ℝ = ⟪xbar, ubar⟫_ℝ - ⟪z, ubar⟫_ℝ := by
      simp [inner_sub_left]
    linarith [hopt.inner_eq_inner]
  have hargmin_shifted :
      xbar ∈ Argmin (shiftedInnerObjective f z ubar) :=
    (mem_argmin_shiftedInner_iff f z ubar xbar).2 hopt.mem_argmin
  have hsInf_eq :
      (f xbar : EReal) = sInf (Set.range (shiftedInnerObjective f z ubar)) :=
    eq_sInf_of_mem_argmin_shiftedInner_and_inner_eq_zero
      (f := f) (z := z) hargmin_shifted hinner_zero
  -- Feed the translated optimality system back into the generic saddle-point criterion.
  have hsaddle_generic :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set H)
        (ℒ[inequalityConstraintPerturbation f (translatedConstraintMap z) K]) xbar ubar :=
    (isSaddlePointOn_lagrangian_inequalityConstraintPerturbation_iff
      f (translatedConstraintMap z) K
      hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas
      xbar ubar).2 ⟨hxbar_generic, hopt.mem_polarCone, hsInf_eq⟩
  simpa [translatedConePerturbation] using hsaddle_generic

/-- Helper for the translated-cone specialization: the perturbation `F` has the branch formula
displayed in `(19.62)`. -/
@[simp] theorem translatedConePerturbation_apply
    (x y : H) :
    (translatedConePerturbation f z K (x, y) : EReal) =
      if x ∈ (z - y) +ᵥ K then (f x : EReal) else ⊤ := by
  -- Rewrite the generic inequality-constraint branches through the translated-cone membership test.
  by_cases hxy : x - z + y ∈ K
  · have hmem : x ∈ (z - y) +ᵥ K := (mem_translatedConeFiber_iff z K x y).1 hxy
    simpa [translatedConePerturbation, hmem] using
      (inequalityConstraintPerturbation_apply_of_mem
        f (translatedConstraintMap z) K hxy)
  · have hmem : x ∉ (z - y) +ᵥ K := by
      intro hxmem
      exact hxy ((mem_translatedConeFiber_iff z K x y).2 hxmem)
    simpa [translatedConePerturbation, hmem] using
      (inequalityConstraintPerturbation_apply_of_not_mem
        f (translatedConstraintMap z) K hxy)

/-- Clause (i) for the translated-cone specialization: if `f ∈ Γ₀(H)`, if `K` is a closed convex
cone, and if `z ∈ effectiveDomain f - K`, then the perturbation `F` belongs to `Γ₀(H × H)`. -/
theorem translatedConePerturbation_mem_gammaZero
    (hf : f ∈ Γ₀(H))
    (hK_closed : IsClosed K)
    (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hz : z ∈ effectiveDomain f - K) :
    translatedConePerturbation f z K ∈ Γ₀(H × H) := by
  -- Specialize Proposition 19.25 to the translated map `R x = x - z`.
  obtain ⟨hK_nonempty, hfeas⟩ := translatedConeFeasibilityData f z K hz
  have hR_cont : Continuous (translatedConstraintMap z) := continuous_id.sub continuous_const
  have hR_convex :
      (translatedConstraintMap z).IsConvexWithRespectTo ℝ K :=
    translatedConstraintMap_isConvexWithRespectTo
      (z := z) (K := K) hK_nonempty hK_closed hK_cone
  simpa [translatedConePerturbation] using
    inequalityConstraintPerturbation_mem_gammaZero
      f (translatedConstraintMap z) K
      hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas

theorem perturbationPrimalObjective_translatedConePerturbation
    : perturbationPrimalObjective (translatedConePerturbation f z K) =
      fun x : H ↦ if x ∈ z +ᵥ K then (f x : EReal) else ⊤ := by
  -- Evaluate the generic primal objective and rewrite the feasible slice as `z +ᵥ K`.
  funext x
  have hmain :=
    congrFun
      (perturbationPrimalObjective_inequalityConstraintPerturbation
        f (translatedConstraintMap z) K)
      x
  by_cases hx : x - z ∈ K
  · have hmem : x ∈ z +ᵥ K := (mem_translatedCone_iff z K x).1 hx
    rw [if_pos hx] at hmain
    simpa [hmem] using hmain
  · have hmem : x ∉ z +ᵥ K := by simpa [mem_translatedCone_iff z K x] using hx
    rw [if_neg hx] at hmain
    simpa [hmem] using hmain

/-- Clause (iii) for the translated-cone specialization: under the standing assumptions, the dual
objective is
`u ↦ f^*(-u) + ⟪z, u⟫` on `Kᵒ⊖` and `+∞` outside `Kᵒ⊖`. -/
theorem perturbationDualObjective_translatedConePerturbation
    (hf : f ∈ Γ₀(H))
    (hK_closed : IsClosed K)
    (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hz : z ∈ effectiveDomain f - K) :
    perturbationDualObjective (translatedConePerturbation f z K) =
      fun u : H ↦
        if u ∈ Kᵒ⊖ then
          f.asEReal∗ (-u) + (⟪z, u⟫_ℝ : EReal)
        else
          ⊤ := by
  obtain ⟨hK_nonempty, hfeas⟩ := translatedConeFeasibilityData f z K hz
  have hR_cont : Continuous (translatedConstraintMap z) := continuous_id.sub continuous_const
  have hR_convex :
      (translatedConstraintMap z).IsConvexWithRespectTo ℝ K :=
    translatedConstraintMap_isConvexWithRespectTo
      (z := z) (K := K) hK_nonempty hK_closed hK_cone
  -- Specialize the dual owner and normalize its branch with the translated conjugate identity.
  funext u
  by_cases hu : u ∈ Kᵒ⊖
  · have hspecialized :=
      congrFun
        (perturbationDualObjective_inequalityConstraintPerturbation
          f (translatedConstraintMap z) K
          hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas)
        u
    rw [if_pos hu] at hspecialized ⊢
    simpa [translatedConePerturbation, hu] using
      hspecialized.trans (translatedDualBranch_eq_conjugateNeg_add_inner f z u)
  · have hspecialized :=
      congrFun
        (perturbationDualObjective_inequalityConstraintPerturbation
          f (translatedConstraintMap z) K
          hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas)
        u
    rw [if_neg hu] at hspecialized ⊢
    simpa [translatedConePerturbation, hu] using hspecialized

/-- Clause (iv) for the translated-cone specialization: under the standing assumptions, the
Lagrangian has the branch formula displayed in `(19.65)`. -/
theorem lagrangian_translatedConePerturbation
    (hf : f ∈ Γ₀(H))
    (hK_closed : IsClosed K)
    (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hz : z ∈ effectiveDomain f - K)
    (x u : H) :
    ℒ[translatedConePerturbation f z K] x u =
      if x ∈ effectiveDomain f then
        if u ∈ Kᵒ⊖ then
          (f x : EReal) + (⟪x - z, u⟫_ℝ : EReal)
        else
          ⊥
      else
        ⊤ := by
  obtain ⟨hK_nonempty, hfeas⟩ := translatedConeFeasibilityData f z K hz
  have hR_cont : Continuous (translatedConstraintMap z) := continuous_id.sub continuous_const
  have hR_convex :
      (translatedConstraintMap z).IsConvexWithRespectTo ℝ K :=
    translatedConstraintMap_isConvexWithRespectTo
      (z := z) (K := K) hK_nonempty hK_closed hK_cone
  -- The generic Lagrangian branch formula already has exactly the translated residual `x - z`.
  simpa [translatedConePerturbation] using
    lagrangian_inequalityConstraintPerturbation
      f (translatedConstraintMap z) K
      hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas x u

/-- Example 19.27. Clause `(v)`, corrected via the specialization of Proposition 19.25 (5): after
rewriting the specialized `sInf` condition as an `Argmin` statement for
`x ↦ f x + ⟪x, ū⟫`, the optimality system must also retain the complementary-slackness
identity `⟪x̄, ū⟫ = ⟪z, ū⟫`. -/
theorem isSaddlePointOn_lagrangian_translatedConePerturbation_iff
    (hf : f ∈ Γ₀(H))
    (hK_closed : IsClosed K)
    (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hz : z ∈ effectiveDomain f - K)
    (xbar ubar : H) :
    IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set H)
      (ℒ[translatedConePerturbation f z K]) xbar ubar ↔
        TranslatedConePerturbationOptimalitySystem f z K xbar ubar := by
  constructor
  · intro hsaddle
    exact
      translatedConeOptimalitySystem_of_isSaddlePointOn
        (f := f) (z := z) (K := K)
        hf hK_closed hK_convex hK_cone hz hsaddle
  · intro hopt
    exact
      isSaddlePointOn_of_translatedConeOptimalitySystem
        (f := f) (z := z) (K := K)
        hf hK_closed hK_convex hK_cone hz hopt

/-- The trailing `in which case` conclusions for clause `(v)`: every saddle point
`(x̄, ū)` satisfies `⟪x̄, ū⟫ = ⟪z, ū⟫`, and its first component is a primal
solution. -/
theorem
    inner_eq_inner_and_mem_argmin_perturbationPrimalObjective_of_isSaddlePointOn_lagrangian_translatedConePerturbation
    (hf : f ∈ Γ₀(H))
    (hK_closed : IsClosed K)
    (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K)
    (hz : z ∈ effectiveDomain f - K)
    {xbar ubar : H}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set H)
        (ℒ[translatedConePerturbation f z K]) xbar ubar) :
    ⟪xbar, ubar⟫_ℝ = ⟪z, ubar⟫_ℝ ∧
      xbar ∈ Argmin
        (perturbationPrimalObjective (translatedConePerturbation f z K)) := by
  obtain ⟨hK_nonempty, hfeas⟩ := translatedConeFeasibilityData f z K hz
  have hR_cont : Continuous (translatedConstraintMap z) := continuous_id.sub continuous_const
  have hR_convex :
      (translatedConstraintMap z).IsConvexWithRespectTo ℝ K :=
    translatedConstraintMap_isConvexWithRespectTo
      (z := z) (K := K) hK_nonempty hK_closed hK_cone
  have hsaddle_generic :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set H)
        (ℒ[inequalityConstraintPerturbation f (translatedConstraintMap z) K]) xbar ubar := by
    simpa [translatedConePerturbation] using hsaddle
  obtain ⟨hinner_zero, hargmin⟩ :=
    inner_eq_zero_and_mem_argmin_perturbationPrimalObjective_of_isSaddlePointOn_lagrangian_inequalityConstraintPerturbation
      f (translatedConstraintMap z) K
      hf hK_nonempty hK_closed hK_convex hK_cone hR_cont hR_convex hfeas hsaddle_generic
  refine ⟨?_, ?_⟩
  · -- Convert complementary slackness for `xbar - z` into the displayed inner-product identity.
    have hinner_sub : ⟪xbar - z, ubar⟫_ℝ = ⟪xbar, ubar⟫_ℝ - ⟪z, ubar⟫_ℝ := by
      simp [inner_sub_left]
    linarith
  · -- The generic primal argmin consequence is already the translated perturbation statement.
    simpa [translatedConePerturbation] using hargmin

end

end ERealFunction
