import BauschkeLean.Chap10.Definition_10_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

section

variable {f : H → Set.Ioi (⊥ : EReal)}

-- In this owner API, `f : H → ]-∞,+∞]` already rules out the value `-∞`, and
-- `hconv.nonempty` supplies the nonempty effective domain. Thus the explicit binder
-- `hconv : ConvexOn f (effectiveDomain f)` is exactly the source's proper-convex hypothesis in
-- the current canonical surface.
--
-- Keep `hconv` as an explicit theorem binder, not merely a section variable: with a placeholder,
-- an unused section hypothesis would disappear from the exported declaration type.

/-- Helper for Proposition 10.12: effective-domain values can be rewritten through `EReal.toReal`
when normalizing a diagonal Jensen gap. -/
private theorem coe_toReal_eq {X : Type u} {f : X → Set.Ioi (⊥ : EReal)} {x : X}
    (hx : x ∈ effectiveDomain f) :
    (((f x : EReal).toReal : ℝ) : EReal) = (f x : EReal) := by
  exact EReal.coe_toReal (ne_of_lt (mem_effectiveDomain_iff.mp hx)) (ne_of_gt (f x).2)

/-- Helper for Proposition 10.12: the diagonal normalized Jensen gap at weight `1 / 2`
vanishes. -/
private theorem normalizedJensenGap_self_half_eq_zero
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ effectiveDomain f) :
    jensenGap f (1 / 2 : ℝ) x x / (((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ)) = 0 := by
  -- Rewrite the diagonal value through `toReal` so the remaining arithmetic lives in `ℝ`.
  have hdiag : (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • x = x := by
    calc
      (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • x = ((1 / 2 : ℝ) + (1 - (1 / 2 : ℝ))) • x := by
        rw [← add_smul]
      _ = x := by norm_num
  rw [jensenGap, hdiag, ← coe_toReal_eq hx, ← coe_toReal_eq hx, ← coe_toReal_eq hx]
  let r : ℝ := (f x : EReal).toReal
  have hcalc :
      ((((1 / 2 : ℝ) * r + (1 - (1 / 2 : ℝ)) * r - r) /
          ((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ))) : ℝ)) = 0 := by
    field_simp
    ring
  simpa [r, EReal.coe_add, EReal.coe_mul, EReal.coe_sub, EReal.coe_div] using
    congrArg (fun z : ℝ ↦ (z : EReal)) hcalc

-- Proof sketch: use `hconv.nonempty` to pick a point of the effective domain, then evaluate the
-- defining infimum at the diagonal pair `x = y`; convexity gives the opposite inequality for every
-- normalized Jensen gap, so the infimum at radius `0` is exactly `0`.
/-- The first conclusion of Proposition 10.12: for a proper convex `]-∞,+∞]`-valued function,
the exact modulus of convexity vanishes at `0`. -/
theorem exactModulusOfConvexity_zero
    (hconv : ConvexOn f (effectiveDomain f)) :
    exactModulusOfConvexity f 0 = 0 := by
  rcases hconv.nonempty with ⟨x, hx⟩
  have hnonneg : 0 ≤ exactModulusOfConvexity f 0 :=
    exactModulusOfConvexity_nonneg f hconv 0
  have hupper :
      exactModulusOfConvexity f 0 ≤ 0 := by
    -- Evaluate the defining infimum at the diagonal witness `(x, x, 1 / 2)`.
    have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
    have hdist : ‖x - x‖₊ = (0 : NNReal) := by simp
    calc
      exactModulusOfConvexity f 0
          ≤ jensenGap f (1 / 2 : ℝ) x x / (((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ)) :=
        exactModulusOfConvexity_le_normalizedGap f hx hx hdist hhalf
      _ = 0 := normalizedJensenGap_self_half_eq_zero hx
  exact le_antisymm hupper hnonneg

-- Proof sketch: swap the endpoints and replace `α` by `1 - α`; the affine midpoint and the
-- weighted endpoint sum are unchanged up to commutativity.
/-- Helper for Proposition 10.12: the Jensen gap is symmetric after swapping the endpoints and
replacing `α` by `1 - α`. -/
private theorem jensenGap_swap
    (f : H → Set.Ioi (⊥ : EReal)) (α : ℝ) (x y : H) :
    jensenGap f α x y = jensenGap f (1 - α) y x := by
  -- Normalize the swapped affine combination and then reorder the weighted sum.
  have hone : 1 - (1 - α) = α := by ring
  have honeE : (1 - ((1 - α : ℝ) : EReal)) = (α : EReal) := by
    exact_mod_cast hone
  have hcoeff : (1 - (α : EReal)) = ((1 - α : ℝ) : EReal) := by
    exact_mod_cast rfl
  have hswap : (1 - α) • y + (1 - (1 - α)) • x = α • x + (1 - α) • y := by
    rw [hone]
    abel_nf
  rw [jensenGap, jensenGap, hswap, honeE, hcoeff]
  rw [add_comm]

/-- Helper for Proposition 10.12: a finite exact modulus value admits an explicit normalized-gap
witness below any positive error perturbation. -/
private theorem exactModulusOfConvexity_exists_lt_normalizedGap
    (r : NNReal) (hbot : ⊥ < exactModulusOfConvexity f r)
    (hfin : exactModulusOfConvexity f r < ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ effectiveDomain f, ∃ y ∈ effectiveDomain f, ‖x - y‖₊ = r ∧
      ∃ α : ℝ, α ∈ Set.Ioo (0 : ℝ) 1 ∧
        jensenGap f α x y / (α * (1 - α) : ℝ) <
          exactModulusOfConvexity f r + (ε : EReal) := by
  -- Move from the infimum value to an explicit witness by perturbing it upward by `ε`.
  have hlt : exactModulusOfConvexity f r <
      exactModulusOfConvexity f r + (ε : EReal) := by
    have hε' : (0 : EReal) < (ε : EReal) := by
      exact_mod_cast hε
    have hadd :
        (0 : EReal) + exactModulusOfConvexity f r <
          (ε : EReal) + exactModulusOfConvexity f r := by
      exact EReal.add_lt_add_of_lt_of_le' hε' le_rfl (ne_of_gt hbot)
        (fun ht _ ↦ False.elim (hfin.ne ht))
    simpa [add_comm] using hadd
  rw [exactModulusOfConvexity] at hlt
  obtain ⟨δ, hδmem, hδlt⟩ := (sInf_lt_iff).1 hlt
  rcases hδmem with ⟨x, hx, y, hy, hxy, α, hα, rfl⟩
  exact ⟨x, hx, y, hy, hxy, α, hα, hδlt⟩

/-- Helper for Proposition 10.12: the near-minimizing normalized-gap witness can be chosen with
coefficient at most `1 / 2` after swapping the endpoints if needed. -/
private theorem exactModulusOfConvexity_exists_lt_normalizedGap_le_half
    (r : NNReal) (hbot : ⊥ < exactModulusOfConvexity f r)
    (hfin : exactModulusOfConvexity f r < ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ effectiveDomain f, ∃ y ∈ effectiveDomain f, ‖x - y‖₊ = r ∧
      ∃ α : ℝ, α ∈ Set.Ioo (0 : ℝ) 1 ∧ α ≤ 1 / 2 ∧
        jensenGap f α x y / (α * (1 - α) : ℝ) <
          exactModulusOfConvexity f r + (ε : EReal) := by
  rcases exactModulusOfConvexity_exists_lt_normalizedGap (f := f) r hbot hfin hε with
    ⟨x, hx, y, hy, hxy, α, hα, hlt⟩
  rcases Set.mem_Ioo.mp hα with ⟨hα0, hα1⟩
  by_cases hhalf : α ≤ 1 / 2
  · -- Keep the witness as is when its coefficient is already in the preferred half-interval.
    exact ⟨x, hx, y, hy, hxy, α, hα, hhalf, hlt⟩
  · -- Otherwise swap the endpoints and replace `α` by `1 - α`.
    have hα' : 1 - α ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · linarith
      · linarith
    have hhalf' : 1 - α ≤ 1 / 2 := by
      linarith
    have hyx : ‖y - x‖₊ = r := by
      have hsym : ‖y - x‖₊ = ‖x - y‖₊ := by
        simpa [nndist_eq_nnnorm] using (nndist_comm y x)
      exact hsym.trans hxy
    have hswap :
        jensenGap f (1 - α) y x / (((1 - α) * (1 - (1 - α)) : ℝ)) =
          jensenGap f α x y / (α * (1 - α) : ℝ) := by
      have hone : 1 - (1 - α) = α := by ring
      rw [jensenGap_swap, hone, mul_comm]
    refine ⟨y, hy, x, hx, hyx, 1 - α, hα', hhalf', ?_⟩
    rw [hswap]
    simpa [mul_comm] using hlt

/-- Helper for Proposition 10.12: a finite normalized Jensen gap is the coercion of the
corresponding real-valued quotient. -/
private theorem normalizedJensenGap_eq_coe_toReal
    {x y : H} {α : ℝ} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    (hz : α • x + (1 - α) • y ∈ effectiveDomain f) :
    jensenGap f α x y / (α * (1 - α) : ℝ) =
      ((((α * (f x : EReal).toReal + (1 - α) * (f y : EReal).toReal -
          (f (α • x + (1 - α) • y) : EReal).toReal) / (α * (1 - α)) : ℝ)) : EReal) := by
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hz_top : (f (α • x + (1 - α) • y) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz)
  have hx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
  have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
  have hz_bot : (f (α • x + (1 - α) • y) : EReal) ≠ ⊥ := ne_of_gt (f _).2
  have hcoeff : (1 - (α : EReal)) = ((1 - α : ℝ) : EReal) := by
    exact_mod_cast rfl
  -- Rewrite every finite value through `EReal.toReal`, so the quotient lives in `ℝ`.
  rw [jensenGap, hcoeff, ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hy_top hy_bot,
    ← EReal.coe_toReal hz_top hz_bot]
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_div]
  simp

/-- Helper for Proposition 10.12: on the half-interval `α ≤ 1 / 2`, the source error factor is
controlled uniformly for every `1 < γ < 2`. -/
private theorem halfIntervalErrorFactor_le
    {γ α : ℝ} (hγ1 : 1 < γ) (hγ2 : γ < 2) (_hα0 : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (1 - α) / (1 - γ * α) ≤ 1 / (2 - γ) := by
  -- Both denominators are positive in the source half-interval regime.
  have hden1 : 0 < 1 - γ * α := by
    nlinarith
  have hden2 : 0 < 2 - γ := by
    linarith
  have hcross : (1 - α) * (2 - γ) ≤ 1 - γ * α := by
    nlinarith
  exact (div_le_div_iff₀ hden1 hden2).2 (by simpa using hcross)

/-- Helper for Proposition 10.12: the rescaled coefficient `γ * α` stays in `]0,1[` when
`α ≤ 1 / 2` and `1 < γ < 2`. -/
private theorem scaledWeight_mem_Ioo_of_lt_two
    {γ α : ℝ} (hγ1 : 1 < γ) (hγ2 : γ < 2) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hαhalf : α ≤ 1 / 2) :
    γ * α ∈ Set.Ioo (0 : ℝ) 1 := by
  rcases Set.mem_Ioo.mp hα with ⟨hα0, _hα1⟩
  constructor
  · nlinarith
  · nlinarith

/-- Helper for Proposition 10.12: the source rescaled point satisfies
`zδ - y = (1 / γ) • (x - y)`. -/
private theorem rescaledPoint_sub_eq_inv_smul
    {γ : NNReal} {x y : H} :
    ((1 / (γ : ℝ)) • x + (1 - 1 / (γ : ℝ)) • y) - y = (1 / (γ : ℝ)) • (x - y) := by
  -- Rewrite the affine combination around `y` and factor out the common scalar.
  calc
    ((1 / (γ : ℝ)) • x + (1 - 1 / (γ : ℝ)) • y) - y
        = (1 / (γ : ℝ)) • x + ((1 - 1 / (γ : ℝ)) • y - y) := by
          abel_nf
    _ = (1 / (γ : ℝ)) • x + ((1 - 1 / (γ : ℝ)) • y + (-1 : ℝ) • y) := by
          simp [sub_eq_add_neg]
    _ = (1 / (γ : ℝ)) • x + (((1 - 1 / (γ : ℝ)) + (-1 : ℝ)) • y) := by
          rw [← add_smul]
    _ = (1 / (γ : ℝ)) • x + (-(1 / (γ : ℝ)) • y) := by
          congr 1
          ring
    _ = (1 / (γ : ℝ)) • x - (1 / (γ : ℝ)) • y := by
          simp [sub_eq_add_neg]
    _ = (1 / (γ : ℝ)) • (x - y) := by
          rw [smul_sub]

/-- Helper for Proposition 10.12: the source affine point
`α • x + (1 - α) • y` can be rewritten through the rescaled point `zδ`. -/
private theorem affineCombination_eq_rescaledCombination
    {γ : NNReal} (hγ0 : γ ≠ 0) {α : ℝ} {x y : H} :
    α • x + (1 - α) • y =
      (((γ : ℝ) * α) • ((1 / (γ : ℝ)) • x + (1 - 1 / (γ : ℝ)) • y) +
        (1 - (γ : ℝ) * α) • y) := by
  have hγmul : (γ : ℝ) * (1 / (γ : ℝ)) = 1 := by
    field_simp [show (γ : ℝ) ≠ 0 by exact_mod_cast hγ0]
  -- Expand the right-hand side once, then collapse the two coefficient identities.
  symm
  calc
    (((γ : ℝ) * α) • ((1 / (γ : ℝ)) • x + (1 - 1 / (γ : ℝ)) • y) +
        (1 - (γ : ℝ) * α) • y)
        = (((γ : ℝ) * α) * (1 / (γ : ℝ))) • x +
            (((γ : ℝ) * α) * (1 - 1 / (γ : ℝ))) • y +
              (1 - (γ : ℝ) * α) • y := by
                rw [smul_add, smul_smul, smul_smul]
    _ = (((γ : ℝ) * α) * (1 / (γ : ℝ))) • x +
          ((((γ : ℝ) * α) * (1 - 1 / (γ : ℝ))) + (1 - (γ : ℝ) * α)) • y := by
            rw [add_assoc, ← add_smul]
    _ = α • x + (1 - α) • y := by
          have hxcoeff : ((γ : ℝ) * α) * (1 / (γ : ℝ)) = α := by
            field_simp [show (γ : ℝ) ≠ 0 by exact_mod_cast hγ0]
          have hycoeff :
              (((γ : ℝ) * α) * (1 - 1 / (γ : ℝ)) + (1 - (γ : ℝ) * α)) = 1 - α := by
            field_simp [show (γ : ℝ) ≠ 0 by exact_mod_cast hγ0]
            ring
          rw [hxcoeff, hycoeff]

/-- Helper for Proposition 10.12: a witness at radius `γ * t` with `1 < γ < 2` produces a finite
exact modulus value at radius `t` after rescaling the first endpoint by `1 / γ`. -/
private theorem exactModulusOfConvexity_lt_top_of_rescaledWitness
    (hconv : ConvexOn f (effectiveDomain f)) {t γ : NNReal}
    (hγ1 : 1 < γ) (hγ2 : γ < 2) {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    (hxy : ‖x - y‖₊ = γ * t) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hαhalf : α ≤ 1 / 2) :
    exactModulusOfConvexity f t < ⊤ := by
  let zδ : H := (1 / (γ : ℝ)) • x + (1 - 1 / (γ : ℝ)) • y
  have hγ1_real : (1 : ℝ) < γ := by
    exact_mod_cast hγ1
  have hγ2_real : (γ : ℝ) < 2 := by
    exact_mod_cast hγ2
  have hγ0 : γ ≠ 0 := by
    exact ne_of_gt (lt_trans zero_lt_one hγ1)
  have hγ0_real : (γ : ℝ) ≠ 0 := by
    exact_mod_cast hγ0
  have hγ_pos : (0 : ℝ) < γ := by
    linarith
  have hδ_pos : 0 < 1 / (γ : ℝ) := by
    exact one_div_pos.mpr hγ_pos
  have hδ_le : 0 ≤ 1 / (γ : ℝ) := hδ_pos.le
  have hδ_one : 1 / (γ : ℝ) < 1 := by
    simpa [one_div] using inv_lt_one_of_one_lt₀ hγ1_real
  have hdom_convex : Convex ℝ (effectiveDomain f) := hconv.convex_effectiveDomain
  have hzδ : zδ ∈ effectiveDomain f := by
    -- Keep the rescaled point in the effective domain using convexity of that domain.
    refine hdom_convex hx hy hδ_le ?_ ?_
    · linarith
    · ring
  have hzα : α • x + (1 - α) • y ∈ effectiveDomain f := by
    rcases Set.mem_Ioo.mp hα with ⟨hα0, hα1⟩
    -- The original affine combination is finite because it stays in the convex effective domain.
    refine hdom_convex hx hy hα0.le ?_ ?_
    · linarith
    · ring
  have hγα : (γ : ℝ) * α ∈ Set.Ioo (0 : ℝ) 1 :=
    scaledWeight_mem_Ioo_of_lt_two hγ1_real hγ2_real hα hαhalf
  have hzγα : ((γ : ℝ) * α) • zδ + (1 - (γ : ℝ) * α) • y ∈ effectiveDomain f := by
    -- Rewrite the target affine combination back to the already-known point `α • x + (1 - α) • y`.
    rw [← affineCombination_eq_rescaledCombination (γ := γ) hγ0 (α := α) (x := x) (y := y)]
    exact hzα
  have hzδ_dist : ‖zδ - y‖₊ = t := by
    apply NNReal.eq
    have hxy_real : ‖x - y‖ = (γ : ℝ) * t := by
      simpa [NNReal.coe_mul] using congrArg (fun r : NNReal ↦ (r : ℝ)) hxy
    -- Rewrite the rescaled distance into a scalar multiple of `‖x - y‖`.
    calc
      ‖zδ - y‖ = ‖(1 / (γ : ℝ)) • (x - y)‖ := by
        rw [rescaledPoint_sub_eq_inv_smul]
      _ = ‖1 / (γ : ℝ)‖ * ‖x - y‖ := by
        rw [norm_smul]
      _ = (1 / (γ : ℝ)) * ((γ : ℝ) * t) := by
        rw [Real.norm_of_nonneg hδ_le, hxy_real]
      _ = t := by
        field_simp [hγ0_real]
  have hbound :
      exactModulusOfConvexity f t ≤
        jensenGap f ((γ : ℝ) * α) zδ y / (((γ : ℝ) * α) * (1 - (γ : ℝ) * α) : ℝ) :=
    exactModulusOfConvexity_le_normalizedGap f hzδ hy hzδ_dist hγα
  have hfiniteGap :
      jensenGap f ((γ : ℝ) * α) zδ y / (((γ : ℝ) * α) * (1 - (γ : ℝ) * α) : ℝ) < ⊤ := by
    -- Normalize the finite Jensen gap through `toReal`, so the upper bound is visibly a real.
    rw [normalizedJensenGap_eq_coe_toReal (f := f) hzδ hy hzγα]
    exact EReal.coe_lt_top _
  exact lt_of_le_of_lt hbound hfiniteGap

/-- Helper for Proposition 10.12: a finite exact modulus value is the coercion of its real part. -/
private theorem exactModulusOfConvexity_eq_coe_toReal
    (hconv : ConvexOn f (effectiveDomain f)) {t : NNReal}
    (hfin : exactModulusOfConvexity f t < ⊤) :
    (((exactModulusOfConvexity f t).toReal : ℝ) : EReal) = exactModulusOfConvexity f t := by
  -- Combine finiteness with nonnegativity to rule out both infinities before applying
  -- `EReal.coe_toReal`.
  have hnonneg : 0 ≤ exactModulusOfConvexity f t :=
    exactModulusOfConvexity_nonneg f hconv t
  have hnot_bot : exactModulusOfConvexity f t ≠ ⊥ := by
    intro hbot
    rw [hbot] at hnonneg
    simp at hnonneg
  exact EReal.coe_toReal (ne_of_lt hfin) hnot_bot

/-- Helper for Proposition 10.12: the source inequalities (10.8) to (10.10) imply the real
add-error estimate (10.11) once all `EReal` transport has been removed. -/
private theorem exactModulusOfConvexity_mul_ge_sq_mul_realCore
    {φt φγ fx fy fzδ fzα γ α ε : ℝ}
    (hγ1 : 1 < γ) (hγ2 : γ < 2) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hαhalf : α ≤ 1 / 2)
    (_hε : 0 < ε)
    (hzδ : fzδ ≤ (1 / γ) * fx + (1 - 1 / γ) * fy - (1 / γ) * (1 - 1 / γ) * φγ)
    (hzα : fzα ≤ (γ * α) * fzδ + (1 - γ * α) * fy - (γ * α) * (1 - γ * α) * φt)
    (hw : α * fx + (1 - α) * fy - α * (1 - α) * φγ - ε * (α * (1 - α)) < fzα) :
    γ ^ (2 : ℕ) * φt < φγ + ε * γ * ((1 - α) / (1 - γ * α)) := by
  rcases Set.mem_Ioo.mp hα with ⟨hα0, hα1⟩
  have hγ0 : γ ≠ 0 := by
    linarith
  have hγα_lt_one : γ * α < 1 := by
    nlinarith
  have hden : 0 < 1 - γ * α := by
    nlinarith
  have hw' :
      α * fx + (1 - α) * fy - α * (1 - α) * φγ - ε * (α * (1 - α)) <
        (γ * α) * fzδ + (1 - γ * α) * fy - (γ * α) * (1 - γ * α) * φt :=
    lt_of_lt_of_le hw hzα
  have hzδ' := hzδ
  -- Clear the single rational coefficient `1 / γ` once before the final polynomial elimination.
  field_simp [hγ0] at hzδ'
  have hcore :
      (γ ^ (2 : ℕ) * φt - φγ) * (1 - γ * α) < ε * γ * (1 - α) := by
    nlinarith [hzδ', hw', hγ1, hγ2, hα0, hα1, hαhalf]
  have hsub :
      γ ^ (2 : ℕ) * φt - φγ < ε * γ * ((1 - α) / (1 - γ * α)) := by
    have hdiv :
        γ ^ (2 : ℕ) * φt - φγ < (ε * γ * (1 - α)) / (1 - γ * α) := by
      exact (lt_div_iff₀ hden).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hcore)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
  nlinarith

/-- Helper for Proposition 10.12: a fixed near-minimizing witness at radius `γ * t` yields the
source-style add-error inequality on the half-interval `1 < γ < 2`. -/
private theorem exactModulusOfConvexity_mul_ge_sq_mul_add_error_of_witness
    (hconv : ConvexOn f (effectiveDomain f)) {t γ : NNReal}
    (hγ1 : 1 < γ) (hγ2 : γ < 2) {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    (hxy : ‖x - y‖₊ = γ * t) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hαhalf : α ≤ 1 / 2) {ε : ℝ} (hε : 0 < ε)
    (hw : jensenGap f α x y / (α * (1 - α) : ℝ) <
      exactModulusOfConvexity f (γ * t) + (ε : EReal))
    (hfinγ : exactModulusOfConvexity f (γ * t) < ⊤)
    (hfin_t : exactModulusOfConvexity f t < ⊤) :
    (((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f t ≤
      exactModulusOfConvexity f (γ * t) + (((ε * γ / (2 - γ) : ℝ)) : EReal) := by
  let zδ : H := (1 / (γ : ℝ)) • x + (1 - 1 / (γ : ℝ)) • y
  let zα : H := α • x + (1 - α) • y
  let φt : ℝ := (exactModulusOfConvexity f t).toReal
  let φγ : ℝ := (exactModulusOfConvexity f (γ * t)).toReal
  let fx : ℝ := (f x : EReal).toReal
  let fy : ℝ := (f y : EReal).toReal
  let fzδ : ℝ := (f zδ : EReal).toReal
  let fzα : ℝ := (f zα : EReal).toReal
  have hγ1_real : (1 : ℝ) < γ := by
    exact_mod_cast hγ1
  have hγ2_real : (γ : ℝ) < 2 := by
    exact_mod_cast hγ2
  have hγ0 : γ ≠ 0 := by
    exact ne_of_gt (lt_trans zero_lt_one hγ1)
  have hγ0_real : (γ : ℝ) ≠ 0 := by
    exact_mod_cast hγ0
  have hγ_pos : (0 : ℝ) < γ := by
    linarith
  have hφγ_coe :
      (((φγ : ℝ) : EReal)) = exactModulusOfConvexity f (γ * t) := by
    simpa [φγ] using (exactModulusOfConvexity_eq_coe_toReal (f := f) hconv hfinγ)
  have hφt_coe :
      (((φt : ℝ) : EReal)) = exactModulusOfConvexity f t := by
    simpa [φt] using (exactModulusOfConvexity_eq_coe_toReal (f := f) hconv hfin_t)
  have hδ_pos : 0 < 1 / (γ : ℝ) := by
    exact one_div_pos.mpr hγ_pos
  have hδ_mem : 1 / (γ : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact hδ_pos
    · simpa [one_div] using inv_lt_one_of_one_lt₀ hγ1_real
  have hdom_convex : Convex ℝ (effectiveDomain f) := hconv.convex_effectiveDomain
  have hzδ : zδ ∈ effectiveDomain f := by
    have hδ_one_nonneg : 0 ≤ 1 - 1 / (γ : ℝ) := by
      linarith [show (1 / (γ : ℝ)) < 1 from hδ_mem.2]
    -- Keep the rescaled point in the effective domain using convexity of that domain.
    refine hdom_convex hx hy hδ_pos.le hδ_one_nonneg ?_
    · ring
  have hzα : zα ∈ effectiveDomain f := by
    rcases Set.mem_Ioo.mp hα with ⟨hα0, hα1⟩
    -- The original affine point is finite because it stays in the convex effective domain.
    refine hdom_convex hx hy hα0.le ?_ ?_
    · linarith
    · ring
  have hγα : (γ : ℝ) * α ∈ Set.Ioo (0 : ℝ) 1 :=
    scaledWeight_mem_Ioo_of_lt_two hγ1_real hγ2_real hα hαhalf
  have hrescaled_eq :
      ((γ : ℝ) * α) • zδ + (1 - (γ : ℝ) * α) • y = zα := by
    -- Normalize the rescaled affine combination back to the original source point.
    simpa [zδ, zα] using
      (affineCombination_eq_rescaledCombination (γ := γ) hγ0 (α := α) (x := x) (y := y)).symm
  have hzγα :
      ((γ : ℝ) * α) • zδ + (1 - (γ : ℝ) * α) • y ∈ effectiveDomain f := by
    rw [hrescaled_eq]
    exact hzα
  have hzδ_dist : ‖zδ - y‖₊ = t := by
    apply NNReal.eq
    have hxy_real : ‖x - y‖ = (γ : ℝ) * t := by
      simpa [NNReal.coe_mul] using congrArg (fun r : NNReal ↦ (r : ℝ)) hxy
    have hsub_eq : zδ - y = (1 / (γ : ℝ)) • (x - y) := by
      simpa [zδ] using (rescaledPoint_sub_eq_inv_smul (γ := γ) (x := x) (y := y))
    -- Rewrite the rescaled distance into a scalar multiple of `‖x - y‖`.
    calc
      ‖zδ - y‖ = ‖(1 / (γ : ℝ)) • (x - y)‖ := by
        rw [hsub_eq]
      _ = ‖1 / (γ : ℝ)‖ * ‖x - y‖ := by
        rw [norm_smul]
      _ = (1 / (γ : ℝ)) * ((γ : ℝ) * t) := by
        rw [Real.norm_of_nonneg hδ_pos.le, hxy_real]
      _ = t := by
        field_simp [hγ0_real]
  have hδ_gap :
      exactModulusOfConvexity f (γ * t) ≤
        jensenGap f (1 / (γ : ℝ)) x y /
          (((1 / (γ : ℝ)) * (1 - 1 / (γ : ℝ)) : ℝ)) :=
    exactModulusOfConvexity_le_normalizedGap f hx hy hxy hδ_mem
  have hδ_bound :
      φγ ≤
        ((1 / (γ : ℝ)) * fx + (1 - 1 / (γ : ℝ)) * fy - fzδ) /
          ((1 / (γ : ℝ)) * (1 - 1 / (γ : ℝ))) := by
    have htmp :
        (((φγ : ℝ) : EReal)) ≤
          ((((1 / (γ : ℝ)) * fx + (1 - 1 / (γ : ℝ)) * fy - fzδ) /
              ((1 / (γ : ℝ)) * (1 - 1 / (γ : ℝ))) : ℝ) : EReal) := by
      calc
        (((φγ : ℝ) : EReal)) = exactModulusOfConvexity f (γ * t) := hφγ_coe
        _ ≤
            jensenGap f (1 / (γ : ℝ)) x y /
              (((1 / (γ : ℝ)) * (1 - 1 / (γ : ℝ)) : ℝ)) :=
          hδ_gap
        _ =
            ((((1 / (γ : ℝ)) * fx + (1 - 1 / (γ : ℝ)) * fy - fzδ) /
                ((1 / (γ : ℝ)) * (1 - 1 / (γ : ℝ))) : ℝ) : EReal) := by
          simpa [zδ, fx, fy, fzδ] using
            (normalizedJensenGap_eq_coe_toReal (f := f) (x := x) (y := y)
              (α := 1 / (γ : ℝ)) hx hy hzδ)
    exact EReal.coe_le_coe_iff.mp htmp
  have hzδ_real :
      fzδ ≤
        (1 / (γ : ℝ)) * fx + (1 - 1 / (γ : ℝ)) * fy -
          (1 / (γ : ℝ)) * (1 - 1 / (γ : ℝ)) * φγ := by
    have hδ_one_pos : 0 < 1 - 1 / (γ : ℝ) := by
      linarith [show (1 / (γ : ℝ)) < 1 from hδ_mem.2]
    have hden_pos : 0 < (1 / (γ : ℝ)) * (1 - 1 / (γ : ℝ)) := by
      positivity
    have hnum :
        φγ * ((1 / (γ : ℝ)) * (1 - 1 / (γ : ℝ))) ≤
          (1 / (γ : ℝ)) * fx + (1 - 1 / (γ : ℝ)) * fy - fzδ := by
      exact (le_div_iff₀ hden_pos).mp hδ_bound
    nlinarith
  have hzt_gap :
      exactModulusOfConvexity f t ≤
        jensenGap f ((γ : ℝ) * α) zδ y /
          ((((γ : ℝ) * α) * (1 - (γ : ℝ) * α) : ℝ)) :=
    exactModulusOfConvexity_le_normalizedGap f hzδ hy hzδ_dist hγα
  have hzt_bound :
      φt ≤
        (((γ : ℝ) * α) * fzδ + (1 - (γ : ℝ) * α) * fy - fzα) /
          (((γ : ℝ) * α) * (1 - (γ : ℝ) * α)) := by
    have htmp :
        (((φt : ℝ) : EReal)) ≤
          (((((γ : ℝ) * α) * fzδ + (1 - (γ : ℝ) * α) * fy - fzα) /
              (((γ : ℝ) * α) * (1 - (γ : ℝ) * α)) : ℝ) : EReal) := by
      calc
        (((φt : ℝ) : EReal)) = exactModulusOfConvexity f t := hφt_coe
        _ ≤
            jensenGap f ((γ : ℝ) * α) zδ y /
              ((((γ : ℝ) * α) * (1 - (γ : ℝ) * α) : ℝ)) :=
          hzt_gap
        _ =
            (((((γ : ℝ) * α) * fzδ + (1 - (γ : ℝ) * α) * fy - fzα) /
                (((γ : ℝ) * α) * (1 - (γ : ℝ) * α)) : ℝ) : EReal) := by
          simpa [zα, fx, fy, fzδ, fzα, hrescaled_eq] using
            (normalizedJensenGap_eq_coe_toReal (f := f) (x := zδ) (y := y)
              (α := (γ : ℝ) * α) hzδ hy hzγα)
    exact EReal.coe_le_coe_iff.mp htmp
  have hzα_real :
      fzα ≤
        ((γ : ℝ) * α) * fzδ + (1 - (γ : ℝ) * α) * fy -
          ((γ : ℝ) * α) * (1 - (γ : ℝ) * α) * φt := by
    rcases Set.mem_Ioo.mp hγα with ⟨hγα0, hγα1⟩
    have hden_pos : 0 < ((γ : ℝ) * α) * (1 - (γ : ℝ) * α) := by
      nlinarith
    have hnum :
        φt * (((γ : ℝ) * α) * (1 - (γ : ℝ) * α)) ≤
          ((γ : ℝ) * α) * fzδ + (1 - (γ : ℝ) * α) * fy - fzα := by
      exact (le_div_iff₀ hden_pos).mp hzt_bound
    nlinarith
  have hφγ_add :
      exactModulusOfConvexity f (γ * t) + (ε : EReal) = (((φγ + ε : ℝ)) : EReal) := by
    -- Move the finite exact modulus to its real representative before adding the real error.
    rw [← hφγ_coe, ← EReal.coe_add]
  have hw_real :
      α * fx + (1 - α) * fy - α * (1 - α) * φγ - ε * (α * (1 - α)) < fzα := by
    have htmp :
        ((((α * fx + (1 - α) * fy - fzα) / (α * (1 - α)) : ℝ)) : EReal) <
          (((φγ + ε : ℝ)) : EReal) := by
      calc
        ((((α * fx + (1 - α) * fy - fzα) / (α * (1 - α)) : ℝ)) : EReal) =
            jensenGap f α x y / (α * (1 - α) : ℝ) := by
          simpa [zα, fx, fy, fzα] using
            (normalizedJensenGap_eq_coe_toReal (f := f) (x := x) (y := y)
              (α := α) hx hy hzα).symm
        _ < exactModulusOfConvexity f (γ * t) + (ε : EReal) := hw
        _ = (((φγ + ε : ℝ)) : EReal) := hφγ_add
    have htmp_real :
        (α * fx + (1 - α) * fy - fzα) / (α * (1 - α)) < φγ + ε :=
      EReal.coe_lt_coe_iff.mp htmp
    rcases Set.mem_Ioo.mp hα with ⟨hα0, hα1⟩
    have hden_pos : 0 < α * (1 - α) := by
      nlinarith
    have hnum :
        α * fx + (1 - α) * fy - fzα < (φγ + ε) * (α * (1 - α)) := by
      exact (div_lt_iff₀ hden_pos).mp htmp_real
    nlinarith
  have hcore :
      (γ : ℝ) ^ (2 : ℕ) * φt < φγ + ε * (γ : ℝ) * ((1 - α) / (1 - (γ : ℝ) * α)) := by
    -- Feed the normalized real inequalities into the textbook algebraic core.
    exact exactModulusOfConvexity_mul_ge_sq_mul_realCore hγ1_real hγ2_real hα hαhalf hε
      hzδ_real hzα_real hw_real
  have herr_le :
      ε * (γ : ℝ) * ((1 - α) / (1 - (γ : ℝ) * α)) ≤ ε * (γ : ℝ) * (1 / (2 - (γ : ℝ))) := by
    have hfactor :
        (1 - α) / (1 - (γ : ℝ) * α) ≤ 1 / (2 - (γ : ℝ)) :=
      halfIntervalErrorFactor_le hγ1_real hγ2_real (Set.mem_Ioo.mp hα).1 hαhalf
    have hεγ_nonneg : 0 ≤ ε * (γ : ℝ) := by
      nlinarith
    exact mul_le_mul_of_nonneg_left hfactor hεγ_nonneg
  have hcore' :
      (γ : ℝ) ^ (2 : ℕ) * φt < φγ + ε * (γ : ℝ) / (2 - (γ : ℝ)) := by
    refine lt_of_lt_of_le hcore ?_
    have hrewrite :
        ε * (γ : ℝ) * (1 / (2 - (γ : ℝ))) = ε * (γ : ℝ) / (2 - (γ : ℝ)) := by
      ring
    simpa [hrewrite] using add_le_add_left herr_le φγ
  have hfinal :
      ((((γ : ℝ) ^ (2 : ℕ) * φt : ℝ)) : EReal) ≤
        (((φγ + ε * (γ : ℝ) / (2 - (γ : ℝ)) : ℝ)) : EReal) := by
    exact_mod_cast (le_of_lt hcore')
  -- Cast the real estimate back to the exact-modulus values using the finiteness hypotheses.
  calc
    (((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f t
        = ((((γ : ℝ) ^ (2 : ℕ) * φt : ℝ)) : EReal) := by
          calc
            (((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f t
                = (((γ : ℝ) ^ (2 : ℕ)) : EReal) * (((φt : ℝ) : EReal)) := by
                    rw [hφt_coe]
            _ = ((((γ : ℝ) ^ (2 : ℕ) * φt : ℝ)) : EReal) := by
                    simp
    _ ≤ (((φγ + ε * (γ : ℝ) / (2 - (γ : ℝ)) : ℝ)) : EReal) := hfinal
    _ = exactModulusOfConvexity f (γ * t) + (((ε * γ / (2 - γ) : ℝ)) : EReal) := by
          calc
            (((φγ + ε * (γ : ℝ) / (2 - (γ : ℝ)) : ℝ)) : EReal)
                = (((φγ : ℝ) : EReal) + (((ε * (γ : ℝ) / (2 - (γ : ℝ)) : ℝ)) : EReal)) := by
                    rw [EReal.coe_add]
            _ = exactModulusOfConvexity f (γ * t) +
                  (((ε * γ / (2 - γ) : ℝ)) : EReal) := by
                    rw [hφγ_coe]

/-- Helper for Proposition 10.12: the quadratic scaling inequality holds on the local half-interval
`1 ≤ γ < 2`. -/
private theorem exactModulusOfConvexity_mul_ge_sq_mul_of_lt_two
    (hconv : ConvexOn f (effectiveDomain f))
    (t γ : NNReal) (hγ1 : 1 ≤ γ) (hγ2 : γ < 2) :
    exactModulusOfConvexity f (γ * t) ≥
      (((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f t := by
  by_cases ht : t = 0
  · -- At radius `0`, Proposition 10.12(1) collapses both sides to `0`.
    subst ht
    simp [exactModulusOfConvexity_zero hconv]
  by_cases hγeq : γ = 1
  · -- At scale factor `1`, the target inequality is an equality.
    subst hγeq
    simp
  have hγlt : 1 < γ := lt_of_le_of_ne hγ1 (Ne.symm hγeq)
  by_cases htop : exactModulusOfConvexity f (γ * t) = ⊤
  · -- If the larger-radius modulus is infinite, the inequality is automatic.
    rw [htop]
    exact le_top
  have hfinγ : exactModulusOfConvexity f (γ * t) < ⊤ := lt_of_le_of_ne le_top htop
  have hφγ_nonneg : 0 ≤ exactModulusOfConvexity f (γ * t) :=
    exactModulusOfConvexity_nonneg f hconv (γ * t)
  have hnot_bot : exactModulusOfConvexity f (γ * t) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hφγ_nonneg
    simp at hφγ_nonneg
  have hbot : ⊥ < exactModulusOfConvexity f (γ * t) := lt_of_le_of_ne bot_le hnot_bot.symm
  have hγ_real : (1 : ℝ) < γ := by
    exact_mod_cast hγlt
  have hγ0 : γ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hγlt)
  have hγ0_real : (γ : ℝ) ≠ 0 := by
    exact_mod_cast hγ0
  have hφγ_coe :
      (((exactModulusOfConvexity f (γ * t)).toReal : ℝ) : EReal) =
        exactModulusOfConvexity f (γ * t) := by
    exact exactModulusOfConvexity_eq_coe_toReal (f := f) hconv hfinγ
  -- Route correction: in the finite branch, it is cleaner to remove the error on real values
  -- directly instead of transporting the whole inequality through `toENNReal`.
  have hreal :
      (γ : ℝ) ^ (2 : ℕ) * (exactModulusOfConvexity f t).toReal ≤
        (exactModulusOfConvexity f (γ * t)).toReal := by
    refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
    let ε : ℝ := δ * (2 - (γ : ℝ)) / (γ : ℝ)
    have hε : 0 < ε := by
      have hγ_pos : 0 < (γ : ℝ) := by
        exact_mod_cast (lt_trans zero_lt_one hγlt)
      have htwo_sub_pos : 0 < 2 - (γ : ℝ) := by
        nlinarith [show (γ : ℝ) < 2 from by exact_mod_cast hγ2]
      dsimp [ε]
      positivity
    obtain ⟨x, hx, y, hy, hxy, α, hα, hαhalf, hw⟩ :=
      exactModulusOfConvexity_exists_lt_normalizedGap_le_half (f := f) (γ * t) hbot hfinγ hε
    have hfin_t : exactModulusOfConvexity f t < ⊤ :=
      exactModulusOfConvexity_lt_top_of_rescaledWitness hconv hγlt hγ2 hx hy hxy hα hαhalf
    have hstep :
        (((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f t ≤
          exactModulusOfConvexity f (γ * t) +
            (((ε * γ / (2 - γ) : ℝ)) : EReal) :=
      exactModulusOfConvexity_mul_ge_sq_mul_add_error_of_witness hconv hγlt hγ2 hx hy hxy
        hα hαhalf hε hw hfinγ hfin_t
    have hε_cancel : ε * (γ : ℝ) / (2 - (γ : ℝ)) = δ := by
      dsimp [ε]
      have htwo_sub_ne : 2 - (γ : ℝ) ≠ 0 := by
        linarith [show (γ : ℝ) < 2 from by exact_mod_cast hγ2]
      field_simp [hγ0_real, htwo_sub_ne]
    have hleft :
        ((((γ : ℝ) ^ (2 : ℕ) * (exactModulusOfConvexity f t).toReal : ℝ)) : EReal) =
          (((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f t := by
      calc
        ((((γ : ℝ) ^ (2 : ℕ) * (exactModulusOfConvexity f t).toReal : ℝ)) : EReal)
            = (((γ : ℝ) ^ (2 : ℕ)) : EReal) *
                (((exactModulusOfConvexity f t).toReal : ℝ) : EReal) := by
                  simp
        _ = (((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f t := by
              rw [exactModulusOfConvexity_eq_coe_toReal (f := f) hconv hfin_t]
    have hright :
        exactModulusOfConvexity f (γ * t) + (((ε * γ / (2 - γ) : ℝ)) : EReal) =
          ((((exactModulusOfConvexity f (γ * t)).toReal + δ : ℝ)) : EReal) := by
      calc
        exactModulusOfConvexity f (γ * t) + (((ε * γ / (2 - γ) : ℝ)) : EReal)
            = (((exactModulusOfConvexity f (γ * t)).toReal : ℝ) : EReal) + (δ : EReal) := by
                rw [← hφγ_coe]
                simp [hε_cancel]
        _ = ((((exactModulusOfConvexity f (γ * t)).toReal + δ : ℝ)) : EReal) := by
              rw [EReal.coe_add]
    have hstep_real :
        ((((γ : ℝ) ^ (2 : ℕ) * (exactModulusOfConvexity f t).toReal : ℝ)) : EReal) ≤
          ((((exactModulusOfConvexity f (γ * t)).toReal + δ : ℝ)) : EReal) := by
      rw [hleft, ← hright]
      exact hstep
    exact EReal.coe_le_coe_iff.mp hstep_real
  have hfin_t : exactModulusOfConvexity f t < ⊤ := by
    obtain ⟨x, hx, y, hy, hxy, α, hα, hαhalf, _hw⟩ :=
      exactModulusOfConvexity_exists_lt_normalizedGap_le_half (f := f) (γ * t) hbot hfinγ
        (ε := 1) (by norm_num)
    exact exactModulusOfConvexity_lt_top_of_rescaledWitness hconv hγlt hγ2 hx hy hxy hα hαhalf
  have hrealE :
      ((((γ : ℝ) ^ (2 : ℕ) * (exactModulusOfConvexity f t).toReal : ℝ)) : EReal) ≤
        exactModulusOfConvexity f (γ * t) := by
    calc
      ((((γ : ℝ) ^ (2 : ℕ) * (exactModulusOfConvexity f t).toReal : ℝ)) : EReal) ≤
          ((((exactModulusOfConvexity f (γ * t)).toReal : ℝ)) : EReal) := by
            exact_mod_cast hreal
      _ = exactModulusOfConvexity f (γ * t) := hφγ_coe
  have hleft :
      ((((γ : ℝ) ^ (2 : ℕ) * (exactModulusOfConvexity f t).toReal : ℝ)) : EReal) =
        (((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f t := by
    calc
      ((((γ : ℝ) ^ (2 : ℕ) * (exactModulusOfConvexity f t).toReal : ℝ)) : EReal)
          = (((γ : ℝ) ^ (2 : ℕ)) : EReal) *
              (((exactModulusOfConvexity f t).toReal : ℝ) : EReal) := by
                simp
      _ = (((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f t := by
            rw [exactModulusOfConvexity_eq_coe_toReal (f := f) hconv hfin_t]
  rw [← hleft]
  exact hrealE

-- Proof sketch: rewrite convexity through the Jensen-on-domain inequality from Chapter 8, then
-- follow the textbook two-case argument. For `1 < γ < 2`, rescale an admissible pair for `γ * t`
-- and compare the corresponding normalized gaps; for `γ ≥ 2`, factor `γ` into finitely many terms
-- in `(1,2)` and iterate the first step.
/-- Proposition 10.12 (2): for a proper convex `]-∞,+∞]`-valued function, the exact modulus of
convexity satisfies `φ (γ t) ≥ γ^2 φ t` for every `t ∈ ℝ_+` and every `γ ≥ 1`. -/
theorem exactModulusOfConvexity_mul_ge_sq_mul
    (hconv : ConvexOn f (effectiveDomain f))
    (t γ : NNReal) (hγ : 1 ≤ γ) :
    exactModulusOfConvexity f (γ * t) ≥
      (((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f t := by
  by_cases hγ2 : γ < 2
  · -- The local half-interval theorem packages the source's rescaling argument.
    exact exactModulusOfConvexity_mul_ge_sq_mul_of_lt_two hconv t γ hγ hγ2
  let ρ : NNReal := NNReal.sqrt 2
  have hρsq_real : (ρ : ℝ) ^ (2 : ℕ) = 2 := by
    dsimp [ρ]
    norm_num [NNReal.sq_sqrt]
  have hρ_one_lt : 1 < ρ := by
    have hρ_one_lt_real : (1 : ℝ) < (ρ : ℝ) := by
      nlinarith [hρsq_real]
    exact_mod_cast hρ_one_lt_real
  have hρ1 : 1 ≤ ρ := by
    -- The factor `ρ = √2` keeps every local rescaling inside the strict `< 2` range.
    exact le_of_lt hρ_one_lt
  have hρlt : ρ < 2 := by
    have hρ_nonneg : 0 ≤ (ρ : ℝ) := by
      positivity
    have hρ_lt_real : (ρ : ℝ) < 2 := by
      nlinarith [hρsq_real]
    exact_mod_cast hρ_lt_real
  have hρpos : 0 < ρ := lt_trans zero_lt_one hρ_one_lt
  have hρ0 : ρ ≠ 0 := ne_of_gt hρpos
  have hρ0_real : (ρ : ℝ) ≠ 0 := by
    exact_mod_cast hρ0
  obtain ⟨n, hnle, hnlt⟩ := exists_nat_pow_near hγ hρ_one_lt
  let β : NNReal := γ / ρ ^ n
  have hρpow_pos : 0 < ρ ^ n := by
    exact pow_pos hρpos n
  have hβ1 : 1 ≤ β := by
    dsimp [β]
    exact (one_le_div hρpow_pos).2 hnle
  have hβltρ : β < ρ := by
    have hβ_eq : (β : ℝ) = (γ : ℝ) / (((ρ ^ n : NNReal) : ℝ)) := by
      simp [β]
    have hβltρ_real : (β : ℝ) < (ρ : ℝ) := by
      rw [hβ_eq]
      have hnlt_real : (γ : ℝ) < (((ρ ^ n : NNReal) : ℝ)) * (ρ : ℝ) := by
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
          (show (γ : ℝ) < (((ρ ^ (n + 1) : NNReal) : ℝ)) from by exact_mod_cast hnlt)
      exact (div_lt_iff₀ (show 0 < (((ρ ^ n : NNReal) : ℝ)) from by exact_mod_cast hρpow_pos)).2
        (by simpa [mul_comm] using hnlt_real)
    exact_mod_cast hβltρ_real
  have hβ2 : β < 2 := lt_trans hβltρ hρlt
  have hβ_factor : β * ρ ^ n = γ := by
    -- Recover `γ` from the residual factor `β = γ / ρ^n`.
    dsimp [β]
    exact div_mul_cancel₀ _ (pow_ne_zero n hρ0)
  have hpow :
      ∀ m : ℕ,
        exactModulusOfConvexity f ((ρ ^ m) * t) ≥
          ((((ρ ^ m : NNReal) : ℝ) ^ (2 : ℕ)) : EReal) *
            exactModulusOfConvexity f t := by
    intro m
    induction m with
    | zero =>
        -- The zero-step amplification is the identity scale.
        simp [ρ]
    | succ m ihm =>
        have hρsq_nonneg : 0 ≤ (((ρ : ℝ) ^ (2 : ℕ)) : EReal) := by
          exact_mod_cast sq_nonneg ((ρ : ℝ))
        have hlocal :
            exactModulusOfConvexity f (ρ * ((ρ ^ m) * t)) ≥
              (((ρ : ℝ) ^ (2 : ℕ)) : EReal) *
                exactModulusOfConvexity f ((ρ ^ m) * t) :=
          exactModulusOfConvexity_mul_ge_sq_mul_of_lt_two hconv ((ρ ^ m) * t) ρ hρ1 hρlt
        have hcoeff :
            (((ρ : ℝ) ^ (2 : ℕ)) : EReal) *
                ((((ρ ^ m : NNReal) : ℝ) ^ (2 : ℕ)) : EReal) =
              ((((ρ ^ (m + 1) : NNReal) : ℝ) ^ (2 : ℕ)) : EReal) := by
          have hmul :
              (ρ : ℝ) * (((ρ ^ m : NNReal) : ℝ)) = (((ρ ^ (m + 1) : NNReal) : ℝ)) := by
            simpa [mul_comm] using congrArg (fun z : NNReal ↦ (z : ℝ)) (pow_succ ρ m).symm
          have hcoeff_real :
              (ρ : ℝ) ^ (2 : ℕ) * (((ρ ^ m : NNReal) : ℝ) ^ (2 : ℕ)) =
                (((ρ ^ (m + 1) : NNReal) : ℝ) ^ (2 : ℕ)) := by
            calc
              (ρ : ℝ) ^ (2 : ℕ) * (((ρ ^ m : NNReal) : ℝ) ^ (2 : ℕ)) =
                  (((ρ : ℝ) * (((ρ ^ m : NNReal) : ℝ))) ^ (2 : ℕ)) := by
                    ring
              _ = (((ρ ^ (m + 1) : NNReal) : ℝ) ^ (2 : ℕ)) := by
                    rw [hmul]
          exact_mod_cast hcoeff_real
        calc
          exactModulusOfConvexity f ((ρ ^ (m + 1)) * t)
              = exactModulusOfConvexity f (ρ * ((ρ ^ m) * t)) := by
                  simp [pow_succ, mul_left_comm, mul_comm]
          _ ≥ (((ρ : ℝ) ^ (2 : ℕ)) : EReal) *
                exactModulusOfConvexity f ((ρ ^ m) * t) := hlocal
          _ ≥ (((ρ : ℝ) ^ (2 : ℕ)) : EReal) *
                (((((ρ ^ m : NNReal) : ℝ) ^ (2 : ℕ)) : EReal) *
                  exactModulusOfConvexity f t) := by
                    exact mul_le_mul_of_nonneg_left ihm hρsq_nonneg
          _ = ((((ρ ^ (m + 1) : NNReal) : ℝ) ^ (2 : ℕ)) : EReal) *
                exactModulusOfConvexity f t := by
                  rw [← mul_assoc, hcoeff]
  have hβ_real : (β : ℝ) * (((ρ ^ n : NNReal) : ℝ)) = (γ : ℝ) := by
    exact_mod_cast hβ_factor
  have hcoeff :
      (((β : ℝ) ^ (2 : ℕ)) : EReal) *
          ((((ρ ^ n : NNReal) : ℝ) ^ (2 : ℕ)) : EReal) =
        (((γ : ℝ) ^ (2 : ℕ)) : EReal) := by
    have hcoeff_real :
        (β : ℝ) ^ (2 : ℕ) * (((ρ ^ n : NNReal) : ℝ) ^ (2 : ℕ)) = (γ : ℝ) ^ (2 : ℕ) := by
      calc
        (β : ℝ) ^ (2 : ℕ) * (((ρ ^ n : NNReal) : ℝ) ^ (2 : ℕ)) =
            (((β : ℝ) * (((ρ ^ n : NNReal) : ℝ))) ^ (2 : ℕ)) := by
              ring
        _ = (γ : ℝ) ^ (2 : ℕ) := by
              rw [hβ_real]
    exact_mod_cast hcoeff_real
  calc
    exactModulusOfConvexity f (γ * t)
        = exactModulusOfConvexity f (β * ((ρ ^ n) * t)) := by
            rw [← hβ_factor, mul_assoc]
    _ ≥ (((β : ℝ) ^ (2 : ℕ)) : EReal) *
          exactModulusOfConvexity f ((ρ ^ n) * t) :=
        exactModulusOfConvexity_mul_ge_sq_mul_of_lt_two hconv ((ρ ^ n) * t) β hβ1 hβ2
    _ ≥ (((β : ℝ) ^ (2 : ℕ)) : EReal) *
          (((((ρ ^ n : NNReal) : ℝ) ^ (2 : ℕ)) : EReal) *
            exactModulusOfConvexity f t) := by
              have hβsq_nonneg : 0 ≤ (((β : ℝ) ^ (2 : ℕ)) : EReal) := by
                exact_mod_cast sq_nonneg ((β : ℝ))
              exact mul_le_mul_of_nonneg_left (hpow n) hβsq_nonneg
    _ = (((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f t := by
          rw [← mul_assoc, hcoeff]

-- Proof sketch: if `s ≤ t`, write `t = γ * s` with `γ ≥ 1`; then apply the quadratic-scaling
-- inequality and use that the exact modulus takes values in `[0,+∞]` to conclude `φ s ≤ φ t`.
/-- The third conclusion of Proposition 10.12: for a proper convex `]-∞,+∞]`-valued function,
the exact modulus of convexity is increasing on `ℝ_+`. -/
theorem exactModulusOfConvexity_monotone
    (hconv : ConvexOn f (effectiveDomain f)) :
    Monotone (exactModulusOfConvexity f) := by
  intro s t hst
  by_cases hs : s = 0
  · -- The left endpoint is the zero radius, where Proposition 10.12 already gives vanishing.
    subst hs
    rw [exactModulusOfConvexity_zero hconv]
    exact exactModulusOfConvexity_nonneg f hconv t
  · have hs_pos : 0 < s := pos_iff_ne_zero.mpr hs
    let γ : NNReal := t / s
    have hγ : 1 ≤ γ := by
      -- Normalize `s ≤ t` by dividing through the positive radius `s`.
      dsimp [γ]
      exact (one_le_div hs_pos).2 hst
    have ht : t = γ * s := by
      -- Recover `t` from the quotient factor.
      dsimp [γ]
      exact (div_mul_cancel₀ _ hs).symm
    have hnonneg : 0 ≤ exactModulusOfConvexity f s :=
      exactModulusOfConvexity_nonneg f hconv s
    have hγsq : (1 : EReal) ≤ (((γ : ℝ) ^ (2 : ℕ)) : EReal) := by
      have hγ_real : (1 : ℝ) ≤ (γ : ℝ) := by
        exact_mod_cast hγ
      have hγsq_real : (1 : ℝ) ≤ (γ : ℝ) ^ (2 : ℕ) := by
        nlinarith
      exact_mod_cast hγsq_real
    have hscale :
        (((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f s ≤
          exactModulusOfConvexity f (γ * s) :=
      exactModulusOfConvexity_mul_ge_sq_mul hconv s γ hγ
    -- Insert the factor `γ² ≥ 1` between `φ s` and `φ (γ s) = φ t`.
    calc
      exactModulusOfConvexity f s
          = (1 : EReal) * exactModulusOfConvexity f s := by simp
      _ ≤ (((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f s :=
        mul_le_mul_of_nonneg_right hγsq hnonneg
      _ ≤ exactModulusOfConvexity f (γ * s) :=
        hscale
      _ = exactModulusOfConvexity f t := by
        rw [ht]

end

end ERealFunction
