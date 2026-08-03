import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap01.Definition_1_8
import BauschkeLean.Chap01.Lemma_1_24
import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap03.Theorem_3_16_2
import BauschkeLean.Chap05.Theorem_5_5
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap10.Definition_10_20
import BauschkeLean.Chap10.Definition_10_7
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap11.Proposition_11_29
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap12.Proposition_12_26
import BauschkeLean.Chap12.Proposition_12_27
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_44
import BauschkeLean.Chap16.Theorem_16_3
import BauschkeLean.Chap22.Example_22_5
import BauschkeLean.Chap26.Theorem_26_17

open Filter
open scoped BigOperators InnerProductSpace Pointwise SetValuedOperator Topology

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: this item is the proximal-point iteration for `f` itself, so the main
  statements stay on the Chapter 12 surface `Prox[γ, f, hf]`.
- `core/canonical`: the repository-level canonical objects used in the statements are `Argmin`,
  `IsMinimizingSequence`, `lowerLevelSet`, and weak convergence in `WeakSpace ℝ H`.
- `bridge/view`: the source-facing recursion is kept directly as `IsProximalPointOrbit`, since the
  statement surface here does not need the Chapter 23 resolvent recursion owner.
-/

section ProximalPointAlgorithm

variable {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
variable {γ : ℕ → PosReal} {x0 : H} {x : ℕ → H}

/-- A sequence `x` satisfies the source proximal-point recursion of this item for `f`, step
sizes `γ`, and initial point `x0`. -/
def IsProximalPointOrbit (γ : ℕ → PosReal) (x0 : H) (x : ℕ → H) : Prop :=
  x 0 = x0 ∧ ∀ n : ℕ, x (n + 1) = Prox[γ n, f, hf] (x n)

/-- A source-facing proximal-point orbit starts at the prescribed point. -/
theorem IsProximalPointOrbit.x_zero (hx : IsProximalPointOrbit hf γ x0 x) :
    x 0 = x0 :=
  hx.1

/-- A source-facing proximal-point orbit satisfies the proximal recursion at every step. -/
theorem IsProximalPointOrbit.x_succ_eq
    (hx : IsProximalPointOrbit hf γ x0 x) (n : ℕ) :
    x (n + 1) = Prox[γ n, f, hf] (x n) :=
  hx.2 n

/-- Helper for Theorem 28.1: every scaled proximal value is bounded above by the value at the base
point. -/
private theorem proxValue_asEReal_le_self_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) (γ : PosReal) :
    f.asEReal (Prox[γ, f, hf] x) ≤ f.asEReal x := by
  let p := Prox[γ, f, hf] x
  -- Drop the nonnegative squared-distance term from Proposition 12.27.
  have hineq := sqDist_add_smul_proxValue_le_smul_self_of_mem_gammaZero f hf x γ
  have hnorm_nonneg : (0 : EReal) ≤ (((‖x - p‖ ^ 2 : ℝ) : EReal)) := by
    exact_mod_cast sq_nonneg ‖x - p‖
  have hscaled : ((γ • f) p : EReal) ≤ ((γ • f) x : EReal) := by
    exact le_trans (le_add_of_nonneg_left hnorm_nonneg) (by simpa [p] using hineq)
  have hmul : (f p : EReal) * (γ : ℝ) ≤ (f x : EReal) * (γ : ℝ) := by
    simpa [posReal_smul_apply, mul_comm] using hscaled
  have hbase : (f p : EReal) ≤ (f x : EReal) := by
    have hγ0 : (0 : ℝ) < (γ : ℝ) := γ.2
    have hdiv :
        ((f p : EReal) * (γ : ℝ)) / ((γ : ℝ) : EReal) ≤
          ((f x : EReal) * (γ : ℝ)) / ((γ : ℝ) : EReal) := by
      exact EReal.div_le_div_right_of_nonneg (by exact_mod_cast hγ0.le) hmul
    have hcancel_p :
        ((f p : EReal) * (γ : ℝ)) / ((γ : ℝ) : EReal) = (f p : EReal) := by
      rw [EReal.div_eq_iff (EReal.coe_ne_bot _) (EReal.coe_ne_top _) (by exact_mod_cast hγ0.ne')]
    have hcancel_x :
        ((f x : EReal) * (γ : ℝ)) / ((γ : ℝ) : EReal) = (f x : EReal) := by
      rw [EReal.div_eq_iff (EReal.coe_ne_bot _) (EReal.coe_ne_top _) (by exact_mod_cast hγ0.ne')]
    simpa [hcancel_p, hcancel_x] using hdiv
  simpa [p, Function.asEReal] using hbase

/-- Helper for Theorem 28.1: every iterate after the initial point lies in `effectiveDomain f`. -/
private theorem proximalPointOrbit_succ_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {γ : ℕ → PosReal} {x0 : H} {x : ℕ → H} (hx : IsProximalPointOrbit hf γ x0 x) (n : ℕ) :
    x (n + 1) ∈ effectiveDomain f := by
  -- Rewrite the recursion and apply the Chapter 12 domain lemma for scaled proximal points.
  rw [hx.x_succ_eq (hf := hf) n]
  exact scaledProximityOperator_mem_effectiveDomain_of_mem_gammaZero f hf (x n) (γ n)

/-- Helper for Theorem 28.1: each proximal step satisfies the scaled variational inequality
against every comparison point. -/
private theorem inner_add_gamma_mul_nextValue_le_gamma_mul_value
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {γ : ℕ → PosReal} {x0 : H} {x : ℕ → H} (hx : IsProximalPointOrbit hf γ x0 x)
    (n : ℕ) (z : H) :
    (⟪z - x (n + 1), x n - x (n + 1)⟫_ℝ : EReal) +
        (((γ n) • f) (x (n + 1)) : EReal) ≤
      (((γ n) • f) z : EReal) := by
  let hγf : (γ n) • f ∈ Γ₀(H) := smul_mem_gammaZero f hf (γ n)
  have hprox :
      IsProxPoint (((γ n) • f : H → Set.Ioi (⊥ : EReal))) (x n) (x (n + 1)) := by
    -- Read the orbit step as the canonical proximal point of the scaled function `γ_n • f`.
    rw [hx.x_succ_eq (hf := hf) n]
    simpa [scaledProximityOperator] using
      (proximityOperator_isProxPoint
        (((γ n) • f : H → Set.Ioi (⊥ : EReal)))
        (hasUniqueProxPoint_of_mem_gammaZero (((γ n) • f : H → Set.Ioi (⊥ : EReal))) hγf)
        (x n))
  exact
    (isProxPoint_iff_forall_inner_add_le (((γ n) • f : H → Set.Ioi (⊥ : EReal))) hγf.2
      (x n) (x (n + 1))).mp hprox z

/-- Helper for Theorem 28.1: the proximal residual at step `n` is a subgradient of `f` at
`x (n + 1)`. -/
private theorem proximalPointOrbit_invStep_mem_subdifferential_next
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {γ : ℕ → PosReal} {x0 : H} {x : ℕ → H} (hx : IsProximalPointOrbit hf γ x0 x)
    (n : ℕ) :
    ((γ n : ℝ)⁻¹ • (x n - x (n + 1))) ∈ (∂ f) (x (n + 1)) := by
  let hγf : ((γ n) • f : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H) := smul_mem_gammaZero f hf (γ n)
  have hscaled :
      x n - x (n + 1) ∈ (∂ (((γ n) • f : H → Set.Ioi (⊥ : EReal)))) (x (n + 1)) := by
    -- Read the source recursion as the proximal identity for the scaled function `γₙ • f`.
    rw [hx.x_succ_eq (hf := hf) n]
    exact
      (eq_proximityOperator_iff_sub_mem_subdifferential hγf (x n)
        (Prox[γ n, f, hf] (x n))).1 rfl
  rw [subdifferential_posReal_smul_eq_smul (f := f) (γ := γ n)] at hscaled
  -- Cancel the positive scalar in the scaled subdifferential description.
  change x n - x (n + 1) ∈ (γ n : ℝ) • ((∂ f) (x (n + 1))) at hscaled
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (γ n).2.ne'] at hscaled
  simpa using hscaled

/-- Helper for Theorem 28.1: after converting the scaled variational inequality to real values,
each proximal step bounds the source inner product by the corresponding objective-value gap. -/
private theorem inner_le_gamma_mul_valueGap_next
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {γ : ℕ → PosReal} {x0 : H} {x : ℕ → H} (hx : IsProximalPointOrbit hf γ x0 x)
    {z : H} (hz : z ∈ effectiveDomain f) (n : ℕ) :
    ⟪z - x (n + 1), x n - x (n + 1)⟫_ℝ ≤
      (γ n : ℝ) * ((f z : EReal).toReal - (f (x (n + 1)) : EReal).toReal) := by
  have hnext_dom := proximalPointOrbit_succ_mem_effectiveDomain (hf := hf) hx n
  have hnext_top : (f (x (n + 1)) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hnext_dom)
  have hnext_bot : (f (x (n + 1)) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x (n + 1)) : EReal) from (f (x (n + 1))).2)
  have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz)
  have hz_bot : (f z : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
  have hstepE := inner_add_gamma_mul_nextValue_le_gamma_mul_value (hf := hf) hx n z
  have hcast :
      (((⟪z - x (n + 1), x n - x (n + 1)⟫_ℝ +
            (γ n : ℝ) * (f (x (n + 1)) : EReal).toReal : ℝ) : EReal)) ≤
        ((((γ n : ℝ) * (f z : EReal).toReal : ℝ) : EReal)) := by
    simpa [posReal_smul_apply, EReal.coe_toReal hnext_top hnext_bot,
      EReal.coe_toReal hz_top hz_bot, EReal.coe_add, EReal.coe_mul] using hstepE
  have hreal :
      ⟪z - x (n + 1), x n - x (n + 1)⟫_ℝ +
          (γ n : ℝ) * (f (x (n + 1)) : EReal).toReal ≤
        (γ n : ℝ) * (f z : EReal).toReal := by
    exact_mod_cast hcast
  linarith

/-- Helper for Theorem 28.1: the real-valued objective sequence along the tail converges to the
minimum value `sInf (Set.range f.asEReal)`. -/
private theorem proximalPointOrbit_tailValue_tendsto_sInf
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hargmin : (Argmin f.asEReal).Nonempty)
    {γ : ℕ → PosReal}
    (hγ_diverges :
      Tendsto (fun N : ℕ ↦ (Finset.range N).sum (fun n ↦ (γ n : ℝ))) atTop atTop)
    {x0 : H} {x : ℕ → H} (hx : IsProximalPointOrbit hf γ x0 x) :
    Tendsto (fun n : ℕ ↦ f.asEReal (x (n + 1))) atTop (nhds (sInf (Set.range f.asEReal))) := by
  rcases hargmin with ⟨z, hzarg⟩
  have hz_dom :
      z ∈ effectiveDomain f := by
    exact mem_dom_of_mem_argmin_of_isProper (isProper_of_mem_gammaZero hf) hzarg
  have hz_eq : f.asEReal z = sInf (Set.range f.asEReal) := mem_argmin_iff_eq_sInf.mp hzarg
  let tailReal : ℕ → ℝ := fun n ↦ (f (x (n + 1)) : EReal).toReal
  let gap : ℕ → ℝ := fun n ↦ tailReal n - (f z : EReal).toReal
  have hgap_nonneg : ∀ n : ℕ, 0 ≤ gap n := by
    intro n
    have hnext_dom := proximalPointOrbit_succ_mem_effectiveDomain (hf := hf) hx n
    have hmin : (f z : EReal) ≤ (f (x (n + 1)) : EReal) := by
      exact (isMinOn_univ_iff.mp ((mem_argmin_iff).mp hzarg)) (x (n + 1))
    have hcast :
        (((f z : EReal).toReal : ℝ) : EReal) ≤
          (((f (x (n + 1)) : EReal).toReal : ℝ) : EReal) := by
      have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz_dom)
      have hz_bot : (f z : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
      have hnext_top : (f (x (n + 1)) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hnext_dom)
      have hnext_bot : (f (x (n + 1)) : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f (x (n + 1)) : EReal) from (f (x (n + 1))).2)
      simpa [EReal.coe_toReal hz_top hz_bot, EReal.coe_toReal hnext_top hnext_bot] using hmin
    have hreal : (f z : EReal).toReal ≤ (f (x (n + 1)) : EReal).toReal := by
      exact_mod_cast hcast
    exact sub_nonneg.mpr hreal
  have hgap_antitone : Antitone gap := by
    refine antitone_nat_of_succ_le ?_
    intro n
    -- Each proximal step decreases the objective value.
    have hstep :
        f.asEReal (x (n + 2)) ≤ f.asEReal (x (n + 1)) := by
      rw [hx.x_succ_eq (hf := hf) (n + 1)]
      exact proxValue_asEReal_le_self_of_mem_gammaZero f hf (x (n + 1)) (γ (n + 1))
    have hnext_dom := proximalPointOrbit_succ_mem_effectiveDomain (hf := hf) hx n
    have hnextnext_dom := proximalPointOrbit_succ_mem_effectiveDomain (hf := hf) hx (n + 1)
    have hnext_top : (f (x (n + 1)) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hnext_dom)
    have hnext_bot : (f (x (n + 1)) : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f (x (n + 1)) : EReal) from (f (x (n + 1))).2)
    have hnextnext_top : (f (x (n + 2)) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hnextnext_dom)
    have hnextnext_bot : (f (x (n + 2)) : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f (x (n + 2)) : EReal) from (f (x (n + 2))).2)
    have hcast :
        (((f (x (n + 2)) : EReal).toReal : ℝ) : EReal) ≤
          (((f (x (n + 1)) : EReal).toReal : ℝ) : EReal) := by
      simpa [EReal.coe_toReal hnextnext_top hnextnext_bot,
        EReal.coe_toReal hnext_top hnext_bot] using hstep
    have hreal : tailReal (n + 1) ≤ tailReal n := by
      exact_mod_cast hcast
    dsimp [gap]
    linarith
  have hweighted_drop :
      ∀ n : ℕ,
        2 * (γ n : ℝ) * gap n ≤ ‖x n - z‖ ^ 2 - ‖x (n + 1) - z‖ ^ 2 := by
    intro n
    -- Expand the source Fejer estimate using the one-step variational inequality at the argmin.
    have hstep := inner_le_gamma_mul_valueGap_next (hf := hf) hx hz_dom n
    have hsq :
        ‖x (n + 1) - z‖ ^ 2 =
          ‖x n - z‖ ^ 2 - ‖x n - x (n + 1)‖ ^ 2 +
            2 * ⟪z - x (n + 1), x n - x (n + 1)⟫_ℝ := by
      have hnorm :=
        norm_sub_sq_real (x n - z) (x n - x (n + 1))
      have hrew : x n - z - (x n - x (n + 1)) = x (n + 1) - z := by
        abel_nf
      rw [hrew] at hnorm
      have hsplit :
          ⟪x n - z, x n - x (n + 1)⟫_ℝ =
            ‖x n - x (n + 1)‖ ^ 2 +
              ⟪x (n + 1) - z, x n - x (n + 1)⟫_ℝ := by
        have hdecomp : x n - z = (x n - x (n + 1)) + (x (n + 1) - z) := by
          abel_nf
        rw [hdecomp, inner_add_left]
        simp [real_inner_self_eq_norm_sq, real_inner_comm]
      have hinner_neg :
          ⟪x (n + 1) - z, x n - x (n + 1)⟫_ℝ =
            -⟪z - x (n + 1), x n - x (n + 1)⟫_ℝ := by
        have hneg : x (n + 1) - z = -(z - x (n + 1)) := by
          abel_nf
        rw [hneg, inner_neg_left]
      nlinarith [hnorm, hsplit, hinner_neg]
    dsimp [gap]
    nlinarith [hsq, hstep, sq_nonneg ‖x n - x (n + 1)‖]
  have hsum_bound :
      ∀ N : ℕ,
        (Finset.range N).sum (fun n ↦ 2 * (γ n : ℝ) * gap n) ≤
          ‖x0 - z‖ ^ 2 - ‖x N - z‖ ^ 2 := by
    intro N
    induction N with
    | zero =>
        simpa [hx.x_zero (hf := hf)]
    | succ N ih =>
        have hdrop := hweighted_drop N
        rw [Finset.sum_range_succ]
        nlinarith
  have hgap_tendsto_zero : Tendsto gap atTop (𝓝 (0 : ℝ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    by_contra hnot
    rw [Filter.eventually_atTop] at hnot
    push Not at hnot
    have hlower : ∀ N : ℕ, ε ≤ gap N := by
      intro N
      rcases hnot N with ⟨m, hmN, hmε⟩
      have hmε' : ε ≤ gap m := by
        simpa [Real.dist_eq, abs_of_nonneg (hgap_nonneg m)] using hmε
      exact le_trans hmε' (hgap_antitone hmN)
    let M : ℝ := (‖x0 - z‖ ^ 2 + 1) / (2 * ε)
    have hM_event :
        ∀ᶠ N : ℕ in atTop,
          M ≤ (Finset.range N).sum (fun n ↦ (γ n : ℝ)) := by
      exact tendsto_atTop.1 hγ_diverges M
    rw [Filter.eventually_atTop] at hM_event
    rcases hM_event with ⟨N, hN⟩
    have hM_le : M ≤ (Finset.range N).sum (fun n ↦ (γ n : ℝ)) := hN N le_rfl
    have hterm_le :
        ∀ n : ℕ, 2 * ε * (γ n : ℝ) ≤ 2 * (γ n : ℝ) * gap n := by
      intro n
      have hγ_nonneg : 0 ≤ (γ n : ℝ) := (γ n).2.le
      have hgap_ge : ε ≤ gap n := hlower n
      nlinarith
    have hsum_ge :
        2 * ε * (Finset.range N).sum (fun n ↦ (γ n : ℝ)) ≤
          (Finset.range N).sum (fun n ↦ 2 * (γ n : ℝ) * gap n) := by
      calc
        2 * ε * (Finset.range N).sum (fun n ↦ (γ n : ℝ)) =
            (Finset.range N).sum (fun n ↦ 2 * ε * (γ n : ℝ)) := by
              rw [Finset.mul_sum]
        _ ≤ (Finset.range N).sum (fun n ↦ 2 * (γ n : ℝ) * gap n) := by
              exact Finset.sum_le_sum fun n _hn ↦ hterm_le n
    have hcontr :
        ‖x0 - z‖ ^ 2 + 1 ≤ ‖x0 - z‖ ^ 2 := by
      have hM_eq : 2 * ε * M = ‖x0 - z‖ ^ 2 + 1 := by
        dsimp [M]
        field_simp [show (2 * ε) ≠ 0 by positivity]
      calc
        ‖x0 - z‖ ^ 2 + 1 = 2 * ε * M := hM_eq.symm
        _ ≤ 2 * ε * (Finset.range N).sum (fun n ↦ (γ n : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hM_le (by positivity)
        _ ≤ (Finset.range N).sum (fun n ↦ 2 * (γ n : ℝ) * gap n) := hsum_ge
        _ ≤ ‖x0 - z‖ ^ 2 - ‖x N - z‖ ^ 2 := hsum_bound N
        _ ≤ ‖x0 - z‖ ^ 2 := by nlinarith [sq_nonneg ‖x N - z‖]
    nlinarith
  have htailReal_tendsto :
      Tendsto tailReal atTop (𝓝 ((f z : EReal).toReal)) := by
    -- Recover the tail values by adding the vanishing gap back to the minimum value.
    simpa [gap, tailReal, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      hgap_tendsto_zero.const_add ((f z : EReal).toReal)
  have htailEReal_tendsto :
      Tendsto (fun n ↦ (((tailReal n : ℝ) : EReal))) atTop
        (nhds ((((f z : EReal).toReal : ℝ) : EReal))) := by
    exact continuous_coe_real_ereal.continuousAt.tendsto.comp htailReal_tendsto
  have htailEq :
      ∀ n : ℕ, (((tailReal n : ℝ) : EReal)) = f.asEReal (x (n + 1)) := by
    intro n
    have hnext_dom := proximalPointOrbit_succ_mem_effectiveDomain (hf := hf) hx n
    have hnext_top : (f (x (n + 1)) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hnext_dom)
    have hnext_bot : (f (x (n + 1)) : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f (x (n + 1)) : EReal) from (f (x (n + 1))).2)
    simpa [tailReal, Function.asEReal, EReal.coe_toReal hnext_top hnext_bot]
  have hz_value :
      ((((f z : EReal).toReal : ℝ) : EReal)) = sInf (Set.range f.asEReal) := by
    have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz_dom)
    have hz_bot : (f z : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
    calc
      ((((f z : EReal).toReal : ℝ) : EReal)) = (f z : EReal) := EReal.coe_toReal hz_top hz_bot
      _ = sInf (Set.range f.asEReal) := by simpa [Function.asEReal] using hz_eq
  have htailEReal_eq :
      (fun n : ℕ ↦ (((tailReal n : ℝ) : EReal))) = fun n : ℕ ↦ f.asEReal (x (n + 1)) := by
    funext n
    exact htailEq n
  simpa [htailEReal_eq, hz_value] using htailEReal_tendsto

/-- Part (1) of Theorem 28.1: the objective values along a source-facing proximal-point orbit decrease
monotonically to `min f(H)`. This states the book's "more precisely" clause directly, because the
source allows the initial point `x0` to be arbitrary. -/
theorem proximalPointAlgorithm_objective_tendsto_inf_and_antitone
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hargmin : (Argmin f.asEReal).Nonempty)
    {γ : ℕ → PosReal}
    (hγ_diverges :
      Tendsto (fun N : ℕ ↦ (Finset.range N).sum (fun n ↦ (γ n : ℝ))) atTop atTop)
    {x0 : H} {x : ℕ → H} (hx : IsProximalPointOrbit hf γ x0 x) :
    Tendsto (fun n : ℕ ↦ f.asEReal (x n)) atTop (nhds (sInf (Set.range f.asEReal))) ∧
      Antitone (fun n : ℕ ↦ f.asEReal (x n)) := by
  -- First prove the source tail converges to `min f(H)` by the weighted-gap argument.
  have htail_tendsto :=
    proximalPointOrbit_tailValue_tendsto_sInf (hf := hf) hargmin hγ_diverges hx
  have hanti : Antitone (fun n : ℕ ↦ f.asEReal (x n)) := by
    -- Each step is a scaled proximal-point descent step.
    refine antitone_nat_of_succ_le ?_
    intro n
    rw [hx.x_succ_eq (hf := hf) n]
    exact proxValue_asEReal_le_self_of_mem_gammaZero f hf (x n) (γ n)
  refine ⟨?_, hanti⟩
  -- Shift back from the tail convergence to the full source sequence.
  exact (Filter.tendsto_add_atTop_iff_nat 1).1 (by simpa [Function.comp, Nat.add_comm] using htail_tendsto)

/-- Companion to part (1) of Theorem 28.1: although the source allows the prescribed initial point `x0`
to lie outside `dom f`, the proximal iterates from `x 1` onward form a minimizing sequence in the
canonical Definition 1.8 sense. -/
theorem proximalPointAlgorithm_tail_isMinimizingSequence
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hargmin : (Argmin f.asEReal).Nonempty)
    {γ : ℕ → PosReal}
    (hγ_diverges :
      Tendsto (fun N : ℕ ↦ (Finset.range N).sum (fun n ↦ (γ n : ℝ))) atTop atTop)
    {x0 : H} {x : ℕ → H} (hx : IsProximalPointOrbit hf γ x0 x) :
    IsMinimizingSequence f.asEReal (fun n : ℕ ↦ x (n + 1)) := by
  -- The tail stays in `dom f` and its objective values converge to the global infimum.
  refine ⟨?_, proximalPointOrbit_tailValue_tendsto_sInf (hf := hf) hargmin hγ_diverges hx⟩
  intro n
  simpa [dom, mem_dom_iff, Function.asEReal] using
    (mem_effectiveDomain_iff.mp (proximalPointOrbit_succ_mem_effectiveDomain (hf := hf) hx n))

/-- Helper for Theorem 28.1 (2): the proximal-point iterate value is finite, so the textbook level
`f.asEReal (x (n + 1))` agrees with the real threshold used by `lowerLevelSet`. -/
theorem proximalPointAlgorithm_nextValue_asEReal_eq_coe_toReal
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hargmin : (Argmin f.asEReal).Nonempty)
    {γ : ℕ → PosReal}
    (hγ_diverges :
      Tendsto (fun N : ℕ ↦ (Finset.range N).sum (fun n ↦ (γ n : ℝ))) atTop atTop)
    {x0 : H} {x : ℕ → H} (hx : IsProximalPointOrbit hf γ x0 x) (n : ℕ) :
    f.asEReal (x (n + 1)) = (((f.asEReal (x (n + 1))).toReal : ℝ) : EReal) := by
  -- The `(n + 1)`-st iterate lies in `effectiveDomain f`, so its `EReal` value is finite.
  have hnext_dom := proximalPointOrbit_succ_mem_effectiveDomain (hf := hf) hx n
  have hnext_top : (f (x (n + 1)) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hnext_dom)
  have hnext_bot : (f (x (n + 1)) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x (n + 1)) : EReal) from (f (x (n + 1))).2)
  simpa [Function.asEReal] using (EReal.coe_toReal hnext_top hnext_bot).symm

/-- Part (2) of Theorem 28.1: each next iterate is the metric projection of `x n` onto the lower level
set at height `f.asEReal (x (n + 1))`, expressed on the canonical set-valued projector surface
via the companion bridge `proximalPointAlgorithm_nextValue_asEReal_eq_coe_toReal`. -/
theorem proximalPointAlgorithm_projector_lowerLevelSet_eq_singleton
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hargmin : (Argmin f.asEReal).Nonempty)
    {γ : ℕ → PosReal}
    (hγ_diverges :
      Tendsto (fun N : ℕ ↦ (Finset.range N).sum (fun n ↦ (γ n : ℝ))) atTop atTop)
    {x0 : H} {x : ℕ → H} (hx : IsProximalPointOrbit hf γ x0 x) (n : ℕ) :
    P[lowerLevelSet f.asEReal ((f.asEReal (x (n + 1))).toReal)] (x n) = ({x (n + 1)} : Set H) :=
  by
  let C : Set H := lowerLevelSet f.asEReal ((f.asEReal (x (n + 1))).toReal)
  have hnext_mem : x (n + 1) ∈ C := by
    -- The current objective value is finite, so it sits exactly on the chosen level surface.
    change f.asEReal (x (n + 1)) ≤ (((f.asEReal (x (n + 1))).toReal : ℝ) : EReal)
    simpa using le_of_eq (proximalPointAlgorithm_nextValue_asEReal_eq_coe_toReal
      (hf := hf) hargmin hγ_diverges hx n)
  have hC_nonempty : C.Nonempty := ⟨x (n + 1), hnext_mem⟩
  have hC_closed : IsClosed C := by
    -- Lower semicontinuity of `f` closes every real lower level set.
    simpa [C] using
      ((lowerSemicontinuous_iff_isClosed_lowerLevelSet f.asEReal).1 hf.1)
        ((f.asEReal (x (n + 1))).toReal)
  have hC_convex : Convex ℝ C := by
    -- The Chapter 9 lower-level-set lemma provides the convexity input directly.
    simpa [C] using
      convex_lowerLevelSet_asEReal_of_mem_gammaZero hf ((f.asEReal (x (n + 1))).toReal)
  have hpoint :
      x (n + 1) =
        projectionPoint C
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
          (x n) := by
    -- Route correction: prove the single-valued projection identity first, then convert it back
    -- to the canonical set-valued projector surface.
    apply (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
      hC_nonempty hC_closed hC_convex).2
    constructor
    · exact hnext_mem
    · intro y hy
      have hy_finite : f.asEReal y < ⊤ := by
        have hlevel_top :
            ((((f.asEReal (x (n + 1))).toReal : ℝ) : EReal)) < ⊤ := by
          simpa using (EReal.coe_lt_top ((f.asEReal (x (n + 1))).toReal))
        exact lt_of_le_of_lt hy hlevel_top
      have hy_dom : y ∈ effectiveDomain f := by
        simpa [C, Function.asEReal, mem_effectiveDomain_iff] using hy_finite
      have hstep := inner_le_gamma_mul_valueGap_next (hf := hf) hx hy_dom n
      have hnext_dom := proximalPointOrbit_succ_mem_effectiveDomain (hf := hf) hx n
      have hnext_top : (f (x (n + 1)) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hnext_dom)
      have hnext_bot : (f (x (n + 1)) : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f (x (n + 1)) : EReal) from (f (x (n + 1))).2)
      have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom)
      have hy_bot : (f y : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
      have hy_real :
          (f y : EReal).toReal ≤ (f (x (n + 1)) : EReal).toReal := by
        have hcast :
            ((((f y : EReal).toReal : ℝ) : EReal)) ≤
              ((((f (x (n + 1)) : EReal).toReal : ℝ) : EReal)) := by
          have hy' :
              f.asEReal y ≤ f.asEReal (x (n + 1)) := by
            calc
              f.asEReal y ≤ (((f.asEReal (x (n + 1))).toReal : ℝ) : EReal) := hy
              _ = f.asEReal (x (n + 1)) := by
                symm
                exact proximalPointAlgorithm_nextValue_asEReal_eq_coe_toReal
                  (hf := hf) hargmin hγ_diverges hx n
          simpa [Function.asEReal, EReal.coe_toReal hy_top hy_bot,
            EReal.coe_toReal hnext_top hnext_bot] using hy'
        exact_mod_cast hcast
      have hgap_nonpos :
          (γ n : ℝ) * ((f y : EReal).toReal - (f (x (n + 1)) : EReal).toReal) ≤ 0 := by
        nlinarith [(γ n).2, hy_real]
      exact le_trans hstep hgap_nonpos
  calc
    P[C] (x n) =
        ({projectionPoint C
            (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
            (x n)} : Set H) := by
          simpa [C] using
            (setValuedProjector_eq_singleton_projectionPoint
              C
              (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
              (x n))
    _ = ({x (n + 1)} : Set H) := by simp [hpoint]

/-- Helper for Theorem 28.1: metric projections onto a nonempty closed convex set satisfy the
Pythagorean lower bound against every comparison point in that set. -/
private theorem projectionPoint_sqdist_add_sqdist_le_sqdist
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {x p z : H}
    (hp :
      p =
        projectionPoint C
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
          x)
    (hz : z ∈ C) :
    ‖x - p‖ ^ 2 + ‖p - z‖ ^ 2 ≤ ‖x - z‖ ^ 2 := by
  subst p
  have hcross_nonneg :
      0 ≤
        ⟪x -
            projectionPoint C
              (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x,
          projectionPoint C
              (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x - z⟫_ℝ := by
    have hinner :
        ⟪z -
              projectionPoint C
                (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x,
            x -
              projectionPoint C
                (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x⟫_ℝ ≤
          0 := by
      exact
        ((eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex).mp rfl).2 z hz
    have hinner' :
        ⟪x -
              projectionPoint C
                (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x,
            projectionPoint C
                (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x - z⟫_ℝ =
          -⟪z -
              projectionPoint C
                (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x,
            x -
              projectionPoint C
                (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x⟫_ℝ := by
      have hzproj :
          projectionPoint C
                (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x - z =
            -(z -
                projectionPoint C
                  (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x) := by
        abel_nf
      rw [hzproj, inner_neg_right]
      simpa [real_inner_comm] using real_inner_comm
        (x -
          projectionPoint C
            (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x)
        (z -
          projectionPoint C
            (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x)
    rw [hinner']
    exact neg_nonneg.mpr hinner
  have hsq_expand :
      ‖x - z‖ ^ 2 =
        ‖x -
            projectionPoint C
              (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x‖ ^ 2 +
          2 *
            ⟪x -
                projectionPoint C
                  (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x,
              projectionPoint C
                  (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x -
                z⟫_ℝ +
          ‖projectionPoint C
                (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x -
              z‖ ^ 2 := by
    have hdecomp :
        x - z =
          (x -
              projectionPoint C
                (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x) +
            (projectionPoint C
                (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x - z) := by
      abel_nf
    calc
      ‖x - z‖ ^ 2 =
          ‖(x -
                projectionPoint C
                  (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x) +
              (projectionPoint C
                  (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x - z)‖ ^ 2 := by
            rw [hdecomp]
      _ =
          ‖x -
              projectionPoint C
                (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x‖ ^ 2 +
            2 *
              ⟪x -
                  projectionPoint C
                    (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x,
                projectionPoint C
                    (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x - z⟫_ℝ +
            ‖projectionPoint C
                  (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x - z‖ ^ 2 := by
            simpa using
              norm_add_sq_real
                (x -
                  projectionPoint C
                    (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x)
                (projectionPoint C
                  (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x - z)
  nlinarith [hsq_expand, hcross_nonneg]

/-- Helper for Theorem 28.1: if a tail difference sequence fails to converge to `0`, then some
strictly monotone subsequence stays a fixed positive distance away from `0`. -/
private theorem exists_strictMono_subseq_norm_ge_of_not_tendsto_zero
    (u : ℕ → H) (hnot : ¬ Tendsto u atTop (𝓝 (0 : H))) :
    ∃ c > 0, ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ n, c ≤ ‖u (k n)‖ := by
  -- Extract a frequent escape from a neighborhood of `0`, then keep the escaped indices.
  rcases Filter.not_tendsto_iff_exists_frequently_notMem.1 hnot with ⟨s, hs0, hfreq⟩
  obtain ⟨c, hcpos, hcball⟩ := Metric.mem_nhds_iff.1 hs0
  rcases Filter.extraction_of_frequently_atTop hfreq with ⟨k, hkmono, hkout⟩
  refine ⟨c, hcpos, k, hkmono, ?_⟩
  intro n
  have hnot_ball : u (k n) ∉ Metric.ball (0 : H) c := by
    intro hkball
    exact hkout n (hcball hkball)
  have hdist : c ≤ dist (u (k n)) 0 := by
    by_contra hlt
    exact hnot_ball (by simpa [Metric.mem_ball, dist_eq_norm] using hlt)
  simpa [dist_eq_norm] using hdist

/-- Part (3) of Theorem 28.1: the proximal-point orbit converges weakly to a point of `Argmin f.asEReal`.
Weak convergence is expressed in the canonical weak topology `WeakSpace ℝ H`. -/
theorem proximalPointAlgorithm_exists_weakLimit_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hargmin : (Argmin f.asEReal).Nonempty)
    {γ : ℕ → PosReal}
    (hγ_diverges :
      Tendsto (fun N : ℕ ↦ (Finset.range N).sum (fun n ↦ (γ n : ℝ))) atTop atTop)
    {x0 : H} {x : ℕ → H} (hx : IsProximalPointOrbit hf γ x0 x) :
    ∃ z ∈ Argmin f.asEReal,
      Tendsto (fun n : ℕ ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H z)) := by
  have hquasi : QuasiconvexOn ℝ Set.univ f.asEReal := by
    rw [quasiconvexOn_univ_iff_convex_lowerLevelSet ℝ f.asEReal]
    intro ξ
    simpa using convex_lowerLevelSet_asEReal_of_mem_gammaZero hf ξ
  have hfejer : FejerMonotone (Argmin f.asEReal) x := by
    intro z hz n
    let C : Set H := lowerLevelSet f.asEReal ((f.asEReal (x (n + 1))).toReal)
    have hzC : z ∈ C := by
      change f.asEReal z ≤ (((f.asEReal (x (n + 1))).toReal : ℝ) : EReal)
      have hzmin : f.asEReal z ≤ f.asEReal (x (n + 1)) :=
        (isMinOn_univ_iff.mp ((mem_argmin_iff).mp hz)) (x (n + 1))
      calc
        f.asEReal z ≤ f.asEReal (x (n + 1)) := hzmin
        _ = (((f.asEReal (x (n + 1))).toReal : ℝ) : EReal) := by
          exact proximalPointAlgorithm_nextValue_asEReal_eq_coe_toReal
            (hf := hf) hargmin hγ_diverges hx n
    have hC_nonempty : C.Nonempty := ⟨x (n + 1), by
      change f.asEReal (x (n + 1)) ≤ (((f.asEReal (x (n + 1))).toReal : ℝ) : EReal)
      simpa using le_of_eq (proximalPointAlgorithm_nextValue_asEReal_eq_coe_toReal
        (hf := hf) hargmin hγ_diverges hx n)⟩
    have hC_closed : IsClosed C := by
      simpa [C] using
        ((lowerSemicontinuous_iff_isClosed_lowerLevelSet f.asEReal).1 hf.1)
          ((f.asEReal (x (n + 1))).toReal)
    have hC_convex : Convex ℝ C := by
      simpa [C] using
        convex_lowerLevelSet_asEReal_of_mem_gammaZero hf ((f.asEReal (x (n + 1))).toReal)
    have hprojset := proximalPointAlgorithm_projector_lowerLevelSet_eq_singleton
      (hf := hf) hargmin hγ_diverges hx n
    have hsingle :
        ({projectionPoint C
            (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
            (x n)} : Set H) = ({x (n + 1)} : Set H) := by
      rw [← hprojset]
      simpa [C] using
        (setValuedProjector_eq_singleton_projectionPoint
          C
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
          (x n)).symm
    have hpoint :
        projectionPoint C
            (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
            (x n) = x (n + 1) :=
      Set.singleton_injective hsingle
    have hpyth := projectionPoint_sqdist_add_sqdist_le_sqdist
      hC_nonempty hC_closed hC_convex hpoint.symm hzC
    have hsq :
        ‖x n - x (n + 1)‖ ^ 2 + ‖x (n + 1) - z‖ ^ 2 ≤ ‖x n - z‖ ^ 2 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, norm_sub_rev] using hpyth
    have hdrop : ‖x (n + 1) - z‖ ^ 2 ≤ ‖x n - z‖ ^ 2 := by
      nlinarith [hsq, sq_nonneg ‖x n - x (n + 1)‖]
    simpa [dist_eq_norm] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hdrop
  have hdiff_tendsto :
      Tendsto (fun n ↦ x n - x (n + 1)) atTop (𝓝 (0 : H)) := by
    rcases hargmin with ⟨z, hz⟩
    have hargmin' : (Argmin f.asEReal).Nonempty := ⟨z, hz⟩
    obtain ⟨l, hdist_tendsto⟩ := FejerMonotone.dist_tendsto hfejer hz
    have hsq_tendsto :
        Tendsto (fun n ↦ ‖x n - z‖ ^ 2) atTop (𝓝 (l ^ 2)) := by
      simpa [dist_eq_norm] using hdist_tendsto.pow 2
    have hsq_shift :
        Tendsto (fun n ↦ ‖x (n + 1) - z‖ ^ 2) atTop (𝓝 (l ^ 2)) := by
      simpa [Function.comp, Nat.add_comm] using
        (Filter.tendsto_add_atTop_iff_nat 1).2 hsq_tendsto
    have hgap_tendsto :
        Tendsto (fun n ↦ ‖x n - z‖ ^ 2 - ‖x (n + 1) - z‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
      simpa using hsq_tendsto.sub hsq_shift
    have hstep_sq_le :
        ∀ n : ℕ, ‖x n - x (n + 1)‖ ^ 2 ≤ ‖x n - z‖ ^ 2 - ‖x (n + 1) - z‖ ^ 2 := by
      intro n
      let C : Set H := lowerLevelSet f.asEReal ((f.asEReal (x (n + 1))).toReal)
      have hzC : z ∈ C := by
        change f.asEReal z ≤ (((f.asEReal (x (n + 1))).toReal : ℝ) : EReal)
        have hzmin : f.asEReal z ≤ f.asEReal (x (n + 1)) :=
          (isMinOn_univ_iff.mp ((mem_argmin_iff).mp hz)) (x (n + 1))
        calc
          f.asEReal z ≤ f.asEReal (x (n + 1)) := hzmin
          _ = (((f.asEReal (x (n + 1))).toReal : ℝ) : EReal) := by
            exact proximalPointAlgorithm_nextValue_asEReal_eq_coe_toReal
              (hf := hf) hargmin' hγ_diverges hx n
      have hC_nonempty : C.Nonempty := ⟨x (n + 1), by
        change f.asEReal (x (n + 1)) ≤ (((f.asEReal (x (n + 1))).toReal : ℝ) : EReal)
        simpa using le_of_eq (proximalPointAlgorithm_nextValue_asEReal_eq_coe_toReal
          (hf := hf) hargmin' hγ_diverges hx n)⟩
      have hC_closed : IsClosed C := by
        simpa [C] using
          ((lowerSemicontinuous_iff_isClosed_lowerLevelSet f.asEReal).1 hf.1)
            ((f.asEReal (x (n + 1))).toReal)
      have hC_convex : Convex ℝ C := by
        simpa [C] using
          convex_lowerLevelSet_asEReal_of_mem_gammaZero hf ((f.asEReal (x (n + 1))).toReal)
      have hprojset := proximalPointAlgorithm_projector_lowerLevelSet_eq_singleton
        (hf := hf) hargmin' hγ_diverges hx n
      have hsingle :
          ({projectionPoint C
              (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
              (x n)} : Set H) = ({x (n + 1)} : Set H) := by
        rw [← hprojset]
        simpa [C] using
          (setValuedProjector_eq_singleton_projectionPoint
            C
            (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
            (x n)).symm
      have hpoint :
          projectionPoint C
              (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
              (x n) = x (n + 1) :=
        Set.singleton_injective hsingle
      have hpyth := projectionPoint_sqdist_add_sqdist_le_sqdist
        hC_nonempty hC_closed hC_convex hpoint.symm hzC
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, norm_sub_rev] using hpyth
    have hsqstep_tendsto :
        Tendsto (fun n ↦ ‖x n - x (n + 1)‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
      refine squeeze_zero' (Eventually.of_forall fun n ↦ sq_nonneg ‖x n - x (n + 1)‖)
        (Eventually.of_forall hstep_sq_le) hgap_tendsto
    have hnorm_tendsto :
        Tendsto (fun n ↦ ‖x n - x (n + 1)‖) atTop (𝓝 (0 : ℝ)) := by
      have hsqrt_tendsto :
          Tendsto (fun n ↦ Real.sqrt (‖x n - x (n + 1)‖ ^ 2)) atTop
            (𝓝 (Real.sqrt 0)) := by
        exact Real.continuous_sqrt.continuousAt.tendsto.comp hsqstep_tendsto
      simpa [Real.sqrt_zero, Real.sqrt_sq_eq_abs] using hsqrt_tendsto
    exact (tendsto_zero_iff_norm_tendsto_zero).mpr hnorm_tendsto
  have hcluster :
      ∀ z : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H z) →
          z ∈ Argmin f.asEReal := by
    intro z hzcluster
    rcases hzcluster.exists_subseq_tendsto with ⟨φ, hφmono, hφtendsto⟩
    have hsubdiff :
        Tendsto (fun n ↦ x (φ n) - x (φ n + 1)) atTop (𝓝 (0 : H)) := by
      simpa [Function.comp] using hdiff_tendsto.comp hφmono.tendsto_atTop
    have hshift_tendsto :
        Tendsto (fun n ↦ toWeakSpace ℝ H (x (φ n + 1))) atTop (𝓝 (toWeakSpace ℝ H z)) :=
      SetValuedOperator.tendstoWeaklyOfSubTendstoZeroSeq hφtendsto hsubdiff
    have htail_cluster :
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x (n + 1))) (toWeakSpace ℝ H z) :=
      ⟨φ, hφmono, by simpa [Function.comp, Nat.add_comm] using hshift_tendsto⟩
    exact
      IsSequentialClusterPt.mem_argmin_of_isMinimizingSequence_of_quasiconvexOn_univ
        htail_cluster hquasi hf.1
        (proximalPointAlgorithm_tail_isMinimizingSequence (hf := hf) hargmin hγ_diverges hx)
  exact
    tendsto_weakly_of_fejerMonotone_of_weakSequentialClusterPts_mem
      hargmin x hfejer hcluster

/-- Theorem 28.1 (4): if `f` is uniformly convex on every nonempty bounded subset of `(∂ f).dom`,
then the proximal-point iterates converge strongly to a minimizer, and the argmin set is the
singleton containing that limit. -/
theorem proximalPointAlgorithm_exists_strongLimit_of_uniformlyConvexOnSubdiffDom
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hargmin : (Argmin f.asEReal).Nonempty)
    {γ : ℕ → PosReal}
    (hγ_diverges :
      Tendsto (fun N : ℕ ↦ (Finset.range N).sum (fun n ↦ (γ n : ℝ))) atTop atTop)
    {x0 : H} {x : ℕ → H} (hx : IsProximalPointOrbit hf γ x0 x)
    (huniform :
      ∀ ⦃C : Set H⦄, C.Nonempty → Bornology.IsBounded C → C ⊆ (∂ f).dom →
        ∃ φ : NNReal → EReal, UniformlyConvexOn f C φ) :
    ∃ z ∈ Argmin f.asEReal, Tendsto x atTop (𝓝 z) ∧
      Argmin f.asEReal = ({z} : Set H) := by
  obtain ⟨z, hzarg, hzweak⟩ :=
    proximalPointAlgorithm_exists_weakLimit_mem_argmin (hf := hf) hargmin hγ_diverges hx
  have hz_dom :
      z ∈ (∂ f).dom := by
    -- Fermat's rule turns the minimizing weak limit into a subdifferential zero.
    rw [argmin_eq_zeros_subdifferential, SetValuedOperator.mem_zeros_iff] at hzarg
    exact (SetValuedOperator.mem_dom_iff (∂ f) z).2 ⟨0, hzarg⟩
  have hz_eff :
      z ∈ effectiveDomain f :=
    mem_dom_of_mem_argmin_of_isProper (isProper_of_mem_gammaZero hf) hzarg
  have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz_eff)
  have hz_bot : (f z : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
  have hobj_tendsto :
      Tendsto (fun n : ℕ ↦ f.asEReal (x n)) atTop (nhds (sInf (Set.range f.asEReal))) :=
    (proximalPointAlgorithm_objective_tendsto_inf_and_antitone
      (hf := hf) hargmin hγ_diverges hx).1
  have htail_obj_tendsto :
      Tendsto (fun n : ℕ ↦ f.asEReal (x (n + 1))) atTop (𝓝 (f.asEReal z)) := by
    have hshift :
        Tendsto (fun n : ℕ ↦ f.asEReal (x (n + 1))) atTop
          (𝓝 (sInf (Set.range f.asEReal))) := by
      simpa [Function.comp, Nat.add_comm] using
        (Filter.tendsto_add_atTop_iff_nat 1).2 hobj_tendsto
    simpa [mem_argmin_iff_eq_sInf.mp hzarg] using hshift
  have htail_obj_real_tendsto :
      Tendsto (fun n : ℕ ↦ (f (x (n + 1)) : EReal).toReal) atTop
        (𝓝 ((f z : EReal).toReal)) := by
    -- The tail objective values stay finite, so `EReal.toReal` preserves the limit.
    simpa [Function.asEReal] using (EReal.tendsto_toReal hz_top hz_bot).comp htail_obj_tendsto
  have hzweak_shift :
      Tendsto (fun n : ℕ ↦ toWeakSpace ℝ H (x (n + 1))) atTop (𝓝 (toWeakSpace ℝ H z)) := by
    simpa [Function.comp, Nat.add_comm] using
      (Filter.tendsto_add_atTop_iff_nat 1).2 hzweak
  have hx_bounded : Bornology.IsBounded (Set.range x) :=
    bounded_range_of_tendsto_weakly hzweak
  have htail_bounded : Bornology.IsBounded (Set.range fun n ↦ x (n + 1)) := by
    exact hx_bounded.subset fun _ hy ↦ by
      rcases hy with ⟨n, rfl⟩
      exact ⟨n + 1, rfl⟩
  let C : Set H := Set.insert z (Set.range fun n ↦ x (n + 1))
  have hC_bounded : Bornology.IsBounded C := by
    change Bornology.IsBounded (Set.insert z (Set.range fun n ↦ x (n + 1)))
    exact
      (Bornology.isBounded_insert (x := z) (s := Set.range fun n ↦ x (n + 1))).2
        htail_bounded
  have hC_dom : C ⊆ (∂ f).dom := by
    intro w hw
    rcases Set.mem_insert_iff.mp hw with hw | hw
    · subst w
      exact hz_dom
    · rcases hw with ⟨n, rfl⟩
      exact
        (SetValuedOperator.mem_dom_iff (∂ f) (x (n + 1))).2
          ⟨((γ n : ℝ)⁻¹ • (x n - x (n + 1))),
            proximalPointOrbit_invStep_mem_subdifferential_next (hf := hf) hx n⟩
  obtain ⟨φ, hφ⟩ := huniform ⟨z, Set.mem_insert z (Set.range fun n ↦ x (n + 1))⟩
    hC_bounded hC_dom
  have hxshift_zero :
      Tendsto (fun n ↦ x (n + 1) - z) atTop (𝓝 (0 : H)) := by
    by_contra hnot
    rcases exists_strictMono_subseq_norm_ge_of_not_tendsto_zero
      (fun n ↦ x (n + 1) - z) hnot with
      ⟨c, hc, k, hkmono, hkbound⟩
    let cNN : NNReal := ⟨c, hc.le⟩
    have hz_mem : z ∈ C := by
      change z ∈ Set.insert z (Set.range fun n ↦ x (n + 1))
      exact Set.mem_insert z (Set.range fun n ↦ x (n + 1))
    have hk0_mem : x (k 0 + 1) ∈ C := by
      exact Set.mem_insert_iff.mpr (Or.inr ⟨k 0, rfl⟩)
    have hφ_c_nonneg : (0 : EReal) ≤ φ cNN := by
      rw [← (hφ.modulus_eq_zero_iff 0).2 rfl]
      exact hφ.monotone bot_le
    have hcNN_ne_zero : cNN ≠ 0 := by
      intro hcNN_zero
      have hc_zero : c = 0 := by
        simpa [cNN] using congrArg (fun r : NNReal ↦ (r : ℝ)) hcNN_zero
      exact (ne_of_gt hc) hc_zero
    have hφ_c_ne_zero : φ cNN ≠ 0 := by
      intro hzero
      exact hcNN_ne_zero ((hφ.modulus_eq_zero_iff cNN).1 hzero)
    have hcNN_le0 : cNN ≤ ‖x (k 0 + 1) - z‖₊ := by
      exact_mod_cast hkbound 0
    have hφ_c_top :
        φ cNN < ⊤ := by
      have htop0 :
          φ ‖x (k 0 + 1) - z‖₊ < ⊤ :=
        modulus_value_lt_top_of_uniformlyConvexOn hφ hk0_mem hz_mem
      exact lt_of_le_of_lt (hφ.monotone hcNN_le0) htop0
    have hφ_c_bot : φ cNN ≠ ⊥ := by
      intro hbot
      rw [hbot] at hφ_c_nonneg
      simp at hφ_c_nonneg
    let qcoef : EReal := (((1 / 2 * (1 - (1 / 2 : ℝ)) : ℝ) : EReal))
    let qconst : EReal := qcoef * φ cNN
    have hqcoef_nonneg : (0 : EReal) ≤ qcoef := by
      positivity
    have hqconst_nonneg : (0 : EReal) ≤ qconst := by
      exact mul_nonneg hqcoef_nonneg hφ_c_nonneg
    have hqconst_pos : (0 : EReal) < qconst := by
      -- The modulus stays strictly positive away from `0`, so the fixed quarter-gap is positive.
      have hqcoef_pos : (0 : EReal) < qcoef := by
        positivity
      exact EReal.mul_pos hqcoef_pos
        (lt_of_le_of_ne hφ_c_nonneg (Ne.symm hφ_c_ne_zero))
    have hqconst_top : qconst ≠ ⊤ := by
      change qcoef * φ cNN ≠ ⊤
      have hqcoef_bot : qcoef ≠ ⊥ := by
        dsimp [qcoef]
        exact EReal.coe_ne_bot ((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)))
      have hqcoef_top : qcoef ≠ ⊤ := by
        dsimp [qcoef]
        exact EReal.coe_ne_top ((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)))
      exact (EReal.mul_ne_top qcoef (φ cNN)).2
        ⟨Or.inl hqcoef_bot, Or.inl hqcoef_nonneg, Or.inl hqcoef_top, Or.inr hφ_c_top.ne⟩
    have hqconst_bot : qconst ≠ ⊥ := by
      intro hbot
      rw [hbot] at hqconst_nonneg
      simp at hqconst_nonneg
    have htail_gap_tendsto :
        Tendsto (fun n : ℕ ↦ (f (x (n + 1)) : EReal).toReal - (f z : EReal).toReal)
          atTop (𝓝 (0 : ℝ)) := by
      have hzconst_real :
          Tendsto (fun _ : ℕ ↦ (f z : EReal).toReal) atTop (𝓝 ((f z : EReal).toReal)) :=
        tendsto_const_nhds
      simpa using htail_obj_real_tendsto.sub hzconst_real
    have hsubtail_gap_tendsto :
        Tendsto (fun n : ℕ ↦ (f (x (k n + 1)) : EReal).toReal - (f z : EReal).toReal)
          atTop (𝓝 (0 : ℝ)) := by
      simpa [Function.comp, Nat.add_comm] using htail_gap_tendsto.comp hkmono.tendsto_atTop
    have hsmall :
        ∀ᶠ n in atTop,
          dist ((f (x (k n + 1)) : EReal).toReal - (f z : EReal).toReal) 0 < qconst.toReal := by
      exact (Metric.tendsto_nhds.1 hsubtail_gap_tendsto) qconst.toReal (by
        have hcast :
            (0 : EReal) < (((qconst.toReal : ℝ) : EReal)) := by
          simpa [EReal.coe_toReal hqconst_top hqconst_bot] using hqconst_pos
        exact_mod_cast hcast)
    rw [Filter.eventually_atTop] at hsmall
    rcases hsmall with ⟨N, hN⟩
    have hgap_nonneg :
        0 ≤ (f (x (k N + 1)) : EReal).toReal - (f z : EReal).toReal := by
      have hmin :
          (f z : EReal) ≤ (f (x (k N + 1)) : EReal) :=
        (isMinOn_univ_iff.mp ((mem_argmin_iff).mp hzarg)) (x (k N + 1))
      have hxn_eff :
          x (k N + 1) ∈ effectiveDomain f :=
        proximalPointOrbit_succ_mem_effectiveDomain (hf := hf) hx (k N)
      have hxn_top : (f (x (k N + 1)) : EReal) ≠ ⊤ :=
        ne_of_lt (mem_effectiveDomain_iff.mp hxn_eff)
      have hxn_bot : (f (x (k N + 1)) : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f (x (k N + 1)) : EReal) from (f _).2)
      have hcast :
          (((f z : EReal).toReal : ℝ) : EReal) ≤
            (((f (x (k N + 1)) : EReal).toReal : ℝ) : EReal) := by
        simpa [EReal.coe_toReal hz_top hz_bot, EReal.coe_toReal hxn_top hxn_bot] using hmin
      have hreal : (f z : EReal).toReal ≤ (f (x (k N + 1)) : EReal).toReal := by
        exact_mod_cast hcast
      linarith
    have hlt :
        (f (x (k N + 1)) : EReal).toReal - (f z : EReal).toReal < qconst.toReal := by
      simpa [Real.dist_eq, abs_of_nonneg hgap_nonneg] using hN N le_rfl
    have hxn_mem : x (k N + 1) ∈ C := by
      exact Set.mem_insert_iff.mpr (Or.inr ⟨k N, rfl⟩)
    have hcNN_le :
        cNN ≤ ‖x (k N + 1) - z‖₊ := by
      exact_mod_cast hkbound N
    have hmon :
        qconst ≤ qcoef * φ ‖x (k N + 1) - z‖₊ := by
      dsimp [qconst]
      exact mul_le_mul_of_nonneg_left (hφ.monotone hcNN_le) hqcoef_nonneg
    have hmid :
        (f ((1 / 2 : ℝ) • x (k N + 1) + (1 - (1 / 2 : ℝ)) • z) : EReal) +
            (qcoef * φ ‖x (k N + 1) - z‖₊) ≤
          (1 / 2 : EReal) * (f (x (k N + 1)) : EReal) +
            (1 - (1 / 2 : ℝ) : EReal) * (f z : EReal) := by
      -- Route correction: use the midpoint inequality only to force a fixed objective gap.
      have hmid_raw :=
        hφ.ineq (x := x (k N + 1)) (y := z) hxn_mem hz_mem
          (α := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      simpa [qcoef] using hmid_raw
    have hzmid :
        (f z : EReal) ≤
          (f ((1 / 2 : ℝ) • x (k N + 1) + (1 - (1 / 2 : ℝ)) • z) : EReal) :=
      (isMinOn_univ_iff.mp ((mem_argmin_iff).mp hzarg))
        ((1 / 2 : ℝ) • x (k N + 1) + (1 - (1 / 2 : ℝ)) • z)
    have hgapE :
        (f z : EReal) + qconst ≤
          (1 / 2 : EReal) * (f (x (k N + 1)) : EReal) +
            (1 - (1 / 2 : ℝ) : EReal) * (f z : EReal) := by
      calc
        (f z : EReal) + qconst ≤
            (f z : EReal) + (qcoef * φ ‖x (k N + 1) - z‖₊) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left hmon (f z : EReal)
        _ ≤
            (f ((1 / 2 : ℝ) • x (k N + 1) + (1 - (1 / 2 : ℝ)) • z) : EReal) +
              (qcoef * φ ‖x (k N + 1) - z‖₊) := by
                simpa [add_comm, add_left_comm, add_assoc] using
                  add_le_add_right hzmid (qcoef * φ ‖x (k N + 1) - z‖₊)
        _ ≤
            (1 / 2 : EReal) * (f (x (k N + 1)) : EReal) +
              (1 - (1 / 2 : ℝ) : EReal) * (f z : EReal) := hmid
    have hxn_eff :
        x (k N + 1) ∈ effectiveDomain f :=
      proximalPointOrbit_succ_mem_effectiveDomain (hf := hf) hx (k N)
    have hxn_top : (f (x (k N + 1)) : EReal) ≠ ⊤ :=
      ne_of_lt (mem_effectiveDomain_iff.mp hxn_eff)
    have hxn_bot : (f (x (k N + 1)) : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f (x (k N + 1)) : EReal) from (f _).2)
    have hgap_real :
        (f z : EReal).toReal + qconst.toReal ≤
          (1 / 2 : ℝ) * (f (x (k N + 1)) : EReal).toReal +
            (1 - (1 / 2 : ℝ)) * (f z : EReal).toReal := by
      have hcast :
          ((((f z : EReal).toReal + (qcoef * φ cNN).toReal : ℝ) : EReal)) ≤
            ((((1 / 2 : ℝ) * (f (x (k N + 1)) : EReal).toReal +
                (1 - (1 / 2 : ℝ)) * (f z : EReal).toReal : ℝ) : EReal)) := by
        have hleft :
            ((((f z : EReal).toReal + (qcoef * φ cNN).toReal : ℝ) : EReal)) =
              (f z : EReal) + qcoef * φ cNN := by
          rw [EReal.coe_add, EReal.coe_toReal hz_top hz_bot,
            EReal.coe_toReal hqconst_top hqconst_bot]
        have hright :
            ((((1 / 2 : ℝ) * (f (x (k N + 1)) : EReal).toReal +
                  (1 - (1 / 2 : ℝ)) * (f z : EReal).toReal : ℝ) : EReal)) =
              (((1 / 2 : ℝ) : EReal) * (f (x (k N + 1)) : EReal) +
                (((1 - (1 / 2 : ℝ)) : ℝ) : EReal) * (f z : EReal)) := by
          -- Keep the coefficient casts explicit so the `toReal` bridge rewrites syntactically.
          rw [EReal.coe_add, EReal.coe_mul, EReal.coe_toReal hxn_top hxn_bot,
            EReal.coe_mul, EReal.coe_toReal hz_top hz_bot]
        rw [hleft, hright]
        simpa using hgapE
      have hreal :
          (f z : EReal).toReal + (qcoef * φ cNN).toReal ≤
            (1 / 2 : ℝ) * (f (x (k N + 1)) : EReal).toReal +
              (1 - (1 / 2 : ℝ)) * (f z : EReal).toReal := by
        exact_mod_cast hcast
      simpa [qconst, qcoef] using hreal
    have hbig :
        2 * qconst.toReal ≤ (f (x (k N + 1)) : EReal).toReal - (f z : EReal).toReal := by
      nlinarith
    nlinarith
  have hxshift_strong :
      Tendsto (fun n ↦ x (n + 1)) atTop (𝓝 z) := by
    -- Add the limit point back after the tail difference converges to `0`.
    have hsum :
        Tendsto (fun n ↦ (x (n + 1) - z) + z) atTop (𝓝 ((0 : H) + z)) :=
      hxshift_zero.add tendsto_const_nhds
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
  have hxstrong :
      Tendsto x atTop (𝓝 z) := by
    exact (Filter.tendsto_add_atTop_iff_nat 1).1
      (by simpa [Function.comp, Nat.add_comm] using hxshift_strong)
  have hsingleton : Argmin f.asEReal = ({z} : Set H) := by
    ext y
    constructor
    · intro hy
      let Cpair : Set H := Set.insert z ({y} : Set H)
      have hy_dom :
          y ∈ (∂ f).dom := by
        rw [argmin_eq_zeros_subdifferential, SetValuedOperator.mem_zeros_iff] at hy
        exact (SetValuedOperator.mem_dom_iff (∂ f) y).2 ⟨0, hy⟩
      have hpair_dom : Cpair ⊆ (∂ f).dom := by
        intro w hw
        rcases Set.mem_insert_iff.mp hw with hw | hw
        · subst w
          exact hz_dom
        · rcases Set.mem_singleton_iff.mp hw with rfl
          exact hy_dom
      obtain ⟨φpair, hpair_uniform⟩ :=
        huniform ⟨z, Set.mem_insert z ({y} : Set H)⟩
          ((Set.finite_singleton y).insert z).isBounded hpair_dom
      rcases
          subdifferential_isUniformlyMonotoneOn_of_convexOn_of_uniformlyConvexOn
            f hf.2 hpair_dom hpair_uniform
        with
        ⟨ψ, hψ⟩
      have hy_mem : y ∈ Cpair := by
        change y ∈ Set.insert z ({y} : Set H)
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton y))
      have hz_mem_pair : z ∈ Cpair := by
        change z ∈ Set.insert z ({y} : Set H)
        exact Set.mem_insert z ({y} : Set H)
      have hy0 : (0 : H) ∈ (∂ f) y := by
        rw [argmin_eq_zeros_subdifferential, SetValuedOperator.mem_zeros_iff] at hy
        simpa using hy
      have hz0 : (0 : H) ∈ (∂ f) z := by
        rw [argmin_eq_zeros_subdifferential, SetValuedOperator.mem_zeros_iff] at hzarg
        simpa using hzarg
      have hyz : y = z := by
        exact
          SetValuedOperator.eq_of_modulus_le_zero hψ.monotone hψ.modulus_eq_zero_iff
            (by simpa using hψ.ineq hy_mem hz_mem_pair hy0 hz0)
      simp [hyz]
    · intro hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact hzarg
  exact ⟨z, hzarg, hxstrong, hsingleton⟩

end ProximalPointAlgorithm

end ERealFunction
