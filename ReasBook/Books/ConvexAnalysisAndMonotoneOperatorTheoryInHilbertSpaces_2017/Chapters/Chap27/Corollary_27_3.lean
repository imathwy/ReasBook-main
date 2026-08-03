import BauschkeLean.Chap20.Theorem_20_25
import BauschkeLean.Chap23.Example_23_3
import BauschkeLean.Chap17.Definition_17_1
import BauschkeLean.Chap17.Proposition_17_21
import BauschkeLean.Chap27.Proposition_27_5

open Set
open scoped InnerProductSpace Pointwise SetValuedOperator

noncomputable section

universe u

namespace ERealFunction

section GeneralCharacterizationsOfMinimizers

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Semantic recall note: `lean_leansearch` only surfaced generic calculus lemmas here, not the
-- Chapter 27/26 convex-optimization owners. The verified local surfaces for this corollary are
-- `CompositePrimalObjectiveRegularity`, `∂`, `Prox[γ, f, hf]`, `Function.fixedPoints`, `sri`,
-- `ri`, and the Chapter 26 Douglas--Rachford / forward-backward fixed-point owners.

/-- The three source regularity alternatives in Corollary 27.3 for the pointwise-sum problem
`minimize f(x) + g(x)`. -/
inductive PointwiseAddRegularity
    (f g : H → Set.Ioi (⊥ : EReal)) : Prop where
  | zero_mem_sri
      (hsri : (0 : H) ∈ sri (effectiveDomain g - effectiveDomain f)) :
      PointwiseAddRegularity f g
  | finiteDimensional_polyhedral_g
      (hfin : FiniteDimensional ℝ H)
      (hpoly : Polyhedral g.asEReal)
      (hri : (effectiveDomain g ∩ ri (effectiveDomain f)).Nonempty) :
      PointwiseAddRegularity f g
  | finiteDimensional_polyhedral_fg
      (hfin : FiniteDimensional ℝ H)
      (hpolyf : Polyhedral f.asEReal)
      (hpolyg : Polyhedral g.asEReal)
      (hfeas : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
      PointwiseAddRegularity f g

omit [CompleteSpace H] in
/-- The three regularity alternatives in Corollary 27.3 are exactly the identity-map
specializations of the Chapter 27 composite-primal regularity owner. -/
theorem PointwiseAddRegularity.toCompositePrimalObjectiveRegularity
    {f g : H → Set.Ioi (⊥ : EReal)} (hregular : PointwiseAddRegularity f g) :
    CompositePrimalObjectiveRegularity f g (ContinuousLinearMap.id ℝ H) := by
  cases hregular with
  | zero_mem_sri hsri =>
      refine CompositePrimalObjectiveRegularity.zero_mem_sri ?_
      simpa using hsri
  | finiteDimensional_polyhedral_g hfin hpoly hri =>
      refine CompositePrimalObjectiveRegularity.polyhedral_finiteDimensional_ri hfin hpoly ?_
      simpa using hri
  | finiteDimensional_polyhedral_fg hfin hpolyf hpolyg hfeas =>
      refine CompositePrimalObjectiveRegularity.polyhedral_finiteDimensional
        hfin hfin hpolyf hpolyg ?_
      rcases hfeas with ⟨x, hfx, hgx⟩
      exact ⟨x, hgx, ⟨x, hfx, rfl⟩⟩

/-- The minimizer/zero-set equivalence appearing in Corollary 27.3: under one of the three source
regularity alternatives, `xbar` minimizes `f + g` if and only if
`xbar ∈ zer (∂ f + ∂ g)`. -/
theorem mem_argmin_add_iff_mem_zeros_subdifferential_add_of_regularity
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hregular : PointwiseAddRegularity f g) {xbar : H} :
    xbar ∈ Argmin (f + g).asEReal ↔
      xbar ∈ ((∂ f) + (∂ g)).zeros := by
  simpa [compositePrimalObjective, primalObjective,
    ContinuousLinearMap.adjointImageSubdifferential] using
    congrArg (fun S : Set H ↦ xbar ∈ S)
      (argmin_compositePrimalObjective_eq_zeros_subdifferential_sum_of_regular
        hf hg (ContinuousLinearMap.id ℝ H) hregular.toCompositePrimalObjectiveRegularity)

omit [CompleteSpace H] in
/-- Helper for Corollary 27.3: scaling a subgradient by `γ ∈ ℝ_{++}` is equivalent to belonging
to the subdifferential of the scaled function `γ • f`. -/
theorem smul_mem_subdifferential_posReal_smul_iff_local
    {f : H → Set.Ioi (⊥ : EReal)} (γ : PosReal) {x u : H} :
    (γ : ℝ) • u ∈ (∂ ((γ • f : H → Set.Ioi (⊥ : EReal)))) x ↔ u ∈ (∂ f) x := by
  rw [subdifferential_posReal_smul_eq_smul (f := f) (γ := γ)]
  change (γ : ℝ) • u ∈ (γ : ℝ) • ((∂ f) x) ↔ u ∈ (∂ f) x
  constructor
  · intro hu
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] at hu
    simpa [smul_smul, inv_mul_cancel₀ γ.2.ne'] using hu
  · intro hu
    exact Set.smul_mem_smul_set hu

/-- Corollary 27.3: for `f, g ∈ Γ₀(H)` and `γ ∈ ℝ_{++}`, the zero-set condition
`xbar ∈ zer (∂ f + ∂ g)` is equivalent to `xbar` belonging to the image of the fixed points of
`(2 Prox_{γ f} - Id) ∘ (2 Prox_{γ g} - Id)` under `Prox_{γ g}`. -/
theorem mem_zeros_subdifferential_add_iff_mem_scaledProx_image_fixedPoints_reflectedProximity
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (γ : PosReal) {xbar : H} :
    xbar ∈ ((∂ f) + (∂ g)).zeros ↔
      xbar ∈ Prox[γ, g, hg] '' Function.fixedPoints
        ((fun x : H ↦ (2 : ℝ) • Prox[γ, f, hf] x - x) ∘
          fun x : H ↦ (2 : ℝ) • Prox[γ, g, hg] x - x) := by
  constructor
  · intro hxzero
    rw [SetValuedOperator.mem_zeros_iff] at hxzero
    change 0 ∈ (∂ f) xbar + (∂ g) xbar at hxzero
    rw [Set.mem_add] at hxzero
    rcases hxzero with ⟨v, hvf, u, hug, hvu⟩
    have hv_eq : v = -u := by
      simpa using eq_neg_of_add_eq_zero_left hvu
    let y : H := xbar + (γ : ℝ) • u
    have hy_prox_g : xbar = Prox[γ, g, hg] y := by
      apply (eq_proximityOperator_iff_sub_mem_subdifferential
        (f := ((γ : PosReal) • g : H → Set.Ioi (⊥ : EReal)))
        (hf := smul_mem_gammaZero g hg γ)
        (x := y)
        (p := xbar)).2
      have hscaled :
          (γ : ℝ) • u ∈ (∂ ((γ : PosReal) • g : H → Set.Ioi (⊥ : EReal))) xbar :=
        (smul_mem_subdifferential_posReal_smul_iff_local
          (f := g) (γ := γ) (x := xbar) (u := u)).2 hug
      simpa [y, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hscaled
    have hvf' : -u ∈ (∂ f) xbar := by
      simpa [hv_eq] using hvf
    have hy_prox_f : xbar = Prox[γ, f, hf] ((2 : ℝ) • xbar - y) := by
      apply (eq_proximityOperator_iff_sub_mem_subdifferential
        (f := ((γ : PosReal) • f : H → Set.Ioi (⊥ : EReal)))
        (hf := smul_mem_gammaZero f hf γ)
        (x := (2 : ℝ) • xbar - y)
        (p := xbar)).2
      have hscaled :
          (γ : ℝ) • (-u) ∈ (∂ ((γ : PosReal) • f : H → Set.Ioi (⊥ : EReal))) xbar :=
        (smul_mem_subdifferential_posReal_smul_iff_local
          (f := f) (γ := γ) (x := xbar) (u := -u)).2 hvf'
      have hresidual : ((2 : ℝ) • xbar - y) - xbar = (γ : ℝ) • (-u) := by
        calc
          ((2 : ℝ) • xbar - y) - xbar = xbar - y := by
            rw [two_smul, sub_eq_add_neg, sub_eq_add_neg]
            abel_nf
          _ = -(y - xbar) := by
            simp [sub_eq_add_neg]
          _ = (γ : ℝ) • (-u) := by
            simp [y, sub_eq_add_neg, smul_neg]
      simpa [hresidual] using hscaled
    rw [Set.mem_image]
    refine ⟨y, ?_, hy_prox_g.symm⟩
    rw [Function.mem_fixedPoints_iff]
    have hTg :
        ((fun x : H ↦ (2 : ℝ) • Prox[γ, g, hg] x - x) y) = (2 : ℝ) • xbar - y := by
      simp [hy_prox_g]
    calc
      (((fun x : H ↦ (2 : ℝ) • Prox[γ, f, hf] x - x) ∘
          fun x : H ↦ (2 : ℝ) • Prox[γ, g, hg] x - x) y)
          = (2 : ℝ) • Prox[γ, f, hf] (((2 : ℝ) • xbar - y)) - ((2 : ℝ) • xbar - y) := by
              simp [Function.comp, hTg]
      _ = y := by
            calc
              (2 : ℝ) • Prox[γ, f, hf] (((2 : ℝ) • xbar - y)) - ((2 : ℝ) • xbar - y)
                  = (2 : ℝ) • xbar - ((2 : ℝ) • xbar - y) := by
                      exact congrArg
                        (fun t : H ↦ (2 : ℝ) • t - ((2 : ℝ) • xbar - y))
                        hy_prox_f.symm
              _ = y := by abel_nf
  · rintro ⟨y, hyfix, hyprox⟩
    let u : H := (γ : ℝ)⁻¹ • (y - xbar)
    have hscaled_g_raw :
        y - xbar ∈ (∂ ((γ : PosReal) • g : H → Set.Ioi (⊥ : EReal))) xbar :=
      (eq_proximityOperator_iff_sub_mem_subdifferential
        (f := ((γ : PosReal) • g : H → Set.Ioi (⊥ : EReal)))
        (hf := smul_mem_gammaZero g hg γ)
        (x := y)
        (p := xbar)).1 hyprox.symm
    have hscaled_g :
        (γ : ℝ) • u ∈ (∂ ((γ : PosReal) • g : H → Set.Ioi (⊥ : EReal))) xbar := by
      simpa [u, smul_smul, γ.2.ne'] using hscaled_g_raw
    have hu_g : u ∈ (∂ g) xbar :=
      (smul_mem_subdifferential_posReal_smul_iff_local
        (f := g) (γ := γ) (x := xbar) (u := u)).1 hscaled_g
    rw [Function.mem_fixedPoints_iff, Function.comp] at hyfix
    have hyfix' :
        (2 : ℝ) • Prox[γ, f, hf] ((2 : ℝ) • xbar - y) - ((2 : ℝ) • xbar - y) = y := by
      simpa [hyprox] using hyfix
    have htwo :
        (2 : ℝ) • Prox[γ, f, hf] ((2 : ℝ) • xbar - y) = (2 : ℝ) • xbar := by
      calc
        (2 : ℝ) • Prox[γ, f, hf] ((2 : ℝ) • xbar - y)
            = ((2 : ℝ) • Prox[γ, f, hf] ((2 : ℝ) • xbar - y) -
                ((2 : ℝ) • xbar - y)) + ((2 : ℝ) • xbar - y) := by
                  abel_nf
        _ = y + ((2 : ℝ) • xbar - y) := by rw [hyfix']
        _ = (2 : ℝ) • xbar := by abel_nf
    have hy_prox_f : Prox[γ, f, hf] ((2 : ℝ) • xbar - y) = xbar := by
      have hhalf := congrArg (fun t : H ↦ ((2 : ℝ)⁻¹) • t) htwo
      simpa [smul_smul] using hhalf
    have hscaled_f_raw :
        ((2 : ℝ) • xbar - y) - xbar ∈
          (∂ ((γ : PosReal) • f : H → Set.Ioi (⊥ : EReal))) xbar :=
      (eq_proximityOperator_iff_sub_mem_subdifferential
        (f := ((γ : PosReal) • f : H → Set.Ioi (⊥ : EReal)))
        (hf := smul_mem_gammaZero f hf γ)
        (x := (2 : ℝ) • xbar - y)
        (p := xbar)).1 hy_prox_f.symm
    have hscaled_f :
        (γ : ℝ) • (-u) ∈ (∂ ((γ : PosReal) • f : H → Set.Ioi (⊥ : EReal))) xbar := by
      have hresidual : ((2 : ℝ) • xbar - y) - xbar = (γ : ℝ) • (-u) := by
        calc
          ((2 : ℝ) • xbar - y) - xbar = xbar - y := by
            rw [two_smul, sub_eq_add_neg, sub_eq_add_neg]
            abel_nf
          _ = -(y - xbar) := by
            simp [sub_eq_add_neg]
          _ = (γ : ℝ) • (-u) := by
            simp [u, sub_eq_add_neg, smul_neg, smul_smul, γ.2.ne']
      simpa [hresidual] using hscaled_f_raw
    have hu_f : -u ∈ (∂ f) xbar :=
      (smul_mem_subdifferential_posReal_smul_iff_local
        (f := f) (γ := γ) (x := xbar) (u := -u)).1 hscaled_f
    rw [SetValuedOperator.mem_zeros_iff]
    change 0 ∈ (∂ f) xbar + (∂ g) xbar
    rw [Set.mem_add]
    exact ⟨-u, hu_f, u, hu_g, by simp⟩

omit [CompleteSpace H] in
/-- The zero-set/subgradient-witness equivalence used in Corollary 27.3:
`xbar ∈ zer (∂ f + ∂ g)` is equivalent to the existence of `u ∈ ∂ g(xbar)` such that
`-u ∈ ∂ f(xbar)`. -/
theorem mem_zeros_subdifferential_add_iff_exists_mem_subdifferential_neg
    {f g : H → Set.Ioi (⊥ : EReal)} {xbar : H} :
    xbar ∈ ((∂ f) + (∂ g)).zeros ↔
      ∃ u : H, u ∈ (∂ g) xbar ∧ -u ∈ (∂ f) xbar := by
  rw [SetValuedOperator.mem_zeros_iff]
  change 0 ∈ (∂ f) xbar + (∂ g) xbar ↔
    ∃ u : H, u ∈ (∂ g) xbar ∧ -u ∈ (∂ f) xbar
  rw [Set.mem_add]
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    refine ⟨v, hv, ?_⟩
    have hu_eq : u = -v := by
      simpa using eq_neg_of_add_eq_zero_left huv
    simpa [hu_eq] using hu
  · rintro ⟨u, hu, hv⟩
    exact ⟨-u, hv, u, hu, by simp⟩

omit [CompleteSpace H] in
/-- The affine-minorant reformulation used in Corollary 27.3: the existence of a subgradient
`u ∈ ∂ g(xbar)` with `-u ∈ ∂ f(xbar)` is equivalent to the inequality
`⟪xbar - y, u⟫ + f(xbar) ≤ f(y)` for all `y`. -/
theorem exists_mem_subdifferential_neg_iff_exists_subgradient_inequality
    {f g : H → Set.Ioi (⊥ : EReal)} {xbar : H} :
    (∃ u ∈ (∂ g) xbar, -u ∈ (∂ f) xbar) ↔
      ∃ u ∈ (∂ g) xbar,
        ∀ y : H, (⟪xbar - y, u⟫_ℝ : EReal) + (f xbar : EReal) ≤ (f y : EReal) := by
  constructor
  · rintro ⟨u, hu, hneg⟩
    refine ⟨u, hu, ?_⟩
    rw [mem_subdifferential_iff] at hneg
    intro y
    have hshift :
        (⟪xbar - y, u⟫_ℝ : EReal) = (⟪y - xbar, -u⟫_ℝ : EReal) := by
      have hreal : ⟪xbar - y, u⟫_ℝ = ⟪y - xbar, -u⟫_ℝ := by
        calc
          ⟪xbar - y, u⟫_ℝ = ⟪-(y - xbar), u⟫_ℝ := by
            simp [sub_eq_add_neg]
          _ = -⟪y - xbar, u⟫_ℝ := by
            rw [inner_neg_left]
          _ = ⟪y - xbar, -u⟫_ℝ := by
            rw [inner_neg_right]
      exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
    calc
      (⟪xbar - y, u⟫_ℝ : EReal) + (f xbar : EReal)
          = (⟪y - xbar, -u⟫_ℝ : EReal) + (f xbar : EReal) := by rw [hshift]
      _ ≤ (f y : EReal) := hneg y
  · rintro ⟨u, hu, hineq⟩
    refine ⟨u, hu, ?_⟩
    rw [mem_subdifferential_iff]
    intro y
    have hshift :
        (⟪xbar - y, u⟫_ℝ : EReal) = (⟪y - xbar, -u⟫_ℝ : EReal) := by
      have hreal : ⟪xbar - y, u⟫_ℝ = ⟪y - xbar, -u⟫_ℝ := by
        calc
          ⟪xbar - y, u⟫_ℝ = ⟪-(y - xbar), u⟫_ℝ := by
            simp [sub_eq_add_neg]
          _ = -⟪y - xbar, u⟫_ℝ := by
            rw [inner_neg_left]
          _ = ⟪y - xbar, -u⟫_ℝ := by
            rw [inner_neg_right]
      exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
    calc
      (⟪y - xbar, -u⟫_ℝ : EReal) + (f xbar : EReal)
          = (⟪xbar - y, u⟫_ℝ : EReal) + (f xbar : EReal) := by rw [← hshift]
      _ ≤ (f y : EReal) := hineq y

omit [CompleteSpace H] in
/-- Helper for Corollary 27.3: a subgradient at `x` bounds every positive directional increment
quotient from below. -/
private theorem inner_le_increment_quotient_of_mem_subdifferential_local
    (f : H → Set.Ioi (⊥ : EReal))
    {x u y : H} (hx : x ∈ effectiveDomain f) (hu : u ∈ (∂ f) x)
    {α : ℝ} (hα : 0 < α) :
    (⟪y, u⟫_ℝ : EReal) ≤
      (((f (x + α • y) : EReal) - (f x : EReal)) / α) := by
  have huα :
      (⟪α • y, u⟫_ℝ : EReal) + (f x : EReal) ≤
        (f (x + α • y) : EReal) := by
    simpa using (mem_subdifferential_iff f x u).1 hu (x + α • y)
  by_cases hxy : x + α • y ∈ effectiveDomain f
  · have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hxy_top : (f (x + α • y) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hxy)
    have hxy_bot : (f (x + α • y) : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f (x + α • y) : EReal) from (f (x + α • y)).2)
    have huα_real :
        α * ⟪y, u⟫_ℝ + (f x : EReal).toReal ≤
          (f (x + α • y) : EReal).toReal := by
      have hcast :
          (((α * ⟪y, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal)) ≤
            (((f (x + α • y) : EReal).toReal : ℝ) : EReal) := by
        calc
          (((α * ⟪y, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal))
              = (⟪α • y, u⟫_ℝ : EReal) + (f x : EReal) := by
                  rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
                  simp [real_inner_smul_left, EReal.coe_mul]
          _ ≤ (f (x + α • y) : EReal) := huα
          _ = (((f (x + α • y) : EReal).toReal : ℝ) : EReal) := by
                exact (EReal.coe_toReal hxy_top hxy_bot).symm
      exact_mod_cast hcast
    have hquot_real :
        ⟪y, u⟫_ℝ ≤
          ((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α := by
      refine (le_div_iff₀ hα).2 ?_
      linarith
    have hquot_cast :
        (⟪y, u⟫_ℝ : EReal) ≤
          ((((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal) := by
      exact_mod_cast hquot_real
    have hquot_eq :
        (((f (x + α • y) : EReal) - (f x : EReal)) / α) =
          ((((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hxy_top hxy_bot, ← EReal.coe_toReal hx_top hx_bot,
        ← EReal.coe_sub, ← EReal.coe_div]
      simp
    rw [hquot_eq]
    exact hquot_cast
  · have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hxy_top : (f (x + α • y) : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hxy))
    have hαE_pos : (0 : EReal) < (α : EReal) := by
      exact_mod_cast hα
    have hα_ne_top : (α : EReal) ≠ ⊤ := EReal.coe_ne_top _
    rw [hxy_top, EReal.top_sub hx_top, EReal.top_div_of_pos_ne_top hαE_pos hα_ne_top]
    exact le_top

omit [CompleteSpace H] in
/-- Helper for Corollary 27.3: every subgradient yields a pointwise lower bound for the
directional derivative. -/
private theorem forall_inner_le_directionalDerivative_of_mem_subdifferential_local
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x u : H} (hx : x ∈ effectiveDomain f) (hu : u ∈ (∂ f) x) :
    ∀ y : H, (⟪y, u⟫_ℝ : EReal) ≤ directionalDerivative f x y := by
  let _ := hconv
  intro y
  rw [directionalDerivative]
  apply le_sInf
  rintro q ⟨α, rfl⟩
  simpa [directionalDifferenceQuotient] using
    inner_le_increment_quotient_of_mem_subdifferential_local
      (f := f) hx hu (α := (α : ℝ)) α.2

omit [CompleteSpace H] in
/-- Helper for Corollary 27.3: if every directional derivative of `g` at `xbar` is represented by
`gradg`, then the subdifferential of `g` at `xbar` is the singleton `{gradg}`. -/
theorem subdifferential_eq_singleton_of_forall_hasDirectionalDerivativeAt_local
    {g : H → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(H)) {xbar gradg : H}
    (hgrad :
      ∀ y : H,
        HasDirectionalDerivativeAt g xbar y
          ((((InnerProductSpace.toDualMap ℝ H gradg) y : ℝ) : EReal))) :
    (∂ g) xbar = ({gradg} : Set H) := by
  have hconv : ConvexOn g (effectiveDomain g) := (mem_gammaZero_iff.mp hg).2
  have hxbar : xbar ∈ effectiveDomain g := (hgrad 0).1
  have hgrad_mem : gradg ∈ (∂ g) xbar := by
    rw [mem_subdifferential_iff]
    intro z
    have hdir :
        directionalDerivative g xbar (z - xbar) = (⟪z - xbar, gradg⟫_ℝ : EReal) := by
      simpa [real_inner_comm] using
        (directionalDerivative_eq_of_hasDirectionalDerivativeAt
          (f := g) hconv (hgrad (z - xbar)))
    calc
      (⟪z - xbar, gradg⟫_ℝ : EReal) + (g xbar : EReal)
          = directionalDerivative g xbar (z - xbar) + (g xbar : EReal) := by rw [hdir]
      _ ≤ (g z : EReal) := directionalDerivative_add_value_le (f := g) hxbar z
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨hgrad_mem, ?_⟩
  · intro u hu
    -- Any other subgradient has the same inner products against every direction.
    apply ext_inner_left ℝ
    intro y
    have hu_y :
        (⟪y, u⟫_ℝ : EReal) ≤ ((((InnerProductSpace.toDualMap ℝ H gradg) y : ℝ) : EReal)) := by
      have hu_dir :=
        forall_inner_le_directionalDerivative_of_mem_subdifferential_local
          (f := g) hconv hxbar hu y
      rw [ERealFunction.directionalDerivative_eq_of_hasDirectionalDerivativeAt (f := g) hconv
        (hgrad y)] at hu_dir
      exact hu_dir
    have hu_neg :
        (⟪-y, u⟫_ℝ : EReal) ≤
          ((((InnerProductSpace.toDualMap ℝ H gradg) (-y) : ℝ) : EReal)) := by
      have hu_dir :=
        forall_inner_le_directionalDerivative_of_mem_subdifferential_local
          (f := g) hconv hxbar hu (-y)
      rw [ERealFunction.directionalDerivative_eq_of_hasDirectionalDerivativeAt (f := g) hconv
        (hgrad (-y))] at hu_dir
      exact hu_dir
    have hu_y_real : ⟪y, u⟫_ℝ ≤ ⟪y, gradg⟫_ℝ := by
      simpa [real_inner_comm] using EReal.coe_le_coe_iff.mp hu_y
    have hu_neg_real : ⟪y, gradg⟫_ℝ ≤ ⟪y, u⟫_ℝ := by
      simpa [real_inner_comm] using EReal.coe_le_coe_iff.mp hu_neg
    exact le_antisymm hu_y_real hu_neg_real

omit [CompleteSpace H] in
/-- The differentiable-`g` reduction used in Corollary 27.3: if every directional derivative of
`g` at `xbar` is represented by the gradient `gradg`, then the subgradient witness condition is
equivalent to `-gradg ∈ ∂ f(xbar)`. -/
theorem exists_mem_subdifferential_neg_iff_neg_gradient_mem_subdifferential
    {f g : H → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(H)) {xbar gradg : H}
    (hgrad :
      ∀ y : H,
        HasDirectionalDerivativeAt g xbar y
          ((((InnerProductSpace.toDualMap ℝ H gradg) y : ℝ) : EReal))) :
    (∃ u : H, u ∈ (∂ g) xbar ∧ -u ∈ (∂ f) xbar) ↔
      -gradg ∈ (∂ f) xbar := by
  have hsub :
      (∂ g) xbar = ({gradg} : Set H) :=
    subdifferential_eq_singleton_of_forall_hasDirectionalDerivativeAt_local
      (hg := hg) (xbar := xbar) (gradg := gradg) hgrad
  constructor
  · rintro ⟨u, hu, hneg⟩
    have hu_eq : u = gradg := by
      simpa [hsub] using hu
    simpa [hu_eq] using hneg
  · intro hneg
    refine ⟨gradg, ?_, hneg⟩
    simp [hsub]

omit [CompleteSpace H] in
/-- The gradient inequality reformulation used in Corollary 27.3: if every directional derivative
of `g` at `xbar` is represented by the gradient `gradg`, then the existential affine-minorant
condition is equivalent to the concrete inequality with `gradg`. This is the identity-map
specialization of the Chapter 27 owner theorem with the same mathematical content. -/
theorem exists_subgradient_inequality_iff_gradient_inequality_of_identity
    {f g : H → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(H)) {xbar gradg : H}
    (hgrad :
      ∀ y : H,
        HasDirectionalDerivativeAt g xbar y
          ((((InnerProductSpace.toDualMap ℝ H gradg) y : ℝ) : EReal))) :
    (∃ u : H, u ∈ (∂ g) xbar ∧
        ∀ y : H, (⟪xbar - y, u⟫_ℝ : EReal) + (f xbar : EReal) ≤ (f y : EReal)) ↔
      ∀ y : H,
        (⟪xbar - y, gradg⟫_ℝ : EReal) + (f xbar : EReal) ≤ (f y : EReal) := by
  have hsub :
      (∂ g) xbar = ({gradg} : Set H) :=
    subdifferential_eq_singleton_of_forall_hasDirectionalDerivativeAt_local
      (hg := hg) (xbar := xbar) (gradg := gradg) hgrad
  constructor
  · rintro ⟨u, hu, hineq⟩
    have hu_eq : u = gradg := by
      simpa [hsub] using hu
    simpa [hu_eq] using hineq
  · intro hineq
    refine ⟨gradg, ?_, hineq⟩
    simp [hsub]

/-- The forward-backward fixed-point identity used in Corollary 27.3:
`-gradg ∈ ∂ f(xbar)` is equivalent to `xbar = Prox_{γ f}(xbar - γ gradg)`. -/
theorem neg_gradient_mem_subdifferential_iff_eq_scaledProx
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (γ : PosReal) {xbar gradg : H} :
    -gradg ∈ (∂ f) xbar ↔
      xbar = Prox[γ, f, hf] (xbar - (γ : ℝ) • gradg) := by
  constructor
  · intro hsub
    -- Read the proximal fixed-point identity through the scaled subdifferential criterion.
    apply (eq_proximityOperator_iff_sub_mem_subdifferential
      (f := (γ • f : H → Set.Ioi (⊥ : EReal)))
      (hf := smul_mem_gammaZero f hf γ)
      (x := xbar - (γ : ℝ) • gradg)
      (p := xbar)).2
    have hscaled :
        (γ : ℝ) • (-gradg) ∈
          (∂ ((γ • f : H → Set.Ioi (⊥ : EReal)))) xbar :=
      (smul_mem_subdifferential_posReal_smul_iff_local
        (f := f) (γ := γ) (x := xbar) (u := -gradg)).2 hsub
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hscaled
  · intro hprox
    have hscaled :
        (xbar - (γ : ℝ) • gradg) - xbar ∈
          (∂ (((γ : PosReal) • f : H → Set.Ioi (⊥ : EReal)))) xbar :=
      (eq_proximityOperator_iff_sub_mem_subdifferential
        (smul_mem_gammaZero f hf γ) (xbar - (γ : ℝ) • gradg) xbar).1 hprox
    have hbase :
        (γ : ℝ) • (-gradg) ∈
          (∂ (((γ : PosReal) • f : H → Set.Ioi (⊥ : EReal)))) xbar := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hscaled
    simpa using
      (smul_mem_subdifferential_posReal_smul_iff_local
        (f := f) (γ := γ) (x := xbar) (u := -gradg)).1 hbase
omit [CompleteSpace H] in
/-- The Fenchel--Young reformulation used in Corollary 27.3:
`-gradg ∈ ∂ f(xbar)` is equivalent to `f(xbar) + f^*(-gradg) + ⟪xbar, gradg⟫ = 0`. -/
theorem neg_gradient_mem_subdifferential_iff_fenchel_young_eq_zero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {xbar gradg : H} :
    -gradg ∈ (∂ f) xbar ↔
      (f xbar : EReal) + (f∗[hf] (-gradg) : EReal) +
          ((⟪xbar, gradg⟫_ℝ : ℝ) : EReal) = (0 : EReal) := by
  constructor
  · intro hsub
    have hfy :
        (f xbar : EReal) + (f∗[hf] (-gradg) : EReal) =
          ((⟪xbar, -gradg⟫_ℝ : ℝ) : EReal) :=
      (mem_subdifferential_iff_fenchel_young_eq
        (f := f) hf.2.nonempty xbar (-gradg)).1 hsub
    -- Rewrite the Fenchel--Young contact equality by moving the negative inner product left.
    calc
      (f xbar : EReal) + (f∗[hf] (-gradg) : EReal) +
          ((⟪xbar, gradg⟫_ℝ : ℝ) : EReal)
          = ((⟪xbar, -gradg⟫_ℝ : ℝ) : EReal) +
              ((⟪xbar, gradg⟫_ℝ : ℝ) : EReal) := by
                simpa using congrArg
                  (fun t : EReal ↦ t + ((⟪xbar, gradg⟫_ℝ : ℝ) : EReal)) hfy
      _ = 0 := by
            rw [inner_neg_right, EReal.coe_neg]
            rw [← EReal.coe_neg]
            rw [← EReal.coe_add]
            norm_num
  · intro hzero
    have hfy :
        (f xbar : EReal) + (f∗[hf] (-gradg) : EReal) =
          ((⟪xbar, -gradg⟫_ℝ : ℝ) : EReal) := by
      let a : EReal := (f xbar : EReal) + (f∗[hf] (-gradg) : EReal)
      let b : EReal := ((⟪xbar, gradg⟫_ℝ : ℝ) : EReal)
      have hab : a + b = 0 := by
        simpa [a, b] using hzero
      have hb_top : b ≠ ⊤ := EReal.coe_ne_top _
      have hb_bot : b ≠ ⊥ := EReal.coe_ne_bot _
      have ha_top : a ≠ ⊤ := by
        intro ha_top
        have htop : a + b = ⊤ := by
          rw [ha_top]
          exact EReal.top_add_of_ne_bot hb_bot
        exact EReal.zero_ne_top (hab.symm.trans htop)
      have ha_bot : a ≠ ⊥ := by
        intro ha_bot
        have hbot : a + b = ⊥ := by
          rw [ha_bot, EReal.bot_add]
        exact EReal.zero_ne_bot (hab.symm.trans hbot)
      have hEq : a = -b :=
        (ereal_eq_neg_iff_add_eq_zero_of_ne_top_ne_bot ha_top ha_bot hb_top hb_bot).2 hab
      simpa [a, b, inner_neg_right, EReal.coe_neg] using hEq
    exact
      (mem_subdifferential_iff_fenchel_young_eq
        (f := f) hf.2.nonempty xbar (-gradg)).2 hfy

end GeneralCharacterizationsOfMinimizers

end ERealFunction
