import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap16.Proposition_16_10
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_44
import BauschkeLean.Chap17.Definition_17_1
import BauschkeLean.Chap17.Proposition_17_2
import BauschkeLean.Chap17.Proposition_17_14
import BauschkeLean.Chap19.Theorem_19_1
import BauschkeLean.Chap27.Proposition_27_5

open InnerProductSpace
open ContinuousLinearMap
open scoped InnerProductSpace Pointwise

noncomputable section

universe u v

namespace ERealFunction

section GeneralCharacterizationsOfMinimizers

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Semantic recall: `lean_leansearch` only surfaced generic calculus lemmas here; the verified
-- project-facing owners used below are `compositePrimalObjective`,
-- `CompositePrimalObjectiveRegularity`, `adjointImageSubdifferential`, `∂`, and `Prox[γ, f, hf]`.

/-- Theorem 27.2 (1): under any of the textbook regularity hypotheses, `xbar` solves
`min_x f x + g (L x)` if and only if `xbar` lies in the zero set of
`∂ f + L^* ∘ (∂ g) ∘ L`, realized as `(∂ f) + adjointImageSubdifferential L g`. -/
theorem mem_argmin_compositePrimalObjective_iff_mem_zeros_subdifferential_sum_of_regular
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) {xbar : H}
    (hregular : CompositePrimalObjectiveRegularity f g L) :
    xbar ∈ Argmin (compositePrimalObjective f g L) ↔
      xbar ∈ ((∂ f) + ContinuousLinearMap.adjointImageSubdifferential L g).zeros := by
  -- Reuse the Chapter 27 owner theorem and specialize the resulting set equality at `xbar`.
  rw [argmin_compositePrimalObjective_eq_zeros_subdifferential_sum_of_regular hf hg L hregular]

/-- Helper for Theorem 27.2: membership of `xbar` in the zero set of
`∂ f + L^* ∘ (∂ g) ∘ L` is equivalent to the existence of a subgradient
`v ∈ ∂ g (L xbar)` such that `-L^* v ∈ ∂ f (xbar)`. -/
theorem mem_zeros_subdifferential_sum_iff_exists_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} {g : K → Set.Ioi (⊥ : EReal)}
    (L : H →L[ℝ] K) {xbar : H} :
    xbar ∈ ((∂ f) + ContinuousLinearMap.adjointImageSubdifferential L g).zeros ↔
      ∃ v : K, v ∈ (∂ g) (L xbar) ∧ -L.adjoint v ∈ (∂ f) xbar := by
  -- Unpack the zero-set membership into a Minkowski-sum decomposition and read the second summand
  -- through the adjoint-image owner.
  rw [SetValuedOperator.mem_zeros_iff]
  change 0 ∈ (∂ f) xbar + ContinuousLinearMap.adjointImageSubdifferential L g xbar ↔
    ∃ v : K, v ∈ (∂ g) (L xbar) ∧ -L.adjoint v ∈ (∂ f) xbar
  rw [Set.mem_add, ContinuousLinearMap.adjointImageSubdifferential_apply]
  constructor
  · rintro ⟨u, hu, w, hw, huw⟩
    rcases hw with ⟨v, hv, rfl⟩
    refine ⟨v, hv, ?_⟩
    have hu_eq : u = -L.adjoint v := by
      simpa using eq_neg_of_add_eq_zero_left huw
    simpa [hu_eq] using hu
  · rintro ⟨v, hv, hu⟩
    refine ⟨-L.adjoint v, hu, L.adjoint v, ?_, by simp⟩
    exact ⟨v, hv, rfl⟩

/-- Helper for Theorem 27.2: moving the minus sign from `-L^* v` onto the displacement turns the
subgradient pairing `⟪y - xbar, -L^* v⟫` into `⟪xbar - y, L^* v⟫`. -/
theorem neg_adjoint_sub_eq_inner_sub
    (L : H →L[ℝ] K) (xbar y : H) (v : K) :
    (⟪y - xbar, -L.adjoint v⟫_ℝ : EReal) = (⟪xbar - y, L.adjoint v⟫_ℝ : EReal) := by
  have hreal :
      ⟪y - xbar, -L.adjoint v⟫_ℝ = ⟪xbar - y, L.adjoint v⟫_ℝ := by
    calc
      ⟪y - xbar, -L.adjoint v⟫_ℝ = -⟪y - xbar, L.adjoint v⟫_ℝ := by
        rw [inner_neg_right]
      _ = ⟪-(y - xbar), L.adjoint v⟫_ℝ := by
        rw [inner_neg_left]
      _ = ⟪xbar - y, L.adjoint v⟫_ℝ := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal

/-- Helper for Theorem 27.2: a witness `v ∈ ∂ g (L xbar)` with
`-L^* v ∈ ∂ f (xbar)` is equivalent to the corresponding global affine-minorant inequality for
`f`. -/
theorem exists_mem_subdifferential_iff_exists_subgradient_inequality
    {f : H → Set.Ioi (⊥ : EReal)} {g : K → Set.Ioi (⊥ : EReal)}
    (L : H →L[ℝ] K) {xbar : H} :
    (∃ v : K, v ∈ (∂ g) (L xbar) ∧ -L.adjoint v ∈ (∂ f) xbar) ↔
      ∃ v : K, v ∈ (∂ g) (L xbar) ∧
        ∀ y : H, (⟪xbar - y, L.adjoint v⟫_ℝ : EReal) + (f xbar : EReal) ≤ (f y : EReal) := by
  constructor
  · rintro ⟨v, hv, hu⟩
    refine ⟨v, hv, ?_⟩
    -- Rewrite the subgradient condition with the sign moved from the subgradient to `xbar - y`.
    rw [mem_subdifferential_iff] at hu
    intro y
    calc
      (⟪xbar - y, L.adjoint v⟫_ℝ : EReal) + (f xbar : EReal)
          = (⟪y - xbar, -L.adjoint v⟫_ℝ : EReal) + (f xbar : EReal) := by
              rw [neg_adjoint_sub_eq_inner_sub (L := L) (xbar := xbar) (y := y) (v := v)]
      _ ≤ (f y : EReal) := hu y
  · rintro ⟨v, hv, hineq⟩
    refine ⟨v, hv, ?_⟩
    -- The displayed affine-minorant inequality is exactly the defining condition for
    -- `-L.adjoint v ∈ ∂ f(xbar)` after the same sign normalization.
    rw [mem_subdifferential_iff]
    intro y
    calc
      (⟪y - xbar, -L.adjoint v⟫_ℝ : EReal) + (f xbar : EReal)
          = (⟪xbar - y, L.adjoint v⟫_ℝ : EReal) + (f xbar : EReal) := by
              rw [neg_adjoint_sub_eq_inner_sub (L := L) (xbar := xbar) (y := y) (v := v)]
      _ ≤ (f y : EReal) := hineq y

/-- Helper for Theorem 27.2: if every source directional derivative of `g` at `x` is given by the
linear functional represented by `gradg`, then the subdifferential of `g` at `x` is the singleton
`{gradg}`. -/
theorem subdifferential_eq_singleton_of_forall_hasDirectionalDerivativeAt
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K)) {x gradg : K}
    (hgrad :
      ∀ y : K,
        HasDirectionalDerivativeAt g x y
          ((((toDualMap ℝ K gradg) y : ℝ) : EReal))) :
    (∂ g) x = ({gradg} : Set K) := by
  -- Route correction: use the stronger source directional-derivative hypothesis directly instead
  -- of the problematic Proposition 17.31 API.
  have hconv : ConvexOn g (effectiveDomain g) := (mem_gammaZero_iff.mp hg).2
  have hx : x ∈ effectiveDomain g := (hgrad 0).1
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨?_, ?_⟩
  · -- The directional-derivative formula identifies `gradg` as a subgradient.
    rw [ERealFunction.mem_subdifferential_iff_inner_le_directionalDerivative
      (f := g) hconv hx]
    intro y
    rw [ERealFunction.directionalDerivative_eq_of_hasDirectionalDerivativeAt (f := g) hconv
      (hgrad y)]
    simpa [real_inner_comm]
  · intro u hu
    -- Any other subgradient has the same inner products against every direction, hence is equal
    -- to `gradg`.
    apply ext_inner_left ℝ
    intro y
    have hu_y :
        (⟪y, u⟫_ℝ : EReal) ≤ ((((toDualMap ℝ K gradg) y : ℝ) : EReal)) := by
      have hu_dir :=
        (ERealFunction.mem_subdifferential_iff_inner_le_directionalDerivative
          (f := g) hconv hx).1 hu y
      rw [ERealFunction.directionalDerivative_eq_of_hasDirectionalDerivativeAt (f := g) hconv
        (hgrad y)] at hu_dir
      exact hu_dir
    have hu_neg :
        (⟪-y, u⟫_ℝ : EReal) ≤ ((((toDualMap ℝ K gradg) (-y) : ℝ) : EReal)) := by
      have hu_dir :=
        (ERealFunction.mem_subdifferential_iff_inner_le_directionalDerivative
          (f := g) hconv hx).1 hu (-y)
      rw [ERealFunction.directionalDerivative_eq_of_hasDirectionalDerivativeAt (f := g) hconv
        (hgrad (-y))] at hu_dir
      exact hu_dir
    have hu_y_real : ⟪y, u⟫_ℝ ≤ ⟪y, gradg⟫_ℝ := by
      simpa [real_inner_comm] using EReal.coe_le_coe_iff.mp hu_y
    have hu_neg_real : ⟪y, gradg⟫_ℝ ≤ ⟪y, u⟫_ℝ := by
      simpa [real_inner_comm] using EReal.coe_le_coe_iff.mp hu_neg
    have hgrad_y_real : ⟪y, gradg⟫_ℝ ≤ ⟪y, u⟫_ℝ := by
      exact hu_neg_real
    exact le_antisymm hu_y_real hgrad_y_real

/-- Helper for Theorem 27.2: if `g ∈ Γ₀(K)` and `g` has Gâteaux gradient `gradg` at `L xbar`,
then the existential
subgradient condition from clause `(iii)` is equivalent to `-L^* gradg ∈ ∂ f (xbar)`. -/
theorem exists_mem_subdifferential_iff_neg_adjoint_gradient_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) {xbar : H} {gradg : K}
    (hgrad :
      ∀ y : K,
        HasDirectionalDerivativeAt g (L xbar) y
          ((((toDualMap ℝ K gradg) y : ℝ) : EReal))) :
    (∃ v : K, v ∈ (∂ g) (L xbar) ∧ -L.adjoint v ∈ (∂ f) xbar) ↔
      -L.adjoint gradg ∈ (∂ f) xbar := by
  have hsub :
      (∂ g) (L xbar) = ({gradg} : Set K) :=
    subdifferential_eq_singleton_of_forall_hasDirectionalDerivativeAt
      (hg := hg) (x := L xbar) (gradg := gradg) hgrad
  constructor
  · rintro ⟨v, hv, hu⟩
    have hv_eq : v = gradg := by
      simpa [hsub] using hv
    simpa [hv_eq] using hu
  · intro hu
    -- Once the subdifferential is a singleton, the existential witness must be `gradg`.
    refine ⟨gradg, ?_, hu⟩
    simpa [hsub]

/-- Helper for Theorem 27.2: if `g ∈ Γ₀(K)` and `g` has Gâteaux gradient `gradg` at `L xbar`,
then the affine-minorant
clause from `(iv)` is equivalent to the concrete inequality with `gradg`. -/
theorem exists_subgradient_inequality_iff_gradient_inequality
    {f : H → Set.Ioi (⊥ : EReal)} {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) {xbar : H} {gradg : K}
    (hgrad :
      ∀ y : K,
        HasDirectionalDerivativeAt g (L xbar) y
          ((((toDualMap ℝ K gradg) y : ℝ) : EReal))) :
    (∃ v : K, v ∈ (∂ g) (L xbar) ∧
        ∀ y : H, (⟪xbar - y, L.adjoint v⟫_ℝ : EReal) + (f xbar : EReal) ≤ (f y : EReal)) ↔
      ∀ y : H,
        (⟪xbar - y, L.adjoint gradg⟫_ℝ : EReal) + (f xbar : EReal) ≤ (f y : EReal) := by
  constructor
  · intro hexists
    have hsub :
        ∃ v : K, v ∈ (∂ g) (L xbar) ∧ -L.adjoint v ∈ (∂ f) xbar :=
      (exists_mem_subdifferential_iff_exists_subgradient_inequality
        (f := f) (g := g) (L := L) (xbar := xbar)).2 hexists
    have hgradSub :
        -L.adjoint gradg ∈ (∂ f) xbar :=
      (exists_mem_subdifferential_iff_neg_adjoint_gradient_mem_subdifferential
        (f := f) (g := g) hg L (xbar := xbar) (gradg := gradg) hgrad).1 hsub
    -- Return to the affine-minorant formulation with the concrete gradient witness.
    rw [mem_subdifferential_iff] at hgradSub
    intro y
    calc
      (⟪xbar - y, L.adjoint gradg⟫_ℝ : EReal) + (f xbar : EReal)
          = (⟪y - xbar, -L.adjoint gradg⟫_ℝ : EReal) + (f xbar : EReal) := by
              rw [neg_adjoint_sub_eq_inner_sub
                (L := L) (xbar := xbar) (y := y) (v := gradg)]
      _ ≤ (f y : EReal) := hgradSub y
  · intro hineq
    have hgradSub :
        -L.adjoint gradg ∈ (∂ f) xbar := by
      -- The concrete inequality is exactly the subgradient condition for `-L.adjoint gradg`.
      rw [mem_subdifferential_iff]
      intro y
      calc
        (⟪y - xbar, -L.adjoint gradg⟫_ℝ : EReal) + (f xbar : EReal)
            = (⟪xbar - y, L.adjoint gradg⟫_ℝ : EReal) + (f xbar : EReal) := by
                rw [neg_adjoint_sub_eq_inner_sub
                  (L := L) (xbar := xbar) (y := y) (v := gradg)]
        _ ≤ (f y : EReal) := hineq y
    have hsub :
        ∃ v : K, v ∈ (∂ g) (L xbar) ∧ -L.adjoint v ∈ (∂ f) xbar :=
      (exists_mem_subdifferential_iff_neg_adjoint_gradient_mem_subdifferential
        (f := f) (g := g) hg L (xbar := xbar) (gradg := gradg) hgrad).2 hgradSub
    exact
      (exists_mem_subdifferential_iff_exists_subgradient_inequality
        (f := f) (g := g) (L := L) (xbar := xbar)).1 hsub

/-- Helper for Theorem 27.2: scaling a subgradient by `γ ∈ ℝ_{++}` is equivalent to belonging to
the subdifferential of the scaled function `γ • f`. -/
theorem smul_mem_subdifferential_posReal_smul_iff
    {f : H → Set.Ioi (⊥ : EReal)} (γ : PosReal) {x u : H} :
    (γ : ℝ) • u ∈ (∂ ((γ • f : H → Set.Ioi (⊥ : EReal)))) x ↔ u ∈ (∂ f) x := by
  -- Rewrite the scaled subdifferential owner once, then cancel the positive scalar on the set
  -- side.
  rw [subdifferential_posReal_smul_eq_smul (f := f) (γ := γ)]
  change (γ : ℝ) • u ∈ (γ : ℝ) • ((∂ f) x) ↔ u ∈ (∂ f) x
  constructor
  · intro hu
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] at hu
    simpa [smul_smul, inv_mul_cancel₀ γ.2.ne'] using hu
  · intro hu
    exact Set.smul_mem_smul_set hu

/-- Helper for Theorem 27.2: for `f ∈ Γ₀(H)`, the explicit subgradient inclusion
`-L^* gradg ∈ ∂ f (xbar)` is equivalent to the scaled proximal-point fixed-point identity
`xbar = Prox_{γ f} (xbar - γ L^* gradg)` for every `γ ∈ ℝ_{++}`. -/
theorem neg_adjoint_gradient_mem_subdifferential_iff_eq_scaledProx
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {L : H →L[ℝ] K} {xbar : H} {gradg : K} :
    -L.adjoint gradg ∈ (∂ f) xbar ↔
      ∀ γ : PosReal, xbar = Prox[γ, f, hf] (xbar - (γ : ℝ) • L.adjoint gradg) := by
  constructor
  · intro hsub γ
    -- Read the scaled proximal fixed-point identity through Proposition 16.44 for `γ • f`.
    apply (eq_proximityOperator_iff_sub_mem_subdifferential
      (f := (γ • f : H → Set.Ioi (⊥ : EReal)))
      (hf := smul_mem_gammaZero f hf γ)
      (x := xbar - (γ : ℝ) • L.adjoint gradg)
      (p := xbar)).2
    have hscaled :
        (γ : ℝ) • (-L.adjoint gradg) ∈
          (∂ ((γ • f : H → Set.Ioi (⊥ : EReal)))) xbar :=
      (smul_mem_subdifferential_posReal_smul_iff
        (f := f) (γ := γ) (x := xbar) (u := -L.adjoint gradg)).2 hsub
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hscaled
  · intro hprox
    have hscaled :
        (xbar - (1 : ℝ) • L.adjoint gradg) - xbar ∈
          (∂ (((1 : PosReal) • f : H → Set.Ioi (⊥ : EReal)))) xbar :=
      (eq_proximityOperator_iff_sub_mem_subdifferential
        (f := (((1 : PosReal) • f : H → Set.Ioi (⊥ : EReal))))
        (hf := smul_mem_gammaZero f hf (1 : PosReal))
        (x := xbar - (1 : ℝ) • L.adjoint gradg)
        (p := xbar)).1 (hprox 1)
    have hbase :
        (1 : ℝ) • (-L.adjoint gradg) ∈
          (∂ (((1 : PosReal) • f : H → Set.Ioi (⊥ : EReal)))) xbar := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hscaled
    simpa using
      (smul_mem_subdifferential_posReal_smul_iff
        (f := f) (γ := (1 : PosReal)) (x := xbar) (u := -L.adjoint gradg)).1 hbase

/-- Helper for Theorem 27.2: for `f ∈ Γ₀(H)`, the explicit subgradient inclusion
`-L^* gradg ∈ ∂ f (xbar)` is equivalent to the Fenchel--Young equality
`f xbar + f^* (-L^* gradg) + ⟪L xbar, gradg⟫ = 0`. -/
theorem neg_adjoint_gradient_mem_subdifferential_iff_fenchel_young_eq_zero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {L : H →L[ℝ] K} {xbar : H} {gradg : K} :
    -L.adjoint gradg ∈ (∂ f) xbar ↔
      (f xbar : EReal) + (f∗[hf] (-L.adjoint gradg) : EReal) +
          ((⟪L xbar, gradg⟫_ℝ : ℝ) : EReal) = (0 : EReal) := by
  constructor
  · intro hsub
    have hfy :
        (f xbar : EReal) + (f∗[hf] (-L.adjoint gradg) : EReal) =
          ((⟪xbar, -L.adjoint gradg⟫_ℝ : ℝ) : EReal) :=
      (mem_subdifferential_iff_fenchel_young_eq
        (f := f) hf.2.nonempty xbar (-L.adjoint gradg)).1 hsub
    -- Rewrite the Fenchel--Young contact equality through the adjoint pairing and move the
    -- resulting negative inner-product term to the left.
    calc
      (f xbar : EReal) + (f∗[hf] (-L.adjoint gradg) : EReal) +
          ((⟪L xbar, gradg⟫_ℝ : ℝ) : EReal)
          = ((⟪xbar, -L.adjoint gradg⟫_ℝ : ℝ) : EReal) +
              ((⟪L xbar, gradg⟫_ℝ : ℝ) : EReal) := by
                simpa using congrArg
                  (fun t : EReal ↦ t + ((⟪L xbar, gradg⟫_ℝ : ℝ) : EReal)) hfy
      _ = 0 := by
            rw [inner_neg_right, ContinuousLinearMap.adjoint_inner_right, EReal.coe_neg]
            rw [← EReal.coe_neg]
            rw [← EReal.coe_add]
            norm_num
  · intro hzero
    have hfy :
        (f xbar : EReal) + (f∗[hf] (-L.adjoint gradg) : EReal) =
          ((⟪xbar, -L.adjoint gradg⟫_ℝ : ℝ) : EReal) := by
      let a : EReal := (f xbar : EReal) + (f∗[hf] (-L.adjoint gradg) : EReal)
      let b : EReal := ((⟪L xbar, gradg⟫_ℝ : ℝ) : EReal)
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
      simpa [a, b, inner_neg_right, ContinuousLinearMap.adjoint_inner_right, EReal.coe_neg] using
        hEq
    exact
      (mem_subdifferential_iff_fenchel_young_eq
        (f := f) hf.2.nonempty xbar (-L.adjoint gradg)).2 hfy

end GeneralCharacterizationsOfMinimizers

end ERealFunction
