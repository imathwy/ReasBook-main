import Mathlib
import BauschkeLean.Chap01.Text_1_0_57
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap15.Definition_15_19
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap17.Proposition_17_41
import BauschkeLean.Chap19.Definition_19_11
import BauschkeLean.Chap19.Definition_19_16
import BauschkeLean.Chap19.Proposition_19_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Helper for Proposition 19 21: if an `EReal`-valued family is `⊤` away from one point, then
its `iInf` is the value at that point. -/
private theorem iInf_eq_of_forall_ne_top
    {ι : Type*} (φ : ι → EReal) (c : ι)
    (hφ : ∀ i, i ≠ c → φ i = ⊤) :
    (⨅ i, φ i) = φ c := by
  refine le_antisymm (iInf_le φ c) ?_
  refine le_iInf ?_
  intro i
  by_cases hi : i = c
  · simp [hi]
  · rw [hφ i hi]
    exact le_top

/-- Helper for Proposition 19 21: the constraint equation `a = r - y` is equivalent to the
residual identity `y = r - a`. -/
private theorem constraint_eq_iff_residual_eq
    {K : Type*} [AddCommGroup K] {a r y : K} :
    a = r - y ↔ y = r - a := by
  constructor
  · intro h
    rw [eq_sub_iff_add_eq]
    rw [eq_sub_iff_add_eq] at h
    simpa [add_comm] using h
  · intro h
    rw [eq_sub_iff_add_eq]
    rw [eq_sub_iff_add_eq] at h
    simpa [add_comm] using h

/-- Helper for Proposition 19 21: outside the effective domain, the function value is `⊤`. -/
private theorem value_eq_top_of_not_mem_effectiveDomain
    {H : Type*} (f : H → Set.Ioi (⊥ : EReal)) {x : H}
    (hx : x ∉ effectiveDomain f) :
    (f x : EReal) = ⊤ := by
  -- The effective domain is exactly the set where the value is strictly below `⊤`.
  exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))

/- Source/core/bridge triage:
- `source-facing`: Proposition 19.21 specializes the composite perturbation formalism to the
  equality constraint `L x = r`.
- `core/canonical`: the owner abstraction is `compositePerturbationFunction` together with
  `perturbationPrimalObjective`, `perturbationDualObjective`, and `lagrangian`.
- `bridge/view`: this file should therefore keep only the singleton-indicator specialization
  `equalityConstraintPerturbation` and the source-facing rewrites of the canonical owners, while
  avoiding extra public helper wrappers that merely restate upstream owners.
-/

section Basic

variable {H : Type u} {K : Type v}
variable [SeminormedAddCommGroup H] [NormedSpace ℝ H]
variable [SeminormedAddCommGroup K] [NormedSpace ℝ K]

/-- The perturbation function attached to the equality constraint `L x = r`, expressed as the
singleton-indicator specialization of the canonical composite perturbation owner. -/
abbrev equalityConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (r : K) :
    H × K → Set.Ioi (⊥ : EReal) :=
  compositePerturbationFunction f (ι[{r}]) L

-- Proof sketch: specialize `compositePerturbationFunction` to the singleton indicator
-- with `g = ι_{ {r} }`; the singleton indicator is `0` exactly when `L x + y = r`,
-- equivalently `L x = r - y`, and is `⊤` otherwise.
/-- Evaluating the equality-constraint perturbation function gives the piecewise formula from
Proposition 19.21. -/
@[simp] theorem equalityConstraintPerturbation_apply
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (r : K) (x : H) (y : K) :
    (equalityConstraintPerturbation f L r (x, y) : EReal) =
      if L x = r - y then (f x : EReal) else ⊤ := by
  rw [equalityConstraintPerturbation, compositePerturbationFunction_apply]
  by_cases h : L x = r - y
  · have hxy : L x + y = r := by
      exact (eq_sub_iff_add_eq).1 h
    rw [if_pos h]
    simp [indicator_apply, hxy]
  · have hxy : L x + y ≠ r := by
      intro hxy
      exact h ((eq_sub_iff_add_eq).2 hxy)
    rw [if_neg h]
    simp [indicator_apply, hxy, EReal.add_top_of_ne_bot (ne_of_gt (f x).2)]

-- Proof sketch: evaluate `perturbationPrimalObjective` at the zero perturbation and simplify the
-- singleton indicator term at `L x`, which vanishes exactly when `L x = r`.
/-- Proposition 19.21 (2): the primal problem attached to the equality-constraint perturbation is
the constrained minimization of `f` over `L ⁻¹' {r}`. -/
theorem perturbationPrimalObjective_equalityConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (r : K) :
    perturbationPrimalObjective (equalityConstraintPerturbation f L r) =
      fun x : H ↦ if L x = r then (f x : EReal) else ⊤ := by
  funext x
  simpa using equalityConstraintPerturbation_apply f L r x 0

end Basic

section InnerProduct

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

-- Proof sketch: specialize Proposition 19.20 (4) to the singleton-indicator composite
-- perturbation and simplify the
-- conjugate term to `⟪v, r⟫`, so the Lagrangian becomes `f x + ⟪L x - r, v⟫` on `dom f`.
/-- Proposition 19.21 (4): the Lagrangian is the piecewise map
`(x, v) ↦ f x + ⟪L x - r, v⟫` on the effective domain of `f`, and `+∞` outside it. -/
theorem lagrangian_equalityConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (r : K) (x : H) (v : K) :
    ℒ[equalityConstraintPerturbation f L r] x v =
      if _hx : x ∈ effectiveDomain f then
        (f x : EReal) + (⟪L x - r, v⟫_ℝ : EReal)
      else
        ⊤ := by
  rw [lagrangian_apply]
  by_cases hx : x ∈ effectiveDomain f
  · let y0 : K := r - L x
    let φ : K → EReal := fun y ↦
      (equalityConstraintPerturbation f L r (x, y) : EReal) - (⟪y, v⟫_ℝ : EReal)
    have hconstraint (y : K) : L x = r - y ↔ y = y0 := by
      simpa [y0] using (constraint_eq_iff_residual_eq (a := L x) (r := r) (y := y))
    have hφ_ne (y : K) (hy : y ≠ y0) : φ y = ⊤ := by
      have hneq : L x ≠ r - y := by
        intro hxy
        exact hy ((hconstraint y).mp hxy)
      have hxy : L x + y ≠ r := by
        intro hxy
        exact hneq ((eq_sub_iff_add_eq).2 hxy)
      simp [φ, equalityConstraintPerturbation, Function.comp, indicator_apply, hxy,
        EReal.add_top_of_ne_bot (ne_of_gt (f x).2)]
    have hφ_y0 : φ y0 = (f x : EReal) + (⟪L x - r, v⟫_ℝ : EReal) := by
      have hy0 : L x = r - y0 := (hconstraint y0).2 rfl
      have hxy0 : L x + y0 = r := by
        simp [y0]
      have hinner :
          (-⟪r - L x, v⟫_ℝ : EReal) = (⟪L x - r, v⟫_ℝ : EReal) := by
        have hinner_real : -⟪r - L x, v⟫_ℝ = ⟪L x - r, v⟫_ℝ := by
          calc
            -⟪r - L x, v⟫_ℝ = -(⟪r, v⟫_ℝ - ⟪L x, v⟫_ℝ) := by
              simp [inner_sub_left]
            _ = -⟪r, v⟫_ℝ + ⟪L x, v⟫_ℝ := by
              ring
            _ = ⟪L x, v⟫_ℝ - ⟪r, v⟫_ℝ := by
              ring
            _ = ⟪L x - r, v⟫_ℝ := by
              simp [inner_sub_left]
        exact_mod_cast hinner_real
      have hbase :
          φ y0 = (f x : EReal) + (-⟪r - L x, v⟫_ℝ : EReal) := by
        change
          (equalityConstraintPerturbation f L r (x, y0) : EReal) - (⟪y0, v⟫_ℝ : EReal) =
            (f x : EReal) + (-⟪r - L x, v⟫_ℝ : EReal)
        rw [equalityConstraintPerturbation_apply, if_pos hy0, sub_eq_add_neg]
      calc
        φ y0 = (f x : EReal) + (-⟪r - L x, v⟫_ℝ : EReal) := hbase
        _ = (f x : EReal) + (⟪L x - r, v⟫_ℝ : EReal) := by rw [hinner]
    have hrewrite :
        (⨅ y : K,
            (equalityConstraintPerturbation f L r (x, y) : EReal) - (⟪y, v⟫_ℝ : EReal)) =
          ⨅ y : K, φ y := by
      rfl
    have hiInf : (⨅ y : K, φ y) = φ y0 :=
      iInf_eq_of_forall_ne_top φ y0 hφ_ne
    rw [hrewrite]
    rw [hiInf]
    simpa [hx] using hφ_y0
  · have htop : (f x : EReal) = ⊤ := by
      exact value_eq_top_of_not_mem_effectiveDomain f hx
    have hfiber :
        (fun y : K ↦
          (equalityConstraintPerturbation f L r (x, y) : EReal) - (⟪y, v⟫_ℝ : EReal)) =
          fun _ : K ↦ (⊤ : EReal) := by
      funext y
      rw [equalityConstraintPerturbation_apply, htop]
      by_cases hxy : L x = r - y
      · simp [hxy]
      · simp [hxy]
    rw [hfiber]
    simp [hx]

-- Proof sketch: use the whole-space saddle-point owner `lagrangian_isSaddlePointOn_iff` together
-- with the branch formula above. The saddle-point supremum in the multiplier variable forces
-- feasibility `L x̄ = r`, unless `f` is identically `+∞`; then the primal infimum clause becomes
-- the `Argmin` statement for the constrained objective.
/-- If `(x̄, v̄)` is a saddle point of the Lagrangian attached to the equality-constraint
perturbation, then `x̄` solves the corresponding equality-constrained primal problem. -/
theorem
 mem_argmin_perturbationPrimalObjective_of_isSaddlePointOn_lagrangian_equalityConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) (r : K)
    {xbar : H} {vbar : K}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set K)
        (ℒ[equalityConstraintPerturbation f L r]) xbar vbar) :
    xbar ∈ Argmin (perturbationPrimalObjective (equalityConstraintPerturbation f L r)) := by
  let F := equalityConstraintPerturbation f L r
  let ψ : H → EReal := fun z ↦ ℒ[F] z vbar
  have hsaddleF :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set K) (ℒ[F]) xbar vbar := by
    simpa [F] using hsaddle
  have hψ : xbar ∈ Argmin ψ := by
    rw [mem_argmin_iff_eq_sInf]
    simpa [ψ] using
      (lagrangian_isSaddlePointOn_iff F xbar vbar).mp hsaddleF |>.2.symm
  have hψmin : ∀ z : H, ψ xbar ≤ ψ z := by
    rw [mem_argmin_iff, isMinOn_univ_iff] at hψ
    exact hψ
  have hlag (z : H) :
      ψ z =
        if hz : z ∈ effectiveDomain f then
          (f z : EReal) + (⟪L z - r, vbar⟫_ℝ : EReal)
        else
          ⊤ := by
    simpa [ψ, F] using lagrangian_equalityConstraintPerturbation f L r z vbar
  rw [mem_argmin_iff, isMinOn_univ_iff]
  intro x
  by_cases hxbar : xbar ∈ effectiveDomain f
  · have hrbar : L xbar = r := by
      have hsup :
          sSup (Set.range fun w : K ↦ ℒ[F] xbar w) = ℒ[F] xbar vbar :=
        (lagrangian_isSaddlePointOn_iff F xbar vbar).mp hsaddleF |>.1
      by_contra hneq
      let w : K := vbar + (L xbar - r)
      have hw_le : ℒ[F] xbar w ≤ ℒ[F] xbar vbar := by
        calc
          ℒ[F] xbar w ≤ sSup (Set.range fun u : K ↦ ℒ[F] xbar u) := by
            exact le_sSup ⟨w, rfl⟩
          _ = ℒ[F] xbar vbar := hsup
      have hf_ne_top : (f xbar : EReal) ≠ ⊤ :=
        ne_of_lt (mem_effectiveDomain_iff.mp hxbar)
      have hf_ne_bot : (f xbar : EReal) ≠ ⊥ :=
        ne_of_gt (f xbar).2
      let fxbar : ℝ := (f xbar : EReal).toReal
      have hfxbar : (f xbar : EReal) = (fxbar : EReal) := by
        simp [fxbar, EReal.coe_toReal, hf_ne_top, hf_ne_bot]
      rw [lagrangian_equalityConstraintPerturbation f L r xbar w,
        lagrangian_equalityConstraintPerturbation f L r xbar vbar] at hw_le
      rw [hfxbar] at hw_le
      have hinner_split :
          ⟪L xbar - r, vbar + (L xbar - r)⟫_ℝ =
            ⟪L xbar - r, vbar⟫_ℝ + ‖L xbar - r‖ ^ 2 := by
        simp [inner_add_right]
      have hw_le' :
          (((fxbar + (⟪L xbar - r, vbar⟫_ℝ + ‖L xbar - r‖ ^ 2) : ℝ) : EReal)) ≤
            (((fxbar + ⟪L xbar - r, vbar⟫_ℝ : ℝ) : EReal)) := by
        simpa [hxbar, w, hinner_split, EReal.coe_add, add_assoc] using hw_le
      have hreal :
          fxbar + (⟪L xbar - r, vbar⟫_ℝ + ‖L xbar - r‖ ^ 2) ≤
            fxbar + ⟪L xbar - r, vbar⟫_ℝ := by
        exact_mod_cast hw_le'
      have hpos : 0 < ‖L xbar - r‖ ^ 2 := by
        exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hneq))
      linarith
    by_cases hx : x ∈ effectiveDomain f
    · by_cases hxeq : L x = r
      · have hle : ψ xbar ≤ ψ x := hψmin x
        have hfx_le : (f xbar : EReal) ≤ (f x : EReal) := by
          rw [hlag xbar, hlag x] at hle
          simpa [hxbar, hrbar, hx, hxeq] using hle
        rw [perturbationPrimalObjective_equalityConstraintPerturbation]
        simpa [hxbar, hrbar, hx, hxeq] using hfx_le
      · rw [perturbationPrimalObjective_equalityConstraintPerturbation]
        simp [hrbar, hxeq]
    · rw [perturbationPrimalObjective_equalityConstraintPerturbation]
      have hfx_top : (f x : EReal) = ⊤ := by
        exact value_eq_top_of_not_mem_effectiveDomain f hx
      simp [hrbar, hfx_top]
  · have hψxbar_top : ψ xbar = ⊤ := by
      rw [hlag xbar]
      simp [hxbar]
    have hall_top : ∀ z : H, (f z : EReal) = ⊤ := by
      intro z
      by_cases hz : z ∈ effectiveDomain f
      · have hle : ℒ[F] xbar vbar ≤ ℒ[F] z vbar := hψmin z
        have hψz_top : ψ z = ⊤ := by
          have hle' : ψ xbar ≤ ψ z := hψmin z
          have hle_top : ⊤ ≤ ψ z := by
            simpa [hψxbar_top] using hle'
          exact le_antisymm le_top hle_top
        rw [hlag z] at hψz_top
        have hfz_ne_top : (f z : EReal) ≠ ⊤ :=
          ne_of_lt (mem_effectiveDomain_iff.mp hz)
        have hsum_ne_top :
            (f z : EReal) + (⟪L z - r, vbar⟫_ℝ : EReal) ≠ ⊤ :=
          EReal.add_ne_top hfz_ne_top (EReal.coe_ne_top _)
        have hsum_top :
            (f z : EReal) + (⟪L z - r, vbar⟫_ℝ : EReal) = ⊤ := by
          simpa [hz] using hψz_top
        have hfalse : False := hsum_ne_top hsum_top
        exact False.elim hfalse
      · exact value_eq_top_of_not_mem_effectiveDomain f hz
    have hobj_top : ∀ z : H, perturbationPrimalObjective F z = ⊤ := by
      intro z
      rw [perturbationPrimalObjective_equalityConstraintPerturbation]
      simp [hall_top z]
    rw [perturbationPrimalObjective_equalityConstraintPerturbation]
    simp [hall_top xbar, hall_top x]

-- Proof sketch: use the same saddle-point owner and branch formula, then shift the constant term
-- `⟪r, v̄⟫` from `f x + ⟪L x - r, v̄⟫` to `f x + ⟪L x, v̄⟫`.
-- The infimum clause is then exactly
-- the `Argmin` condition for the affine objective associated with the multiplier `v̄`.
/-- If `(x̄, v̄)` is a saddle point of the Lagrangian attached to the equality-constraint
perturbation, then `x̄` minimizes the affine objective `x ↦ f x + ⟪L x, v̄⟫`. -/
theorem mem_argmin_of_isSaddlePointOn_lagrangian_equalityConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) (r : K)
    {xbar : H} {vbar : K}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set K)
        (ℒ[equalityConstraintPerturbation f L r]) xbar vbar) :
    xbar ∈ Argmin (fun x : H ↦ (f x : EReal) + (⟪L x, vbar⟫_ℝ : EReal)) := by
  let F := equalityConstraintPerturbation f L r
  let ψ : H → EReal := fun z ↦ ℒ[F] z vbar
  let φ : H → EReal := fun z ↦ (f z : EReal) + (⟪L z, vbar⟫_ℝ : EReal)
  have hψ : xbar ∈ Argmin ψ := by
    rw [mem_argmin_iff_eq_sInf]
    simpa [ψ, F] using
      (lagrangian_isSaddlePointOn_iff F xbar vbar).mp hsaddle |>.2.symm
  have hshift (z : H) : (⟪r, vbar⟫_ℝ : EReal) + ℒ[F] z vbar = φ z := by
    by_cases hz : z ∈ effectiveDomain f
    · have hfz_ne_top : (f z : EReal) ≠ ⊤ :=
        ne_of_lt (mem_effectiveDomain_iff.mp hz)
      have hfz_ne_bot : (f z : EReal) ≠ ⊥ :=
        ne_of_gt (f z).2
      lift (f z : EReal) to ℝ using ⟨hfz_ne_top, hfz_ne_bot⟩ with fz
      have hpair :
          (⟪r, vbar⟫_ℝ : EReal) + (⟪L z - r, vbar⟫_ℝ : EReal) =
            (⟪L z, vbar⟫_ℝ : EReal) := by
        have hpair_real :
            ⟪r, vbar⟫_ℝ + ⟪L z - r, vbar⟫_ℝ = ⟪L z, vbar⟫_ℝ := by
          simp [inner_sub_left]
        exact_mod_cast hpair_real
      have hlag : ℒ[F] z vbar = (f z : EReal) + (⟪L z - r, vbar⟫_ℝ : EReal) := by
        simpa [F, hz] using lagrangian_equalityConstraintPerturbation f L r z vbar
      calc
        (⟪r, vbar⟫_ℝ : EReal) + ℒ[F] z vbar =
            (⟪r, vbar⟫_ℝ : EReal) + ((f z : EReal) + (⟪L z - r, vbar⟫_ℝ : EReal)) := by
              rw [hlag]
        _ = (f z : EReal) + ((⟪r, vbar⟫_ℝ : EReal) + (⟪L z - r, vbar⟫_ℝ : EReal)) := by
              simp only [add_left_comm]
        _ = (f z : EReal) + (⟪L z, vbar⟫_ℝ : EReal) := by
              rw [hpair]
        _ = φ z := by
              simp [φ]
    · have hfz_top : (f z : EReal) = ⊤ := by
        exact value_eq_top_of_not_mem_effectiveDomain f hz
      have hlag : ℒ[F] z vbar = ⊤ := by
        simpa [F, hz] using lagrangian_equalityConstraintPerturbation f L r z vbar
      calc
        (⟪r, vbar⟫_ℝ : EReal) + ℒ[F] z vbar = (⟪r, vbar⟫_ℝ : EReal) + ⊤ := by
          rw [hlag]
        _ = ⊤ := by
          simp
        _ = φ z := by
          simp [φ, hfz_top]
  rw [mem_argmin_iff, isMinOn_univ_iff] at hψ ⊢
  intro x
  have hle :
      (⟪r, vbar⟫_ℝ : EReal) + ψ xbar ≤ (⟪r, vbar⟫_ℝ : EReal) + ψ x :=
    by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_left (hψ x) (⟪r, vbar⟫_ℝ : EReal)
  have hshift_xbar : (⟪r, vbar⟫_ℝ : EReal) + ψ xbar = φ xbar := by
    simpa [ψ] using hshift xbar
  have hshift_x : (⟪r, vbar⟫_ℝ : EReal) + ψ x = φ x := by
    simpa [ψ] using hshift x
  rw [hshift_xbar, hshift_x] at hle
  simpa [φ] using hle

end InnerProduct

section ProductL2Ambient

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/-- Helper for Proposition 19 21: the singleton indicator belongs to `Γ₀(K)`. -/
private theorem singleton_indicator_mem_gammaZero
    (r : K) :
    (ι[{r}] : K → Set.Ioi (⊥ : EReal)) ∈ Γ₀(K) := by
  rw [mem_gammaZero_iff]
  constructor
  · simpa using
      (lowerSemicontinuous_indicator_compl_top_iff_isClosed ({r} : Set K)).2 isClosed_singleton
  · refine ⟨by simp, subset_rfl, ?_⟩
    intro x hx y hy a ha0 ha1
    have hx' : x = r := by simpa using hx
    have hy' : y = r := by simpa using hy
    subst x
    subst y
    have hcomb : a • r + (1 - a) • r = r := by
      rw [← add_smul]
      simp
    simp [indicator_apply, hcomb]

-- Proof sketch: specialize Proposition 19.20 (1) to the singleton indicator `ι_{ {r} }`.
-- The domain-intersection hypothesis becomes `r ∈ L '' effectiveDomain f` because the effective
-- domain of the singleton indicator is `{r}`.
/-- Proposition 19 21 (1): if `f ∈ Γ₀(ℋ)` and `r ∈ L (dom f)`, then the equality-constraint
perturbation function belongs to `Γ₀(ℋ ⊕ 𝒦)`. -/
theorem equalityConstraintPerturbation_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K) (r : K)
    (hr : r ∈ L '' effectiveDomain f) :
    equalityConstraintPerturbation f L r ∈ Γ₀(H × K) := by
  let _ := hr
  -- Route correction: return to the canonical composite-perturbation owner and specialize it to
  -- the singleton indicator, instead of rebuilding the shear-domain argument locally.
  simpa [equalityConstraintPerturbation] using
    compositePerturbationFunction_mem_gammaZero
      (f := f) (g := ι[{r}]) (L := L) hf (singleton_indicator_mem_gammaZero r)

end ProductL2Ambient

section CompleteDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
variable {f : H → Set.Ioi (⊥ : EReal)}
variable (L : H →L[ℝ] K) (r : K)

-- Proof sketch: specialize the dual formula from Proposition 19.20 to the singleton-indicator
-- composite perturbation and rewrite the
-- conjugate as `v ↦ ⟪v, r⟫`.
/-- Proposition 19.21 (3): the dual problem is
`v ↦ f^*(-L^* v) + ⟪v, r⟫`. -/
theorem perturbationDualObjective_equalityConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal)) :
    perturbationDualObjective (equalityConstraintPerturbation f L r) =
      fun v : K ↦
        f.asEReal∗ (-L.adjoint v) + (⟪v, r⟫_ℝ : EReal) := by
  funext v
  rw [equalityConstraintPerturbation, perturbationDualObjective_compositePerturbationFunction,
    compositeDualObjective_apply, conjugate_indicator_eq_supportFunction,
    supportFunction_eq_sSup_image]
  simp [real_inner_comm]

variable (hf : f ∈ Γ₀(H)) (hr : r ∈ L '' effectiveDomain f)
variable (hμ :
  ∃ μ : ℝ,
    sInf
        (Set.range
          (perturbationPrimalObjective (equalityConstraintPerturbation f L r))) = μ ∧
      sInf
          (Set.range
          (perturbationDualObjective (equalityConstraintPerturbation f L r))) = -μ)

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Proof sketch: specialize Proposition 19.20 (5) to the singleton-indicator composite
-- perturbation. Then rewrite the
-- second subdifferential condition using that the conjugate of the singleton indicator has
-- singleton subdifferential `{r}`.
section

omit [CompleteSpace K]

/-- Helper for Proposition 19 21: the packaged conjugate of the singleton indicator is the
linear functional `v ↦ ⟪v, r⟫`. -/
private theorem singleton_indicator_gammaZeroConjugate_apply
    (v : K) :
    (gammaZeroConjugate
      (ι[{r}] : K → Set.Ioi (⊥ : EReal))
      (singleton_indicator_mem_gammaZero r) v : EReal) =
      (⟪v, r⟫_ℝ : EReal) := by
  rw [gammaZeroConjugate_apply, conjugate_indicator_eq_supportFunction,
    supportFunction_eq_sSup_image]
  simp [real_inner_comm]

/-- Helper for Proposition 19 21: the subdifferential of the singleton-indicator conjugate is the
singleton `{r}` at every base point. -/
private theorem mem_subdifferential_singleton_indicator_gammaZeroConjugate_iff
    (u v : K) :
    u ∈ (∂ (gammaZeroConjugate
      (ι[{r}] : K → Set.Ioi (⊥ : EReal))
      (singleton_indicator_mem_gammaZero r))) v ↔
      u = r := by
  let g : K → Set.Ioi (⊥ : EReal) :=
    gammaZeroConjugate
      (ι[{r}] : K → Set.Ioi (⊥ : EReal))
      (singleton_indicator_mem_gammaZero r)
  constructor
  · intro hu
    change u ∈ (∂ g) v at hu
    rw [mem_subdifferential_iff] at hu
    let z : K := u - r
    have hz' :
        (⟪z, u⟫_ℝ : EReal) + (⟪v, r⟫_ℝ : EReal) ≤ (⟪v + z, r⟫_ℝ : EReal) := by
      have hzu := hu (v + z)
      have hg_vz : (g (v + z) : EReal) = (⟪v + z, r⟫_ℝ : EReal) := by
        simpa [g] using singleton_indicator_gammaZeroConjugate_apply (r := r) (v := v + z)
      have hg_v : (g v : EReal) = (⟪v, r⟫_ℝ : EReal) := by
        simpa [g] using singleton_indicator_gammaZeroConjugate_apply (r := r) (v := v)
      have hzu' :
          (⟪v + z - v, u⟫_ℝ : EReal) + (⟪v, r⟫_ℝ : EReal) ≤
            (⟪v + z, r⟫_ℝ : EReal) := by
        rw [← hg_v, ← hg_vz]
        exact hzu
      simpa [z, sub_eq_add_neg, inner_add_left, add_assoc, add_left_comm, add_comm] using hzu'
    have hz_real : ⟪z, u⟫_ℝ ≤ ⟪z, r⟫_ℝ := by
      have hz'' :
          (⟪v, r⟫_ℝ : EReal) + (⟪z, u⟫_ℝ : EReal) ≤
            (⟪v, r⟫_ℝ : EReal) + (⟪z, r⟫_ℝ : EReal) := by
        simpa [inner_add_left, EReal.coe_add, add_assoc, add_left_comm, add_comm] using hz'
      have hz_real' : ⟪v, r⟫_ℝ + ⟪z, u⟫_ℝ ≤ ⟪v, r⟫_ℝ + ⟪z, r⟫_ℝ := by
        exact_mod_cast hz''
      linarith
    have hsq : ‖u - r‖ ^ 2 ≤ 0 := by
      have hz_real' : ⟪u - r, u⟫_ℝ ≤ ⟪u - r, r⟫_ℝ := by
        simpa [z] using hz_real
      have hinner :
          ‖u - r‖ ^ 2 = ⟪u - r, u⟫_ℝ - ⟪u - r, r⟫_ℝ := by
        rw [← real_inner_self_eq_norm_sq, inner_sub_right]
      linarith
    have hzero : ‖u - r‖ = 0 := by
      nlinarith [sq_nonneg ‖u - r‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  · intro hu
    subst u
    change r ∈ (∂ g) v
    rw [mem_subdifferential_iff]
    intro w
    have hg_w : (g w : EReal) = (⟪w, r⟫_ℝ : EReal) := by
      simpa [g] using singleton_indicator_gammaZeroConjugate_apply (r := r) (v := w)
    have hg_v : (g v : EReal) = (⟪v, r⟫_ℝ : EReal) := by
      simpa [g] using singleton_indicator_gammaZeroConjugate_apply (r := r) (v := v)
    have hsum : ⟪w - v, r⟫_ℝ + ⟪v, r⟫_ℝ = ⟪w, r⟫_ℝ := by
      calc
        ⟪w - v, r⟫_ℝ + ⟪v, r⟫_ℝ =
            (⟪w, r⟫_ℝ - ⟪v, r⟫_ℝ) + ⟪v, r⟫_ℝ := by
          simp [inner_sub_left]
        _ = ⟪w, r⟫_ℝ := by
          ring
    have hw' :
        (⟪w - v, r⟫_ℝ : EReal) + (⟪v, r⟫_ℝ : EReal) ≤ (⟪w, r⟫_ℝ : EReal) :=
      le_of_eq (by exact_mod_cast hsum)
    calc
      (⟪w - v, r⟫_ℝ : EReal) + (g v : EReal) =
          (⟪w - v, r⟫_ℝ : EReal) + (⟪v, r⟫_ℝ : EReal) := by
            rw [hg_v]
      _ ≤ (⟪w, r⟫_ℝ : EReal) := hw'
      _ = (g w : EReal) := by
            rw [hg_w]

end

include hf hr hμ

/-- Proposition 19.21 (5): under strong duality, `(x, v)` is a saddle point of the Lagrangian if
and only if it satisfies the corresponding saddle-point optimality system. -/
theorem isSaddlePointOn_lagrangian_equalityConstraintPerturbation_iff
    (x : H) (v : K) :
    IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set K)
        (ℒ[equalityConstraintPerturbation f L r]) x v ↔
      -L.adjoint v ∈ (∂ f) x ∧
        L x = r := by
  -- Route correction: keep the source-faithful composite-perturbation saddle-point criterion and
  -- only rewrite the singleton-indicator conjugate subdifferential to the equality constraint.
  let _ := hf
  let _ := hr
  let _ := hμ
  have hμ' :
      ∃ μ : ℝ,
        compositePrimalOptimalValue f (ι[{r}]) L = μ ∧
          compositeDualOptimalValue f (ι[{r}]) L = -μ := by
    rcases hμ with ⟨μ, hprimal, hdual⟩
    refine ⟨μ, ?_, ?_⟩
    · simpa [equalityConstraintPerturbation, compositePrimalOptimalValue_def] using hprimal
    · rw [compositeDualOptimalValue_def]
      simpa [equalityConstraintPerturbation,
        perturbationDualObjective_compositePerturbationFunction]
        using hdual
  have hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set K)
        (ℒ[compositePerturbationFunction f (ι[{r}]) L]) x v ↔
      -L.adjoint v ∈ (∂ f) x ∧
        L x ∈ (∂ (gammaZeroConjugate
          (ι[{r}] : K → Set.Ioi (⊥ : EReal))
          (singleton_indicator_mem_gammaZero r))) v := by
    simpa using
      isSaddlePointOn_lagrangian_compositePerturbationFunction_iff
        (f := f) (g := ι[{r}]) (L := L) hf (singleton_indicator_mem_gammaZero r) hμ' x v
  rw [show compositePerturbationFunction f (ι[{r}]) L =
      equalityConstraintPerturbation f L r by rfl] at hsaddle
  constructor
  · intro hs
    have hs' := hsaddle.mp hs
    refine ⟨hs'.1, ?_⟩
    exact (mem_subdifferential_singleton_indicator_gammaZeroConjugate_iff
      (r := r) (u := L x) (v := v)).mp hs'.2
  · rintro ⟨hsub, hfeas⟩
    apply hsaddle.mpr
    refine ⟨hsub, ?_⟩
    exact (mem_subdifferential_singleton_indicator_gammaZeroConjugate_iff
      (r := r) (u := L x) (v := v)).mpr hfeas

-- Proof sketch: Proposition 19.21 (5) turns a saddle point into primal optimality for the
-- equality-constrained problem, and the feasibility branch reduces the primal objective to `f x`.
/-- Proposition 19.21 (6): at a saddle point, `f x` equals the optimal primal value of the
equality-constrained problem. -/
theorem
    value_eq_perturbationPrimalObjective_sInf_of_isSaddlePointOn_equalityConstraintPerturbation
    {x : H} {v : K}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set K)
        (ℒ[equalityConstraintPerturbation f L r]) x v) :
    (f x : EReal) =
      sInf
        (Set.range (perturbationPrimalObjective (equalityConstraintPerturbation f L r))) := by
  have hargmin :
      x ∈ Argmin (perturbationPrimalObjective (equalityConstraintPerturbation f L r)) :=
 mem_argmin_perturbationPrimalObjective_of_isSaddlePointOn_lagrangian_equalityConstraintPerturbation
      f L r hsaddle
  have hsub_feas :
      -L.adjoint v ∈ (∂ f) x ∧ L x = r :=
    (isSaddlePointOn_lagrangian_equalityConstraintPerturbation_iff
      (f := f) (L := L) (r := r) hf hr hμ x v).mp hsaddle
  have hx : x ∈ effectiveDomain f :=
    effectiveDomain_of_mem_subdifferential hf hsub_feas.1
  rw [mem_argmin_iff_eq_sInf] at hargmin
  simpa [perturbationPrimalObjective_equalityConstraintPerturbation, hsub_feas.2, hx] using hargmin

-- Proof sketch: the saddle-point infimum clause identifies the fixed-`v` Lagrangian fiber value at
-- `x`, and Proposition 19.21 (5) gives both feasibility `L x = r` and effective-domain
-- membership of `x` through the subgradient clause.
/-- Proposition 19.21 (7): at a saddle point, `f x` also equals the infimum of the Lagrangian
fiber `z ↦ 𝓛(z, v)`. -/
theorem
    value_eq_lagrangian_sInf_of_isSaddlePointOn_equalityConstraintPerturbation
    {x : H} {v : K}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set K)
        (ℒ[equalityConstraintPerturbation f L r]) x v) :
    (f x : EReal) =
      sInf (Set.range fun z : H ↦ ℒ[equalityConstraintPerturbation f L r] z v) := by
  let F := equalityConstraintPerturbation f L r
  have hsub_feas :
      -L.adjoint v ∈ (∂ f) x ∧ L x = r :=
    (isSaddlePointOn_lagrangian_equalityConstraintPerturbation_iff
      (f := f) (L := L) (r := r) hf hr hμ x v).mp hsaddle
  have hx : x ∈ effectiveDomain f :=
    effectiveDomain_of_mem_subdifferential hf hsub_feas.1
  have hsInf :
      sInf (Set.range fun z : H ↦ ℒ[F] z v) = ℒ[F] x v :=
    (lagrangian_isSaddlePointOn_iff F x v).mp (by simpa [F] using hsaddle) |>.2
  have hlag : ℒ[F] x v = (f x : EReal) := by
    simpa [F, hx, hsub_feas.2] using lagrangian_equalityConstraintPerturbation f L r x v
  calc
    (f x : EReal) = ℒ[F] x v := hlag.symm
    _ = sInf (Set.range fun z : H ↦ ℒ[F] z v) := hsInf.symm

end CompleteDuality

end

end ERealFunction
