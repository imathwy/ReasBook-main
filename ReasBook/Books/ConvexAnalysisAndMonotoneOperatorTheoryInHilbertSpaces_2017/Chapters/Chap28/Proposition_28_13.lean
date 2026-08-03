import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap01.Definition_1_8
import BauschkeLean.Chap10.Definition_10_27
import BauschkeLean.Chap11.Corollary_11_30
import BauschkeLean.Chap12.Proposition_12_27
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap24.Proposition_24_1
import BauschkeLean.Chap28.Corollary_28_9

open Filter SetValuedOperator
open scoped Gradient InnerProductSpace Pointwise SetValuedOperator Topology

universe u

namespace ERealFunction

noncomputable section

local notation "dom" => effectiveDomain

/- Source/core/bridge triage:
- `source-facing`: Proposition 28.13 is the variable-step forward-backward recursion `(28.37)` for
  the composite objective `f + g`.
- `core/canonical`: the reusable minimization surface is the extended-real objective
  `(f + g.toEReal).asEReal`, together with `Argmin`, `IsMinimizingSequence`, and weak
  convergence in `WeakSpace ℝ H`.
- `bridge/view`: the textbook real-valued smooth term `g` is kept together with an explicit
  gradient field `gradg`, while the nonsmooth term stays on the Chapter 12 proximal surface.

Semantic recall note: `lean_leansearch` returned only generic gradient/argmin hits here, so the
owner/API choice was fixed from the local Chapter 10/11/12/28 precedent. -/

section ForwardBackwardAlgorithm

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

namespace VariableStepRelaxedForwardBackwardProximalGradient

variable {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (gradg : H → H)
variable (γ : ℕ → PosReal) (relax : ℕ → ℝ) (x0 : H)

/-- The variable-step forward-backward operator at stage `n`,
`x ↦ Prox_{γ_n f}(x - γ_n gradg(x))`. -/
def step : ℕ → H → H :=
  fun n x ↦ Prox[γ n, f, hf] (x - (γ n : ℝ) • gradg x)

/-- The recursively generated `x`-sequence of the variable-step forward-backward recursion
`(28.37)`. -/
def orbit : ℕ → H :=
  relaxedOperatorIteration (step hf gradg γ) relax x0

/-- The forward sequence `y_n = x_n - γ_n gradg(x_n)` attached to `(28.37)`. -/
def y : ℕ → H :=
  fun n ↦ orbit hf gradg γ relax x0 n - (γ n : ℝ) • gradg (orbit hf gradg γ relax x0 n)

/-- The backward sequence `z_n = step_n(x_n) = Prox_{γ_n f}(y_n)` attached to `(28.37)`. -/
def z : ℕ → H :=
  fun n ↦ step hf gradg γ n (orbit hf gradg γ relax x0 n)

/-- The `x`-sequence of `(28.37)` is the Chapter 5 relaxed iteration of the operator family
`n ↦ Prox_{γ_n f} ∘ (Id - γ_n gradg)`. -/
theorem orbit_eq_relaxedOperatorIteration :
    orbit hf gradg γ relax x0 =
      relaxedOperatorIteration (step hf gradg γ) relax x0 := rfl

/-- The stage operator acts by the explicit proximal-gradient formula. -/
@[simp] theorem step_apply (n : ℕ) (x : H) :
    step hf gradg γ n x = Prox[γ n, f, hf] (x - (γ n : ℝ) • gradg x) := rfl

/-- The recursive orbit starts from the prescribed initial point `x0`. -/
@[simp] theorem orbit_zero :
    orbit hf gradg γ relax x0 0 = x0 := by
  simp [orbit]

/-- The companion forward sequence satisfies `y_n = x_n - γ_n gradg(x_n)`. -/
@[simp] theorem y_eq (n : ℕ) :
    y hf gradg γ relax x0 n =
      orbit hf gradg γ relax x0 n - (γ n : ℝ) • gradg (orbit hf gradg γ relax x0 n) := rfl

/-- The companion backward sequence satisfies `z_n = Prox_{γ_n f}(y_n)`. -/
@[simp] theorem z_eq (n : ℕ) :
    z hf gradg γ relax x0 n = Prox[γ n, f, hf] (y hf gradg γ relax x0 n) := rfl

/-- At each stage, applying the variable-step operator to the current iterate produces `z_n`. -/
@[simp] theorem step_apply_orbit (n : ℕ) :
    step hf gradg γ n (orbit hf gradg γ relax x0 n) =
      z hf gradg γ relax x0 n := rfl

/-- The recursive orbit satisfies the relaxed update
`x_{n+1} = x_n + λ_n (z_n - x_n)`. -/
@[simp] theorem orbit_succ (n : ℕ) :
    orbit hf gradg γ relax x0 (n + 1) =
      orbit hf gradg γ relax x0 n +
        relax n • (z hf gradg γ relax x0 n - orbit hf gradg γ relax x0 n) := by
  rw [orbit_eq_relaxedOperatorIteration, relaxedOperatorIteration_succ]
  simp [orbit, step, z]

/-- Any sequence starting at `x0` and satisfying the recursive `x`-update of `(28.37)` is the
canonical variable-step forward-backward orbit. -/
theorem eq_orbit_of_zero_of_succ {x : ℕ → H}
    (hx_zero : x 0 = x0)
    (hx_succ :
      ∀ n : ℕ,
        x (n + 1) = x n + relax n • (step hf gradg γ n (x n) - x n)) :
    x = orbit hf gradg γ relax x0 := by
  funext n
  induction n with
  | zero =>
      simpa using hx_zero
  | succ n ih =>
      rw [hx_succ n, orbit_succ, ih]
      simp

end VariableStepRelaxedForwardBackwardProximalGradient

open VariableStepRelaxedForwardBackwardProximalGradient

section Statements

/-- Helper for Proposition 28.13: every proximal point of a `Γ₀(H)` function has finite value. -/
theorem mem_effectiveDomain_of_isProxPoint_of_mem_gammaZero
    {g : H → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(H)) {x p : H} (hp : IsProxPoint g x p) :
    p ∈ effectiveDomain g := by
  rcases hg.2.nonempty with ⟨q, hq⟩
  have hpq := (isProxPoint_iff_forall_inner_add_le g hg.2 x p).mp hp q
  by_contra hp_dom
  have hgp_top : (g p : EReal) = ⊤ := by
    exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hp_dom))
  have hgq_top : (g q : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hq)
  have hleft_top : ((⟪q - p, x - p⟫_ℝ : EReal) + (g p : EReal)) = ⊤ := by
    rw [hgp_top]
    exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)
  rw [hleft_top] at hpq
  exact hgq_top (top_le_iff.mp hpq)

/-- Helper for Proposition 28.13: proximal points satisfy the finite variational inequality
against every finite comparison point. -/
theorem inner_add_toReal_le_toReal_of_isProxPoint_of_mem_gammaZero
    {g : H → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(H)) {x p y : H} (hp : IsProxPoint g x p)
    (hy : y ∈ effectiveDomain g) :
    ⟪y - p, x - p⟫_ℝ + (g p : EReal).toReal ≤ (g y : EReal).toReal := by
  have hp_dom : p ∈ effectiveDomain g :=
    mem_effectiveDomain_of_isProxPoint_of_mem_gammaZero hg hp
  have hgp_top : (g p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
  have hgp_bot : (g p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (g p : EReal) from (g p).2)
  have hgy_top : (g y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hgy_bot : (g y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (g y : EReal) from (g y).2)
  have hpq := (isProxPoint_iff_forall_inner_add_le g hg.2 x p).mp hp y
  have hcast :
      (((⟪y - p, x - p⟫_ℝ + (g p : EReal).toReal : ℝ) : EReal)) ≤
        (((g y : EReal).toReal : ℝ) : EReal) := by
    simpa [EReal.coe_toReal hgp_top hgp_bot, EReal.coe_toReal hgy_top hgy_bot, EReal.coe_add]
      using hpq
  exact_mod_cast hcast

/-- Helper for Proposition 28.13: on the whole space, firm nonexpansiveness is equivalent to the
Hilbert-space inequality `‖T x - T y‖² ≤ ⟪T x - T y, x - y⟫`. -/
theorem firmlyNonexpansive_iff_norm_sq_le_inner {T : H → H} :
    FirmlyNonexpansive T ↔
      ∀ x y : H, ‖T x - T y‖ ^ (2 : ℕ) ≤ inner ℝ (T x - T y) (x - y) := by
  constructor
  · intro h x y
    have hfirm : FirmlyNonexpansiveOn (Set.univ : Set H) T := h
    have hxy :
        ‖T x - T y‖ ^ (2 : ℕ) + ‖(x - T x) - (y - T y)‖ ^ (2 : ℕ) ≤ ‖x - y‖ ^ (2 : ℕ) := by
      simpa using (firmlyNonexpansiveOn_iff.mp hfirm) x (by simp) y (by simp)
    have hrewrite :
        ‖(x - T x) - (y - T y)‖ ^ (2 : ℕ) =
          ‖x - y‖ ^ (2 : ℕ) - 2 * inner ℝ (x - y) (T x - T y) + ‖T x - T y‖ ^ (2 : ℕ) := by
      have hsub : (x - T x) - (y - T y) = (x - y) - (T x - T y) := by
        abel_nf
      rw [hsub]
      simpa using norm_sub_sq_real (x - y) (T x - T y)
    rw [hrewrite] at hxy
    have hcomm : inner ℝ (x - y) (T x - T y) = inner ℝ (T x - T y) (x - y) := by
      rw [real_inner_comm]
    nlinarith [hxy, hcomm]
  · intro h
    change FirmlyNonexpansiveOn (Set.univ : Set H) T
    rw [firmlyNonexpansiveOn_iff]
    intro x _ y _
    have hxy := h x y
    have hrewrite :
        ‖(x - T x) - (y - T y)‖ ^ (2 : ℕ) =
          ‖x - y‖ ^ (2 : ℕ) - 2 * inner ℝ (x - y) (T x - T y) + ‖T x - T y‖ ^ (2 : ℕ) := by
      have hsub : (x - T x) - (y - T y) = (x - y) - (T x - T y) := by
        abel_nf
      rw [hsub]
      simpa using norm_sub_sq_real (x - y) (T x - T y)
    have hcomm : inner ℝ (x - y) (T x - T y) = inner ℝ (T x - T y) (x - y) := by
      rw [real_inner_comm]
    rw [hrewrite]
    nlinarith [hxy, hcomm]

/-- Helper for Proposition 28.13: proximal points at two base points satisfy the pairwise firm
inequality that characterizes firm nonexpansiveness. -/
theorem proxPointPairwiseFirmInequality
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x y p q : H}
    (hp : IsProxPoint f x p) (hq : IsProxPoint f y q) :
    ‖p - q‖ ^ (2 : ℕ) ≤ inner ℝ (p - q) (x - y) := by
  have hp_dom : p ∈ effectiveDomain f :=
    mem_effectiveDomain_of_isProxPoint_of_mem_gammaZero hf hp
  have hq_dom : q ∈ effectiveDomain f :=
    mem_effectiveDomain_of_isProxPoint_of_mem_gammaZero hf hq
  have hpq :
      ⟪q - p, x - p⟫_ℝ + (f p : EReal).toReal ≤ (f q : EReal).toReal :=
    inner_add_toReal_le_toReal_of_isProxPoint_of_mem_gammaZero hf hp hq_dom
  have hqp :
      ⟪p - q, y - q⟫_ℝ + (f q : EReal).toReal ≤ (f p : EReal).toReal :=
    inner_add_toReal_le_toReal_of_isProxPoint_of_mem_gammaZero hf hq hp_dom
  have hsum : ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ ≤ 0 := by
    linarith
  let d : H := p - q
  have hsub : y - q - (x - p) = d - (x - y) := by
    dsimp [d]
    abel_nf
  have hqpd : q - p = -d := by
    dsimp [d]
    abel_nf
  have hrewrite :
      ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ =
        ‖d‖ ^ (2 : ℕ) - inner ℝ d (x - y) := by
    calc
      ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ
          = inner ℝ (-d) (x - p) + inner ℝ d (y - q) := by rw [hqpd]
      _ = -inner ℝ d (x - p) + inner ℝ d (y - q) := by simp
      _ = inner ℝ d (y - q) - inner ℝ d (x - p) := by ring_nf
      _ = inner ℝ d ((y - q) - (x - p)) := by
            symm
            rw [inner_sub_right]
      _ = inner ℝ d (d - (x - y)) := by rw [hsub]
      _ = inner ℝ d d - inner ℝ d (x - y) := by rw [inner_sub_right]
      _ = ‖d‖ ^ (2 : ℕ) - inner ℝ d (x - y) := by rw [real_inner_self_eq_norm_sq]
  rw [hrewrite] at hsum
  have hfinal : ‖d‖ ^ (2 : ℕ) ≤ inner ℝ d (x - y) := by
    linarith
  simpa [d] using hfinal

/-- Helper for Proposition 28.13: the proximity operator `Prox_f` is firmly nonexpansive for
every `f ∈ Γ₀(H)`. -/
theorem proximityOperator_firmlyNonexpansive_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    FirmlyNonexpansive (Prox[f, hf]) := by
  rw [firmlyNonexpansive_iff_norm_sq_le_inner]
  intro x y
  have hp : IsProxPoint f x (Prox[f, hf] x) := by
    simpa using
      proximityOperator_isProxPoint f (hasUniqueProxPoint_of_mem_gammaZero (f := f) hf) x
  have hq : IsProxPoint f y (Prox[f, hf] y) := by
    simpa using
      proximityOperator_isProxPoint f (hasUniqueProxPoint_of_mem_gammaZero (f := f) hf) y
  simpa using proxPointPairwiseFirmInequality hf hp hq

/-- Helper for Proposition 28.13: the residual map `Id - Prox_f` is firmly nonexpansive for
every `f ∈ Γ₀(H)`. -/
theorem id_sub_proximityOperator_firmlyNonexpansive_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    FirmlyNonexpansive (fun z : H ↦ z - Prox[f, hf] z) := by
  rw [firmlyNonexpansive_iff_norm_sq_le_inner]
  intro x y
  have hprox :=
    (firmlyNonexpansive_iff_norm_sq_le_inner.mp
      (proximityOperator_firmlyNonexpansive_of_mem_gammaZero (f := f) hf)) x y
  let d : H := Prox[f, hf] x - Prox[f, hf] y
  let e : H := x - y
  have hsub :
      (x - Prox[f, hf] x) - (y - Prox[f, hf] y) = e - d := by
    dsimp [d, e]
    abel_nf
  have hrewrite :
      ‖e - d‖ ^ (2 : ℕ) =
        ‖e‖ ^ (2 : ℕ) - 2 * inner ℝ e d + ‖d‖ ^ (2 : ℕ) := by
    simpa using norm_sub_sq_real e d
  have hinner : inner ℝ (e - d) e = ‖e‖ ^ (2 : ℕ) - inner ℝ e d := by
    calc
      inner ℝ (e - d) e = inner ℝ e e - inner ℝ d e := by
        rw [inner_sub_left]
      _ = ‖e‖ ^ (2 : ℕ) - inner ℝ e d := by
        rw [real_inner_self_eq_norm_sq, real_inner_comm]
  rw [hsub, hrewrite, hinner]
  have hprox' : ‖d‖ ^ (2 : ℕ) ≤ inner ℝ e d := by
    simpa [d, e, real_inner_comm] using hprox
  nlinarith

/-- Helper for Proposition 28.13: `(γ : ℝ) • u ∈ ∂ (γ • f) x` iff `u ∈ ∂ f x` for
`γ ∈ ℝ_{++}`. -/
theorem smul_mem_subdifferential_posRealScale_iff
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

/-- Helper for Proposition 28.13: positive scaling preserves `effectiveDomain`. -/
theorem mem_effectiveDomain_posReal_smul_iff
    {f : H → Set.Ioi (⊥ : EReal)} (γ : PosReal) (x : H) :
    x ∈ effectiveDomain ((γ • f : H → Set.Ioi (⊥ : EReal))) ↔ x ∈ effectiveDomain f := by
  rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff, posReal_smul_apply, lt_top_iff_ne_top,
    lt_top_iff_ne_top]
  constructor
  · intro hmul htop
    have htop_mul :
        (((γ : ℝ) : EReal) * (⊤ : EReal)) = (⊤ : EReal) :=
      EReal.coe_mul_top_of_pos γ.2
    exact hmul (by simpa [htop] using htop_mul)
  · intro hf_top
    rw [EReal.mul_ne_top]
    exact
      ⟨Or.inl (EReal.coe_ne_bot (γ : ℝ)), Or.inl (EReal.coe_nonneg.mpr γ.2.le),
        Or.inl (EReal.coe_ne_top (γ : ℝ)), Or.inr hf_top⟩

/-- Helper for Proposition 28.13: `-gradg ∈ ∂ f(xbar)` is equivalent to the scaled proximal fixed
point identity `xbar = Prox_{γ f}(xbar - γ gradg)`. -/
theorem neg_gradient_mem_subdifferential_iff_eq_scaledProx_local
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (γ : PosReal) {xbar gradg : H} :
    -gradg ∈ (∂ f) xbar ↔
      xbar = Prox[γ, f, hf] (xbar - (γ : ℝ) • gradg) := by
  constructor
  · intro hsub
    apply (eq_proximityOperator_iff_sub_mem_subdifferential
      (f := (γ • f : H → Set.Ioi (⊥ : EReal)))
      (hf := smul_mem_gammaZero f hf γ)
      (x := xbar - (γ : ℝ) • gradg)
      (p := xbar)).2
    have hscaled :
        (γ : ℝ) • (-gradg) ∈
          (∂ ((γ • f : H → Set.Ioi (⊥ : EReal)))) xbar :=
      (smul_mem_subdifferential_posRealScale_iff (f := f) (γ := γ) (x := xbar)
        (u := -gradg)).2 hsub
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hscaled
  · intro hprox
    have hscaled :
        (xbar - (γ : ℝ) • gradg) - xbar ∈
          (∂ ((γ • f : H → Set.Ioi (⊥ : EReal)))) xbar :=
      (eq_proximityOperator_iff_sub_mem_subdifferential
        (f := ((γ : PosReal) • f : H → Set.Ioi (⊥ : EReal)))
        (hf := smul_mem_gammaZero f hf γ)
        (x := xbar - (γ : ℝ) • gradg)
        (p := xbar)).1 hprox
    have hbase :
        (γ : ℝ) • (-gradg) ∈
          (∂ ((γ • f : H → Set.Ioi (⊥ : EReal)))) xbar := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hscaled
    simpa using
      (smul_mem_subdifferential_posRealScale_iff (f := f) (γ := γ) (x := xbar)
        (u := -gradg)).1 hbase

/-- Helper for Proposition 28.13: every orbit iterate `x_n` and proximal point `z_n` stays in
`dom f`. -/
theorem orbit_mem_dom_and_z_mem_dom
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (gradg : H → H)
    (γ : ℕ → PosReal) {relax : ℕ → ℝ}
    (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (0 : ℝ) 1)
    (x0 : H) (hx0 : x0 ∈ dom f) :
    ∀ n : ℕ,
      orbit hf gradg γ relax x0 n ∈ effectiveDomain f ∧
        z hf gradg γ relax x0 n ∈ effectiveDomain f := by
  let hconvf : ConvexOn f (effectiveDomain f) := (mem_gammaZero_iff.mp hf).2
  intro n
  induction n with
  | zero =>
      constructor
      · simpa using hx0
      · -- The first proximal point is always finite for a `Γ₀(H)` function.
        simpa [z_eq, y_eq, orbit_zero] using
          scaledProximityOperator_mem_effectiveDomain_of_mem_gammaZero
            f hf (x0 - (γ 0 : ℝ) • gradg x0) (γ 0)
  | succ n ih =>
      rcases ih with ⟨hxn, hzn⟩
      constructor
      · -- Rewrite the relaxed update as a convex combination inside `dom f`.
        have hnext :
            orbit hf gradg γ relax x0 (n + 1) =
              (1 - relax n) • orbit hf gradg γ relax x0 n +
                relax n • z hf gradg γ relax x0 n := by
          rw [orbit_succ]
          calc
            orbit hf gradg γ relax x0 n +
                relax n • (z hf gradg γ relax x0 n - orbit hf gradg γ relax x0 n) =
                orbit hf gradg γ relax x0 n +
                  (relax n • z hf gradg γ relax x0 n -
                    relax n • orbit hf gradg γ relax x0 n) := by
                      rw [smul_sub]
            _ = (1 - relax n) • orbit hf gradg γ relax x0 n +
                relax n • z hf gradg γ relax x0 n := by
                  rw [sub_eq_add_neg, sub_smul, one_smul]
                  abel_nf
        rw [hnext]
        simpa [add_comm, add_left_comm, add_assoc] using
          hconvf.convex_effectiveDomain hxn hzn
            (sub_nonneg.mpr (hrelax_bounds n).2) (hrelax_bounds n).1 (by ring)
      · -- Once `x_(n+1)` is in `dom f`, the next proximal point is again finite.
        simpa [z_eq, y_eq] using
          scaledProximityOperator_mem_effectiveDomain_of_mem_gammaZero
            f hf
            (orbit hf gradg γ relax x0 (n + 1) -
              (γ (n + 1) : ℝ) • gradg (orbit hf gradg γ relax x0 (n + 1)))
            (γ (n + 1))

/-- Helper for Proposition 28.13: every minimizer of `(f + g)` is fixed by each stage operator. -/
theorem step_fixed_of_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (γ : ℕ → PosReal)
    {xstar : H} (hxstar : xstar ∈ Argmin ((f + g.toEReal).asEReal)) (n : ℕ) :
    step hf gradg γ n xstar = xstar := by
  -- Translate the minimizer into the Chapter 26 primal inclusion surface for `∂ f + ∇ g`.
  have hdiff : Differentiable ℝ g := fun x ↦ (hgrad x).differentiableAt
  have hgrad_eq : ∇ g = gradg := by
    apply gradient_eq
    intro x
    simpa using hgrad x
  have hconv : _root_.ConvexOn ℝ Set.univ g := by
    simpa [Function.effectiveDomain_toEReal] using hg.2.toReal_convexOn_effectiveDomain
  have hprimal :
      xstar ∈ primal_inclusion_solution_set (∂ f) ((∇ g).toSetValuedOperator) := by
    simpa [argmin_eq_primalForwardBackwardSolutionSet (hf := hf) (g := g) hconv hdiff] using
      hxstar
  rw [SetValuedOperator.mem_primal_inclusion_solution_set, Function.toSetValuedOperator_apply,
    Set.mem_add] at hprimal
  rcases hprimal with ⟨u, hu, v, hv, huv⟩
  have hv_eq : v = gradg xstar := by simpa [hgrad_eq] using hv
  have hu_eq : u = -gradg xstar := by
    rw [hv_eq] at huv
    simpa [eq_neg_iff_add_eq_zero] using huv
  have hsub : -gradg xstar ∈ (∂ f) xstar := by simpa [hu_eq] using hu
  have hprox :
      xstar = Prox[γ n, f, hf] (xstar - (γ n : ℝ) • gradg xstar) :=
    (neg_gradient_mem_subdifferential_iff_eq_scaledProx_local (hf := hf) (γ := γ n)).mp hsub
  -- Rewriting the stage operator finishes the fixed-point identity.
  simpa [step_apply] using hprox.symm

/-- Helper for Proposition 28.13: subtracting a point from an affine combination with weights
summing to `1` distributes across both terms. -/
theorem affineCombination_sub_eq_smul_sub
    (a b : ℝ) (hab : a + b = 1) (x y z : H) :
    a • x + b • y - z = a • (x - z) + b • (y - z) := by
  -- Expand `-z` as the affine combination `a • (-z) + b • (-z)` and then regroup terms.
  have hz :
      a • (-z) + b • (-z) = -z := by
    calc
      a • (-z) + b • (-z) = (a + b) • (-z) := by rw [← add_smul]
      _ = (1 : ℝ) • (-z) := by rw [hab]
      _ = -z := by simp
  calc
    a • x + b • y - z = a • x + b • y + -z := by
      rw [sub_eq_add_neg]
    _ = a • x + b • y + (a • (-z) + b • (-z)) := by
      simpa using congrArg (fun t : H ↦ a • x + b • y + t) hz.symm
    _ = (a • x + a • (-z)) + (b • y + b • (-z)) := by
      abel_nf
    _ = a • (x - z) + b • (y - z) := by
      rw [sub_eq_add_neg, sub_eq_add_neg, smul_add, smul_add]

/-- Helper for Proposition 28.13: each stage operator is nonexpansive relative to every minimizer
of `(f + g)`. -/
theorem step_dist_le_of_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (0 : ℝ) (2 * (β : ℝ)))
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    {xstar : H} (hxstar : xstar ∈ Argmin ((f + g.toEReal).asEReal)) (n : ℕ) (x : H) :
    ‖step hf gradg γ n x - xstar‖ ≤ ‖x - xstar‖ := by
  -- First package the smooth term as a cocoercive gradient on the whole space.
  have hdiff : Differentiable ℝ g := fun z ↦ (hgrad z).differentiableAt
  have hconv : _root_.ConvexOn ℝ Set.univ g := by
    simpa [Function.effectiveDomain_toEReal] using hg.2.toReal_convexOn_effectiveDomain
  let βInv : Set.Ioi (0 : ℝ) := ⟨(β : ℝ)⁻¹, by
    change 0 < (β : ℝ)⁻¹
    exact inv_pos.mpr β.2⟩
  have hgrad_eq : ∇ g = gradg := by
    apply gradient_eq
    intro z
    simpa using hgrad z
  have hCoco :
      CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun z : Set.univ ↦ gradg z) := by
    simpa [βInv, one_div, inv_inv, hgrad_eq] using
      gradient_lipschitz_imp_cocoercive_of_differentiable_convex
        g hdiff hconv βInv (by simpa [βInv, hgrad_eq] using hgrad_lipschitz)
  have hForward_nonexp : LipschitzWith 1 (fun z : H ↦ z - (γ n : ℝ) • gradg z) := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro a b
    have hco := hCoco.2 ⟨a, by simp⟩ ⟨b, by simp⟩
    have hsq :
        ‖(a - (γ n : ℝ) • gradg a) - (b - (γ n : ℝ) • gradg b)‖ ^ 2 ≤ ‖a - b‖ ^ 2 := by
      have hexpand :
          ‖(a - (γ n : ℝ) • gradg a) - (b - (γ n : ℝ) • gradg b)‖ ^ 2 =
            ‖a - b‖ ^ 2 - 2 * (γ n : ℝ) * ⟪a - b, gradg a - gradg b⟫_ℝ +
              ((γ n : ℝ) ^ 2) * ‖gradg a - gradg b‖ ^ 2 := by
        calc
          ‖(a - (γ n : ℝ) • gradg a) - (b - (γ n : ℝ) • gradg b)‖ ^ 2 =
              ‖(a - b) - (γ n : ℝ) • (gradg a - gradg b)‖ ^ 2 := by
                have hsub :
                    (a - (γ n : ℝ) • gradg a) - (b - (γ n : ℝ) • gradg b) =
                      (a - b) - (γ n : ℝ) • (gradg a - gradg b) := by
                  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
                rw [hsub]
          _ = ‖a - b‖ ^ 2 -
                2 * inner ℝ (a - b) ((γ n : ℝ) • (gradg a - gradg b)) +
                ‖(γ n : ℝ) • (gradg a - gradg b)‖ ^ 2 := by
                  simpa using norm_sub_sq_real (a - b) ((γ n : ℝ) • (gradg a - gradg b))
          _ = ‖a - b‖ ^ 2 - 2 * (γ n : ℝ) * ⟪a - b, gradg a - gradg b⟫_ℝ +
                ((γ n : ℝ) ^ 2) * ‖gradg a - gradg b‖ ^ 2 := by
                  rw [real_inner_smul_right, norm_smul, Real.norm_of_nonneg (hγ_bounds n).1,
                    pow_two]
                  ring
      rw [hexpand]
      have hco' :
          (β : ℝ) * ‖gradg a - gradg b‖ ^ 2 ≤ ⟪a - b, gradg a - gradg b⟫_ℝ := by
        simpa using hco
      have hbound :
          ‖a - b‖ ^ 2 - 2 * (γ n : ℝ) * ⟪a - b, gradg a - gradg b⟫_ℝ +
              ((γ n : ℝ) ^ 2) * ‖gradg a - gradg b‖ ^ 2 ≤
            ‖a - b‖ ^ 2 -
              (γ n : ℝ) * (2 * (β : ℝ) - (γ n : ℝ)) * ‖gradg a - gradg b‖ ^ 2 := by
        have hscale :
            (-2 * (γ n : ℝ)) * ⟪a - b, gradg a - gradg b⟫_ℝ ≤
              (-2 * (γ n : ℝ)) * ((β : ℝ) * ‖gradg a - gradg b‖ ^ 2) := by
          exact mul_le_mul_of_nonpos_left hco' (by nlinarith [(hγ_bounds n).1])
        nlinarith [hscale]
      have hnonneg :
          0 ≤ (γ n : ℝ) * (2 * (β : ℝ) - (γ n : ℝ)) * ‖gradg a - gradg b‖ ^ 2 := by
        have hsq_nonneg : 0 ≤ ‖gradg a - gradg b‖ ^ 2 := sq_nonneg _
        have hgap_nonneg : 0 ≤ 2 * (β : ℝ) - (γ n : ℝ) := by
          nlinarith [(hγ_bounds n).2]
        exact mul_nonneg (mul_nonneg (hγ_bounds n).1 hgap_nonneg) hsq_nonneg
      linarith
    have hnorm :
        ‖(a - (γ n : ℝ) • gradg a) - (b - (γ n : ℝ) • gradg b)‖ ≤ ‖a - b‖ := by
      have habs := sq_le_sq.mp hsq
      simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using habs
    simpa [dist_eq_norm, one_mul] using hnorm
  have hProx_firm :
      FirmlyNonexpansive (fun z : H ↦ Prox[γ n, f, hf] z) := by
    rw [firmlyNonexpansive_iff_norm_sq_le_inner]
    intro a b
    let p := Prox[γ n, f, hf] a
    let q := Prox[γ n, f, hf] b
    let hγf : (γ n) • f ∈ Γ₀(H) := smul_mem_gammaZero f hf (γ n)
    have hp : IsProxPoint (((γ n) • f : H → Set.Ioi (⊥ : EReal))) a p := by
      simpa [p, scaledProximityOperator] using
        proximityOperator_isProxPoint
          (((γ n) • f : H → Set.Ioi (⊥ : EReal)))
          (hasUniqueProxPoint_of_mem_gammaZero (((γ n) • f : H → Set.Ioi (⊥ : EReal))) hγf) a
    have hq : IsProxPoint (((γ n) • f : H → Set.Ioi (⊥ : EReal))) b q := by
      simpa [q, scaledProximityOperator] using
        proximityOperator_isProxPoint
          (((γ n) • f : H → Set.Ioi (⊥ : EReal)))
          (hasUniqueProxPoint_of_mem_gammaZero (((γ n) • f : H → Set.Ioi (⊥ : EReal))) hγf) b
    have hp_dom :
        p ∈ effectiveDomain (((γ n) • f : H → Set.Ioi (⊥ : EReal))) :=
      mem_effectiveDomain_of_isProxPoint_of_mem_gammaZero (g := (γ n) • f) hγf hp
    have hq_dom :
        q ∈ effectiveDomain (((γ n) • f : H → Set.Ioi (⊥ : EReal))) :=
      mem_effectiveDomain_of_isProxPoint_of_mem_gammaZero (g := (γ n) • f) hγf hq
    have hpq :
        ⟪q - p, a - p⟫_ℝ + ((((γ n) • f) p : EReal)).toReal ≤
          ((((γ n) • f) q : EReal)).toReal :=
      inner_add_toReal_le_toReal_of_isProxPoint_of_mem_gammaZero
        (g := (γ n) • f) hγf hp hq_dom
    have hqp :
        ⟪p - q, b - q⟫_ℝ + ((((γ n) • f) q : EReal)).toReal ≤
          ((((γ n) • f) p : EReal)).toReal :=
      inner_add_toReal_le_toReal_of_isProxPoint_of_mem_gammaZero
        (g := (γ n) • f) hγf hq hp_dom
    have hsum : ⟪q - p, a - p⟫_ℝ + ⟪p - q, b - q⟫_ℝ ≤ 0 := by
      linarith
    let d : H := p - q
    have hsub : b - q - (a - p) = d - (a - b) := by
      dsimp [d]
      abel_nf
    have hqpd : q - p = -d := by
      dsimp [d]
      abel_nf
    have hrewrite :
        ⟪q - p, a - p⟫_ℝ + ⟪p - q, b - q⟫_ℝ =
          ‖d‖ ^ (2 : ℕ) - inner ℝ d (a - b) := by
      calc
        ⟪q - p, a - p⟫_ℝ + ⟪p - q, b - q⟫_ℝ
            = inner ℝ (-d) (a - p) + inner ℝ d (b - q) := by
                rw [hqpd]
        _ = -inner ℝ d (a - p) + inner ℝ d (b - q) := by simp
        _ = inner ℝ d (b - q) - inner ℝ d (a - p) := by ring_nf
        _ = inner ℝ d ((b - q) - (a - p)) := by
              symm
              rw [inner_sub_right]
        _ = inner ℝ d (d - (a - b)) := by rw [hsub]
        _ = inner ℝ d d - inner ℝ d (a - b) := by rw [inner_sub_right]
        _ = ‖d‖ ^ (2 : ℕ) - inner ℝ d (a - b) := by rw [real_inner_self_eq_norm_sq]
    rw [hrewrite] at hsum
    have hfinal : ‖d‖ ^ (2 : ℕ) ≤ inner ℝ d (a - b) := by
      linarith
    simpa [d, p, q] using hfinal
  have hProx_nonexp : LipschitzWith 1 (fun z : H ↦ Prox[γ n, f, hf] z) := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro a b
    have hfirm := (firmlyNonexpansive_iff_norm_sq_le_inner.mp hProx_firm) a b
    have hsq :
        ‖Prox[γ n, f, hf] a - Prox[γ n, f, hf] b‖ ^ 2 ≤
          ‖Prox[γ n, f, hf] a - Prox[γ n, f, hf] b‖ * ‖a - b‖ := by
      exact le_trans hfirm (real_inner_le_norm _ _)
    have hnorm :
        ‖Prox[γ n, f, hf] a - Prox[γ n, f, hf] b‖ ≤ ‖a - b‖ := by
      nlinarith [hsq, norm_nonneg (Prox[γ n, f, hf] a - Prox[γ n, f, hf] b), norm_nonneg (a - b)]
    simpa [dist_eq_norm, one_mul] using hnorm
  have hStep_nonexp := hProx_nonexp.comp hForward_nonexp
  have hfixed := step_fixed_of_mem_argmin hf g hg gradg hgrad γ hxstar n
  have hfixed' : Prox[γ n, f, hf] (xstar - (γ n : ℝ) • gradg xstar) = xstar := by
    simpa [step_apply] using hfixed
  -- Apply the composite nonexpansive estimate to `x` and the minimizing fixed point `xstar`.
  simpa [dist_eq_norm, hfixed', one_mul] using hStep_nonexp.dist_le_mul x xstar

/-- Helper for Proposition 28.13: the variable-step forward-backward orbit is Fejér monotone with
respect to the minimizer set of the composite objective. -/
theorem orbit_fejerMonotone_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (0 : ℝ) (2 * (β : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (0 : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) :
    FejerMonotone (Argmin ((f + g.toEReal).asEReal)) (orbit hf gradg γ relax x0) := by
  -- Rewrite the relaxed update as a convex combination and combine it with the stage estimate.
  intro xstar hxstar n
  have hstep :
      ‖step hf gradg γ n (orbit hf gradg γ relax x0 n) - xstar‖ ≤
        ‖orbit hf gradg γ relax x0 n - xstar‖ :=
    step_dist_le_of_mem_argmin
      hf g hg gradg hgrad β hγ_bounds hgrad_lipschitz hxstar n
      (orbit hf gradg γ relax x0 n)
  have hnext :
      orbit hf gradg γ relax x0 (n + 1) =
        (1 - relax n) • orbit hf gradg γ relax x0 n +
          relax n • step hf gradg γ n (orbit hf gradg γ relax x0 n) := by
    -- Rewrite the relaxed update as the affine combination from the source recursion.
    rw [orbit_succ, step_apply_orbit]
    calc
      orbit hf gradg γ relax x0 n +
          relax n •
            (step hf gradg γ n (orbit hf gradg γ relax x0 n) -
              orbit hf gradg γ relax x0 n) =
          orbit hf gradg γ relax x0 n +
            (relax n • step hf gradg γ n (orbit hf gradg γ relax x0 n) -
              relax n • orbit hf gradg γ relax x0 n) := by
                rw [smul_sub]
      _ =
          (1 - relax n) • orbit hf gradg γ relax x0 n +
            relax n • step hf gradg γ n (orbit hf gradg γ relax x0 n) := by
              rw [sub_eq_add_neg, sub_smul, one_smul]
              abel_nf
  have hnorm :
      ‖orbit hf gradg γ relax x0 (n + 1) - xstar‖ ≤
        ‖orbit hf gradg γ relax x0 n - xstar‖ := by
    have hscaled :
        relax n * ‖step hf gradg γ n (orbit hf gradg γ relax x0 n) - xstar‖ ≤
          relax n * ‖orbit hf gradg γ relax x0 n - xstar‖ := by
      exact mul_le_mul_of_nonneg_left hstep (hrelax_bounds n).1
    have hsub :
        (1 - relax n) • orbit hf gradg γ relax x0 n +
            relax n • step hf gradg γ n (orbit hf gradg γ relax x0 n) - xstar =
          (1 - relax n) • (orbit hf gradg γ relax x0 n - xstar) +
            relax n • (step hf gradg γ n (orbit hf gradg γ relax x0 n) - xstar) := by
      simpa using
        affineCombination_sub_eq_smul_sub
          (a := 1 - relax n) (b := relax n) (x := orbit hf gradg γ relax x0 n)
          (y := step hf gradg γ n (orbit hf gradg γ relax x0 n)) (z := xstar) (by ring)
    rw [hnext]
    calc
      ‖(1 - relax n) • orbit hf gradg γ relax x0 n +
            relax n • step hf gradg γ n (orbit hf gradg γ relax x0 n) - xstar‖
          =
          ‖(1 - relax n) • (orbit hf gradg γ relax x0 n - xstar) +
              relax n • (step hf gradg γ n (orbit hf gradg γ relax x0 n) - xstar)‖ := by
                rw [hsub]
      _ ≤ ‖(1 - relax n) • (orbit hf gradg γ relax x0 n - xstar)‖ +
            ‖relax n • (step hf gradg γ n (orbit hf gradg γ relax x0 n) - xstar)‖ := by
              exact norm_add_le _ _
      _ = (1 - relax n) * ‖orbit hf gradg γ relax x0 n - xstar‖ +
            relax n * ‖step hf gradg γ n (orbit hf gradg γ relax x0 n) - xstar‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr (hrelax_bounds n).2),
                Real.norm_of_nonneg (hrelax_bounds n).1]
      _ ≤ (1 - relax n) * ‖orbit hf gradg γ relax x0 n - xstar‖ +
            relax n * ‖orbit hf gradg γ relax x0 n - xstar‖ := by
              exact add_le_add le_rfl hscaled
      _ = ‖orbit hf gradg γ relax x0 n - xstar‖ := by
            ring
  -- Convert the norm estimate into the distance inequality used by `FejerMonotone`.
  simpa [dist_eq_norm] using hnorm

/-
Proposition 28.13 (1): let `f ∈ Γ₀(H)`, let `β ∈ ℝ_{++}`, let `g : H → ℝ` be convex with a
`1 / β`-Lipschitz continuous gradient realized by `gradg`, let `ε ∈ ]0, min {1, β}[`, let
`γ n ∈ [ε, 2β - ε]`, let `λ n ∈ [ε, 1]`, and let `(x_n)`, `(y_n)`, `(z_n)` be the recursively
defined families from `(28.37)` starting at `x0 ∈ dom f`. If
`xstar ∈ Argmin (f + g.toEReal).asEReal`, then
`∑ ‖∇g(x_n) - ∇g(xstar)‖² < +∞`.
-/
/-- Helper for Proposition 28.13: the forward explicit-gradient step contracts squared distance by
the cocoercive gradient gap. -/
lemma forwardStep_sqNorm_le_sqNorm_sub_cocoerciveGap
    (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (0 : ℝ) (2 * (β : ℝ)))
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (n : ℕ) (x xstar : H) :
    ‖(x - (γ n : ℝ) • gradg x) - (xstar - (γ n : ℝ) • gradg xstar)‖ ^ 2 ≤
      ‖x - xstar‖ ^ 2 -
        (γ n : ℝ) * (2 * (β : ℝ) - (γ n : ℝ)) * ‖gradg x - gradg xstar‖ ^ 2 := by
  -- Route correction: use the public cocoercivity owner for `∇ g` and expand the squared norm
  -- once, instead of trying to squeeze the term through a generic nonexpansive estimate.
  have hdiff : Differentiable ℝ g := fun z ↦ (hgrad z).differentiableAt
  have hconv : _root_.ConvexOn ℝ Set.univ g := by
    simpa [Function.effectiveDomain_toEReal] using hg.2.toReal_convexOn_effectiveDomain
  let βInv : Set.Ioi (0 : ℝ) := ⟨(β : ℝ)⁻¹, by
    change 0 < (β : ℝ)⁻¹
    exact inv_pos.mpr β.2⟩
  have hCoco :
      CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun z : Set.univ ↦ gradg z) := by
    have hgrad_eq : ∇ g = gradg := by
      apply gradient_eq
      intro z
      simpa using hgrad z
    simpa [βInv, one_div, inv_inv, hgrad_eq] using
      gradient_lipschitz_imp_cocoercive_of_differentiable_convex
        g hdiff hconv βInv (by simpa [βInv, hgrad_eq] using hgrad_lipschitz)
  have hco := hCoco.2 ⟨x, by simp⟩ ⟨xstar, by simp⟩
  have hexpand :
      ‖(x - (γ n : ℝ) • gradg x) - (xstar - (γ n : ℝ) • gradg xstar)‖ ^ 2 =
        ‖x - xstar‖ ^ 2 -
          2 * (γ n : ℝ) * ⟪x - xstar, gradg x - gradg xstar⟫_ℝ +
            ((γ n : ℝ) ^ 2) * ‖gradg x - gradg xstar‖ ^ 2 := by
    calc
      ‖(x - (γ n : ℝ) • gradg x) - (xstar - (γ n : ℝ) • gradg xstar)‖ ^ 2 =
          ‖(x - xstar) - (γ n : ℝ) • (gradg x - gradg xstar)‖ ^ 2 := by
            have hsub :
                (x - (γ n : ℝ) • gradg x) - (xstar - (γ n : ℝ) • gradg xstar) =
                  (x - xstar) - (γ n : ℝ) • (gradg x - gradg xstar) := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
            rw [hsub]
      _ = ‖x - xstar‖ ^ 2 -
            2 * inner ℝ (x - xstar) ((γ n : ℝ) • (gradg x - gradg xstar)) +
            ‖(γ n : ℝ) • (gradg x - gradg xstar)‖ ^ 2 := by
              simpa using
                norm_sub_sq_real (x - xstar) ((γ n : ℝ) • (gradg x - gradg xstar))
      _ = ‖x - xstar‖ ^ 2 -
            2 * (γ n : ℝ) * ⟪x - xstar, gradg x - gradg xstar⟫_ℝ +
            ((γ n : ℝ) ^ 2) * ‖gradg x - gradg xstar‖ ^ 2 := by
              rw [real_inner_smul_right, norm_smul, Real.norm_of_nonneg (hγ_bounds n).1, pow_two]
              ring
  -- The cocoercive lower bound on the cross term yields the textbook quadratic drop.
  rw [hexpand]
  have hco' :
      (β : ℝ) * ‖gradg x - gradg xstar‖ ^ 2 ≤
        ⟪x - xstar, gradg x - gradg xstar⟫_ℝ := by
    simpa using hco
  have hbound :
      ‖x - xstar‖ ^ 2 -
          2 * (γ n : ℝ) * ⟪x - xstar, gradg x - gradg xstar⟫_ℝ +
          ((γ n : ℝ) ^ 2) * ‖gradg x - gradg xstar‖ ^ 2 ≤
        ‖x - xstar‖ ^ 2 -
          (γ n : ℝ) * (2 * (β : ℝ) - (γ n : ℝ)) *
            ‖gradg x - gradg xstar‖ ^ 2 := by
    have hscale :
        (-2 * (γ n : ℝ)) * ⟪x - xstar, gradg x - gradg xstar⟫_ℝ ≤
          (-2 * (γ n : ℝ)) * ((β : ℝ) * ‖gradg x - gradg xstar‖ ^ 2) := by
      exact mul_le_mul_of_nonpos_left hco' (by nlinarith [(hγ_bounds n).1])
    nlinarith [hscale]
  exact hbound

/-- Helper for Proposition 28.13: one stage of the variable-step proximal-gradient map controls
the proximal residual and the cocoercive gradient gap against any minimizer. -/
lemma step_sqDist_add_residualSq_le_sqDist_sub_cocoerciveGap_of_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (0 : ℝ) (2 * (β : ℝ)))
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    {relax : ℕ → ℝ} (x0 : H)
    {xstar : H} (hxstar : xstar ∈ Argmin ((f + g.toEReal).asEReal)) (n : ℕ) :
    ‖z hf gradg γ relax x0 n - xstar‖ ^ 2 +
        ‖y hf gradg γ relax x0 n - z hf gradg γ relax x0 n + (γ n : ℝ) • gradg xstar‖ ^ 2 ≤
      ‖orbit hf gradg γ relax x0 n - xstar‖ ^ 2 -
        (γ n : ℝ) * (2 * (β : ℝ) - (γ n : ℝ)) *
          ‖gradg (orbit hf gradg γ relax x0 n) - gradg xstar‖ ^ 2 := by
  let yn := y hf gradg γ relax x0 n
  let zn := z hf gradg γ relax x0 n
  let xref := xstar - (γ n : ℝ) • gradg xstar
  let hγf : (γ n) • f ∈ Γ₀(H) := smul_mem_gammaZero f hf (γ n)
  have hProx_firm :
      FirmlyNonexpansive (fun u : H ↦ Prox[γ n, f, hf] u) := by
    simpa [scaledProximityOperator] using
      proximityOperator_firmlyNonexpansive_of_mem_gammaZero (f := (γ n) • f) hγf
  have hRes_firm :
      FirmlyNonexpansive (fun u : H ↦ u - Prox[γ n, f, hf] u) := by
    simpa [scaledProximityOperator] using
      id_sub_proximityOperator_firmlyNonexpansive_of_mem_gammaZero (f := (γ n) • f) hγf
  have hfixed : Prox[γ n, f, hf] xref = xstar := by
    -- Rewrite the minimizing point as a fixed point of the stage map, then expose the prox input.
    simpa [step_apply, xref] using step_fixed_of_mem_argmin hf g hg gradg hgrad γ hxstar n
  have hprox :
      ‖zn - xstar‖ ^ 2 ≤ inner ℝ (zn - xstar) (yn - xref) := by
    simpa [yn, zn, xref, hfixed] using
      (firmlyNonexpansive_iff_norm_sq_le_inner.mp hProx_firm) yn xref
  have hres :
      ‖(yn - zn) - (xref - xstar)‖ ^ 2 ≤
        inner ℝ ((yn - zn) - (xref - xstar)) (yn - xref) := by
    simpa [yn, zn, xref, hfixed] using
      (firmlyNonexpansive_iff_norm_sq_le_inner.mp hRes_firm) yn xref
  have hsplit :
      (zn - xstar) + ((yn - zn) - (xref - xstar)) = yn - xref := by
    dsimp [yn, zn, xref]
    abel_nf
  have hsum :
      ‖zn - xstar‖ ^ 2 + ‖(yn - zn) - (xref - xstar)‖ ^ 2 ≤ ‖yn - xref‖ ^ 2 := by
    have hinner_sum :
        inner ℝ (zn - xstar) (yn - xref) +
            inner ℝ ((yn - zn) - (xref - xstar)) (yn - xref) =
          inner ℝ (yn - xref) (yn - xref) := by
      calc
        inner ℝ (zn - xstar) (yn - xref) +
            inner ℝ ((yn - zn) - (xref - xstar)) (yn - xref) =
          inner ℝ ((zn - xstar) + ((yn - zn) - (xref - xstar))) (yn - xref) := by
            rw [inner_add_left]
        _ = inner ℝ (yn - xref) (yn - xref) := by rw [hsplit]
    have hnorm :
        inner ℝ (yn - xref) (yn - xref) = ‖yn - xref‖ ^ 2 := by
      rw [real_inner_self_eq_norm_sq]
    nlinarith [hprox, hres, hinner_sum, hnorm]
  have hforward :
      ‖yn - xref‖ ^ 2 ≤
        ‖orbit hf gradg γ relax x0 n - xstar‖ ^ 2 -
          (γ n : ℝ) * (2 * (β : ℝ) - (γ n : ℝ)) *
            ‖gradg (orbit hf gradg γ relax x0 n) - gradg xstar‖ ^ 2 := by
    simpa [yn, xref, y_eq] using
      forwardStep_sqNorm_le_sqNorm_sub_cocoerciveGap
        g hg gradg hgrad β hγ_bounds hgrad_lipschitz n
        (orbit hf gradg γ relax x0 n) xstar
  -- The prox/residual pairwise estimate is the source `(28.39)` after the forward-step rewrite.
  simpa [yn, zn, xref, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    le_trans hsum hforward

/-- Helper for Proposition 28.13: the relaxed update inherits the source energy drop against a
fixed minimizer. -/
lemma relaxedStep_sqDist_drop_of_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (0 : ℝ) (2 * (β : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (0 : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) {xstar : H} (hxstar : xstar ∈ Argmin ((f + g.toEReal).asEReal)) (n : ℕ) :
    ‖orbit hf gradg γ relax x0 (n + 1) - xstar‖ ^ 2 +
        relax n *
          ((γ n : ℝ) * (2 * (β : ℝ) - (γ n : ℝ)) *
              ‖gradg (orbit hf gradg γ relax x0 n) - gradg xstar‖ ^ 2 +
            ‖y hf gradg γ relax x0 n - z hf gradg γ relax x0 n + (γ n : ℝ) • gradg xstar‖ ^ 2) ≤
      ‖orbit hf gradg γ relax x0 n - xstar‖ ^ 2 := by
  -- Route correction: combine the affine relaxation estimate with the source one-step drop.
  have hstep :
      ‖z hf gradg γ relax x0 n - xstar‖ ^ 2 +
          ‖y hf gradg γ relax x0 n - z hf gradg γ relax x0 n + (γ n : ℝ) • gradg xstar‖ ^ 2 ≤
        ‖orbit hf gradg γ relax x0 n - xstar‖ ^ 2 -
          (γ n : ℝ) * (2 * (β : ℝ) - (γ n : ℝ)) *
            ‖gradg (orbit hf gradg γ relax x0 n) - gradg xstar‖ ^ 2 :=
    step_sqDist_add_residualSq_le_sqDist_sub_cocoerciveGap_of_mem_argmin
      hf g hg gradg hgrad β hγ_bounds hgrad_lipschitz x0 hxstar n
  have hnext :
      orbit hf gradg γ relax x0 (n + 1) =
        (1 - relax n) • orbit hf gradg γ relax x0 n +
          relax n • z hf gradg γ relax x0 n := by
    -- Rewrite the recursive update into the affine combination used by the source proof.
    rw [orbit_succ]
    calc
      orbit hf gradg γ relax x0 n +
          relax n • (z hf gradg γ relax x0 n - orbit hf gradg γ relax x0 n) =
        orbit hf gradg γ relax x0 n +
          (relax n • z hf gradg γ relax x0 n -
            relax n • orbit hf gradg γ relax x0 n) := by
              rw [smul_sub]
      _ = (1 - relax n) • orbit hf gradg γ relax x0 n +
          relax n • z hf gradg γ relax x0 n := by
            rw [sub_eq_add_neg, sub_smul, one_smul]
            abel_nf
  have hconv :
      ‖orbit hf gradg γ relax x0 (n + 1) - xstar‖ ^ 2 ≤
        (1 - relax n) * ‖orbit hf gradg γ relax x0 n - xstar‖ ^ 2 +
          relax n * ‖z hf gradg γ relax x0 n - xstar‖ ^ 2 := by
    rw [hnext]
    have hsub :
        (1 - relax n) • orbit hf gradg γ relax x0 n +
            relax n • z hf gradg γ relax x0 n - xstar =
          (1 - relax n) • (orbit hf gradg γ relax x0 n - xstar) +
            relax n • (z hf gradg γ relax x0 n - xstar) := by
      simpa using
        affineCombination_sub_eq_smul_sub
          (a := 1 - relax n) (b := relax n) (x := orbit hf gradg γ relax x0 n)
          (y := z hf gradg γ relax x0 n) (z := xstar) (by ring)
    rw [hsub]
    let u := orbit hf gradg γ relax x0 n - xstar
    let v := z hf gradg γ relax x0 n - xstar
    have htriangle :
        ‖(1 - relax n) • u + relax n • v‖ ≤
          (1 - relax n) * ‖u‖ + relax n * ‖v‖ := by
      calc
        ‖(1 - relax n) • u + relax n • v‖
            ≤ ‖(1 - relax n) • u‖ + ‖relax n • v‖ := norm_add_le _ _
        _ = (1 - relax n) * ‖u‖ + relax n * ‖v‖ := by
              rw [norm_smul, norm_smul]
              simp [Real.norm_of_nonneg (sub_nonneg.mpr (hrelax_bounds n).2),
                Real.norm_of_nonneg (hrelax_bounds n).1]
    have hsq :
        ‖(1 - relax n) • u + relax n • v‖ ^ 2 ≤
          ((1 - relax n) * ‖u‖ + relax n * ‖v‖) ^ 2 := by
      have hrhs_nonneg : 0 ≤ (1 - relax n) * ‖u‖ + relax n * ‖v‖ := by
        have hu_nonneg : 0 ≤ ‖u‖ := norm_nonneg _
        have hv_nonneg : 0 ≤ ‖v‖ := norm_nonneg _
        nlinarith [(hrelax_bounds n).1, (hrelax_bounds n).2, hu_nonneg, hv_nonneg]
      exact (sq_le_sq₀ (norm_nonneg _) hrhs_nonneg).2 htriangle
    have hweighted_sq :
        ((1 - relax n) * ‖u‖ + relax n * ‖v‖) ^ 2 ≤
          (1 - relax n) * ‖u‖ ^ 2 + relax n * ‖v‖ ^ 2 := by
      have hiden :
          (1 - relax n) * ‖u‖ ^ 2 + relax n * ‖v‖ ^ 2 -
              ((1 - relax n) * ‖u‖ + relax n * ‖v‖) ^ 2 =
            relax n * (1 - relax n) * (‖u‖ - ‖v‖) ^ 2 := by
        ring
      have hnonneg :
          0 ≤ relax n * (1 - relax n) * (‖u‖ - ‖v‖) ^ 2 := by
        exact mul_nonneg
          (mul_nonneg (hrelax_bounds n).1 (sub_nonneg.mpr (hrelax_bounds n).2))
          (sq_nonneg _)
      nlinarith [hiden]
    have hfinal :
        ‖(1 - relax n) • u + relax n • v‖ ^ 2 ≤
          (1 - relax n) * ‖u‖ ^ 2 + relax n * ‖v‖ ^ 2 := by
      exact le_trans hsq hweighted_sq
    simpa [u, v, smul_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hfinal
  have hnonneg : 0 ≤ relax n := (hrelax_bounds n).1
  -- Multiply the stage estimate by the relaxation weight and add the convexity bound.
  have hweighted :
      relax n *
          (‖z hf gradg γ relax x0 n - xstar‖ ^ 2 +
            ‖y hf gradg γ relax x0 n - z hf gradg γ relax x0 n + (γ n : ℝ) • gradg xstar‖ ^ 2) ≤
        relax n *
          (‖orbit hf gradg γ relax x0 n - xstar‖ ^ 2 -
            (γ n : ℝ) * (2 * (β : ℝ) - (γ n : ℝ)) *
              ‖gradg (orbit hf gradg γ relax x0 n) - gradg xstar‖ ^ 2) := by
    exact mul_le_mul_of_nonneg_left hstep hnonneg
  nlinarith [hconv, hweighted]

/-- Helper for Proposition 28.13: the relaxed stage-energy drop telescopes into a uniform bound
on every finite partial sum of the source energy terms. -/
lemma energyPartialSums_le_initialSqDist_of_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (0 : ℝ) (2 * (β : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (0 : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) {xstar : H} (hxstar : xstar ∈ Argmin ((f + g.toEReal).asEReal))
    (N : ℕ) :
    Finset.sum (Finset.range N)
        (fun k ↦
          relax k *
            ((γ k : ℝ) * (2 * (β : ℝ) - (γ k : ℝ)) *
                ‖gradg (orbit hf gradg γ relax x0 k) - gradg xstar‖ ^ 2 +
              ‖y hf gradg γ relax x0 k - z hf gradg γ relax x0 k +
                  (γ k : ℝ) • gradg xstar‖ ^ 2)) ≤
      ‖x0 - xstar‖ ^ 2 := by
  have hpartial_aux :
      ∀ M : ℕ,
        Finset.sum (Finset.range M)
            (fun k ↦
              relax k *
                ((γ k : ℝ) * (2 * (β : ℝ) - (γ k : ℝ)) *
                    ‖gradg (orbit hf gradg γ relax x0 k) - gradg xstar‖ ^ 2 +
                  ‖y hf gradg γ relax x0 k - z hf gradg γ relax x0 k +
                      (γ k : ℝ) • gradg xstar‖ ^ 2)) +
            ‖orbit hf gradg γ relax x0 M - xstar‖ ^ 2 ≤
          ‖x0 - xstar‖ ^ 2 := by
    intro M
    induction M with
    | zero =>
        -- The empty partial sum leaves exactly the initial squared distance.
        simp
    | succ M ih =>
        -- Add the next stage drop inequality and telescope the orbit term.
        rw [Finset.sum_range_succ]
        have hdrop :=
          relaxedStep_sqDist_drop_of_mem_argmin
            hf g hg gradg hgrad β hγ_bounds hrelax_bounds hgrad_lipschitz x0 hxstar M
        linarith
  have hnonneg : 0 ≤ ‖orbit hf gradg γ relax x0 N - xstar‖ ^ 2 := sq_nonneg _
  -- Dropping the nonnegative tail term yields the uniform partial-sum bound.
  linarith [hpartial_aux N]

/-- Helper for Proposition 28.13: the telescoped stage-energy bound yields separate square
summability of the gradient gap and of the proximal residual surface. -/
lemma gradientAndResidual_sqSummable_of_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    (ε : Set.Ioo (0 : ℝ) (min 1 (β : ℝ))) {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (ε : ℝ) (2 * (β : ℝ) - (ε : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (ε : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) {xstar : H} (hxstar : xstar ∈ Argmin ((f + g.toEReal).asEReal)) :
    Summable
      (fun n : ℕ ↦
        ‖gradg (orbit hf gradg γ relax x0 n) - gradg xstar‖ ^ 2) ∧
      Summable
        (fun n : ℕ ↦
          ‖y hf gradg γ relax x0 n - z hf gradg γ relax x0 n +
              (γ n : ℝ) • gradg xstar‖ ^ 2) := by
  let gradSq : ℕ → ℝ :=
    fun n ↦ ‖gradg (orbit hf gradg γ relax x0 n) - gradg xstar‖ ^ 2
  let residualSq : ℕ → ℝ :=
    fun n ↦ ‖y hf gradg γ relax x0 n - z hf gradg γ relax x0 n +
        (γ n : ℝ) • gradg xstar‖ ^ 2
  have hgrad_partial :
      ∀ N : ℕ, Finset.sum (Finset.range N) gradSq ≤ ‖x0 - xstar‖ ^ 2 / (ε : ℝ) ^ 3 := by
    intro N
    have henergy :=
      energyPartialSums_le_initialSqDist_of_mem_argmin
        hf g hg gradg hgrad β
        (fun n ↦ by
          constructor
          · exact le_trans ε.2.1.le (hγ_bounds n).1
          · have hε_pos : 0 < (ε : ℝ) := ε.2.1
            nlinarith [(hγ_bounds n).2, hε_pos])
        (fun n ↦ by
          constructor
          · exact le_trans ε.2.1.le (hrelax_bounds n).1
          · exact (hrelax_bounds n).2)
        hgrad_lipschitz x0 hxstar N
    have hweight :
        (ε : ℝ) ^ 3 * Finset.sum (Finset.range N) gradSq ≤
          Finset.sum (Finset.range N)
            (fun k ↦
              relax k *
                ((γ k : ℝ) * (2 * (β : ℝ) - (γ k : ℝ)) * gradSq k + residualSq k)) := by
      calc
        (ε : ℝ) ^ 3 * Finset.sum (Finset.range N) gradSq =
            Finset.sum (Finset.range N) (fun k ↦ (ε : ℝ) ^ 3 * gradSq k) := by
              rw [Finset.mul_sum]
        _ ≤ Finset.sum (Finset.range N)
              (fun k ↦
                relax k *
                  ((γ k : ℝ) * (2 * (β : ℝ) - (γ k : ℝ)) * gradSq k + residualSq k)) := by
              refine Finset.sum_le_sum fun k hk ↦ ?_
              have hcoeff :
                  (ε : ℝ) ^ 3 ≤ relax k * (γ k : ℝ) * (2 * (β : ℝ) - (γ k : ℝ)) := by
                have hε_nonneg : 0 ≤ (ε : ℝ) := ε.2.1.le
                have hγ_ge : (ε : ℝ) ≤ (γ k : ℝ) := (hγ_bounds k).1
                have hγ_gap_ge : (ε : ℝ) ≤ 2 * (β : ℝ) - (γ k : ℝ) := by
                  nlinarith [(hγ_bounds k).2]
                have hrelax_ge : (ε : ℝ) ≤ relax k := (hrelax_bounds k).1
                have hγ_gap_nonneg : 0 ≤ 2 * (β : ℝ) - (γ k : ℝ) := le_trans hε_nonneg hγ_gap_ge
                have hε_sq :
                    (ε : ℝ) ^ 2 ≤ (γ k : ℝ) * (2 * (β : ℝ) - (γ k : ℝ)) := by
                  have hmul1 :=
                    mul_le_mul hγ_ge hγ_gap_ge hε_nonneg (le_trans hε_nonneg hγ_ge)
                  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul1
                have hrelax_nonneg : 0 ≤ relax k := le_trans hε_nonneg hrelax_ge
                have hmul :=
                  mul_le_mul hrelax_ge hε_sq
                    (sq_nonneg (ε : ℝ))
                    hrelax_nonneg
                have hmul' := hmul
                ring_nf at hmul' ⊢
                exact hmul'
              have hterm_nonneg : 0 ≤ gradSq k := by
                dsimp [gradSq]
                exact sq_nonneg _
              have hres_nonneg : 0 ≤ residualSq k := by
                dsimp [residualSq]
                exact sq_nonneg _
              have hmain :
                  (ε : ℝ) ^ 3 * gradSq k ≤
                    (relax k * (γ k : ℝ) * (2 * (β : ℝ) - (γ k : ℝ))) * gradSq k := by
                exact mul_le_mul_of_nonneg_right hcoeff hterm_nonneg
              have hmain' :
                  (relax k * (γ k : ℝ) * (2 * (β : ℝ) - (γ k : ℝ))) * gradSq k ≤
                    relax k *
                      ((γ k : ℝ) * (2 * (β : ℝ) - (γ k : ℝ)) * gradSq k + residualSq k) := by
                have hrelax_nonneg : 0 ≤ relax k := le_trans ε.2.1.le (hrelax_bounds k).1
                nlinarith
              nlinarith [hmain, hmain']
    have hε3_pos : 0 < (ε : ℝ) ^ 3 := by
      exact pow_pos ε.2.1 3
    refine (le_div_iff₀ hε3_pos).2 ?_
    have hweight' :
        Finset.sum (Finset.range N) gradSq * (ε : ℝ) ^ 3 ≤
          Finset.sum (Finset.range N)
            (fun k ↦
              relax k *
                ((γ k : ℝ) * (2 * (β : ℝ) - (γ k : ℝ)) * gradSq k + residualSq k)) := by
      simpa [mul_comm] using hweight
    exact le_trans hweight' henergy
  have hresidual_partial :
      ∀ N : ℕ, Finset.sum (Finset.range N) residualSq ≤ ‖x0 - xstar‖ ^ 2 / (ε : ℝ) := by
    intro N
    have henergy :=
      energyPartialSums_le_initialSqDist_of_mem_argmin
        hf g hg gradg hgrad β
        (fun n ↦ by
          constructor
          · exact le_trans ε.2.1.le (hγ_bounds n).1
          · have hε_pos : 0 < (ε : ℝ) := ε.2.1
            nlinarith [(hγ_bounds n).2, hε_pos])
        (fun n ↦ by
          constructor
          · exact le_trans ε.2.1.le (hrelax_bounds n).1
          · exact (hrelax_bounds n).2)
        hgrad_lipschitz x0 hxstar N
    have hweight :
        (ε : ℝ) * Finset.sum (Finset.range N) residualSq ≤
          Finset.sum (Finset.range N)
            (fun k ↦
              relax k *
                ((γ k : ℝ) * (2 * (β : ℝ) - (γ k : ℝ)) * gradSq k + residualSq k)) := by
      calc
        (ε : ℝ) * Finset.sum (Finset.range N) residualSq =
            Finset.sum (Finset.range N) (fun k ↦ (ε : ℝ) * residualSq k) := by
              rw [Finset.mul_sum]
        _ ≤ Finset.sum (Finset.range N)
              (fun k ↦
                relax k *
                  ((γ k : ℝ) * (2 * (β : ℝ) - (γ k : ℝ)) * gradSq k + residualSq k)) := by
              refine Finset.sum_le_sum fun k hk ↦ ?_
              have hrelax_ge : (ε : ℝ) ≤ relax k := (hrelax_bounds k).1
              have hgrad_nonneg : 0 ≤ gradSq k := by
                dsimp [gradSq]
                exact sq_nonneg _
              have hres_nonneg : 0 ≤ residualSq k := by
                dsimp [residualSq]
                exact sq_nonneg _
              have hrelax_nonneg : 0 ≤ relax k := le_trans ε.2.1.le (hrelax_bounds k).1
              have hcoeff_term_nonneg :
                  0 ≤ (γ k : ℝ) * (2 * (β : ℝ) - (γ k : ℝ)) * gradSq k := by
                have hγ_nonneg : 0 ≤ (γ k : ℝ) := le_trans ε.2.1.le (hγ_bounds k).1
                have hgap_nonneg : 0 ≤ 2 * (β : ℝ) - (γ k : ℝ) := by
                  have hγ_le : (γ k : ℝ) ≤ 2 * (β : ℝ) := by
                    nlinarith [(hγ_bounds k).2, ε.2.1]
                  linarith
                exact mul_nonneg (mul_nonneg hγ_nonneg hgap_nonneg) hgrad_nonneg
              calc
                (ε : ℝ) * residualSq k ≤ relax k * residualSq k := by
                  exact mul_le_mul_of_nonneg_right hrelax_ge hres_nonneg
                _ ≤
                    relax k *
                      ((γ k : ℝ) * (2 * (β : ℝ) - (γ k : ℝ)) * gradSq k + residualSq k) := by
                  have hinside :
                      residualSq k ≤
                        (γ k : ℝ) * (2 * (β : ℝ) - (γ k : ℝ)) * gradSq k + residualSq k := by
                    nlinarith [hcoeff_term_nonneg]
                  exact mul_le_mul_of_nonneg_left hinside hrelax_nonneg
    have htmp : (ε : ℝ) * Finset.sum (Finset.range N) residualSq ≤ ‖x0 - xstar‖ ^ 2 := by
      exact le_trans hweight henergy
    exact (le_div_iff₀ ε.2.1).2 (by simpa [mul_comm] using htmp)
  have hgrad_summable : Summable gradSq :=
    summable_of_sum_range_le (fun n ↦ by
      dsimp [gradSq]
      exact sq_nonneg _) hgrad_partial
  have hresidual_summable : Summable residualSq :=
    summable_of_sum_range_le (fun n ↦ by
      dsimp [residualSq]
      exact sq_nonneg _) hresidual_partial
  simpa [gradSq, residualSq] using And.intro hgrad_summable hresidual_summable

/-- Helper for Proposition 28.13: the step correction is pointwise dominated by the source
residual surface and the gradient-gap square. -/
lemma stepCorrection_eq_gradientGap_sub_proxResidual
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (gradg : H → H)
    {γ : ℕ → PosReal} {relax : ℕ → ℝ} (x0 xstar : H) (n : ℕ) :
    z hf gradg γ relax x0 n - orbit hf gradg γ relax x0 n =
      (γ n : ℝ) • (gradg xstar - gradg (orbit hf gradg γ relax x0 n)) -
        (y hf gradg γ relax x0 n - z hf gradg γ relax x0 n + (γ n : ℝ) • gradg xstar) := by
  -- Rewrite `y_n = x_n - γ_n ∇g(x_n)` once so the source residual surface appears explicitly.
  simp [y_eq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  abel_nf

/-- Helper for Proposition 28.13: the step correction is pointwise dominated by the source
residual surface and the gradient-gap square. -/
lemma stepDifference_sq_le_two_mul_residualSq_add_gradientSq
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (_hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (_hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (0 : ℝ) (2 * (β : ℝ)))
    {relax : ℕ → ℝ} (x0 : H) {xstar : H}
    (_hxstar : xstar ∈ Argmin ((f + g.toEReal).asEReal)) (n : ℕ) :
    ‖z hf gradg γ relax x0 n - orbit hf gradg γ relax x0 n‖ ^ 2 ≤
      2 * ‖y hf gradg γ relax x0 n - z hf gradg γ relax x0 n +
          (γ n : ℝ) • gradg xstar‖ ^ 2 +
        2 * (2 * (β : ℝ)) ^ 2 *
          ‖gradg (orbit hf gradg γ relax x0 n) - gradg xstar‖ ^ 2 := by
  -- Route correction: isolate the exact `z_n - x_n` decomposition once, then apply the standard
  -- two-square estimate instead of repeating theorem-local `y_n`/`z_n` algebra.
  let residual : H :=
    y hf gradg γ relax x0 n - z hf gradg γ relax x0 n + (γ n : ℝ) • gradg xstar
  let smoothGap : H :=
    (γ n : ℝ) • (gradg xstar - gradg (orbit hf gradg γ relax x0 n))
  have hdecomp :
      z hf gradg γ relax x0 n - orbit hf gradg γ relax x0 n = smoothGap - residual := by
    -- Invoke the algebraic bridge so the norm comparison sees one stable normal form.
    simpa [residual, smoothGap] using
      stepCorrection_eq_gradientGap_sub_proxResidual
        (hf := hf) (gradg := gradg) (γ := γ) (relax := relax) (x0 := x0) xstar n
  have hadd :
      ‖z hf gradg γ relax x0 n - orbit hf gradg γ relax x0 n‖ ^ 2 ≤
        2 * ‖residual‖ ^ 2 + 2 * ‖smoothGap‖ ^ 2 := by
    rw [hdecomp]
    have hsum : ‖smoothGap - residual‖ ≤ ‖smoothGap‖ + ‖residual‖ := norm_sub_le _ _
    have hsq :
        ‖smoothGap - residual‖ ^ 2 ≤ (‖smoothGap‖ + ‖residual‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hsum
    have hupper :
        (‖smoothGap‖ + ‖residual‖) ^ 2 ≤ 2 * ‖residual‖ ^ 2 + 2 * ‖smoothGap‖ ^ 2 := by
      nlinarith [sq_nonneg (‖residual‖ - ‖smoothGap‖)]
    exact le_trans hsq hupper
  have hsmooth :
      ‖smoothGap‖ ^ 2 ≤
        (2 * (β : ℝ)) ^ 2 *
          ‖gradg (orbit hf gradg γ relax x0 n) - gradg xstar‖ ^ 2 := by
    dsimp [smoothGap]
    have hγ_nonneg : 0 ≤ (γ n : ℝ) := (hγ_bounds n).1
    have hγ_le : (γ n : ℝ) ≤ 2 * (β : ℝ) := (hγ_bounds n).2
    rw [norm_smul, Real.norm_of_nonneg hγ_nonneg]
    have hgrad_norm_nonneg :
        0 ≤ ‖gradg xstar - gradg (orbit hf gradg γ relax x0 n)‖ := norm_nonneg _
    have hmul :
        (γ n : ℝ) * ‖gradg xstar - gradg (orbit hf gradg γ relax x0 n)‖ ≤
          (2 * (β : ℝ)) * ‖gradg xstar - gradg (orbit hf gradg γ relax x0 n)‖ := by
      exact mul_le_mul_of_nonneg_right hγ_le hgrad_norm_nonneg
    have hsq :
        ((γ n : ℝ) * ‖gradg xstar - gradg (orbit hf gradg γ relax x0 n)‖) ^ 2 ≤
          ((2 * (β : ℝ)) * ‖gradg xstar - gradg (orbit hf gradg γ relax x0 n)‖) ^ 2 := by
      have hnonneg_left :
          0 ≤ (γ n : ℝ) * ‖gradg xstar - gradg (orbit hf gradg γ relax x0 n)‖ :=
        mul_nonneg hγ_nonneg hgrad_norm_nonneg
      have hnonneg_right :
          0 ≤ (2 * (β : ℝ)) * ‖gradg xstar - gradg (orbit hf gradg γ relax x0 n)‖ := by
        have htwoβ_nonneg : 0 ≤ 2 * (β : ℝ) := by
          nlinarith [β.2]
        exact mul_nonneg htwoβ_nonneg hgrad_norm_nonneg
      have habs :
          |(γ n : ℝ) * ‖gradg xstar - gradg (orbit hf gradg γ relax x0 n)‖| ≤
            |(2 * (β : ℝ)) * ‖gradg xstar - gradg (orbit hf gradg γ relax x0 n)‖| := by
        rw [abs_of_nonneg hnonneg_left, abs_of_nonneg hnonneg_right]
        exact hmul
      exact (sq_le_sq).2 habs
    calc
      ((γ n : ℝ) * ‖gradg xstar - gradg (orbit hf gradg γ relax x0 n)‖) ^ 2
          ≤ ((2 * (β : ℝ)) * ‖gradg xstar - gradg (orbit hf gradg γ relax x0 n)‖) ^ 2 := hsq
      _ = (2 * (β : ℝ)) ^ 2 *
            ‖gradg (orbit hf gradg γ relax x0 n) - gradg xstar‖ ^ 2 := by
            rw [norm_sub_rev]
            ring
  -- Combine the additive norm estimate with the uniform step-size bound `γ_n ≤ 2β`.
  calc
    ‖z hf gradg γ relax x0 n - orbit hf gradg γ relax x0 n‖ ^ 2
        ≤ 2 * ‖residual‖ ^ 2 + 2 * ‖smoothGap‖ ^ 2 := hadd
    _ ≤ 2 * ‖residual‖ ^ 2 +
          2 * ((2 * (β : ℝ)) ^ 2 *
            ‖gradg (orbit hf gradg γ relax x0 n) - gradg xstar‖ ^ 2) := by
          nlinarith [hsmooth]
    _ = 2 * ‖y hf gradg γ relax x0 n - z hf gradg γ relax x0 n +
            (γ n : ℝ) • gradg xstar‖ ^ 2 +
          2 * (2 * (β : ℝ)) ^ 2 *
            ‖gradg (orbit hf gradg γ relax x0 n) - gradg xstar‖ ^ 2 := by
          dsimp [residual]
          ring
/-- Helper for Proposition 28.13: fixing one minimizer makes both the gradient differences and the
proximal corrections square summable. -/
lemma gradientAndStep_sqSummable_of_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    (ε : Set.Ioo (0 : ℝ) (min 1 (β : ℝ))) {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (ε : ℝ) (2 * (β : ℝ) - (ε : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (ε : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) {xstar : H} (hxstar : xstar ∈ Argmin ((f + g.toEReal).asEReal)) :
    Summable
      (fun n : ℕ ↦
        ‖gradg (orbit hf gradg γ relax x0 n) - gradg xstar‖ ^ 2) ∧
      Summable
        (fun n : ℕ ↦
          ‖z hf gradg γ relax x0 n - orbit hf gradg γ relax x0 n‖ ^ 2) := by
  -- Project the residual package and dominate the step squares pointwise.
  let gradSq : ℕ → ℝ :=
    fun n ↦ ‖gradg (orbit hf gradg γ relax x0 n) - gradg xstar‖ ^ 2
  let residualSq : ℕ → ℝ :=
    fun n ↦ ‖y hf gradg γ relax x0 n - z hf gradg γ relax x0 n +
        (γ n : ℝ) • gradg xstar‖ ^ 2
  let stepSq : ℕ → ℝ :=
    fun n ↦ ‖z hf gradg γ relax x0 n - orbit hf gradg γ relax x0 n‖ ^ 2
  let coeff : ℝ := 2 * (2 * (β : ℝ)) ^ 2
  obtain ⟨hgrad_summable, hresidual_summable⟩ :=
    gradientAndResidual_sqSummable_of_mem_argmin
      hf g hg gradg hgrad β ε hγ_bounds hrelax_bounds hgrad_lipschitz x0 hxstar
  have hstep_bound :
      ∀ n : ℕ,
        stepSq n ≤ 2 * residualSq n + coeff * gradSq n := by
    intro n
    simpa [coeff, gradSq, residualSq, stepSq] using
      stepDifference_sq_le_two_mul_residualSq_add_gradientSq
        hf g hg gradg hgrad β
        (fun k ↦ by
          constructor
          · exact le_trans ε.2.1.le (hγ_bounds k).1
          · nlinarith [(hγ_bounds k).2, ε.2.1])
        x0 hxstar n
  have hdominating_summable :
      Summable (fun n : ℕ ↦ 2 * residualSq n + coeff * gradSq n) := by
    exact (hresidual_summable.mul_left 2).add (hgrad_summable.mul_left coeff)
  have hstep_summable : Summable stepSq := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ ↦ 2 * residualSq n + coeff * gradSq n)
      (g := stepSq)
      (fun n ↦ by positivity) ?_ hdominating_summable
    intro n
    exact hstep_bound n
  exact ⟨by simpa [gradSq] using hgrad_summable, by simpa [stepSq] using hstep_summable⟩
theorem forwardBackward_gradientDifference_summable
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    (ε : Set.Ioo (0 : ℝ) (min 1 (β : ℝ))) {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (ε : ℝ) (2 * (β : ℝ) - (ε : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (ε : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) (_hx0 : x0 ∈ dom f)
    {xstar : H} (hxstar : xstar ∈ Argmin ((f + g.toEReal).asEReal)) :
    Summable
      (fun n : ℕ ↦
        ‖gradg (orbit hf gradg γ relax x0 n) - gradg xstar‖ ^ 2) := by
  -- Project clause `(1)` from the joint square-summability package.
  exact
    (gradientAndStep_sqSummable_of_mem_argmin
      hf g hg gradg hgrad β ε hγ_bounds hrelax_bounds hgrad_lipschitz x0 hxstar).1

/-- Clause (2) of Proposition 28.13: under the hypotheses of Proposition 28.13, the correction
sequence
`(z_n - x_n)` is square summable. -/
theorem forwardBackward_stepDifference_summable
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    (ε : Set.Ioo (0 : ℝ) (min 1 (β : ℝ))) {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (ε : ℝ) (2 * (β : ℝ) - (ε : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (ε : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) (_hx0 : x0 ∈ dom f)
    (hargmin : (Argmin ((f + g.toEReal).asEReal)).Nonempty) :
    Summable
      (fun n : ℕ ↦
        ‖z hf gradg γ relax x0 n - orbit hf gradg γ relax x0 n‖ ^ 2) := by
  rcases hargmin with ⟨xstar, hxstar⟩
  -- Project clause `(2)` from the same source-energy package used for clause `(1)`.
  exact
    (gradientAndStep_sqSummable_of_mem_argmin
      hf g hg gradg hgrad β ε hγ_bounds hrelax_bounds hgrad_lipschitz x0 hxstar).2

/-- Helper for Proposition 28.13: on `effectiveDomain f`, the composite objective
`(f + g.toEReal).asEReal` reduces to the expected real-valued sum. -/
lemma objectiveToReal_eq_fToReal_add_g_of_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (g : H → ℝ) {x : H}
    (hx : x ∈ effectiveDomain f) :
    (((f + g.toEReal).asEReal) x).toReal = (f x : EReal).toReal + g x := by
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  -- Expand the canonical objective and convert the finite `EReal` sum back to `ℝ`.
  simpa [Function.asEReal, Function.toEReal_apply] using
    (EReal.toReal_add hfx_top hfx_bot (by simp) (by simp) :
      (((f x : EReal) + (g x : EReal)).toReal = (f x : EReal).toReal + (g x : EReal).toReal))

/-- Helper for Proposition 28.13: each backward point `z_n` satisfies the real-valued source
descent inequality `h(z_n) ≤ h(x_n) - ((1 / γ_n) - 1 / (2β)) ‖z_n - x_n‖²`. -/
lemma stageObjectiveDrop_atBackwardPoint
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    {γ : ℕ → PosReal}
    (_hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (0 : ℝ) (2 * (β : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (0 : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) (hx0 : x0 ∈ dom f) (n : ℕ) :
    (((f + g.toEReal).asEReal) (z hf gradg γ relax x0 n)).toReal ≤
      (((f + g.toEReal).asEReal) (orbit hf gradg γ relax x0 n)).toReal -
        ((1 / (γ n : ℝ)) - 1 / (2 * (β : ℝ))) *
          ‖z hf gradg γ relax x0 n - orbit hf gradg γ relax x0 n‖ ^ 2 := by
  -- Route correction: compare the prox inequality directly with `x_n`, so the real-valued source
  -- surface is normalized before the Chapter 18 descent estimate is added.
  let h := ((f + g.toEReal).asEReal)
  let xn := orbit hf gradg γ relax x0 n
  let yn := y hf gradg γ relax x0 n
  let zn := z hf gradg γ relax x0 n
  rcases orbit_mem_dom_and_z_mem_dom hf gradg γ hrelax_bounds x0 hx0 n with ⟨hxn_dom, hzn_dom⟩
  have hdiff : Differentiable ℝ g := fun x ↦ (hgrad x).differentiableAt
  have hconv : _root_.ConvexOn ℝ Set.univ g := by
    simpa [Function.effectiveDomain_toEReal] using hg.2.toReal_convexOn_effectiveDomain
  have hgrad_eq : ∇ g = gradg := by
    apply gradient_eq
    intro x
    simpa using hgrad x
  let hγf : (γ n) • f ∈ Γ₀(H) := smul_mem_gammaZero f hf (γ n)
  have hprox :
      IsProxPoint (((γ n) • f : H → Set.Ioi (⊥ : EReal))) yn zn := by
    -- Read `z_n` as the proximal point of `γ_n • f` at the forward point `y_n`.
    simpa [yn, zn, scaledProximityOperator] using
      proximityOperator_isProxPoint
        (((γ n) • f : H → Set.Ioi (⊥ : EReal)))
        (hasUniqueProxPoint_of_mem_gammaZero (((γ n) • f : H → Set.Ioi (⊥ : EReal))) hγf) yn
  have hxn_dom_scaled :
      xn ∈ effectiveDomain (((γ n) • f : H → Set.Ioi (⊥ : EReal))) := by
    exact (mem_effectiveDomain_posReal_smul_iff (f := f) (γ := γ n) xn).2 hxn_dom
  have hprox_raw :
      ⟪xn - zn, yn - zn⟫_ℝ + (γ n : ℝ) * (f zn : EReal).toReal ≤
        (γ n : ℝ) * (f xn : EReal).toReal := by
    have hxn_top : (f xn : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hxn_dom)
    have hxn_bot : (f xn : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f xn : EReal) from (f xn).2)
    have hzn_top : (f zn : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hzn_dom)
    have hzn_bot : (f zn : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f zn : EReal) from (f zn).2)
    simpa [yn, zn, posReal_smul_apply, EReal.toReal_mul, EReal.toReal_coe,
      hxn_top, hxn_bot, hzn_top, hzn_bot] using
      inner_add_toReal_le_toReal_of_isProxPoint_of_mem_gammaZero
        (g := ((γ n) • f : H → Set.Ioi (⊥ : EReal))) hγf hprox hxn_dom_scaled
  have hy_simple :
      yn - zn = (xn - zn) - (γ n : ℝ) • gradg xn := by
    dsimp [yn, xn]
    abel_nf
  have hprox_real :
      ⟪xn - zn, (γ n : ℝ)⁻¹ • (xn - zn) - gradg xn⟫_ℝ ≤
        (f xn : EReal).toReal - (f zn : EReal).toReal := by
    rw [hy_simple, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at hprox_raw
    have hγ_pos : 0 < (γ n : ℝ) := (γ n).2
    have htmp :
        ‖xn - zn‖ ^ 2 - (γ n : ℝ) * ⟪xn - zn, gradg xn⟫_ℝ ≤
          (γ n : ℝ) * ((f xn : EReal).toReal - (f zn : EReal).toReal) := by
      nlinarith [hprox_raw]
    have hscaled :
        ⟪xn - zn, (γ n : ℝ)⁻¹ • (xn - zn) - gradg xn⟫_ℝ =
          (1 / (γ n : ℝ)) * ‖xn - zn‖ ^ 2 - ⟪xn - zn, gradg xn⟫_ℝ := by
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
      simp [one_div]
    rw [hscaled]
    have htmp' :
        (‖xn - zn‖ ^ 2 - (γ n : ℝ) * ⟪xn - zn, gradg xn⟫_ℝ) / (γ n : ℝ) ≤
          (f xn : EReal).toReal - (f zn : EReal).toReal := by
      refine (div_le_iff₀ hγ_pos).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
    have hdiv_eq :
        (‖xn - zn‖ ^ 2 - (γ n : ℝ) * ⟪xn - zn, gradg xn⟫_ℝ) / (γ n : ℝ) =
          (1 / (γ n : ℝ)) * ‖xn - zn‖ ^ 2 - ⟪xn - zn, gradg xn⟫_ℝ := by
      field_simp [show (γ n : ℝ) ≠ 0 from ne_of_gt hγ_pos]
    rw [← hdiv_eq]
    exact htmp'
  have hinner_eq :
      ⟪xn - zn, (γ n : ℝ)⁻¹ • (xn - zn) - gradg xn⟫_ℝ =
        (1 / (γ n : ℝ)) * ‖zn - xn‖ ^ 2 + ⟪zn - xn, gradg xn⟫_ℝ := by
    calc
      ⟪xn - zn, (γ n : ℝ)⁻¹ • (xn - zn) - gradg xn⟫_ℝ
          = ⟪xn - zn, (γ n : ℝ)⁻¹ • (xn - zn)⟫_ℝ - ⟪xn - zn, gradg xn⟫_ℝ := by
              rw [inner_sub_right]
      _ = ((γ n : ℝ)⁻¹) * ‖xn - zn‖ ^ 2 - ⟪xn - zn, gradg xn⟫_ℝ := by
            rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      _ = (1 / (γ n : ℝ)) * ‖xn - zn‖ ^ 2 - ⟪xn - zn, gradg xn⟫_ℝ := by
            simp [one_div]
      _ = (1 / (γ n : ℝ)) * ‖zn - xn‖ ^ 2 + ⟪zn - xn, gradg xn⟫_ℝ := by
            rw [norm_sub_rev, sub_eq_add_neg]
            have hinner_neg : -⟪xn - zn, gradg xn⟫_ℝ = ⟪zn - xn, gradg xn⟫_ℝ := by
              have hsub : zn - xn = -(xn - zn) := by
                abel_nf
              rw [hsub, inner_neg_left]
            rw [hinner_neg]
  have hprox_drop :
      (f zn : EReal).toReal ≤
        (f xn : EReal).toReal -
          (1 / (γ n : ℝ)) * ‖zn - xn‖ ^ 2 -
            ⟪zn - xn, gradg xn⟫_ℝ := by
    rw [hinner_eq] at hprox_real
    linarith
  let βInv : Set.Ioi (0 : ℝ) := ⟨(β : ℝ)⁻¹, by
    change 0 < (β : ℝ)⁻¹
    exact inv_pos.mpr β.2⟩
  have hdesc_aux :
      g zn ≤ g xn + ⟪zn - xn, gradg xn⟫_ℝ + ((βInv : ℝ) / 2) * ‖zn - xn‖ ^ 2 := by
    -- Use the Chapter 18 quadratic model at `x_n` and then normalize the coefficient.
    have hmodel :=
      le_gradient_quadratic_model_of_differentiable_convex_lipschitzGradient
        (f := g) (x := xn) (β := βInv) hdiff hconv
        (by simpa [βInv, hgrad_eq] using hgrad_lipschitz) zn
    rw [gradientAffineModel, hgrad_eq, ContinuousLinearMap.quadraticPotential_apply,
      ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] at hmodel
    simpa [sub_eq_add_neg, norm_sub_rev, pow_two, div_eq_mul_inv, add_assoc, add_left_comm,
      add_comm, mul_assoc, mul_left_comm, mul_comm] using hmodel
  have hbetaInv_half : ((βInv : ℝ) / 2) = 1 / (2 * (β : ℝ)) := by
    change ((β : ℝ)⁻¹) / 2 = 1 / (2 * (β : ℝ))
    field_simp [show (β : ℝ) ≠ 0 from ne_of_gt β.2]
  have hdesc :
      g zn ≤ g xn + ⟪zn - xn, gradg xn⟫_ℝ + (1 / (2 * (β : ℝ))) * ‖zn - xn‖ ^ 2 := by
    simpa [hbetaInv_half] using hdesc_aux
  have hobj_zn :
      (h zn).toReal = (f zn : EReal).toReal + g zn := by
    rw [objectiveToReal_eq_fToReal_add_g_of_mem_effectiveDomain (g := g) hzn_dom]
  have hobj_xn :
      (h xn).toReal = (f xn : EReal).toReal + g xn := by
    rw [objectiveToReal_eq_fToReal_add_g_of_mem_effectiveDomain (g := g) hxn_dom]
  -- Add the proximal descent and the smooth descent so the linear term cancels exactly.
  have hfinal :
      (h zn).toReal ≤ (h xn).toReal -
        ((1 / (γ n : ℝ)) - 1 / (2 * (β : ℝ))) * ‖zn - xn‖ ^ 2 := by
    rw [hobj_zn, hobj_xn]
    linarith [hprox_drop, hdesc]
  simpa [h, xn, zn] using hfinal

/-- Helper for Proposition 28.13: each backward-point objective gap is bounded by the step norm
with an orbit-uniform constant coming from Fejér boundedness around a fixed minimizer. -/
lemma backwardPointObjectiveGap_le_stepNorm_of_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    (ε : Set.Ioo (0 : ℝ) (min 1 (β : ℝ))) {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (ε : ℝ) (2 * (β : ℝ) - (ε : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (ε : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) (hx0 : x0 ∈ dom f)
    {xstar : H} (hxstar : xstar ∈ Argmin ((f + g.toEReal).asEReal)) (n : ℕ) :
    0 ≤ (((f + g.toEReal).asEReal) (z hf gradg γ relax x0 n)).toReal -
        (sInf (Set.range ((f + g.toEReal).asEReal))).toReal ∧
      (((f + g.toEReal).asEReal) (z hf gradg γ relax x0 n)).toReal -
          (sInf (Set.range ((f + g.toEReal).asEReal))).toReal ≤
        (2 * ‖x0 - xstar‖ / (ε : ℝ)) *
          ‖z hf gradg γ relax x0 n - orbit hf gradg γ relax x0 n‖ := by
  -- Combine the support inequality for `g` with the proximal inequality and Fejér boundedness.
  let h := ((f + g.toEReal).asEReal)
  let xn := orbit hf gradg γ relax x0 n
  let yn := y hf gradg γ relax x0 n
  let zn := z hf gradg γ relax x0 n
  rcases orbit_mem_dom_and_z_mem_dom hf gradg γ
      (fun k ↦ by
        constructor
        · exact le_trans ε.2.1.le (hrelax_bounds k).1
        · exact (hrelax_bounds k).2)
      x0 hx0 n with ⟨hxn_dom, hzn_dom⟩
  have hdiff : Differentiable ℝ g := fun x ↦ (hgrad x).differentiableAt
  have hconv : _root_.ConvexOn ℝ Set.univ g := by
    simpa [Function.effectiveDomain_toEReal] using hg.2.toReal_convexOn_effectiveDomain
  have hgrad_eq : ∇ g = gradg := by
    apply gradient_eq
    intro x
    simpa using hgrad x
  have hfg : f + g.toEReal ∈ Γ₀(H) := by
    refine pointwiseAdd_mem_gammaZero f g.toEReal hf hg ?_
    exact ⟨x0, hx0, by simp [Function.effectiveDomain_toEReal]⟩
  have hxstar_dom_h : xstar ∈ effectiveDomain (f + g.toEReal) := by
    exact mem_dom_of_mem_argmin_of_isProper (isProper_of_mem_gammaZero hfg) hxstar
  have hxstar_dom : xstar ∈ effectiveDomain f := by
    rw [mem_effectiveDomain_iff]
    have hsum_top : ((f xstar : EReal) + (g xstar : EReal)) < ⊤ := by
      simpa [Function.effectiveDomain_toEReal, Function.toEReal_apply] using hxstar_dom_h
    refine lt_top_iff_ne_top.mpr ?_
    intro htop
    have hsum_eq_top : ((f xstar : EReal) + (g xstar : EReal)) = ⊤ := by
      simpa [htop] using EReal.add_top_of_ne_bot (EReal.coe_ne_bot (g xstar))
    exact (ne_of_lt hsum_top) hsum_eq_top
  have hxstar_top : (h xstar : EReal) ≠ ⊤ := by
    exact ne_of_lt (by simpa [h, Function.asEReal] using (mem_effectiveDomain_iff.mp hxstar_dom_h))
  have hxstar_bot : (h xstar : EReal) ≠ ⊥ := by
    exact ne_of_gt (by
      simpa [h, Function.asEReal] using
        (show (⊥ : EReal) < ((f + g.toEReal) xstar : EReal) from ((f + g.toEReal) xstar).2))
  have hzn_top : (h zn : EReal) ≠ ⊤ := by
    have hzn_dom_h : zn ∈ effectiveDomain (f + g.toEReal) := by
      rw [mem_effectiveDomain_iff]
      exact EReal.add_lt_top (ne_of_lt (mem_effectiveDomain_iff.mp hzn_dom)) (EReal.coe_ne_top _)
    exact ne_of_lt (by simpa [h, Function.asEReal] using (mem_effectiveDomain_iff.mp hzn_dom_h))
  have hzn_bot : (h zn : EReal) ≠ ⊥ := by
    exact ne_of_gt (by
      simpa [h, Function.asEReal] using
        (show (⊥ : EReal) < ((f + g.toEReal) zn : EReal) from ((f + g.toEReal) zn).2))
  have hmin_le : h xstar ≤ h zn := by
    have hxstar_min : IsMinOn h Set.univ xstar := (mem_argmin_iff).1 hxstar
    rw [isMinOn_univ_iff] at hxstar_min
    exact hxstar_min zn
  have hgap_nonneg :
      0 ≤ (h zn).toReal - (sInf (Set.range h)).toReal := by
    rw [← (mem_argmin_iff_eq_sInf).1 hxstar]
    have htoReal : (h xstar).toReal ≤ (h zn).toReal := by
      exact EReal.toReal_le_toReal hmin_le hxstar_bot hzn_top
    exact sub_nonneg.mpr htoReal
  have hstep_nonexp :
      ‖zn - xstar‖ ≤ ‖xn - xstar‖ := by
    simpa [xn, zn] using
      step_dist_le_of_mem_argmin hf g hg gradg hgrad β
        (fun k ↦ by
          constructor
          · exact le_trans ε.2.1.le (hγ_bounds k).1
          · nlinarith [(hγ_bounds k).2, ε.2.1])
        hgrad_lipschitz hxstar n xn
  have hfejer :
      FejerMonotone (Argmin h) (orbit hf gradg γ relax x0) :=
    orbit_fejerMonotone_argmin hf g hg gradg hgrad β
      (fun k ↦ by
        constructor
        · exact le_trans ε.2.1.le (hγ_bounds k).1
        · nlinarith [(hγ_bounds k).2, ε.2.1])
      (fun k ↦ by
        constructor
        · exact le_trans ε.2.1.le (hrelax_bounds k).1
        · exact (hrelax_bounds k).2)
      hgrad_lipschitz x0
  have horbit_bound : ‖xn - xstar‖ ≤ ‖x0 - xstar‖ := by
    simpa [xn, dist_eq_norm] using hfejer.dist_antitone_of_mem hxstar (Nat.zero_le n)
  have hdist_bound : ‖zn - xstar‖ ≤ ‖x0 - xstar‖ := le_trans hstep_nonexp horbit_bound
  let hγf : (γ n) • f ∈ Γ₀(H) := smul_mem_gammaZero f hf (γ n)
  have hprox :
      IsProxPoint (((γ n) • f : H → Set.Ioi (⊥ : EReal))) yn zn := by
    -- Read the current backward point as the proximal point of `γ_n • f` at `y_n`.
    simpa [yn, zn, scaledProximityOperator] using
      proximityOperator_isProxPoint
        (((γ n) • f : H → Set.Ioi (⊥ : EReal)))
        (hasUniqueProxPoint_of_mem_gammaZero (((γ n) • f : H → Set.Ioi (⊥ : EReal))) hγf) yn
  have hprox_real :
      ⟪xstar - zn, (γ n : ℝ)⁻¹ • (xn - zn) - gradg xn⟫_ℝ ≤
        (f xstar : EReal).toReal - (f zn : EReal).toReal := by
    -- Convert the proximal inequality to the normalized source form.
    have hxstar_dom_scaled :
        xstar ∈ effectiveDomain (((γ n) • f : H → Set.Ioi (⊥ : EReal))) := by
      exact (mem_effectiveDomain_posReal_smul_iff (f := f) (γ := γ n) xstar).2 hxstar_dom
    have hraw :
        ⟪xstar - zn, yn - zn⟫_ℝ + (γ n : ℝ) * (f zn : EReal).toReal ≤
          (γ n : ℝ) * (f xstar : EReal).toReal := by
      have hxstar_top : (f xstar : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hxstar_dom)
      have hxstar_bot_f : (f xstar : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f xstar : EReal) from (f xstar).2)
      have hzn_top_f : (f zn : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hzn_dom)
      have hzn_bot_f : (f zn : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f zn : EReal) from (f zn).2)
      simpa [yn, zn, posReal_smul_apply, EReal.toReal_mul, EReal.toReal_coe,
        hxstar_top, hxstar_bot_f, hzn_top_f, hzn_bot_f] using
        inner_add_toReal_le_toReal_of_isProxPoint_of_mem_gammaZero
          (g := ((γ n) • f : H → Set.Ioi (⊥ : EReal))) hγf hprox hxstar_dom_scaled
    have hy_simple :
        yn - zn = (xn - zn) - (γ n : ℝ) • gradg xn := by
      dsimp [yn, xn]
      abel_nf
    rw [hy_simple, inner_sub_right, real_inner_smul_right] at hraw
    have hγ_pos : 0 < (γ n : ℝ) := (γ n).2
    have htmp :
        ⟪xstar - zn, xn - zn⟫_ℝ - (γ n : ℝ) * ⟪xstar - zn, gradg xn⟫_ℝ ≤
          (γ n : ℝ) * ((f xstar : EReal).toReal - (f zn : EReal).toReal) := by
      nlinarith [hraw]
    have hscaled :
        ⟪xstar - zn, (γ n : ℝ)⁻¹ • (xn - zn) - gradg xn⟫_ℝ =
          (1 / (γ n : ℝ)) * ⟪xstar - zn, xn - zn⟫_ℝ - ⟪xstar - zn, gradg xn⟫_ℝ := by
      rw [inner_sub_right, real_inner_smul_right]
      simp [one_div]
    rw [hscaled]
    have htmp' :
        (⟪xstar - zn, xn - zn⟫_ℝ - (γ n : ℝ) * ⟪xstar - zn, gradg xn⟫_ℝ) / (γ n : ℝ) ≤
          (f xstar : EReal).toReal - (f zn : EReal).toReal := by
      refine (div_le_iff₀ hγ_pos).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
    have hdiv_eq :
        (⟪xstar - zn, xn - zn⟫_ℝ - (γ n : ℝ) * ⟪xstar - zn, gradg xn⟫_ℝ) / (γ n : ℝ) =
          (1 / (γ n : ℝ)) * ⟪xstar - zn, xn - zn⟫_ℝ - ⟪xstar - zn, gradg xn⟫_ℝ := by
      field_simp [show (γ n : ℝ) ≠ 0 from ne_of_gt hγ_pos]
    rw [← hdiv_eq]
    exact htmp'
  have hgrad_support :
      ⟪xstar - zn, gradg zn⟫_ℝ + g zn ≤ g xstar := by
    -- The convex support inequality for `g` at `z_n` compares the minimizer to the backward point.
    simpa [gradientAffineModel, hgrad_eq, add_comm, add_left_comm, add_assoc] using
      gradient_affine_model_le_of_differentiable_convex
        (f := g) (x := zn) hdiff hconv xstar
  have hgap_est :
      (h zn).toReal - (h xstar).toReal ≤
        ‖xstar - zn‖ * ‖zn - xn‖ * ((β : ℝ)⁻¹ + (γ n : ℝ)⁻¹) := by
    -- Add the proximal and smooth inequalities, then bound the resulting negative inner terms by
    -- absolute values and norm estimates.
    have hlip :
        ‖gradg zn - gradg xn‖ ≤ (β : ℝ)⁻¹ * ‖zn - xn‖ := by
      simpa [dist_eq_norm, Real.toNNReal_of_nonneg (inv_nonneg.mpr β.2.le)] using
        hgrad_lipschitz.dist_le_mul zn xn
    have hterm1 :
        |⟪xstar - zn, gradg zn - gradg xn⟫_ℝ| ≤
          ‖xstar - zn‖ * ((β : ℝ)⁻¹ * ‖zn - xn‖) := by
      exact le_trans (abs_real_inner_le_norm _ _) (mul_le_mul_of_nonneg_left hlip (norm_nonneg _))
    have hterm2 :
        |⟪xstar - zn, (γ n : ℝ)⁻¹ • (xn - zn)⟫_ℝ| ≤
          ‖xstar - zn‖ * ((γ n : ℝ)⁻¹ * ‖zn - xn‖) := by
      calc
        |⟪xstar - zn, (γ n : ℝ)⁻¹ • (xn - zn)⟫_ℝ|
            ≤ ‖xstar - zn‖ * ‖(γ n : ℝ)⁻¹ • (xn - zn)‖ := by
                exact abs_real_inner_le_norm _ _
        _ = ‖xstar - zn‖ * ((γ n : ℝ)⁻¹ * ‖xn - zn‖) := by
              rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (γ n).2.le)]
        _ = ‖xstar - zn‖ * ((γ n : ℝ)⁻¹ * ‖zn - xn‖) := by
              simpa [norm_sub_rev]
    have hsum :
        (f zn : EReal).toReal + g zn - ((f xstar : EReal).toReal + g xstar) ≤
          -(⟪xstar - zn, gradg zn - gradg xn⟫_ℝ +
            ⟪xstar - zn, (γ n : ℝ)⁻¹ • (xn - zn)⟫_ℝ) := by
      have hsum_base :
          ⟪xstar - zn, (γ n : ℝ)⁻¹ • (xn - zn) - gradg xn⟫_ℝ +
              (⟪xstar - zn, gradg zn⟫_ℝ + g zn) ≤
            (f xstar : EReal).toReal - (f zn : EReal).toReal + g xstar := by
        linarith [hprox_real, hgrad_support]
      have hrew :
          ⟪xstar - zn, (γ n : ℝ)⁻¹ • (xn - zn) - gradg xn⟫_ℝ +
              ⟪xstar - zn, gradg zn⟫_ℝ =
            ⟪xstar - zn, (γ n : ℝ)⁻¹ • (xn - zn)⟫_ℝ +
              ⟪xstar - zn, gradg zn - gradg xn⟫_ℝ := by
        rw [inner_sub_right, inner_sub_right]
        ring
      have hsum_base' :
          (⟪xstar - zn, (γ n : ℝ)⁻¹ • (xn - zn)⟫_ℝ +
              ⟪xstar - zn, gradg zn - gradg xn⟫_ℝ) + g zn ≤
            (f xstar : EReal).toReal - (f zn : EReal).toReal + g xstar := by
        nlinarith [hprox_real, hgrad_support, hrew]
      nlinarith [hsum_base']
    have hsum' :
        (f zn : EReal).toReal + g zn - ((f xstar : EReal).toReal + g xstar) ≤
          ‖xstar - zn‖ * ((β : ℝ)⁻¹ * ‖zn - xn‖) +
            ‖xstar - zn‖ * ((γ n : ℝ)⁻¹ * ‖zn - xn‖) := by
      have habs :
          -(⟪xstar - zn, gradg zn - gradg xn⟫_ℝ +
              ⟪xstar - zn, (γ n : ℝ)⁻¹ • (xn - zn)⟫_ℝ) ≤
            |⟪xstar - zn, gradg zn - gradg xn⟫_ℝ| +
              |⟪xstar - zn, (γ n : ℝ)⁻¹ • (xn - zn)⟫_ℝ| := by
        have hneg1 :
            -⟪xstar - zn, gradg zn - gradg xn⟫_ℝ ≤
              |⟪xstar - zn, gradg zn - gradg xn⟫_ℝ| := neg_le_abs _
        have hneg2 :
            -⟪xstar - zn, (γ n : ℝ)⁻¹ • (xn - zn)⟫_ℝ ≤
              |⟪xstar - zn, (γ n : ℝ)⁻¹ • (xn - zn)⟫_ℝ| := neg_le_abs _
        nlinarith
      exact le_trans hsum <| le_trans habs (add_le_add hterm1 hterm2)
    have hobj_zn :
        (h zn).toReal = (f zn : EReal).toReal + g zn := by
      rw [objectiveToReal_eq_fToReal_add_g_of_mem_effectiveDomain (g := g) hzn_dom]
    have hobj_xstar :
        (h xstar).toReal = (f xstar : EReal).toReal + g xstar := by
      rw [objectiveToReal_eq_fToReal_add_g_of_mem_effectiveDomain (g := g) hxstar_dom]
    have hgap_est :
        (h zn).toReal - (h xstar).toReal ≤
          ‖xstar - zn‖ * ((β : ℝ)⁻¹ * ‖zn - xn‖) +
            ‖xstar - zn‖ * ((γ n : ℝ)⁻¹ * ‖zn - xn‖) := by
      rw [hobj_zn, hobj_xstar]
      exact hsum'
    have hfactor :
        ‖xstar - zn‖ * ((β : ℝ)⁻¹ * ‖zn - xn‖) +
            ‖xstar - zn‖ * ((γ n : ℝ)⁻¹ * ‖zn - xn‖) =
          ‖xstar - zn‖ * ‖zn - xn‖ * ((β : ℝ)⁻¹ + (γ n : ℝ)⁻¹) := by
      ring
    calc
      (h zn).toReal - (h xstar).toReal
          ≤ ‖xstar - zn‖ * ((β : ℝ)⁻¹ * ‖zn - xn‖) +
              ‖xstar - zn‖ * ((γ n : ℝ)⁻¹ * ‖zn - xn‖) := hgap_est
      _ = ‖xstar - zn‖ * ‖zn - xn‖ * ((β : ℝ)⁻¹ + (γ n : ℝ)⁻¹) := hfactor
  have hcoeff :
      (β : ℝ)⁻¹ + (γ n : ℝ)⁻¹ ≤ 2 / (ε : ℝ) := by
    have hε_lt_beta : (ε : ℝ) < (β : ℝ) := lt_of_lt_of_le ε.2.2 (min_le_right _ _)
    have hβinv : (β : ℝ)⁻¹ ≤ (ε : ℝ)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le ε.2.1 hε_lt_beta.le
    have hγinv : (γ n : ℝ)⁻¹ ≤ (ε : ℝ)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le ε.2.1 (hγ_bounds n).1
    calc
      (β : ℝ)⁻¹ + (γ n : ℝ)⁻¹ ≤ (ε : ℝ)⁻¹ + (ε : ℝ)⁻¹ := add_le_add hβinv hγinv
      _ = 2 / (ε : ℝ) := by
        field_simp [show (ε : ℝ) ≠ 0 from ne_of_gt ε.2.1]
        ring
  have hgap_bound :
      (h zn).toReal - (sInf (Set.range h)).toReal ≤
        (2 * ‖x0 - xstar‖ / (ε : ℝ)) * ‖zn - xn‖ := by
    rw [← (mem_argmin_iff_eq_sInf).1 hxstar]
    have hdist_nonneg : 0 ≤ ‖xstar - zn‖ := norm_nonneg _
    have hstep_nonneg : 0 ≤ ‖zn - xn‖ := norm_nonneg _
    have hdist_bound' : ‖xstar - zn‖ ≤ ‖x0 - xstar‖ := by
      simpa [norm_sub_rev] using hdist_bound
    have hcoeff_nonneg :
        0 ≤ (β : ℝ)⁻¹ + (γ n : ℝ)⁻¹ := by
      have hβinv_nonneg : 0 ≤ (β : ℝ)⁻¹ := by
        exact inv_nonneg.mpr β.2.le
      have hγinv_nonneg : 0 ≤ (γ n : ℝ)⁻¹ := by
        exact inv_nonneg.mpr (γ n).2.le
      nlinarith
    have hbound_coeff :
        ‖xstar - zn‖ * ((β : ℝ)⁻¹ + (γ n : ℝ)⁻¹) ≤
          ‖x0 - xstar‖ * (2 / (ε : ℝ)) := by
      exact mul_le_mul hdist_bound' hcoeff hcoeff_nonneg (norm_nonneg _)
    have hbound1 :
        ‖xstar - zn‖ * ‖zn - xn‖ * ((β : ℝ)⁻¹ + (γ n : ℝ)⁻¹) ≤
          ‖x0 - xstar‖ * ‖zn - xn‖ * (2 / (ε : ℝ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hbound_coeff hstep_nonneg
    have hbound2 :
        ‖x0 - xstar‖ * ‖zn - xn‖ * (2 / (ε : ℝ)) =
          (2 * ‖x0 - xstar‖ / (ε : ℝ)) * ‖zn - xn‖ := by
      field_simp [show (ε : ℝ) ≠ 0 from ne_of_gt ε.2.1]
    exact (le_trans hgap_est hbound1).trans_eq hbound2
  exact ⟨hgap_nonneg, by simpa [h, xn, zn] using hgap_bound⟩
/-- Helper for Proposition 28.13: one convexity step packages the backward-point descent into the
real-valued telescope `orbitVal n - backVal n ≤ ε⁻¹ (orbitVal n - orbitVal (n+1))`. -/
lemma orbitValueGap_le_relaxInv_drop
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    (ε : Set.Ioo (0 : ℝ) (min 1 (β : ℝ))) {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (ε : ℝ) (2 * (β : ℝ) - (ε : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (ε : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) (hx0 : x0 ∈ dom f) (n : ℕ) :
    let h := ((f + g.toEReal).asEReal)
    let orbitVal : ℕ → ℝ := fun k ↦ (h (orbit hf gradg γ relax x0 k)).toReal
    let backVal : ℕ → ℝ := fun k ↦ (h (z hf gradg γ relax x0 k)).toReal
    0 ≤ orbitVal n - backVal n ∧
      orbitVal (n + 1) ≤ orbitVal n ∧
      orbitVal n - backVal n ≤ (ε : ℝ)⁻¹ * (orbitVal n - orbitVal (n + 1)) := by
  -- Convexity gives the one-step orbit/backward comparison, and the relaxation lower bound turns
  -- it into the telescope estimate used later.
  let h := ((f + g.toEReal).asEReal)
  let orbitVal : ℕ → ℝ := fun k ↦ (h (orbit hf gradg γ relax x0 k)).toReal
  let backVal : ℕ → ℝ := fun k ↦ (h (z hf gradg γ relax x0 k)).toReal
  let xn := orbit hf gradg γ relax x0 n
  let zn := z hf gradg γ relax x0 n
  let xn1 := orbit hf gradg γ relax x0 (n + 1)
  rcases orbit_mem_dom_and_z_mem_dom hf gradg γ
      (fun k ↦ by
        constructor
        · exact le_trans ε.2.1.le (hrelax_bounds k).1
        · exact (hrelax_bounds k).2)
      x0 hx0 n with ⟨hxn_dom, hzn_dom⟩
  rcases orbit_mem_dom_and_z_mem_dom hf gradg γ
      (fun k ↦ by
        constructor
        · exact le_trans ε.2.1.le (hrelax_bounds k).1
        · exact (hrelax_bounds k).2)
      x0 hx0 (n + 1) with ⟨hxn1_dom, _⟩
  have hconvg : _root_.ConvexOn ℝ Set.univ g := by
    simpa [Function.effectiveDomain_toEReal] using hg.2.toReal_convexOn_effectiveDomain
  have hconvf : _root_.ConvexOn ℝ (effectiveDomain f) (fun x : H ↦ (f x : EReal).toReal) := by
    exact hf.2.toReal_convexOn_effectiveDomain
  have hxn_top : (f xn : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hxn_dom)
  have hxn_bot : (f xn : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f xn : EReal) from (f xn).2)
  have hzn_top : (f zn : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hzn_dom)
  have hzn_bot : (f zn : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f zn : EReal) from (f zn).2)
  have hcoeff_nonneg : 0 ≤ (1 / (γ n : ℝ)) - 1 / (2 * (β : ℝ)) := by
    have hγ_le_two_beta : (γ n : ℝ) ≤ 2 * (β : ℝ) := by
      nlinarith [(hγ_bounds n).2, ε.2.1]
    have htwo_beta_inv_le : 1 / (2 * (β : ℝ)) ≤ 1 / (γ n : ℝ) := by
      exact one_div_le_one_div_of_le (γ n).2 hγ_le_two_beta
    nlinarith
  have hback_le_orbit : backVal n ≤ orbitVal n := by
    -- Drop the nonnegative quadratic term from the backward-point descent estimate.
    have hdrop :=
      stageObjectiveDrop_atBackwardPoint
        hf g hg gradg hgrad β
        (fun k ↦ by
          constructor
          · exact le_trans ε.2.1.le (hγ_bounds k).1
          · nlinarith [(hγ_bounds k).2, ε.2.1])
        (fun k ↦ by
          constructor
          · exact le_trans ε.2.1.le (hrelax_bounds k).1
          · exact (hrelax_bounds k).2)
        hgrad_lipschitz x0 hx0 n
    have hstep_nonneg :
        0 ≤ ((1 / (γ n : ℝ)) - 1 / (2 * (β : ℝ))) * ‖zn - xn‖ ^ 2 := by
      nlinarith [hcoeff_nonneg, sq_nonneg ‖zn - xn‖]
    dsimp [orbitVal, backVal, h, xn, zn] at hdrop ⊢
    nlinarith
  have horbit_conv_step :
      orbitVal (n + 1) ≤ (1 - relax n) * orbitVal n + relax n * backVal n := by
    -- Convexity of `f` and `g` on the orbit/backward pair gives the textbook orbit-value bound.
    have hnext :
        xn1 = (1 - relax n) • xn + relax n • zn := by
      dsimp [xn, zn, xn1]
      calc
        orbit hf gradg γ relax x0 (n + 1)
            = orbit hf gradg γ relax x0 n +
                relax n •
                  (z hf gradg γ relax x0 n - orbit hf gradg γ relax x0 n) := by
                    simpa using orbit_succ (hf := hf) (gradg := gradg) (γ := γ)
                      (relax := relax) (x0 := x0) n
        _ =
          orbit hf gradg γ relax x0 n +
            (relax n • z hf gradg γ relax x0 n -
              relax n • orbit hf gradg γ relax x0 n) := by
                rw [smul_sub]
        _ =
          (1 - relax n) • orbit hf gradg γ relax x0 n +
            relax n • z hf gradg γ relax x0 n := by
              rw [sub_eq_add_neg, sub_smul, one_smul]
              abel_nf
    have hfineq :
        (f xn1 : EReal).toReal ≤
          (1 - relax n) * (f xn : EReal).toReal + relax n * (f zn : EReal).toReal := by
      rw [hnext]
      exact hconvf.2 hxn_dom hzn_dom
        (sub_nonneg.mpr (hrelax_bounds n).2) (le_trans ε.2.1.le (hrelax_bounds n).1) (by ring)
    have hgineq :
        g xn1 ≤ (1 - relax n) * g xn + relax n * g zn := by
      rw [hnext]
      exact hconvg.2 (by simp) (by simp)
        (sub_nonneg.mpr (hrelax_bounds n).2) (le_trans ε.2.1.le (hrelax_bounds n).1) (by ring)
    have hxn1_top : (f xn1 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hxn1_dom)
    have hxn1_bot : (f xn1 : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f xn1 : EReal) from (f xn1).2)
    have hobj_xn1 :
        (((f xn1 : EReal) + (g xn1 : EReal)).toReal) = (f xn1 : EReal).toReal + g xn1 := by
      simpa [Function.toEReal_apply] using
        (EReal.toReal_add hxn1_top hxn1_bot (by simp) (by simp) :
          (((f xn1 : EReal) + (g xn1 : EReal)).toReal =
            (f xn1 : EReal).toReal + (g xn1 : EReal).toReal))
    have hobj_xn :
        (((f xn : EReal) + (g xn : EReal)).toReal) = (f xn : EReal).toReal + g xn := by
      simpa [Function.toEReal_apply] using
        (EReal.toReal_add hxn_top hxn_bot (by simp) (by simp) :
          (((f xn : EReal) + (g xn : EReal)).toReal =
            (f xn : EReal).toReal + (g xn : EReal).toReal))
    have hobj_zn :
        (((f zn : EReal) + (g zn : EReal)).toReal) = (f zn : EReal).toReal + g zn := by
      simpa [Function.toEReal_apply] using
        (EReal.toReal_add hzn_top hzn_bot (by simp) (by simp) :
          (((f zn : EReal) + (g zn : EReal)).toReal =
            (f zn : EReal).toReal + (g zn : EReal).toReal))
    have hobj_back :
        (((f (z hf gradg γ relax x0 n) : EReal) + (g (z hf gradg γ relax x0 n) : EReal)).toReal) =
          (f zn : EReal).toReal + g zn := by
      simpa [zn] using hobj_zn
    have hobj_back_explicit :
        (((f (Prox[γ n, f, hf]
              (orbit hf gradg γ relax x0 n - (γ n : ℝ) • gradg (orbit hf gradg γ relax x0 n))) :
              EReal) +
            (g (Prox[γ n, f, hf]
              (orbit hf gradg γ relax x0 n - (γ n : ℝ) • gradg (orbit hf gradg γ relax x0 n))) :
              EReal)).toReal) =
          (f zn : EReal).toReal + g zn := by
      simpa [zn, z_eq, y_eq] using hobj_zn
    dsimp [orbitVal, backVal, h, xn, xn1]
    rw [hobj_xn1, hobj_xn, hobj_back_explicit]
    nlinarith
  have horbit_succ_le : orbitVal (n + 1) ≤ orbitVal n := by
    -- Replace the backward-point value by the smaller orbit value from the stage descent.
    have hrelax_nonneg : 0 ≤ relax n := le_trans ε.2.1.le (hrelax_bounds n).1
    have hweighted :
        relax n * backVal n ≤ relax n * orbitVal n := by
      exact mul_le_mul_of_nonneg_left hback_le_orbit hrelax_nonneg
    nlinarith [horbit_conv_step, hweighted]
  have hgap_nonneg : 0 ≤ orbitVal n - backVal n := sub_nonneg.mpr hback_le_orbit
  have hscaled_gap :
      (ε : ℝ) * (orbitVal n - backVal n) ≤ orbitVal n - orbitVal (n + 1) := by
    -- Compare the relaxation weight against `ε`, then rewrite the convexity step as a drop.
    have hrelax_mul :
        (ε : ℝ) * (orbitVal n - backVal n) ≤
          relax n * (orbitVal n - backVal n) := by
      exact mul_le_mul_of_nonneg_right (hrelax_bounds n).1 hgap_nonneg
    have hdrop :
        relax n * (orbitVal n - backVal n) ≤ orbitVal n - orbitVal (n + 1) := by
      nlinarith [horbit_conv_step]
    exact le_trans hrelax_mul hdrop
  have hgap_le :
      orbitVal n - backVal n ≤ (ε : ℝ)⁻¹ * (orbitVal n - orbitVal (n + 1)) := by
    have hscaled_gap' :
        (orbitVal n - backVal n) * (ε : ℝ) ≤ orbitVal n - orbitVal (n + 1) := by
      simpa [mul_comm] using hscaled_gap
    have := (le_div_iff₀ ε.2.1).2 hscaled_gap'
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  exact ⟨hgap_nonneg, horbit_succ_le, hgap_le⟩

/-- Helper for Proposition 28.13: the orbit/backward objective-value gap is summable, its square is
summable, and the orbit objective values are antitone. -/
lemma orbitValueGap_sqSummable
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    (ε : Set.Ioo (0 : ℝ) (min 1 (β : ℝ))) {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (ε : ℝ) (2 * (β : ℝ) - (ε : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (ε : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) (hx0 : x0 ∈ dom f)
    (hargmin : (Argmin ((f + g.toEReal).asEReal)).Nonempty) :
    Summable
      (fun n : ℕ ↦
        (((f + g.toEReal).asEReal) (orbit hf gradg γ relax x0 n)).toReal -
          (((f + g.toEReal).asEReal) (z hf gradg γ relax x0 n)).toReal) ∧
    Summable
      (fun n : ℕ ↦
        ((((f + g.toEReal).asEReal) (orbit hf gradg γ relax x0 n)).toReal -
          (((f + g.toEReal).asEReal) (z hf gradg γ relax x0 n)).toReal) ^ 2) ∧
    Antitone
      (fun n : ℕ ↦ (((f + g.toEReal).asEReal) (orbit hf gradg γ relax x0 n)).toReal) := by
  let h := ((f + g.toEReal).asEReal)
  let orbitVal : ℕ → ℝ := fun k ↦ (h (orbit hf gradg γ relax x0 k)).toReal
  let backVal : ℕ → ℝ := fun k ↦ (h (z hf gradg γ relax x0 k)).toReal
  let m : ℝ := (sInf (Set.range h)).toReal
  rcases hargmin with ⟨xstar, hxstar⟩
  have hfg : f + g.toEReal ∈ Γ₀(H) := by
    refine pointwiseAdd_mem_gammaZero f g.toEReal hf hg ?_
    exact ⟨x0, hx0, by simp [Function.effectiveDomain_toEReal]⟩
  have hxstar_dom_h : xstar ∈ effectiveDomain (f + g.toEReal) := by
    exact mem_dom_of_mem_argmin_of_isProper (isProper_of_mem_gammaZero hfg) hxstar
  have hxstar_top : (h xstar : EReal) ≠ ⊤ := by
    exact ne_of_lt (by simpa [h, Function.asEReal] using (mem_effectiveDomain_iff.mp hxstar_dom_h))
  have hxstar_bot : (h xstar : EReal) ≠ ⊥ := by
    exact ne_of_gt (by
      simpa [h, Function.asEReal] using
        (show (⊥ : EReal) < ((f + g.toEReal) xstar : EReal) from ((f + g.toEReal) xstar).2))
  have horbit_mem_dom_h :
      ∀ n : ℕ, orbit hf gradg γ relax x0 n ∈ effectiveDomain (f + g.toEReal) := by
    intro n
    rcases orbit_mem_dom_and_z_mem_dom hf gradg γ
        (fun k ↦ by
          constructor
          · exact le_trans ε.2.1.le (hrelax_bounds k).1
          · exact (hrelax_bounds k).2)
        x0 hx0 n with ⟨hxn_dom, _⟩
    have hxn_top : (f (orbit hf gradg γ relax x0 n) : EReal) ≠ ⊤ :=
      ne_of_lt (mem_effectiveDomain_iff.mp hxn_dom)
    have hsum_top :
        (((f (orbit hf gradg γ relax x0 n) : EReal) +
            (g (orbit hf gradg γ relax x0 n) : EReal)) : EReal) < ⊤ :=
      EReal.add_lt_top hxn_top (EReal.coe_ne_top _)
    simpa [mem_effectiveDomain_iff, Function.toEReal_apply] using hsum_top
  have horbit_top :
      ∀ n : ℕ, (h (orbit hf gradg γ relax x0 n) : EReal) ≠ ⊤ := by
    intro n
    exact ne_of_lt (by
      simpa [h, Function.asEReal] using (mem_effectiveDomain_iff.mp (horbit_mem_dom_h n)))
  have horbit_bot :
      ∀ n : ℕ, (h (orbit hf gradg γ relax x0 n) : EReal) ≠ ⊥ := by
    intro n
    exact ne_of_gt (by
      simpa [h, Function.asEReal] using
        (show (⊥ : EReal) < ((f + g.toEReal) (orbit hf gradg γ relax x0 n) : EReal) from
          ((f + g.toEReal) (orbit hf gradg γ relax x0 n)).2))
  have hm_le_orbit :
      ∀ n : ℕ, m ≤ orbitVal n := by
    intro n
    have hmin :
        h xstar ≤ h (orbit hf gradg γ relax x0 n) :=
      (isMinOn_univ_iff.mp ((mem_argmin_iff).mp hxstar)) _
    dsimp [m, orbitVal]
    rw [← (mem_argmin_iff_eq_sInf).1 hxstar]
    exact EReal.toReal_le_toReal hmin hxstar_bot (horbit_top n)
  have hgap_nonneg :
      ∀ n : ℕ, 0 ≤ orbitVal n - backVal n := by
    intro n
    have hstep :=
      orbitValueGap_le_relaxInv_drop
        hf g hg gradg hgrad β ε hγ_bounds hrelax_bounds hgrad_lipschitz x0 hx0 n
    simpa [h, orbitVal, backVal] using hstep.1
  have horbit_succ_le :
      ∀ n : ℕ, orbitVal (n + 1) ≤ orbitVal n := by
    intro n
    have hstep :=
      orbitValueGap_le_relaxInv_drop
        hf g hg gradg hgrad β ε hγ_bounds hrelax_bounds hgrad_lipschitz x0 hx0 n
    simpa [h, orbitVal, backVal] using hstep.2.1
  have horbit_antitone : Antitone orbitVal := antitone_nat_of_succ_le horbit_succ_le
  have hgap_partial :
      ∀ N : ℕ, Finset.sum (Finset.range N) (fun k ↦ orbitVal k - backVal k) ≤
        (ε : ℝ)⁻¹ * (orbitVal 0 - m) := by
    intro N
    calc
      Finset.sum (Finset.range N) (fun k ↦ orbitVal k - backVal k)
          ≤ Finset.sum (Finset.range N)
              (fun k ↦ (ε : ℝ)⁻¹ * (orbitVal k - orbitVal (k + 1))) := by
                exact Finset.sum_le_sum fun k hk ↦ by
                  have hstep :=
                    orbitValueGap_le_relaxInv_drop
                      hf g hg gradg hgrad β ε hγ_bounds hrelax_bounds hgrad_lipschitz x0 hx0 k
                  simpa [h, orbitVal, backVal] using hstep.2.2
      _ = (ε : ℝ)⁻¹ *
            Finset.sum (Finset.range N) (fun k ↦ orbitVal k - orbitVal (k + 1)) := by
              rw [← Finset.mul_sum]
      _ = (ε : ℝ)⁻¹ * (orbitVal 0 - orbitVal N) := by
              let a : ℕ → ℝ := orbitVal
              have htel_raw := Finset.sum_range_sub a N
              rw [Finset.sum_sub_distrib] at htel_raw
              have htel_swap :
                  Finset.sum (Finset.range N) (fun i ↦ a i) -
                      Finset.sum (Finset.range N) (fun i ↦ a (i + 1)) =
                    a 0 - a N := by
                calc
                  Finset.sum (Finset.range N) (fun i ↦ a i) -
                      Finset.sum (Finset.range N) (fun i ↦ a (i + 1))
                      = -(Finset.sum (Finset.range N) (fun i ↦ a (i + 1)) -
                          Finset.sum (Finset.range N) (fun i ↦ a i)) := by
                            ring
                  _ = -(a N - a 0) := by rw [htel_raw]
                  _ = a 0 - a N := by ring
              calc
                (ε : ℝ)⁻¹ *
                    Finset.sum (Finset.range N) (fun k ↦ orbitVal k - orbitVal (k + 1))
                    =
                    (ε : ℝ)⁻¹ *
                      (Finset.sum (Finset.range N) (fun i ↦ a i) -
                        Finset.sum (Finset.range N) (fun i ↦ a (i + 1))) := by
                          rw [Finset.sum_sub_distrib]
                _ = (ε : ℝ)⁻¹ * (orbitVal 0 - orbitVal N) := by
                      simpa [a] using congrArg (fun t : ℝ ↦ (ε : ℝ)⁻¹ * t) htel_swap
      _ ≤ (ε : ℝ)⁻¹ * (orbitVal 0 - m) := by
              have hcoeff_nonneg : 0 ≤ (ε : ℝ)⁻¹ := by
                exact inv_nonneg.mpr ε.2.1.le
              have hsub : orbitVal 0 - orbitVal N ≤ orbitVal 0 - m := by
                have := hm_le_orbit N
                linarith
              exact mul_le_mul_of_nonneg_left hsub hcoeff_nonneg
  have hgap_summable :
      Summable (fun n : ℕ ↦ orbitVal n - backVal n) :=
    summable_of_sum_range_le hgap_nonneg hgap_partial
  have hgap_zero_bound : 0 ≤ orbitVal 0 - m := by
    exact sub_nonneg.mpr (hm_le_orbit 0)
  have hgap_sq_bound :
      ∀ n : ℕ, (orbitVal n - backVal n) ^ 2 ≤ (orbitVal 0 - m) * (orbitVal n - backVal n) := by
    intro n
    have hbound :
        orbitVal n - backVal n ≤ orbitVal 0 - m := by
      have hback_ge :
          m ≤ backVal n := by
        have hmin :
            h xstar ≤ h (z hf gradg γ relax x0 n) :=
          (isMinOn_univ_iff.mp ((mem_argmin_iff).mp hxstar)) _
        have hback_top : (h (z hf gradg γ relax x0 n) : EReal) ≠ ⊤ := by
          rcases orbit_mem_dom_and_z_mem_dom hf gradg γ
              (fun k ↦ by
                constructor
                · exact le_trans ε.2.1.le (hrelax_bounds k).1
                · exact (hrelax_bounds k).2)
              x0 hx0 n with ⟨_, hzn_dom⟩
          have hzn_dom_h : z hf gradg γ relax x0 n ∈ effectiveDomain (f + g.toEReal) := by
            have hzn_top' : (f (z hf gradg γ relax x0 n) : EReal) ≠ ⊤ :=
              ne_of_lt (mem_effectiveDomain_iff.mp hzn_dom)
            have hsum_top :
                (((f (z hf gradg γ relax x0 n) : EReal) +
                    (g (z hf gradg γ relax x0 n) : EReal)) : EReal) < ⊤ :=
              EReal.add_lt_top hzn_top' (EReal.coe_ne_top _)
            simpa [mem_effectiveDomain_iff, Function.toEReal_apply] using hsum_top
          exact ne_of_lt (by
            simpa [h, Function.asEReal] using (mem_effectiveDomain_iff.mp hzn_dom_h))
        change (sInf (Set.range h)).toReal ≤ backVal n
        rw [← (mem_argmin_iff_eq_sInf).1 hxstar]
        exact EReal.toReal_le_toReal hmin hxstar_bot hback_top
      have horbit0 : orbitVal n ≤ orbitVal 0 := horbit_antitone (Nat.zero_le n)
      nlinarith
    nlinarith [hgap_nonneg n, hbound]
  have hgap_sq_summable :
      Summable (fun n : ℕ ↦ (orbitVal n - backVal n) ^ 2) := by
    have hdominating :
        Summable (fun n : ℕ ↦ (orbitVal 0 - m) * (orbitVal n - backVal n)) :=
      hgap_summable.mul_left (orbitVal 0 - m)
    refine Summable.of_nonneg_of_le
      (fun n ↦ sq_nonneg (orbitVal n - backVal n)) ?_ hdominating
    intro n
    exact hgap_sq_bound n
  exact ⟨by simpa [h, orbitVal, backVal] using hgap_summable,
    by simpa [h, orbitVal, backVal] using hgap_sq_summable,
    by simpa [h, orbitVal] using horbit_antitone⟩

/-- Helper for Proposition 28.13: fixing a minimizer turns the backward-point objective gap into a
square-summable sequence by domination with the square-summable step norms from clause `(2)`. -/
lemma backwardObjectiveGap_sqSummable_of_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    (ε : Set.Ioo (0 : ℝ) (min 1 (β : ℝ))) {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (ε : ℝ) (2 * (β : ℝ) - (ε : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (ε : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) (hx0 : x0 ∈ dom f)
    {xstar : H} (hxstar : xstar ∈ Argmin ((f + g.toEReal).asEReal)) :
    Summable
      (fun n : ℕ ↦
        ((((f + g.toEReal).asEReal) (z hf gradg γ relax x0 n)).toReal -
          (sInf (Set.range ((f + g.toEReal).asEReal))).toReal) ^ 2) := by
  let h := ((f + g.toEReal).asEReal)
  let backGap : ℕ → ℝ :=
    fun n ↦ (h (z hf gradg γ relax x0 n)).toReal - (sInf (Set.range h)).toReal
  let stepSq : ℕ → ℝ :=
    fun n ↦ ‖z hf gradg γ relax x0 n - orbit hf gradg γ relax x0 n‖ ^ 2
  let c : ℝ := 2 * ‖x0 - xstar‖ / (ε : ℝ)
  have hstep_summable : Summable stepSq := by
    -- Clause `(2)` already controls the square-summable step norms.
    simpa [stepSq] using
      forwardBackward_stepDifference_summable
        hf g hg gradg hgrad β ε hγ_bounds hrelax_bounds hgrad_lipschitz x0 hx0
        ⟨xstar, hxstar⟩
  have hdominating :
      Summable (fun n : ℕ ↦ c ^ 2 * stepSq n) :=
    hstep_summable.mul_left (c ^ 2)
  refine Summable.of_nonneg_of_le
    (fun n ↦ sq_nonneg (backGap n)) ?_ hdominating
  intro n
  rcases
      backwardPointObjectiveGap_le_stepNorm_of_mem_argmin
        hf g hg gradg hgrad β ε hγ_bounds hrelax_bounds hgrad_lipschitz x0 hx0 hxstar n
    with ⟨hback_nonneg, hback_le⟩
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (by positivity) ε.2.1.le
  have hbound_abs :
      |backGap n| ≤
        |c * ‖z hf gradg γ relax x0 n - orbit hf gradg γ relax x0 n‖| := by
    rw [abs_of_nonneg hback_nonneg,
      abs_of_nonneg (mul_nonneg hc_nonneg (norm_nonneg _))]
    exact hback_le
  have hsq :
      backGap n ^ 2 ≤
        (c * ‖z hf gradg γ relax x0 n - orbit hf gradg γ relax x0 n‖) ^ 2 := by
    nlinarith [hbound_abs]
  calc
    backGap n ^ 2 ≤ (c * ‖z hf gradg γ relax x0 n - orbit hf gradg γ relax x0 n‖) ^ 2 := hsq
    _ = c ^ 2 * stepSq n := by
          simp [stepSq, pow_two, c, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Proposition 28.13: clause `(3)` is best proved on the real-valued objective surface,
then transported back to the canonical `EReal` objective. -/
lemma forwardBackward_objectiveControl_package
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    (ε : Set.Ioo (0 : ℝ) (min 1 (β : ℝ))) {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (ε : ℝ) (2 * (β : ℝ) - (ε : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (ε : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) (hx0 : x0 ∈ dom f)
    (hargmin : (Argmin ((f + g.toEReal).asEReal)).Nonempty) :
    Summable
      (fun n : ℕ ↦
        ((((f + g.toEReal).asEReal) (orbit hf gradg γ relax x0 n)).toReal -
          (sInf (Set.range ((f + g.toEReal).asEReal))).toReal) ^ 2) ∧
    IsMinimizingSequence ((f + g.toEReal).asEReal) (orbit hf gradg γ relax x0) ∧
    Antitone (fun n : ℕ ↦ ((f + g.toEReal).asEReal) (orbit hf gradg γ relax x0 n)) := by
  let h := ((f + g.toEReal).asEReal)
  let orbitVal : ℕ → ℝ := fun n ↦ (h (orbit hf gradg γ relax x0 n)).toReal
  let backVal : ℕ → ℝ := fun n ↦ (h (z hf gradg γ relax x0 n)).toReal
  let m : ℝ := (sInf (Set.range h)).toReal
  let frontGap : ℕ → ℝ := fun n ↦ orbitVal n - backVal n
  let backGap : ℕ → ℝ := fun n ↦ backVal n - m
  let totalGap : ℕ → ℝ := fun n ↦ orbitVal n - m
  rcases hargmin with ⟨xstar, hxstar⟩
  have hfg : f + g.toEReal ∈ Γ₀(H) := by
    refine pointwiseAdd_mem_gammaZero f g.toEReal hf hg ?_
    exact ⟨x0, hx0, by simp [Function.effectiveDomain_toEReal]⟩
  have hxstar_dom_h : xstar ∈ effectiveDomain (f + g.toEReal) := by
    exact mem_dom_of_mem_argmin_of_isProper (isProper_of_mem_gammaZero hfg) hxstar
  have hxstar_top : (h xstar : EReal) ≠ ⊤ := by
    exact ne_of_lt (by simpa [h, Function.asEReal] using (mem_effectiveDomain_iff.mp hxstar_dom_h))
  have hxstar_bot : (h xstar : EReal) ≠ ⊥ := by
    exact ne_of_gt (by
      simpa [h, Function.asEReal] using
        (show (⊥ : EReal) < ((f + g.toEReal) xstar : EReal) from ((f + g.toEReal) xstar).2))
  have hsInf_top : (sInf (Set.range h) : EReal) ≠ ⊤ := by
    rw [← (mem_argmin_iff_eq_sInf).1 hxstar]
    exact hxstar_top
  have hsInf_bot : (sInf (Set.range h) : EReal) ≠ ⊥ := by
    rw [← (mem_argmin_iff_eq_sInf).1 hxstar]
    exact hxstar_bot
  have horbit_mem_dom_h :
      ∀ n : ℕ, orbit hf gradg γ relax x0 n ∈ effectiveDomain (f + g.toEReal) := by
    intro n
    rcases orbit_mem_dom_and_z_mem_dom hf gradg γ
        (fun k ↦ by
          constructor
          · exact le_trans ε.2.1.le (hrelax_bounds k).1
          · exact (hrelax_bounds k).2)
        x0 hx0 n with ⟨hxn_dom, _⟩
    have hxn_top : (f (orbit hf gradg γ relax x0 n) : EReal) ≠ ⊤ :=
      ne_of_lt (mem_effectiveDomain_iff.mp hxn_dom)
    have hsum_top :
        (((f (orbit hf gradg γ relax x0 n) : EReal) +
            (g (orbit hf gradg γ relax x0 n) : EReal)) : EReal) < ⊤ :=
      EReal.add_lt_top hxn_top (EReal.coe_ne_top _)
    simpa [mem_effectiveDomain_iff, Function.toEReal_apply] using hsum_top
  have horbit_top :
      ∀ n : ℕ, (h (orbit hf gradg γ relax x0 n) : EReal) ≠ ⊤ := by
    intro n
    exact ne_of_lt (by
      simpa [h, Function.asEReal] using (mem_effectiveDomain_iff.mp (horbit_mem_dom_h n)))
  have horbit_bot :
      ∀ n : ℕ, (h (orbit hf gradg γ relax x0 n) : EReal) ≠ ⊥ := by
    intro n
    exact ne_of_gt (by
      simpa [h, Function.asEReal] using
        (show (⊥ : EReal) < ((f + g.toEReal) (orbit hf gradg γ relax x0 n) : EReal) from
          ((f + g.toEReal) (orbit hf gradg γ relax x0 n)).2))
  have hm_le_orbit :
      ∀ n : ℕ, m ≤ orbitVal n := by
    intro n
    have hmin :
        h xstar ≤ h (orbit hf gradg γ relax x0 n) :=
      (isMinOn_univ_iff.mp ((mem_argmin_iff).mp hxstar)) _
    dsimp [m, orbitVal]
    rw [← (mem_argmin_iff_eq_sInf).1 hxstar]
    exact EReal.toReal_le_toReal hmin hxstar_bot (horbit_top n)
  obtain ⟨hfront_summable, hfront_sq_summable, horbit_antitone_real⟩ :=
    orbitValueGap_sqSummable
      hf g hg gradg hgrad β ε hγ_bounds hrelax_bounds hgrad_lipschitz x0 hx0 ⟨xstar, hxstar⟩
  have hback_sq_summable :
      Summable (fun n : ℕ ↦ backGap n ^ 2) := by
    -- The backward-point gap is reduced to clause `(2)` through the fixed minimizer bound.
    simpa [h, backGap, backVal, m] using
      backwardObjectiveGap_sqSummable_of_mem_argmin
        hf g hg gradg hgrad β ε hγ_bounds hrelax_bounds hgrad_lipschitz x0 hx0 hxstar
  have htotal_sq_bound :
      ∀ n : ℕ, totalGap n ^ 2 ≤ 2 * (frontGap n ^ 2) + 2 * (backGap n ^ 2) := by
    intro n
    dsimp [frontGap, backGap, totalGap]
    have hsplit :
        orbitVal n - m = (orbitVal n - backVal n) + (backVal n - m) := by
      ring
    rw [hsplit]
    nlinarith [sq_nonneg ((orbitVal n - backVal n) - (backVal n - m))]
  have htotal_sq_dominating :
      Summable (fun n : ℕ ↦ 2 * (frontGap n ^ 2) + 2 * (backGap n ^ 2)) := by
    exact (hfront_sq_summable.mul_left 2).add (hback_sq_summable.mul_left 2)
  have htotal_sq_summable :
      Summable (fun n : ℕ ↦ totalGap n ^ 2) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ ↦ 2 * (frontGap n ^ 2) + 2 * (backGap n ^ 2))
      (g := fun n : ℕ ↦ totalGap n ^ 2)
      (fun n ↦ by positivity) ?_ htotal_sq_dominating
    intro n
    exact htotal_sq_bound n
  have htotal_nonneg :
      ∀ n : ℕ, 0 ≤ totalGap n := by
    intro n
    dsimp [totalGap]
    exact sub_nonneg.mpr (hm_le_orbit n)
  have htotal_sq_tendsto_zero :
      Tendsto (fun n : ℕ ↦ totalGap n ^ 2) atTop (𝓝 (0 : ℝ)) :=
    htotal_sq_summable.tendsto_atTop_zero
  have htotal_abs_tendsto_zero :
      Tendsto (fun n : ℕ ↦ |totalGap n|) atTop (𝓝 (0 : ℝ)) := by
    -- Taking square roots converts the squared-gap convergence to the gap itself.
    have hsqrt :
        Tendsto (fun n : ℕ ↦ Real.sqrt (totalGap n ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp htotal_sq_tendsto_zero
    simpa [Real.sqrt_sq_eq_abs] using hsqrt
  have habs_eq :
      (fun n : ℕ ↦ |totalGap n|) = totalGap := by
    funext n
    exact abs_of_nonneg (htotal_nonneg n)
  have htotal_tendsto_zero :
      Tendsto totalGap atTop (𝓝 (0 : ℝ)) := by
    simpa [habs_eq] using htotal_abs_tendsto_zero
  have horbit_real_tendsto :
      Tendsto orbitVal atTop (𝓝 m) := by
    -- Repackage the gap convergence as convergence of the real objective values.
    have hsum :
        Tendsto (fun n : ℕ ↦ totalGap n + m) atTop (𝓝 (0 + m)) :=
      htotal_tendsto_zero.add tendsto_const_nhds
    simpa [totalGap, orbitVal, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
  have horbit_ereal_tendsto :
      Tendsto (h ∘ orbit hf gradg γ relax x0) atTop (𝓝 (sInf (Set.range h))) := by
    -- Once the orbit values are finite, a single `toReal`/`coe` transport returns to `EReal`.
    have hcast :
        Tendsto
          (fun n : ℕ ↦ (((h (orbit hf gradg γ relax x0 n)).toReal : ℝ) : EReal))
          atTop (𝓝 ((m : ℝ) : EReal)) := by
      exact (continuous_coe_real_ereal.tendsto m).comp horbit_real_tendsto
    have horbit_coe :
        (fun n : ℕ ↦ (((h (orbit hf gradg γ relax x0 n)).toReal : ℝ) : EReal)) =
          h ∘ orbit hf gradg γ relax x0 := by
      funext n
      simp [Function.comp, EReal.coe_toReal (horbit_top n) (horbit_bot n)]
    rw [horbit_coe] at hcast
    simpa [m, EReal.coe_toReal hsInf_top hsInf_bot] using hcast
  have horbit_antitone :
      Antitone (fun n : ℕ ↦ h (orbit hf gradg γ relax x0 n)) := by
    intro m' n hmn
    have hreal : orbitVal n ≤ orbitVal m' := horbit_antitone_real hmn
    have hcast :
        (((orbitVal n : ℝ) : EReal)) ≤ (((orbitVal m' : ℝ) : EReal)) := by
      exact_mod_cast hreal
    simpa [orbitVal, EReal.coe_toReal (horbit_top n) (horbit_bot n),
      EReal.coe_toReal (horbit_top m') (horbit_bot m')] using hcast
  refine ⟨?_, ?_, ?_⟩
  · simpa [h, totalGap, orbitVal, m] using htotal_sq_summable
  · constructor
    · intro n
      simpa [h, Function.asEReal] using horbit_mem_dom_h n
    · exact horbit_ereal_tendsto
  · simpa [h] using horbit_antitone

/-- Helper for Proposition 28.13: on a bounded set `S`, uniform quasiconvexity forces a fixed
objective gap away from a minimizer once the distance from that minimizer is bounded below. -/
theorem argminValue_add_uniformGap_le_of_mem_boundedSet
    {h : H → EReal} {S : Set H} {φ : NNReal → EReal}
    (huniform : UniformlyQuasiconvexOn h S φ)
    {x y : H} (hx : x ∈ Argmin h) (hxS : x ∈ S) (hyS : y ∈ S)
    {ε : NNReal} (hε : ε ≤ ‖y - x‖₊) :
    h x + (((1 / 4 : ℝ) : EReal) * φ ε) ≤ h y := by
  have hxy : h x ≤ h y := (isMinOn_univ_iff.mp ((mem_argmin_iff).1 hx)) y
  have hnorm_rev : ‖x - y‖₊ = ‖y - x‖₊ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (nnnorm_neg (x - y)).symm
  have hε' : ε ≤ ‖x - y‖₊ := by
    simpa [hnorm_rev] using hε
  let m : H := (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y
  have hmid_ge : h x ≤ h m := by
    -- The midpoint value stays above the global minimum value at `x`.
    exact (isMinOn_univ_iff.mp ((mem_argmin_iff).1 hx)) m
  have hmax :
      max (h x) (h y) = h y :=
    max_eq_right hxy
  have hmidpoint_gap :
      h x + (((1 / 4 : ℝ) : EReal) * φ ‖x - y‖₊) ≤ h y := by
    have hineq :=
      huniform.ineq hxS hyS (α := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    have hquarter :
        ((((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ) : EReal) * φ ‖x - y‖₊) =
          (((1 / 4 : ℝ) : EReal) * φ ‖x - y‖₊) := by
      norm_num
    have hineq' :
        h m + (((1 / 4 : ℝ) : EReal) * φ ‖x - y‖₊) ≤ h y := by
      calc
        h m + (((1 / 4 : ℝ) : EReal) * φ ‖x - y‖₊) =
            h m + ((((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ) : EReal) * φ ‖x - y‖₊) := by
              rw [hquarter]
        _ ≤ max (h x) (h y) := by
              simpa [m] using hineq
        _ = h y := hmax
    calc
      h x + (((1 / 4 : ℝ) : EReal) * φ ‖x - y‖₊) ≤
          h m + (((1 / 4 : ℝ) : EReal) * φ ‖x - y‖₊) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hmid_ge ((((1 / 4 : ℝ) : EReal) * φ ‖x - y‖₊))
      _ ≤ h y := hineq'
  have hcoef_nonneg : (0 : EReal) ≤ (((1 / 4 : ℝ) : EReal)) := by
    norm_num
  have hmon :
      (((1 / 4 : ℝ) : EReal) * φ ε) ≤
        (((1 / 4 : ℝ) : EReal) * φ ‖x - y‖₊) :=
    mul_le_mul_of_nonneg_left (huniform.monotone hε') hcoef_nonneg
  -- Replacing the distance by the smaller radius `ε` gives the fixed bounded-set gap.
  exact
    le_trans
      (by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hmon (h x))
      hmidpoint_gap

/-- Helper for Proposition 28.13: convert the bounded-set uniform quasiconvexity gap from
`EReal` to the real objective-gap surface once the two objective values are known to be finite. -/
theorem uniformGapToReal_le_objectiveGap_of_mem_boundedSet
    {h : H → EReal} {S : Set H} {φ : NNReal → EReal}
    (huniform : UniformlyQuasiconvexOn h S φ)
    {x y : H} (hx : x ∈ Argmin h) (hxS : x ∈ S) (hyS : y ∈ S)
    {ε : NNReal} (hε : ε ≤ ‖y - x‖₊)
    (hx_top : h x ≠ ⊤) (hx_bot : h x ≠ ⊥) (hy_top : h y ≠ ⊤) (hy_bot : h y ≠ ⊥) :
    ((((1 / 4 : ℝ) : EReal) * φ ε).toReal) ≤ (h y).toReal - (h x).toReal := by
  let qconst : EReal := (((1 / 4 : ℝ) : EReal) * φ ε)
  have hgap :
      h x + qconst ≤ h y := by
    -- First recover the fixed `EReal` gap from the bounded-set quasiconvexity estimate.
    simpa [qconst] using
      argminValue_add_uniformGap_le_of_mem_boundedSet
        huniform hx hxS hyS (ε := ε) hε
  have hφ_nonneg : (0 : EReal) ≤ φ ε := by
    -- The modulus is monotone and vanishes at `0`, so every value is nonnegative.
    rw [← (huniform.modulus_eq_zero_iff 0).2 rfl]
    exact huniform.monotone bot_le
  have hq_nonneg : (0 : EReal) ≤ qconst := by
    exact mul_nonneg (by norm_num) hφ_nonneg
  have hq_bot : qconst ≠ ⊥ := by
    -- The nonnegative quarter-gap cannot be `⊥`.
    intro hq_bot
    rw [hq_bot] at hq_nonneg
    simp at hq_nonneg
  have hq_top : qconst ≠ ⊤ := by
    -- The pointwise gap estimate would force a finite objective value to dominate `⊤`.
    intro hq_top
    have hleft : h x + qconst = ⊤ := by
      simpa [qconst, hq_top] using EReal.add_top_of_ne_bot hx_bot
    exact
      (not_le_of_gt (lt_top_iff_ne_top.mpr hy_top)) <| by
        simpa [hleft] using hgap
  have hcast :
      ((((h x).toReal + qconst.toReal : ℝ) : EReal)) ≤ ((((h y).toReal : ℝ) : EReal)) := by
    -- Rewrite both sides into a single `EReal` spelling before removing `toReal`.
    have hleft :
        ((((h x).toReal + qconst.toReal : ℝ) : EReal)) = h x + qconst := by
      rw [EReal.coe_add, EReal.coe_toReal hx_top hx_bot, EReal.coe_toReal hq_top hq_bot]
    have hright :
        ((((h y).toReal : ℝ) : EReal)) = h y := by
      rw [EReal.coe_toReal hy_top hy_bot]
    rw [hleft, hright]
    exact hgap
  have hreal : (h x).toReal + qconst.toReal ≤ (h y).toReal := by
    exact_mod_cast hcast
  -- Finish on the real surface by subtracting the minimizer value.
  dsimp [qconst] at hreal ⊢
  linarith

/-- Helper for Proposition 28.13: uniform quasiconvexity on every bounded subset of `dom f`
forces the argmin set of `(f + g)` to be a singleton. -/
theorem argmin_subsingleton_of_uniformlyQuasiconvexOnEveryBoundedSubset
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (x0 : H) (hx0 : x0 ∈ dom f)
    (huniform :
      ∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ effectiveDomain f →
          ∃ φ : NNReal → EReal,
            UniformlyQuasiconvexOn ((f + g.toEReal).asEReal) S φ) :
    (Argmin ((f + g.toEReal).asEReal)).Subsingleton := by
  let h := ((f + g.toEReal).asEReal)
  have hfg : f + g.toEReal ∈ Γ₀(H) := by
    refine pointwiseAdd_mem_gammaZero f g.toEReal hf hg ?_
    exact ⟨x0, hx0, by simp [Function.effectiveDomain_toEReal]⟩
  intro x hx y hy
  by_cases hxy : x = y
  · exact hxy
  · let Cpair : Set H := Set.insert x ({y} : Set H)
    have hx_dom_h : x ∈ effectiveDomain (f + g.toEReal) := by
      exact mem_dom_of_mem_argmin_of_isProper (isProper_of_mem_gammaZero hfg) hx
    have hy_dom_h : y ∈ effectiveDomain (f + g.toEReal) := by
      exact mem_dom_of_mem_argmin_of_isProper (isProper_of_mem_gammaZero hfg) hy
    have hx_eff : x ∈ effectiveDomain f := by
      have hsum_top : (((f x : EReal) + (g x : EReal)) : EReal) ≠ ⊤ := ne_of_lt hx_dom_h
      have hfx_top : (f x : EReal) ≠ ⊤ := by
        exact
          (EReal.add_ne_top_iff_of_ne_bot_of_ne_top (EReal.coe_ne_bot _) (EReal.coe_ne_top _)).mp
            hsum_top
      exact mem_effectiveDomain_iff.mpr (lt_top_iff_ne_top.mpr hfx_top)
    have hy_eff : y ∈ effectiveDomain f := by
      have hsum_top : (((f y : EReal) + (g y : EReal)) : EReal) ≠ ⊤ := ne_of_lt hy_dom_h
      have hfy_top : (f y : EReal) ≠ ⊤ := by
        exact
          (EReal.add_ne_top_iff_of_ne_bot_of_ne_top (EReal.coe_ne_bot _) (EReal.coe_ne_top _)).mp
            hsum_top
      exact mem_effectiveDomain_iff.mpr (lt_top_iff_ne_top.mpr hfy_top)
    have hpair_nonempty : Cpair.Nonempty := by
      refine ⟨x, ?_⟩
      change x ∈ Set.insert x ({y} : Set H)
      exact Set.mem_insert x ({y} : Set H)
    have hpair_bounded : Bornology.IsBounded Cpair := by
      change Bornology.IsBounded (Set.insert x ({y} : Set H))
      exact ((Set.finite_singleton y).insert x).isBounded
    have hpair_dom : Cpair ⊆ effectiveDomain f := by
      intro w hw
      rcases Set.mem_insert_iff.mp hw with hw | hw
      · subst w
        exact hx_eff
      · rcases Set.mem_singleton_iff.mp hw with rfl
        exact hy_eff
    obtain ⟨φ, hpair_uniform⟩ := huniform Cpair hpair_nonempty hpair_bounded hpair_dom
    have hx_mem : x ∈ Cpair := by
      change x ∈ Set.insert x ({y} : Set H)
      exact Set.mem_insert x ({y} : Set H)
    have hy_mem : y ∈ Cpair := by
      change y ∈ Set.insert x ({y} : Set H)
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton y))
    let εxy : NNReal := ‖y - x‖₊
    have hgap :
        h x + (((1 / 4 : ℝ) : EReal) * φ εxy) ≤ h y := by
      simpa [εxy] using
        argminValue_add_uniformGap_le_of_mem_boundedSet
          hpair_uniform hx hx_mem hy_mem (ε := εxy) le_rfl
    have hx_eq : h x = sInf (Set.range h) := (mem_argmin_iff_eq_sInf).1 hx
    have hy_eq : h y = sInf (Set.range h) := (mem_argmin_iff_eq_sInf).1 hy
    have hdist_pos : (0 : NNReal) < εxy := by
      exact_mod_cast norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))
    have hφ_nonneg : (0 : EReal) ≤ φ εxy := by
      rw [← (hpair_uniform.modulus_eq_zero_iff 0).2 rfl]
      exact hpair_uniform.monotone bot_le
    have hφ_ne_zero : φ εxy ≠ 0 := by
      intro hzero
      exact (ne_of_gt hdist_pos) ((hpair_uniform.modulus_eq_zero_iff εxy).1 hzero)
    have hq_pos :
        (0 : EReal) < (((1 / 4 : ℝ) : EReal) * φ εxy) := by
      exact EReal.mul_pos (by exact_mod_cast (show (0 : ℝ) < 1 / 4 by norm_num))
        (lt_of_le_of_ne hφ_nonneg (Ne.symm hφ_ne_zero))
    have hx_top : (h x : EReal) ≠ ⊤ := by
      exact ne_of_lt (by simpa [h, Function.asEReal] using (mem_effectiveDomain_iff.mp hx_dom_h))
    have hx_bot : (h x : EReal) ≠ ⊥ := by
      exact ne_of_gt (by
        simpa [h, Function.asEReal] using
          (show (⊥ : EReal) < ((f + g.toEReal) x : EReal) from ((f + g.toEReal) x).2))
    have hlt :
        h x < h x + (((1 / 4 : ℝ) : EReal) * φ εxy) := by
      simpa [add_comm] using
        EReal.add_lt_add_of_lt_of_le hq_pos le_rfl hx_bot hx_top
    have hle : h x + (((1 / 4 : ℝ) : EReal) * φ εxy) ≤ h x := by
      simpa [hx_eq, hy_eq] using hgap
    exact False.elim ((not_le_of_gt hlt) hle)

/-- Helper for Proposition 28.13: a real-valued convergent objective sequence keeps convergence
to `0` after passing to a strictly monotone subsequence and subtracting its limit. -/
theorem subseqObjectiveGapReal_tendsto_zero
    {a : ℕ → ℝ} {L : ℝ} {ψ : ℕ → ℕ}
    (ha : Tendsto a atTop (𝓝 L)) (hψ_mono : StrictMono ψ) :
    Tendsto (fun n : ℕ ↦ a (ψ n) - L) atTop (𝓝 (0 : ℝ)) := by
  -- Compose the limit with the subsequence, then normalize by subtracting the limit constant.
  have hconst : Tendsto (fun _ : ℕ ↦ L) atTop (𝓝 L) := tendsto_const_nhds
  simpa using (ha.comp hψ_mono.tendsto_atTop).sub hconst

/-- Clause (3) of Proposition 28.13: under the hypotheses of Proposition 28.13, the squared
objective
gaps `((f + g)(x_n) - inf (f + g)(H))²` form a summable sequence. The objective is expressed on
the canonical extended-real surface `(f + g.toEReal).asEReal` and converted to real values via
`EReal.toReal`. Together with
`forwardBackward_isMinimizingSequence_and_antitone`, this records source clause `(3)`. -/
theorem forwardBackward_objectiveGap_sq_summable
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    (ε : Set.Ioo (0 : ℝ) (min 1 (β : ℝ))) {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (ε : ℝ) (2 * (β : ℝ) - (ε : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (ε : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) (hx0 : x0 ∈ dom f)
    (hargmin : (Argmin ((f + g.toEReal).asEReal)).Nonempty) :
    Summable
      (fun n : ℕ ↦
        ((((f + g.toEReal).asEReal) (orbit hf gradg γ relax x0 n)).toReal -
          (sInf (Set.range ((f + g.toEReal).asEReal))).toReal) ^ 2) := by
  -- Route correction: clause `(3)` now projects from a dedicated real-surface package theorem,
  -- so the public theorem no longer rebuilds the telescope or the `toReal` transport.
  exact
    (forwardBackward_objectiveControl_package
      hf g hg gradg hgrad β ε hγ_bounds hrelax_bounds hgrad_lipschitz x0 hx0 hargmin).1

/-- Companion theorem for clause `(3)`: under the hypotheses above, `(x_n)` is a
minimizing sequence of `f + g`, and the objective values decrease monotonically. -/
theorem forwardBackward_isMinimizingSequence_and_antitone
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    (ε : Set.Ioo (0 : ℝ) (min 1 (β : ℝ))) {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (ε : ℝ) (2 * (β : ℝ) - (ε : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (ε : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) (hx0 : x0 ∈ dom f)
    (hargmin : (Argmin ((f + g.toEReal).asEReal)).Nonempty) :
    IsMinimizingSequence ((f + g.toEReal).asEReal) (orbit hf gradg γ relax x0) ∧
      Antitone (fun n : ℕ ↦ ((f + g.toEReal).asEReal) (orbit hf gradg γ relax x0 n)) := by
  -- Route correction: the public minimizing-sequence statement is now just the projection of the
  -- packaged real-surface control theorem proved immediately above.
  exact
    (forwardBackward_objectiveControl_package
      hf g hg gradg hgrad β ε hγ_bounds hrelax_bounds hgrad_lipschitz x0 hx0 hargmin).2

/-- Companion theorem for clause `(3)`: the variable-step forward-backward iterates form a
minimizing sequence for `(f + g.toEReal).asEReal`. -/
theorem forwardBackward_isMinimizingSequence
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    (ε : Set.Ioo (0 : ℝ) (min 1 (β : ℝ))) {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (ε : ℝ) (2 * (β : ℝ) - (ε : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (ε : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) (hx0 : x0 ∈ dom f)
    (hargmin : (Argmin ((f + g.toEReal).asEReal)).Nonempty) :
    IsMinimizingSequence ((f + g.toEReal).asEReal) (orbit hf gradg γ relax x0) :=
  (forwardBackward_isMinimizingSequence_and_antitone
    hf g hg gradg hgrad β ε hγ_bounds hrelax_bounds hgrad_lipschitz x0 hx0 hargmin).1

/-- Companion theorem for clause `(3)`: the objective values along the variable-step
forward-backward iterates are monotone decreasing. -/
theorem forwardBackward_objective_antitone
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    (ε : Set.Ioo (0 : ℝ) (min 1 (β : ℝ))) {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (ε : ℝ) (2 * (β : ℝ) - (ε : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (ε : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) (hx0 : x0 ∈ dom f)
    (hargmin : (Argmin ((f + g.toEReal).asEReal)).Nonempty) :
    Antitone (fun n : ℕ ↦ ((f + g.toEReal).asEReal) (orbit hf gradg γ relax x0 n)) :=
  (forwardBackward_isMinimizingSequence_and_antitone
    hf g hg gradg hgrad β ε hγ_bounds hrelax_bounds hgrad_lipschitz x0 hx0 hargmin).2

/-- Clause (4) of Proposition 28.13: under the hypotheses of Proposition 28.13, assume moreover
that
`Argmin (f + g.toEReal).asEReal` is nonempty. Then `(x_n)` converges weakly to a point of
`Argmin (f + g.toEReal).asEReal`. Weak convergence is expressed in the canonical weak topology
`WeakSpace ℝ H`. -/
theorem forwardBackward_exists_weakLimit_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    (ε : Set.Ioo (0 : ℝ) (min 1 (β : ℝ))) {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (ε : ℝ) (2 * (β : ℝ) - (ε : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (ε : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) (hx0 : x0 ∈ dom f)
    (hargmin : (Argmin ((f + g.toEReal).asEReal)).Nonempty) :
    ∃ p ∈ Argmin ((f + g.toEReal).asEReal),
      Tendsto
        (fun n : ℕ ↦ toWeakSpace ℝ H (orbit hf gradg γ relax x0 n))
        atTop (𝓝 (toWeakSpace ℝ H p)) := by
  have hfg : f + g.toEReal ∈ Γ₀(H) := by
    -- The composite objective lives on the canonical `Γ₀(H)` surface used by Corollary 11.30.
    refine pointwiseAdd_mem_gammaZero f g.toEReal hf hg ?_
    exact ⟨x0, hx0, by simp [Function.effectiveDomain_toEReal]⟩
  have hfejer :
      FejerMonotone (Argmin ((f + g.toEReal).asEReal)) (orbit hf gradg γ relax x0) :=
    orbit_fejerMonotone_argmin
      hf g hg gradg hgrad β
      (fun n ↦ by
        constructor
        · exact le_trans ε.2.1.le (hγ_bounds n).1
        · nlinarith [(hγ_bounds n).2, ε.2.1])
      (fun n ↦ by
        constructor
        · exact le_trans ε.2.1.le (hrelax_bounds n).1
        · exact (hrelax_bounds n).2)
      hgrad_lipschitz x0
  have hmin :
      IsMinimizingSequence ((f + g.toEReal).asEReal) (orbit hf gradg γ relax x0) :=
    forwardBackward_isMinimizingSequence
      hf g hg gradg hgrad β ε hγ_bounds hrelax_bounds hgrad_lipschitz x0 hx0 hargmin
  have hcluster :
      ∀ z : H,
        IsSequentialClusterPt
            (fun n : ℕ ↦ toWeakSpace ℝ H (orbit hf gradg γ relax x0 n))
            (toWeakSpace ℝ H z) →
          z ∈ Argmin ((f + g.toEReal).asEReal) := by
    intro z hz
    -- Every weak sequential cluster point of the minimizing orbit is a minimizer.
    exact mem_argmin_of_weakSequentialClusterPoint_of_mem_gammaZero hfg hmin hz
  -- Theorem 5.5 applies once Fejér monotonicity and the cluster-point criterion are available.
  exact
    tendsto_weakly_of_fejerMonotone_of_weakSequentialClusterPts_mem
      hargmin (orbit hf gradg γ relax x0) hfejer hcluster

/-- Proposition 28.13 (5): under the hypotheses of Proposition 28.13, assume moreover that
`Argmin (f + g.toEReal).asEReal` is nonempty and that `f + g` is uniformly quasiconvex on every
bounded subset of `dom f`. Then `(x_n)` converges strongly to the unique minimizer of `f + g`. -/
theorem forwardBackward_exists_strongLimit_of_uniformlyQuasiconvexOnEveryBoundedSubset
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (g : H → ℝ)
    (hg : g.toEReal ∈ Γ₀(H)) (gradg : H → H)
    (hgrad : ∀ x : H, HasGradientAt g (gradg x) x) (β : Set.Ioi (0 : ℝ))
    (ε : Set.Ioo (0 : ℝ) (min 1 (β : ℝ))) {γ : ℕ → PosReal}
    (hγ_bounds : ∀ n : ℕ, (γ n : ℝ) ∈ Set.Icc (ε : ℝ) (2 * (β : ℝ) - (ε : ℝ)))
    {relax : ℕ → ℝ} (hrelax_bounds : ∀ n : ℕ, relax n ∈ Set.Icc (ε : ℝ) 1)
    (hgrad_lipschitz : LipschitzWith (Real.toNNReal ((β : ℝ)⁻¹)) gradg)
    (x0 : H) (hx0 : x0 ∈ dom f)
    (hargmin : (Argmin ((f + g.toEReal).asEReal)).Nonempty)
    (huniform :
      ∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ effectiveDomain f →
          ∃ φ : NNReal → EReal,
            UniformlyQuasiconvexOn ((f + g.toEReal).asEReal) S φ) :
    ∃ p ∈ Argmin ((f + g.toEReal).asEReal),
      Tendsto (orbit hf gradg γ relax x0) atTop (𝓝 p) ∧
        Argmin ((f + g.toEReal).asEReal) = ({p} : Set H) := by
  let h := ((f + g.toEReal).asEReal)
  obtain ⟨p, hp_arg, hpweak⟩ :=
    forwardBackward_exists_weakLimit_mem_argmin
      hf g hg gradg hgrad β ε hγ_bounds hrelax_bounds hgrad_lipschitz x0 hx0 hargmin
  have harg_subsingleton :
      (Argmin h).Subsingleton :=
    argmin_subsingleton_of_uniformlyQuasiconvexOnEveryBoundedSubset
      hf g hg x0 hx0 huniform
  have hminseq :
      IsMinimizingSequence h (orbit hf gradg γ relax x0) :=
    forwardBackward_isMinimizingSequence
      hf g hg gradg hgrad β ε hγ_bounds hrelax_bounds hgrad_lipschitz x0 hx0 hargmin
  have hfg : f + g.toEReal ∈ Γ₀(H) := by
    refine pointwiseAdd_mem_gammaZero f g.toEReal hf hg ?_
    exact ⟨x0, hx0, by simp [Function.effectiveDomain_toEReal]⟩
  have hp_dom_h : p ∈ effectiveDomain (f + g.toEReal) := by
    exact mem_dom_of_mem_argmin_of_isProper (isProper_of_mem_gammaZero hfg) hp_arg
  have hp_top : (h p : EReal) ≠ ⊤ := by
    exact ne_of_lt (mem_effectiveDomain_iff.mp hp_dom_h)
  have hp_bot : (h p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < ((f + g.toEReal) p : EReal) from ((f + g.toEReal) p).2)
  have hp_eff : p ∈ effectiveDomain f := by
    have hsum_top : (((f p : EReal) + (g p : EReal)) : EReal) ≠ ⊤ := ne_of_lt hp_dom_h
    have hfp_top : (f p : EReal) ≠ ⊤ := by
      exact (EReal.add_ne_top_iff_of_ne_bot_of_ne_top (EReal.coe_ne_bot _) (EReal.coe_ne_top _)).mp
        hsum_top
    exact mem_effectiveDomain_iff.mpr (lt_top_iff_ne_top.mpr hfp_top)
  have horbit_mem_dom_h :
      ∀ n : ℕ, orbit hf gradg γ relax x0 n ∈ effectiveDomain (f + g.toEReal) := by
    intro n
    rcases orbit_mem_dom_and_z_mem_dom hf gradg γ
        (fun k ↦ by
          constructor
          · exact le_trans ε.2.1.le (hrelax_bounds k).1
          · exact (hrelax_bounds k).2)
        x0 hx0 n with ⟨hxn_dom, _⟩
    have hxn_top : (f (orbit hf gradg γ relax x0 n) : EReal) ≠ ⊤ :=
      ne_of_lt (mem_effectiveDomain_iff.mp hxn_dom)
    have hsum_top :
        (((f (orbit hf gradg γ relax x0 n) : EReal) +
            (g (orbit hf gradg γ relax x0 n) : EReal)) : EReal) < ⊤ :=
      EReal.add_lt_top hxn_top (EReal.coe_ne_top _)
    simpa [mem_effectiveDomain_iff, Function.toEReal_apply] using hsum_top
  have hsInf_top : (sInf (Set.range h) : EReal) ≠ ⊤ := by
    rw [← (mem_argmin_iff_eq_sInf).1 hp_arg]
    exact hp_top
  have hsInf_bot : (sInf (Set.range h) : EReal) ≠ ⊥ := by
    rw [← (mem_argmin_iff_eq_sInf).1 hp_arg]
    exact hp_bot
  have hsInf_eq : sInf (Set.range h) = h p := by
    simpa using ((mem_argmin_iff_eq_sInf).1 hp_arg).symm
  have hobj_real_tendsto :
      Tendsto (fun n : ℕ ↦ (h (orbit hf gradg γ relax x0 n)).toReal)
        atTop (𝓝 ((h p).toReal)) := by
    -- Convert the minimizing-sequence convergence to the real objective surface once.
    have htoReal :
        Tendsto (fun n : ℕ ↦ (h (orbit hf gradg γ relax x0 n)).toReal)
          atTop (𝓝 ((sInf (Set.range h)).toReal)) := by
      simpa [Function.comp] using
        (EReal.tendsto_toReal hsInf_top hsInf_bot).comp hminseq.tendsto
    simpa [hsInf_eq] using htoReal
  have horbit_bounded :
      Bornology.IsBounded (Set.range (orbit hf gradg γ relax x0)) :=
    bounded_range_of_tendsto_weakly hpweak
  let S : Set H := Set.insert p (Set.range (orbit hf gradg γ relax x0))
  have hS_nonempty : S.Nonempty := by
    refine ⟨p, ?_⟩
    change p ∈ Set.insert p (Set.range (orbit hf gradg γ relax x0))
    exact Set.mem_insert p (Set.range (orbit hf gradg γ relax x0))
  have hS_bounded : Bornology.IsBounded S := by
    change Bornology.IsBounded (Set.insert p (Set.range (orbit hf gradg γ relax x0)))
    exact
      (Bornology.isBounded_insert (x := p) (s := Set.range (orbit hf gradg γ relax x0))).2
        horbit_bounded
  have hS_dom : S ⊆ effectiveDomain f := by
    intro w hw
    rcases Set.mem_insert_iff.mp hw with hw | hw
    · subst w
      exact hp_eff
    · rcases hw with ⟨n, rfl⟩
      have hdom := horbit_mem_dom_h n
      have hsum_top :
          (((f (orbit hf gradg γ relax x0 n) : EReal) +
              (g (orbit hf gradg γ relax x0 n) : EReal)) : EReal) ≠ ⊤ := ne_of_lt hdom
      have hfx_top : (f (orbit hf gradg γ relax x0 n) : EReal) ≠ ⊤ := by
        exact
          (EReal.add_ne_top_iff_of_ne_bot_of_ne_top (EReal.coe_ne_bot _) (EReal.coe_ne_top _)).mp
            hsum_top
      exact mem_effectiveDomain_iff.mpr (lt_top_iff_ne_top.mpr hfx_top)
  obtain ⟨φ, hS_uniform⟩ := huniform S hS_nonempty hS_bounded hS_dom
  have horbit_strong :
      Tendsto (orbit hf gradg γ relax x0) atTop (𝓝 p) := by
    -- Route correction: use the weak-limit point `p` and bounded-set midpoint gaps, not the
    -- old `EReal`-limit comparison. The contradiction now runs entirely on real objective gaps.
    by_contra hnot
    rw [Metric.tendsto_atTop] at hnot
    push Not at hnot
    rcases hnot with ⟨δ, hδpos, hbad⟩
    have hfreq : ∃ᶠ n in atTop, δ ≤ dist (orbit hf gradg γ relax x0 n) p := by
      rw [frequently_atTop]
      intro N
      rcases hbad N with ⟨n, hnN, hndist⟩
      exact ⟨n, hnN, hndist⟩
    rcases extraction_of_frequently_atTop hfreq with ⟨ψ, hψ_mono, hψ_dist⟩
    let δNN : NNReal := ⟨δ, hδpos.le⟩
    let qconst : EReal := (((1 / 4 : ℝ) : EReal) * φ δNN)
    have hp_mem : p ∈ S := by
      change p ∈ Set.insert p (Set.range (orbit hf gradg γ relax x0))
      exact Set.mem_insert p (Set.range (orbit hf gradg γ relax x0))
    have horbitψ_top :
        ∀ n : ℕ, h (orbit hf gradg γ relax x0 (ψ n)) ≠ ⊤ := by
      intro n
      exact ne_of_lt (by simpa [h, Function.asEReal] using horbit_mem_dom_h (ψ n))
    have horbitψ_bot :
        ∀ n : ℕ, h (orbit hf gradg γ relax x0 (ψ n)) ≠ ⊥ := by
      intro n
      exact ne_of_gt (by
        simpa [h, Function.asEReal] using
          (show (⊥ : EReal) < ((f + g.toEReal) (orbit hf gradg γ relax x0 (ψ n)) : EReal) from
            ((f + g.toEReal) _).2))
    have hφ_nonneg : (0 : EReal) ≤ φ δNN := by
      -- The modulus is nonnegative because it is monotone and vanishes at `0`.
      rw [← (hS_uniform.modulus_eq_zero_iff 0).2 rfl]
      exact hS_uniform.monotone bot_le
    have hφ_ne_zero : φ δNN ≠ 0 := by
      intro hzero
      have : δNN = 0 := (hS_uniform.modulus_eq_zero_iff δNN).1 hzero
      exact (ne_of_gt hδpos) <| by
        simpa [δNN] using congrArg (fun r : NNReal ↦ (r : ℝ)) this
    have hq_nonneg : (0 : EReal) ≤ qconst := by
      exact mul_nonneg (by norm_num) hφ_nonneg
    have hq_pos : (0 : EReal) < qconst := by
      exact EReal.mul_pos (by exact_mod_cast (show (0 : ℝ) < 1 / 4 by norm_num))
        (lt_of_le_of_ne hφ_nonneg (Ne.symm hφ_ne_zero))
    have hq_bot : qconst ≠ ⊥ := by
      -- The fixed quarter-gap stays nonnegative, so it cannot be `⊥`.
      intro hq_bot
      rw [hq_bot] at hq_nonneg
      simp at hq_nonneg
    have hq_top : qconst ≠ ⊤ := by
      -- Use one orbit value to certify that the fixed quarter-gap is finite.
      intro hq_top
      have hψ_mem0 : orbit hf gradg γ relax x0 (ψ 0) ∈ S := by
        change orbit hf gradg γ relax x0 (ψ 0) ∈
          Set.insert p (Set.range (orbit hf gradg γ relax x0))
        exact Set.mem_insert_iff.mpr (Or.inr ⟨ψ 0, rfl⟩)
      have hδNN0 :
          δNN ≤ ‖orbit hf gradg γ relax x0 (ψ 0) - p‖₊ := by
        exact_mod_cast (by simpa [dist_eq_norm] using hψ_dist 0)
      have hpointwise0 :
          h p + qconst ≤ h (orbit hf gradg γ relax x0 (ψ 0)) := by
        simpa [qconst] using
          argminValue_add_uniformGap_le_of_mem_boundedSet
            hS_uniform hp_arg hp_mem hψ_mem0 (ε := δNN) hδNN0
      have hleft : h p + qconst = ⊤ := by
        simpa [hq_top] using EReal.add_top_of_ne_bot hp_bot
      have : ¬ ((⊤ : EReal) ≤ h (orbit hf gradg γ relax x0 (ψ 0))) := by
        exact not_le_of_gt (lt_top_iff_ne_top.mpr (horbitψ_top 0))
      exact this <| by
        simpa [hleft] using hpointwise0
    have hq_real_pos : 0 < qconst.toReal := by
      -- Positivity survives the one-time `toReal` transport because the quarter-gap is finite.
      have hcast :
          (0 : EReal) < (((qconst.toReal : ℝ) : EReal)) := by
        simpa [EReal.coe_toReal hq_top hq_bot] using hq_pos
      exact_mod_cast hcast
    have hpointwise_real :
        ∀ n : ℕ,
          qconst.toReal ≤ (h (orbit hf gradg γ relax x0 (ψ n))).toReal - (h p).toReal := by
      intro n
      have hψ_mem : orbit hf gradg γ relax x0 (ψ n) ∈ S := by
        change orbit hf gradg γ relax x0 (ψ n) ∈
          Set.insert p (Set.range (orbit hf gradg γ relax x0))
        exact Set.mem_insert_iff.mpr (Or.inr ⟨ψ n, rfl⟩)
      have hδNN :
          δNN ≤ ‖orbit hf gradg γ relax x0 (ψ n) - p‖₊ := by
        exact_mod_cast (by simpa [dist_eq_norm] using hψ_dist n)
      -- Push the bounded-set uniform gap to the real objective-gap surface once and reuse it.
      simpa [qconst] using
        uniformGapToReal_le_objectiveGap_of_mem_boundedSet
          hS_uniform hp_arg hp_mem hψ_mem (ε := δNN) hδNN
          hp_top hp_bot (horbitψ_top n) (horbitψ_bot n)
    have hsubseq_gap_tendsto :
        Tendsto
          (fun n : ℕ ↦ (h (orbit hf gradg γ relax x0 (ψ n))).toReal - (h p).toReal)
          atTop (𝓝 (0 : ℝ)) := by
      -- Reuse the already proved real objective convergence instead of rebuilding minimizing
      -- sequence transport on the subsequence.
      exact subseqObjectiveGapReal_tendsto_zero hobj_real_tendsto hψ_mono
    have hsmall :
        ∀ᶠ n in atTop,
          dist ((h (orbit hf gradg γ relax x0 (ψ n))).toReal - (h p).toReal) 0 <
            qconst.toReal := by
      exact (Metric.tendsto_nhds.1 hsubseq_gap_tendsto) qconst.toReal hq_real_pos
    rw [Filter.eventually_atTop] at hsmall
    rcases hsmall with ⟨N, hN⟩
    have hgap_nonneg :
        0 ≤ (h (orbit hf gradg γ relax x0 (ψ N))).toReal - (h p).toReal := by
      -- The real objective gap is nonnegative because `p` is a minimizer.
      have hmin :
          h p ≤ h (orbit hf gradg γ relax x0 (ψ N)) :=
        (isMinOn_univ_iff.mp ((mem_argmin_iff).mp hp_arg))
          (orbit hf gradg γ relax x0 (ψ N))
      have hcast :
          ((((h p).toReal : ℝ) : EReal)) ≤
            ((((h (orbit hf gradg γ relax x0 (ψ N))).toReal : ℝ) : EReal)) := by
        simpa [EReal.coe_toReal hp_top hp_bot,
          EReal.coe_toReal (horbitψ_top N) (horbitψ_bot N)] using hmin
      have hreal :
          (h p).toReal ≤ (h (orbit hf gradg γ relax x0 (ψ N))).toReal := by
        exact_mod_cast hcast
      exact sub_nonneg.mpr hreal
    have hlt :
        (h (orbit hf gradg γ relax x0 (ψ N))).toReal - (h p).toReal < qconst.toReal := by
      simpa [Real.dist_eq, abs_of_nonneg hgap_nonneg] using hN N le_rfl
    exact (not_lt_of_ge (hpointwise_real N)) hlt
  have hsingleton : Argmin h = ({p} : Set H) := by
    ext y
    constructor
    · intro hy
      have hy_eq : y = p := harg_subsingleton hy hp_arg
      simp [hy_eq]
    · intro hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact hp_arg
  exact ⟨p, hp_arg, horbit_strong, hsingleton⟩

end Statements

end ForwardBackwardAlgorithm

end

end ERealFunction
