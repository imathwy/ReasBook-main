import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap03.Theorem_3_16_2
import BauschkeLean.Chap03.Proposition_3_21
import BauschkeLean.Chap11.Proposition_11_7
import BauschkeLean.Chap12.Proposition_12_26
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap13.GammaZeroConjugate
import BauschkeLean.Chap14.Remark_14_4
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap18.Proposition_18_22
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap24.Proposition_24_1

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section BasicProperties

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P_C" =>
  P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex]

-- Semantic recall note: `lean_leansearch` only surfaced generic distance/convexity lemmas such as
-- `convexOn_dist`; the repository owners needed for this item are the concrete distance/projection
-- surface `Metric.infDist` and `P[C, hC]`, together with `Γ₀`, `∂`, `Prox`, and `φ∗[hφ]`.

/-- The radial distance profile `x ↦ φ(d_C(x))`, formalized via `Metric.infDist`. -/
noncomputable def distanceProfile (C : Set H) (φ : ℝ → Set.Ioi (⊥ : EReal)) :
    H → Set.Ioi (⊥ : EReal) :=
  φ ∘ fun x : H ↦ Metric.infDist x C

/-- Helper for Proposition 24.27: on `ℝ`, the real inner product is ordinary multiplication. -/
private lemma real_inner_eq_mul_scalar_local (s t : ℝ) :
    inner ℝ s t = s * t := by
  calc
    inner ℝ s t = (starRingEnd ℝ) s * t := RCLike.inner_apply' s t
    _ = s * t := by simp

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Evaluating `distanceProfile C φ` at `x` recovers `φ (d_C(x))`. -/
@[simp] theorem distanceProfile_apply (φ : ℝ → Set.Ioi (⊥ : EReal)) (x : H) :
    distanceProfile C φ x = φ (Metric.infDist x C) :=
  rfl

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- `distanceProfile C φ` is exactly the composition of `φ` with the distance-to-set map. -/
theorem distanceProfile_eq_comp_infDist (φ : ℝ → Set.Ioi (⊥ : EReal)) :
    distanceProfile C φ = φ ∘ fun x : H ↦ Metric.infDist x C :=
  rfl

/-- Helper for Proposition 24.27: the distance-to-set map is convex on the ambient Hilbert space
for a nonempty closed convex set. -/
private lemma convexOn_univ_infDist_of_nonempty_isClosed_convex_local
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    _root_.ConvexOn ℝ Set.univ (fun y : H ↦ Metric.infDist y C) := by
  let hC_cheb' := isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  let P' : H → H := P[C, hC_cheb']
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hPx : P' x ∈ C := projectionPoint_mem C hC_cheb' x
  have hPy : P' y ∈ C := projectionPoint_mem C hC_cheb' y
  have hcombo_mem : a • P' x + b • P' y ∈ C := hC_convex hPx hPy ha hb hab
  have hdistx : Metric.infDist x C = ‖x - P' x‖ := by
    simpa [P', dist_eq_norm] using (projectionPoint_isBestApproximation C hC_cheb' x).2.symm
  have hdisty : Metric.infDist y C = ‖y - P' y‖ := by
    simpa [P', dist_eq_norm] using (projectionPoint_isBestApproximation C hC_cheb' y).2.symm
  calc
    Metric.infDist (a • x + b • y) C
        ≤ dist (a • x + b • y) (a • P' x + b • P' y) := by
            exact Metric.infDist_le_dist_of_mem hcombo_mem
    _ = ‖a • (x - P' x) + b • (y - P' y)‖ := by
          simp [P', dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ ≤ ‖a • (x - P' x)‖ + ‖b • (y - P' y)‖ := norm_add_le _ _
    _ = a * ‖x - P' x‖ + b * ‖y - P' y‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ = a * Metric.infDist x C + b * Metric.infDist y C := by
          rw [hdistx, hdisty]

/-- The distance profile of an even scalar `Γ₀(ℝ)` function over a nonempty closed convex set
again belongs to `Γ₀(H)`. -/
theorem distanceProfile_mem_gammaZero_of_even
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ) :
    distanceProfile C φ ∈ Γ₀(H) := by
  have hφ_even_asEReal : Function.Even φ.asEReal := by
    intro t
    exact congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) (heven t)
  have hφ_mono :
      MonotoneOn φ.asEReal (Set.Ici (0 : ℝ)) :=
    monotoneOn_nonnegative_of_even_convexOn φ hφ.2 hφ_even_asEReal
  have hzero_dom : (0 : ℝ) ∈ effectiveDomain φ := by
    rcases hφ.2.nonempty with ⟨t, ht⟩
    have hneg_dom : -t ∈ effectiveDomain φ := by
      rw [mem_effectiveDomain_iff] at ht ⊢
      simpa [heven t] using ht
    have hmid_dom :
        (1 / 2 : ℝ) * t + (1 - (1 / 2 : ℝ)) * (-t) ∈ effectiveDomain φ :=
      hφ.2.convex_effectiveDomain ht hneg_dom (by norm_num) (by norm_num) (by ring)
    convert hmid_dom using 1
    ring
  constructor
  · -- Compose the scalar lower-semicontinuous profile with the continuous distance map.
    simpa [distanceProfile_eq_comp_infDist, Function.comp] using
      hφ.1.comp (Metric.continuous_infDist_pt C)
  · refine ⟨?_, ?_, ?_⟩
    · rcases hC_nonempty with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      simpa [distanceProfile_apply, effectiveDomain, Metric.infDist_zero_of_mem hp] using hzero_dom
    · intro x hx
      exact hx
    · intro x hx y hy a ha0 ha1
      let z := a • x + (1 - a) • y
      let dx := Metric.infDist x C
      let dy := Metric.infDist y C
      let dz := Metric.infDist z C
      have hxφ : dx ∈ effectiveDomain φ := by
        simpa [distanceProfile_apply, dx] using hx
      have hyφ : dy ∈ effectiveDomain φ := by
        simpa [distanceProfile_apply, dy] using hy
      have hcombo_dom :
          a * dx + (1 - a) * dy ∈ effectiveDomain φ := by
        exact
          hφ.2.convex_effectiveDomain hxφ hyφ
            ha0.le (sub_nonneg.mpr ha1.le) (by ring)
      have hdist_le : dz ≤ a * dx + (1 - a) * dy := by
        simpa [z, dx, dy, dz, smul_eq_mul] using
          (convexOn_univ_infDist_of_nonempty_isClosed_convex_local
            (C := C) hC_nonempty hC_closed hC_convex).2
            (by simp) (by simp) ha0.le (sub_nonneg.mpr ha1.le) (by ring)
      have hcombo_nonneg : 0 ≤ a * dx + (1 - a) * dy := by
        have hdx_nonneg : 0 ≤ dx := Metric.infDist_nonneg (x := x) (s := C)
        have hdy_nonneg : 0 ≤ dy := Metric.infDist_nonneg (x := y) (s := C)
        nlinarith
      have hmono_step :
          (φ dz : EReal) ≤ (φ (a * dx + (1 - a) * dy) : EReal) := by
        exact hφ_mono (Metric.infDist_nonneg (x := z) (s := C)) hcombo_nonneg hdist_le
      have hconv_step :
          (φ (a * dx + (1 - a) * dy) : EReal) ≤
            (a : EReal) * (φ dx : EReal) + (1 - a : EReal) * (φ dy : EReal) :=
        hφ.2.ineq hxφ hyφ ha0 ha1
      -- First compare the distance value to the convex combination of the endpoint distances,
      -- then apply scalar convexity at those finite endpoint radii.
      calc
        (distanceProfile C φ z : EReal) = (φ dz : EReal) := by
          simp [distanceProfile_apply, z, dz]
        _ ≤ (φ (a * dx + (1 - a) * dy) : EReal) := hmono_step
        _ ≤ (a : EReal) * (φ dx : EReal) + (1 - a : EReal) * (φ dy : EReal) := hconv_step
        _ = (a : EReal) * (distanceProfile C φ x : EReal) +
              (1 - a : EReal) * (distanceProfile C φ y : EReal) := by
            simp [distanceProfile_apply, dx, dy]

/-- Helper for Proposition 24.27: a scalar subgradient of an even `Γ₀(ℝ)` owner at a positive
radius is nonnegative. -/
private lemma scalar_subgradient_nonneg_of_even_at_pos
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ) {r a : ℝ} (hr : 0 < r)
    (ha : a ∈ (∂ φ) r) :
    0 ≤ a := by
  -- Evaluate the scalar subgradient inequality at `-r` and use evenness to cancel the function
  -- values, leaving only the sign of the slope.
  have hr_subdom : r ∈ SetValuedOperator.dom (∂ φ) := by
    rw [SetValuedOperator.mem_dom_iff]
    exact ⟨a, ha⟩
  have hr_eff : r ∈ effectiveDomain φ :=
    subdifferential_domain_subset_effectiveDomain φ hφ.2.nonempty hr_subdom
  have hneg_eff : -r ∈ effectiveDomain φ := by
    rw [mem_effectiveDomain_iff] at hr_eff ⊢
    simpa [heven r] using hr_eff
  have hr_top : (φ r : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hr_eff)
  have hr_bot : (φ r : EReal) ≠ ⊥ := ne_of_gt (φ r).2
  have htest_real :
      inner ℝ (-r - r) a ≤ (φ (-r) : EReal).toReal - (φ r : EReal).toReal := by
    have hhalf :
        a ∈
          ⋂ y ∈ effectiveDomain φ,
            {u : ℝ | ⟪y - r, u⟫_ℝ ≤ (φ y : EReal).toReal - (φ r : EReal).toReal} := by
      simpa [subdifferential_eq_iInter_affine_halfspaces φ r hr_eff] using ha
    exact (Set.mem_iInter₂.mp hhalf) (-r) hneg_eff
  have hinner :
      inner ℝ (-r - r) a = (-2 * r) * a := by
    rw [real_inner_eq_mul_scalar_local]
    ring
  have hmul_nonpos : (-2 * r) * a ≤ 0 := by
    simpa [hinner, heven r] using htest_real
  nlinarith

/-- Helper for Proposition 24.27: if the distance `d_C(x)` itself is a scalar subgradient of `φ`
at `0`, then the projection point `P_C x` already satisfies the proximal variational inequality
for `distanceProfile C φ`. -/
private lemma projectionPoint_isProxPoint_distanceProfile_of_mem_subdifferential_zero
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ) {x : H}
    (hdsub : Metric.infDist x C ∈ (∂ φ) 0) :
    IsProxPoint (distanceProfile C φ) x (P_C x) := by
  let hγ :=
    distanceProfile_mem_gammaZero_of_even
      (C := C) hC_nonempty hC_closed hC_convex φ hφ heven
  let q : H := P_C x
  have hq_mem : q ∈ C := projectionPoint_mem C
    (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x
  rw [isProxPoint_iff_forall_inner_add_le (distanceProfile C φ) hγ.2 x q]
  intro y
  let py : H := P_C y
  have hpy_mem : py ∈ C := projectionPoint_mem C
    (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) y
  have hproj :
      ∀ z ∈ C, ⟪z - q, x - q⟫_ℝ ≤ 0 := by
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        (C := C) hC_nonempty hC_closed hC_convex
        (x := x) (p := q)).mp rfl |>.2
  have hres_norm_x : ‖x - q‖ = Metric.infDist x C := by
    simpa [q, dist_eq_norm] using
      (projectionPoint_isBestApproximation
        C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x).2
  have hres_norm_y : ‖y - py‖ = Metric.infDist y C := by
    simpa [py, dist_eq_norm] using
      (projectionPoint_isBestApproximation
        C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) y).2
  have hinner_le :
      ⟪y - q, x - q⟫_ℝ ≤ Metric.infDist y C * Metric.infDist x C := by
    have hresidual_le :
        ⟪y - py, x - q⟫_ℝ ≤ Metric.infDist y C * Metric.infDist x C := by
      calc
        ⟪y - py, x - q⟫_ℝ ≤ ‖y - py‖ * ‖x - q‖ := real_inner_le_norm _ _
        _ = Metric.infDist y C * Metric.infDist x C := by
          rw [hres_norm_y, hres_norm_x]
    have hsum :
        ⟪y - py, x - q⟫_ℝ + ⟪py - q, x - q⟫_ℝ ≤
          Metric.infDist y C * Metric.infDist x C := by
      linarith [hresidual_le, hproj py hpy_mem]
    calc
      ⟪y - q, x - q⟫_ℝ = ⟪y - py, x - q⟫_ℝ + ⟪py - q, x - q⟫_ℝ := by
        rw [show y - q = (y - py) + (py - q) by abel, inner_add_left]
      _ ≤ Metric.infDist y C * Metric.infDist x C := hsum
  have hq_value :
      (distanceProfile C φ q : EReal) = (φ 0 : EReal) := by
    simp [distanceProfile_apply, q, Metric.infDist_zero_of_mem hq_mem]
  have hscalar :=
    (mem_subdifferential_iff (f := φ) (x := 0) (u := Metric.infDist x C)).1 hdsub
      (Metric.infDist y C)
  -- Control the geometric inner product by the scalar distance product, then invoke the scalar
  -- subgradient inequality at `0`.
  rw [hq_value]
  have hinner_ereal :
      ((⟪y - q, x - q⟫_ℝ : ℝ) : EReal) ≤
        (((Metric.infDist y C * Metric.infDist x C : ℝ) : EReal)) := by
    exact_mod_cast hinner_le
  calc
    ((⟪y - q, x - q⟫_ℝ : ℝ) : EReal) + (φ 0 : EReal)
        ≤ (((Metric.infDist y C * Metric.infDist x C : ℝ) : EReal)) + (φ 0 : EReal) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hinner_ereal (φ 0 : EReal)
    _ = ((⟪Metric.infDist y C - 0, Metric.infDist x C⟫_ℝ : ℝ) : EReal) + (φ 0 : EReal) := by
          simp [sub_zero, real_inner_eq_mul_scalar_local, mul_comm]
    _ ≤ (φ (Metric.infDist y C) : EReal) := by
          simpa [sub_zero, real_inner_eq_mul_scalar_local, mul_comm]
            using hscalar
    _ = (distanceProfile C φ y : EReal) := by
          simp [distanceProfile_apply]

/-- Helper for Proposition 24.27: the residual from a point to its projection has norm `d_C(x)`.
-/
private lemma projection_residual_norm_eq_infDist_local (x : H) :
    ‖x - P_C x‖ = Metric.infDist x C := by
  simpa [dist_eq_norm] using
    (projectionPoint_isBestApproximation
      C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x).2

/-- Helper for Proposition 24.27: outside `C`, the normalized projection residual is a
subgradient of the distance-to-set map. -/
private lemma normalized_projection_residual_mem_subdifferential_distanceToSet_of_not_mem
    {x : H} (hx : x ∉ C) :
    (Metric.infDist x C)⁻¹ • (x - P_C x) ∈
      (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x := by
  rw [Set.distanceToSet_mem_subdifferential_iff_real_local]
  let q : H := P_C x
  let d : ℝ := Metric.infDist x C
  have hq_mem : q ∈ C := projectionPoint_mem C
    (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x
  have hproj :
      ∀ z ∈ C, ⟪z - q, x - q⟫_ℝ ≤ 0 := by
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        (C := C) hC_nonempty hC_closed hC_convex
        (x := x) (p := q)).mp rfl |>.2
  have hd_pos : 0 < d := (hC_closed.notMem_iff_infDist_pos hC_nonempty).1 hx
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hres_norm_x : ‖x - q‖ = d := by
    simpa [q, d] using
      projection_residual_norm_eq_infDist_local
        (C := C) hC_nonempty hC_closed hC_convex x
  intro y
  let py : H := P_C y
  have hpy_mem : py ∈ C := projectionPoint_mem C
    (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) y
  have hres_norm_y : ‖y - py‖ = Metric.infDist y C := by
    simpa [py] using
      projection_residual_norm_eq_infDist_local
        (C := C) hC_nonempty hC_closed hC_convex y
  have hinner_le :
      ⟪y - q, x - q⟫_ℝ ≤ Metric.infDist y C * d := by
    have hresidual_le :
        ⟪y - py, x - q⟫_ℝ ≤ Metric.infDist y C * d := by
      calc
        ⟪y - py, x - q⟫_ℝ ≤ ‖y - py‖ * ‖x - q‖ := real_inner_le_norm _ _
        _ = Metric.infDist y C * d := by
              rw [hres_norm_y, hres_norm_x]
    have hsum :
        ⟪y - py, x - q⟫_ℝ + ⟪py - q, x - q⟫_ℝ ≤ Metric.infDist y C * d := by
      linarith [hresidual_le, hproj py hpy_mem]
    calc
      ⟪y - q, x - q⟫_ℝ = ⟪y - py, x - q⟫_ℝ + ⟪py - q, x - q⟫_ℝ := by
        rw [show y - q = (y - py) + (py - q) by abel, inner_add_left]
      _ ≤ Metric.infDist y C * d := hsum
  have hself :
      inner ℝ (x - q) (d⁻¹ • (x - q)) = d := by
    rw [inner_smul_right, real_inner_self_eq_norm_sq, hres_norm_x]
    field_simp [hd_ne]
  have hscaled :
      inner ℝ (y - q) (d⁻¹ • (x - q)) ≤ Metric.infDist y C := by
    rw [inner_smul_right]
    have hmul :
        d⁻¹ * inner ℝ (y - q) (x - q) ≤ d⁻¹ * (Metric.infDist y C * d) :=
      mul_le_mul_of_nonneg_left hinner_le (inv_nonneg.mpr hd_pos.le)
    calc
      d⁻¹ * inner ℝ (y - q) (x - q) ≤ d⁻¹ * (Metric.infDist y C * d) := hmul
      _ = Metric.infDist y C := by
            field_simp [hd_ne]
  have hineq :
      inner ℝ (y - x) (d⁻¹ • (x - q)) + d ≤ Metric.infDist y C := by
    have hsplit_inner :
        inner ℝ (y - x) (d⁻¹ • (x - q)) =
          inner ℝ (y - q) (d⁻¹ • (x - q)) -
            inner ℝ (x - q) (d⁻¹ • (x - q)) := by
      have hsplit : y - x = (y - q) - (x - q) := by
        abel
      calc
        inner ℝ (y - x) (d⁻¹ • (x - q))
            = inner ℝ ((y - q) - (x - q)) (d⁻¹ • (x - q)) := by rw [hsplit]
        _ = inner ℝ (y - q) (d⁻¹ • (x - q)) -
              inner ℝ (x - q) (d⁻¹ • (x - q)) := by
                rw [sub_eq_add_neg, inner_add_left, inner_neg_left]
                simp [sub_eq_add_neg]
    calc
      inner ℝ (y - x) (d⁻¹ • (x - q)) + d
          = (inner ℝ (y - q) (d⁻¹ • (x - q)) -
              inner ℝ (x - q) (d⁻¹ • (x - q))) + d := by
                rw [hsplit_inner]
      _ = inner ℝ (y - q) (d⁻¹ • (x - q)) := by
            rw [hself]
            ring
      _ ≤ Metric.infDist y C := hscaled
  simpa [d, q] using hineq

/-- Helper for Proposition 24.27: an even scalar `Γ₀(ℝ)` owner is always finite at `0`. -/
private lemma zero_mem_effectiveDomain_of_even
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ) :
    (0 : ℝ) ∈ effectiveDomain φ := by
  rcases hφ.2.nonempty with ⟨t, ht⟩
  have hneg_dom : -t ∈ effectiveDomain φ := by
    rw [mem_effectiveDomain_iff] at ht ⊢
    simpa [heven t] using ht
  have hmid_dom :
      (1 / 2 : ℝ) * t + (1 - (1 / 2 : ℝ)) * (-t) ∈ effectiveDomain φ :=
    hφ.2.convex_effectiveDomain ht hneg_dom (by norm_num) (by norm_num) (by ring)
  convert hmid_dom using 1
  ring

/-- Helper for Proposition 24.27: even convexity makes `0` a global scalar minimizer. -/
private lemma value_at_zero_le_of_even
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ) (y : ℝ) :
    (φ 0 : EReal) ≤ φ y := by
  have hφ_even_asEReal : Function.Even φ.asEReal := by
    intro t
    exact congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) (heven t)
  have hφ_mono :
      MonotoneOn φ.asEReal (Set.Ici (0 : ℝ)) :=
    monotoneOn_nonnegative_of_even_convexOn φ hφ.2 hφ_even_asEReal
  by_cases hy_nonneg : 0 ≤ y
  · exact hφ_mono (by simp) hy_nonneg hy_nonneg
  · have hy_neg_nonneg : 0 ≤ -y := by linarith
    have hzero_le_neg : (φ 0 : EReal) ≤ φ (-y) :=
      hφ_mono (by simp) hy_neg_nonneg hy_neg_nonneg
    simpa [heven y] using hzero_le_neg

/-- Helper for Proposition 24.27: the zero slope belongs to the scalar subdifferential at `0`
because `0` minimizes an even convex scalar owner. -/
private lemma zero_mem_subdifferential_zero_of_even
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ) :
    (0 : ℝ) ∈ (∂ φ) 0 := by
  rw [mem_subdifferential_iff]
  intro y
  -- The affine term vanishes, so the subgradient inequality is exactly minimality at `0`.
  simpa [sub_zero, real_inner_eq_mul_scalar_local] using
    value_at_zero_le_of_even φ hφ heven y

/-- Helper for Proposition 24.27: evenness transports scalar subgradients across reflection. -/
private lemma scalar_subdifferential_neg_mem_of_even
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (heven : Function.Even φ)
    {r a : ℝ} (ha : a ∈ (∂ φ) r) :
    -a ∈ (∂ φ) (-r) := by
  rw [mem_subdifferential_iff] at ha ⊢
  intro y
  -- Evaluate the original inequality at `-y` and rewrite both the slope and the owner values.
  have hinner :
      inner ℝ (y - -r) (-a) = inner ℝ ((-y) - r) a := by
    rw [real_inner_eq_mul_scalar_local, real_inner_eq_mul_scalar_local]
    ring
  calc
    (((inner ℝ (y - -r) (-a) : ℝ) : EReal)) + (φ (-r) : EReal)
        = (((inner ℝ ((-y) - r) a : ℝ) : EReal)) + (φ r : EReal) := by
            rw [hinner, heven r]
    _ ≤ (φ (-y) : EReal) := by
          simpa using ha (-y)
    _ = (φ y : EReal) := by
          simp [heven y]

/-- Helper for Proposition 24.27: the zero-fiber subdifferential is symmetric under negation. -/
private lemma subdifferential_zero_neg_mem_of_even
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (heven : Function.Even φ)
    {a : ℝ} (ha : a ∈ (∂ φ) 0) :
    -a ∈ (∂ φ) 0 := by
  simpa using scalar_subdifferential_neg_mem_of_even φ heven (r := 0) ha

/-- Helper for Proposition 24.27: a positive finite test point bounds the scalar subdifferential
at `0` inside a symmetric compact interval. -/
private lemma subdifferential_zero_subset_interval_of_pos_memEffectiveDomain
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ) {t : ℝ} (ht_pos : 0 < t)
    (ht_dom : t ∈ effectiveDomain φ) :
    ∃ M : ℝ, (∂ φ) 0 ⊆ Set.Icc (-M) M := by
  let M : ℝ := ((φ t : EReal).toReal - (φ 0 : EReal).toReal) / t
  refine ⟨M, ?_⟩
  intro a ha
  have hzero_dom : (0 : ℝ) ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_even φ hφ heven
  have hzero_top : (φ 0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hzero_dom)
  have hzero_bot : (φ 0 : EReal) ≠ ⊥ := ne_of_gt (φ 0).2
  have ht_top : (φ t : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp ht_dom)
  have ht_bot : (φ t : EReal) ≠ ⊥ := ne_of_gt (φ t).2
  have htest_pos :
      (((inner ℝ (t - 0) a : ℝ) : EReal)) + (φ 0 : EReal) ≤ (φ t : EReal) :=
    (mem_subdifferential_iff (f := φ) (x := 0) (u := a)).1 ha t
  have htest_neg :
      (((inner ℝ (-t - 0) a : ℝ) : EReal)) + (φ 0 : EReal) ≤ (φ (-t) : EReal) :=
    (mem_subdifferential_iff (f := φ) (x := 0) (u := a)).1 ha (-t)
  have htest_pos_real :
      t * a + (φ 0 : EReal).toReal ≤ (φ t : EReal).toReal := by
    exact EReal.coe_le_coe_iff.mp <| by
      simpa [EReal.coe_add, sub_zero, real_inner_eq_mul_scalar_local,
        EReal.coe_toReal hzero_top hzero_bot, EReal.coe_toReal ht_top ht_bot] using htest_pos
  have htest_neg_real :
      (-t) * a + (φ 0 : EReal).toReal ≤ (φ t : EReal).toReal := by
    exact EReal.coe_le_coe_iff.mp <| by
      simpa [EReal.coe_add, sub_zero, real_inner_eq_mul_scalar_local, heven t,
        EReal.coe_toReal hzero_top hzero_bot, EReal.coe_toReal ht_top ht_bot] using htest_neg
  have hupper_mul :
      a * t ≤ (φ t : EReal).toReal - (φ 0 : EReal).toReal := by
    linarith
  have hlower_mul :
      -((φ t : EReal).toReal - (φ 0 : EReal).toReal) ≤ a * t := by
    linarith
  have hlower : -M ≤ a := by
    have htmp : ((φ 0 : EReal).toReal - (φ t : EReal).toReal) / t ≤ a := by
      rw [div_le_iff₀ ht_pos]
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hlower_mul
    have hnegM : -M = ((φ 0 : EReal).toReal - (φ t : EReal).toReal) / t := by
      dsimp [M]
      ring
    rw [hnegM]
    exact htmp
  have hupper : a ≤ M := by
    have htmp : a ≤ ((φ t : EReal).toReal - (φ 0 : EReal).toReal) / t := by
      rw [le_div_iff₀ ht_pos]
      exact hupper_mul
    simpa [M] using htmp
  exact ⟨hlower, hupper⟩

/-- Helper for Proposition 24.27: once the scalar effective domain contains a positive finite
point, the zero-fiber subdifferential is exactly the centered interval cut out by its supremum. -/
private lemma subdifferentialZero_mem_iff_le_sSup_of_exists_pos_memEffectiveDomain
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ)
    (hpos_dom : ∃ t : ℝ, 0 < t ∧ t ∈ effectiveDomain φ) {d : ℝ} (hd : 0 ≤ d) :
    d ∈ (∂ φ) 0 ↔ d ≤ sSup ((∂ φ) 0) := by
  rcases hpos_dom with ⟨t, ht_pos, ht_dom⟩
  rcases
      subdifferential_zero_subset_interval_of_pos_memEffectiveDomain
        φ hφ heven ht_pos ht_dom with
    ⟨M, hsubset⟩
  let S : Set ℝ := (∂ φ) 0
  have hzero_mem : (0 : ℝ) ∈ S := by
    simpa [S] using zero_mem_subdifferential_zero_of_even φ hφ heven
  have hS_nonempty : S.Nonempty := ⟨0, hzero_mem⟩
  have hS_closed : IsClosed S := by
    simpa [S] using (isClosed_subdifferential φ 0)
  have hS_convex : Convex ℝ S := by
    simpa [S] using (convex_subdifferential φ 0)
  have hS_bddBelow : BddBelow S := by
    refine ⟨-M, ?_⟩
    intro a ha
    exact (hsubset (by simpa [S] using ha)).1
  have hS_bddAbove : BddAbove S := by
    refine ⟨M, ?_⟩
    intro a ha
    exact (hsubset (by simpa [S] using ha)).2
  have hS_symm : ∀ {a : ℝ}, a ∈ S → -a ∈ S := by
    intro a ha
    simpa [S] using subdifferential_zero_neg_mem_of_even φ heven (by simpa [S] using ha)
  have hS_connected : IsConnected S := hS_convex.isConnected hS_nonempty
  have hS_eq_interval : S = Set.Icc (sInf S) (sSup S) :=
    eq_Icc_csInf_csSup_of_connected_bdd_closed hS_connected hS_bddBelow hS_bddAbove hS_closed
  have hsInf_mem : sInf S ∈ S := hS_closed.csInf_mem hS_nonempty hS_bddBelow
  have hsSup_mem : sSup S ∈ S := hS_closed.csSup_mem hS_nonempty hS_bddAbove
  have hInf_le_negSup : sInf S ≤ -sSup S :=
    (isGLB_csInf hS_nonempty hS_bddBelow).1 (hS_symm hsSup_mem)
  have hNegInf_le_sup : -(sInf S) ≤ sSup S :=
    (isLUB_csSup hS_nonempty hS_bddAbove).1 (hS_symm hsInf_mem)
  have hNegSup_le_inf : -sSup S ≤ sInf S := by
    linarith
  have hInf_eq_negSup : sInf S = -sSup S := le_antisymm hInf_le_negSup hNegSup_le_inf
  have hzero_interval : (0 : ℝ) ∈ Set.Icc (sInf S) (sSup S) := by
    rw [← hS_eq_interval]
    exact hzero_mem
  constructor
  · intro hd_mem
    have hd_interval : d ∈ Set.Icc (sInf S) (sSup S) := by
      rw [← hS_eq_interval]
      exact hd_mem
    exact hd_interval.2
  · intro hd_le
    have hd_left : sInf S ≤ d := by
      rw [hInf_eq_negSup]
      linarith [hzero_interval.2, hd]
    have hd_interval : d ∈ Set.Icc (sInf S) (sSup S) := ⟨hd_left, hd_le⟩
    have hd_mem : d ∈ S := by
      rw [hS_eq_interval]
      exact hd_interval
    simpa [S] using hd_mem

/-- Helper for Proposition 24.27: reflecting the scalar proximal point across the origin would
violate the positive-ray subgradient sign, so nonnegative input yields nonnegative scalar prox. -/
private lemma scalarProx_nonneg_of_even_nonneg_input
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ) {d : ℝ} (hd : 0 ≤ d) :
    0 ≤ Prox[φ, hφ] d := by
  let r : ℝ := Prox[φ, hφ] d
  by_cases hr_nonneg : 0 ≤ r
  · exact hr_nonneg
  · have hr_neg : r < 0 := lt_of_not_ge hr_nonneg
    have hsub : d - r ∈ (∂ φ) r := by
      simpa [r] using
        (eq_proximityOperator_iff_sub_mem_subdifferential
          (f := φ) (hf := hφ) (x := d) (p := r)).1 rfl
    have hsub_reflected : -(d - r) ∈ (∂ φ) (-r) :=
      scalar_subdifferential_neg_mem_of_even φ heven hsub
    -- The reflected positive-radius subgradient must be nonnegative, contradicting `d ≥ 0 > r`.
    have hnonneg_reflected :
        0 ≤ -(d - r) :=
      scalar_subgradient_nonneg_of_even_at_pos φ hφ heven (by linarith) hsub_reflected
    linarith

/-- Helper for Proposition 24.27: an even scalar `Γ₀(ℝ)` owner either degenerates to the singleton
effective domain `{0}` or has a positive finite point in its effective domain. -/
private lemma effectiveDomain_eq_singleton_zero_or_exists_pos_mem
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ) :
    effectiveDomain φ = ({0} : Set ℝ) ∨ ∃ t : ℝ, 0 < t ∧ t ∈ effectiveDomain φ := by
  have hzero_dom : (0 : ℝ) ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_even φ hφ heven
  by_cases hpos : ∃ t : ℝ, 0 < t ∧ t ∈ effectiveDomain φ
  · -- In the nondegenerate case, record the positive finite radius directly.
    exact Or.inr hpos
  · left
    ext t
    constructor
    · intro ht
      by_cases ht0 : t = 0
      · simp [ht0]
      · -- Evenness lets us replace any nonzero finite point by its positive absolute value.
        have habs_pos : 0 < |t| := abs_pos.mpr ht0
        have habs_dom : |t| ∈ effectiveDomain φ := by
          by_cases ht_nonneg : 0 ≤ t
          · simpa [abs_of_nonneg ht_nonneg] using ht
          · have ht_neg : t < 0 := lt_of_not_ge ht_nonneg
            have hneg_dom : -t ∈ effectiveDomain φ := by
              rw [mem_effectiveDomain_iff] at ht ⊢
              simpa [heven t] using ht
            simpa [abs_of_neg ht_neg] using hneg_dom
        exact False.elim (hpos ⟨|t|, habs_pos, habs_dom⟩)
    · intro ht
      rw [Set.mem_singleton_iff] at ht
      simpa [ht] using hzero_dom

/-- Helper for Proposition 24.27: if the scalar effective domain collapses to `{0}`, then every
real slope is a subgradient at `0`. -/
private lemma subdifferential_zero_eq_univ_of_effectiveDomain_eq_singleton_zero
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hdom_zero : effectiveDomain φ = ({0} : Set ℝ)) :
    (∂ φ) 0 = Set.univ := by
  ext u
  constructor
  · intro _
    simp
  · intro _
    rw [mem_subdifferential_iff]
    intro y
    by_cases hy : y = 0
    · -- At the unique finite point `0`, the affine inequality is equality.
      simp [hy]
    · -- Outside `{0}`, the value is `⊤`, so the global minorant inequality is automatic.
      have hy_not_mem : y ∉ effectiveDomain φ := by
        rw [hdom_zero]
        simpa [Set.mem_singleton_iff] using hy
      have hy_top : (φ y : EReal) = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy_not_mem))
      change ((⟪y - 0, u⟫_ℝ : EReal) + (φ 0 : EReal) ≤ (φ y : EReal))
      rw [hy_top]
      exact le_top

/-- Helper for Proposition 24.27: if the scalar effective domain is `{0}`, then the scalar
proximal point is always `0`. -/
private lemma scalar_prox_eq_zero_of_effectiveDomain_eq_singleton_zero
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (hdom_zero : effectiveDomain φ = ({0} : Set ℝ)) (d : ℝ) :
    Prox[φ, hφ] d = 0 := by
  -- The degenerate effective domain makes the entire zero-fiber subdifferential equal to `univ`.
  symm
  apply
    (eq_proximityOperator_iff_sub_mem_subdifferential
      (f := φ) (hf := hφ) (x := d) (p := 0)).2
  have hsub_zero : (∂ φ) 0 = Set.univ :=
    subdifferential_zero_eq_univ_of_effectiveDomain_eq_singleton_zero φ hdom_zero
  simp [hsub_zero]

/-- Helper for Proposition 24.27: in the degenerate scalar case `effectiveDomain φ = {0}`, the
displayed piecewise point collapses to the projection `P_C x`. -/
private lemma distanceProfile_piecewise_isProxPoint_of_effectiveDomain_eq_singleton_zero
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ) (x : H)
    (hdom_zero : effectiveDomain φ = ({0} : Set ℝ)) :
    IsProxPoint (distanceProfile C φ) x
      (if Metric.infDist x C > sSup ((∂ φ) 0) then
        x +
          ((Prox[φ∗[hφ], gammaZeroConjugate_mem_gammaZero hφ] (Metric.infDist x C)) /
              Metric.infDist x C) •
            (P_C x - x)
      else
        P_C x) := by
  let d : ℝ := Metric.infDist x C
  have hsub_zero : (∂ φ) 0 = Set.univ :=
    subdifferential_zero_eq_univ_of_effectiveDomain_eq_singleton_zero φ hdom_zero
  have hd_mem : d ∈ (∂ φ) 0 := by
    simp [hsub_zero]
  have hproj :
      IsProxPoint (distanceProfile C φ) x (P_C x) :=
    projectionPoint_isProxPoint_distanceProfile_of_mem_subdifferential_zero
      (C := C) hC_nonempty hC_closed hC_convex φ hφ heven hd_mem
  have hprox_zero : Prox[φ, hφ] d = 0 :=
    scalar_prox_eq_zero_of_effectiveDomain_eq_singleton_zero φ hφ hdom_zero d
  have hprox_conj : Prox[φ∗[hφ], gammaZeroConjugate_mem_gammaZero hφ] d = d := by
    -- Moreau's identity turns the conjugate prox into the residual `d - Prox_φ d`.
    rw [conjugate_proximityOperator_eq_sub_proximityOperator (g := φ) (hg := hφ) d, hprox_zero]
    simp
  have hpoint_eq :
      (if Metric.infDist x C > sSup ((∂ φ) 0) then
        x +
          ((Prox[φ∗[hφ], gammaZeroConjugate_mem_gammaZero hφ] (Metric.infDist x C)) /
              Metric.infDist x C) •
            (P_C x - x)
      else
        P_C x) = P_C x := by
    by_cases hgt : Metric.infDist x C > sSup ((∂ φ) 0)
    · -- The conjugate proximal correction is the whole residual; if `d = 0` then `x = P_C x`.
      have hres_norm : ‖x - P_C x‖ = d := by
        simpa [d, dist_eq_norm] using
          (projectionPoint_isBestApproximation
            C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x).2
      by_cases hd0 : d = 0
      · have hx_eq_proj : x = P_C x := by
          apply sub_eq_zero.mp
          exact norm_eq_zero.mp (by simpa [d, hd0] using hres_norm)
        have hresidual_zero : P_C x - x = 0 := by
          rw [← hx_eq_proj]
          simp
        calc
          (if Metric.infDist x C > sSup ((∂ φ) 0) then
            x +
              ((Prox[φ∗[hφ], gammaZeroConjugate_mem_gammaZero hφ] (Metric.infDist x C)) /
                  Metric.infDist x C) •
                (P_C x - x)
          else
            P_C x)
              =
                x +
                  ((Prox[φ∗[hφ], gammaZeroConjugate_mem_gammaZero hφ] (Metric.infDist x C)) /
                      Metric.infDist x C) •
                    (P_C x - x) := by
                      rw [if_pos hgt]
          _ = x := by simp [hresidual_zero]
          _ = P_C x := hx_eq_proj
      · have hdiv : d / d = 1 := by field_simp [hd0]
        calc
          (if Metric.infDist x C > sSup ((∂ φ) 0) then
            x +
              ((Prox[φ∗[hφ], gammaZeroConjugate_mem_gammaZero hφ] (Metric.infDist x C)) /
                  Metric.infDist x C) •
                (P_C x - x)
          else
            P_C x)
              =
                x +
                  ((Prox[φ∗[hφ], gammaZeroConjugate_mem_gammaZero hφ] (Metric.infDist x C)) /
                      Metric.infDist x C) •
                    (P_C x - x) := by
                      rw [if_pos hgt]
          _ = x + (d / d) • (P_C x - x) := by simp [hprox_conj, d]
          _ = x + (1 : ℝ) • (P_C x - x) := by rw [hdiv]
          _ = P_C x := by
                simp
    · simp [hgt]
  -- Collapse the displayed point to `P_C x`, then reuse the already established projection branch.
  simpa [hpoint_eq] using hproj

/-- Helper for Proposition 24.27: in the nondegenerate scalar branch, the radial point obtained
from the scalar proximal value is itself a proximal point of the distance profile. -/
private lemma radial_candidate_isProxPoint_distanceProfile_of_gt_threshold_of_exists_pos_memEffectiveDomain
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ)
    (hpos_dom : ∃ t : ℝ, 0 < t ∧ t ∈ effectiveDomain φ)
    {x : H} (hgt : Metric.infDist x C > sSup ((∂ φ) 0)) :
    IsProxPoint (distanceProfile C φ) x
      (P_C x + ((Prox[φ, hφ] (Metric.infDist x C)) / Metric.infDist x C) • (x - P_C x)) := by
  let d : ℝ := Metric.infDist x C
  let r : ℝ := Prox[φ, hφ] d
  let a : ℝ := d - r
  let c : H := P_C x
  let p : H := c + (r / d) • (x - c)
  let u : H := (Metric.infDist p C)⁻¹ • (p - P_C p)
  let hγ :=
    distanceProfile_mem_gammaZero_of_even
      (C := C) hC_nonempty hC_closed hC_convex φ hφ heven
  have hd_nonneg : 0 ≤ d := Metric.infDist_nonneg (x := x) (s := C)
  have hr_nonneg : 0 ≤ r :=
    scalarProx_nonneg_of_even_nonneg_input φ hφ heven hd_nonneg
  have hzero_le_sup : 0 ≤ sSup ((∂ φ) 0) := by
    exact
      (subdifferentialZero_mem_iff_le_sSup_of_exists_pos_memEffectiveDomain
        φ hφ heven hpos_dom (d := 0) (by simp)).1
        (zero_mem_subdifferential_zero_of_even φ hφ heven)
  have hd_pos : 0 < d := lt_of_le_of_lt hzero_le_sup hgt
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hresid : a ∈ (∂ φ) r := by
    simpa [a, d, r] using
      (eq_proximityOperator_iff_sub_mem_subdifferential
        (f := φ) (hf := hφ) (x := d) (p := r)).1 rfl
  have hr_ne : r ≠ 0 := by
    intro hr0
    have hd_mem : d ∈ (∂ φ) 0 := by
      simpa [a, d, r, hr0] using hresid
    have hd_le : d ≤ sSup ((∂ φ) 0) := by
      exact
        (subdifferentialZero_mem_iff_le_sSup_of_exists_pos_memEffectiveDomain
          φ hφ heven hpos_dom hd_nonneg).1 hd_mem
    exact (not_le_of_gt hgt) hd_le
  have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr_ne)
  have ha_nonneg : 0 ≤ a :=
    scalar_subgradient_nonneg_of_even_at_pos φ hφ heven hr_pos hresid
  have hcoef_nonneg : 0 ≤ r / d := div_nonneg hr_nonneg hd_nonneg
  have hproj_p : P_C p = c := by
    -- The candidate stays on the ray issuing from `P_C x`, so the metric projection is fixed.
    simpa [p, c, d, r] using
      projectionPoint_ray_fixed_of_nonempty_isClosed_convex
        (C := C) hC_nonempty hC_closed hC_convex x hcoef_nonneg
  have hres_norm_x : ‖x - c‖ = d := by
    simpa [c, d] using
      projection_residual_norm_eq_infDist_local
        (C := C) hC_nonempty hC_closed hC_convex x
  have hdist_p : Metric.infDist p C = r := by
    -- The residual from `p` to its projection is the scaled residual from `x`, hence has norm `r`.
    calc
      Metric.infDist p C = ‖p - P_C p‖ := by
        symm
        simpa [p] using
          projection_residual_norm_eq_infDist_local
            (C := C) hC_nonempty hC_closed hC_convex p
      _ = ‖(r / d) • (x - c)‖ := by
        rw [hproj_p]
        simp [p, c]
      _ = |r / d| * ‖x - c‖ := norm_smul _ _
      _ = (r / d) * d := by
        rw [abs_of_nonneg hcoef_nonneg, hres_norm_x]
      _ = r := by
        field_simp [hd_ne]
  have hp_not_mem : p ∉ C := by
    exact (hC_closed.notMem_iff_infDist_pos hC_nonempty).2 (by simpa [hdist_p] using hr_pos)
  have hu_sub : u ∈ (∂ (fun y : H ↦ Metric.infDist y C).toEReal) p := by
    simpa [u] using
      normalized_projection_residual_mem_subdifferential_distanceToSet_of_not_mem
        (C := C) hC_nonempty hC_closed hC_convex hp_not_mem
  have hu_eq : u = (d⁻¹ : ℝ) • (x - c) := by
    -- Normalize the residual at `p` and rewrite it back to the normalized residual at `x`.
    calc
      u = (r⁻¹ : ℝ) • ((r / d) • (x - c)) := by
        dsimp [u]
        rw [hdist_p, hproj_p]
        simp [p, c]
      _ = ((r⁻¹) * (r / d) : ℝ) • (x - c) := by rw [smul_smul]
      _ = (d⁻¹ : ℝ) • (x - c) := by
        congr 1
        field_simp [hd_ne, hr_ne]
  have hxp_eq : x - p = a • u := by
    -- Compare the displacement `x - p` with the normalized outward residual at `p`.
    have hbase :
        x - p = (1 - r / d) • (x - c) := by
      calc
        x - p = x - (c + (r / d) • (x - c)) := by rfl
        _ = (x - c) - (r / d) • (x - c) := by
              abel_nf
        _ = (1 : ℝ) • (x - c) - (r / d) • (x - c) := by simp
        _ = (1 - r / d) • (x - c) := by rw [sub_smul]
    have hcoef : 1 - r / d = (d - r) / d := by
      field_simp [hd_ne]
    calc
      x - p = (1 - r / d) • (x - c) := hbase
      _ = (((d - r) / d) : ℝ) • (x - c) := by rw [hcoef]
      _ = (((d - r) * d⁻¹ : ℝ)) • (x - c) := by rw [div_eq_mul_inv]
      _ = (a * d⁻¹ : ℝ) • (x - c) := by simp [a]
      _ = a • ((d⁻¹ : ℝ) • (x - c)) := by rw [smul_smul]
      _ = a • u := by rw [hu_eq]
  rw [isProxPoint_iff_forall_inner_add_le (distanceProfile C φ) hγ.2 x p]
  intro y
  have hu_real :
      ⟪y - p, u⟫_ℝ + Metric.infDist p C ≤ Metric.infDist y C := by
    exact EReal.coe_le_coe_iff.mp <| by
      simpa [Function.toEReal_apply, EReal.coe_add] using
        (mem_subdifferential_iff
          (f := (fun z : H ↦ Metric.infDist z C).toEReal) (x := p) (u := u)).1 hu_sub y
  have hu_bound : ⟪y - p, u⟫_ℝ ≤ Metric.infDist y C - r := by
    rw [hdist_p] at hu_real
    linarith
  have hinner_bound :
      ⟪y - p, x - p⟫_ℝ ≤ a * (Metric.infDist y C - r) := by
    rw [hxp_eq, inner_smul_right]
    nlinarith
  have hinner_bound_ereal :
      (((⟪y - p, x - p⟫_ℝ : ℝ) : EReal)) ≤
        (((a * (Metric.infDist y C - r) : ℝ) : EReal)) := by
    exact_mod_cast hinner_bound
  have hscalar :
      (((a * (Metric.infDist y C - r) : ℝ) : EReal)) + (φ r : EReal) ≤
        (φ (Metric.infDist y C) : EReal) := by
    simpa [a, real_inner_eq_mul_scalar_local, mul_comm, mul_left_comm, mul_assoc] using
      (mem_subdifferential_iff (f := φ) (x := r) (u := a)).1 hresid (Metric.infDist y C)
  have hp_value : (distanceProfile C φ p : EReal) = (φ r : EReal) := by
    simp [distanceProfile_apply, hdist_p]
  calc
    (((⟪y - p, x - p⟫_ℝ : ℝ) : EReal)) + (distanceProfile C φ p : EReal)
        = (((⟪y - p, x - p⟫_ℝ : ℝ) : EReal)) + (φ r : EReal) := by rw [hp_value]
    _ ≤ (((a * (Metric.infDist y C - r) : ℝ) : EReal)) + (φ r : EReal) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hinner_bound_ereal (φ r : EReal)
    _ ≤ (φ (Metric.infDist y C) : EReal) := hscalar
    _ = (distanceProfile C φ y : EReal) := by simp [distanceProfile_apply]

/-- Proposition 24.27: if `C` is a nonempty closed convex subset of `H`, if `φ ∈ Γ₀(ℝ)` is even
and differentiable on `ℝ \ {0}`, and if `f = φ ∘ d_C`, then the proximal point `Prox_f x`
is the projection `P_C x` below the threshold `max ∂φ(0)` and otherwise equals the radial
correction from equation `(24.35)`, written with the canonical threshold `sSup ((∂ φ) 0)`.
This source-facing form states that the displayed point is a proximal point of `f` at `x`. -/
theorem distanceProfile_piecewise_isProxPoint
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ)
    (hdiff : DifferentiableOn ℝ (fun t : ℝ ↦ (φ t : EReal).toReal) (({0} : Set ℝ)ᶜ))
    (x : H) :
    IsProxPoint (distanceProfile C φ) x
      (if Metric.infDist x C > sSup ((∂ φ) 0) then
        x +
          ((Prox[φ∗[hφ], gammaZeroConjugate_mem_gammaZero hφ] (Metric.infDist x C)) /
              Metric.infDist x C) •
            (P_C x - x)
      else
        P_C x) := by
  let _ := hdiff
  rcases effectiveDomain_eq_singleton_zero_or_exists_pos_mem φ hφ heven with
      hdom_zero | hpos_dom
  · -- Route correction: the degenerate source branch no longer reasons through `sSup`; both
    -- displayed cases collapse to `P_C x` because the scalar prox is identically zero.
    exact
      distanceProfile_piecewise_isProxPoint_of_effectiveDomain_eq_singleton_zero
        (C := C) hC_nonempty hC_closed hC_convex φ hφ heven x hdom_zero
  · -- The nondegenerate source branch still needs the bounded symmetric-interval bridge from a
    -- positive finite radius to `d_C(x) ∈ (∂ φ) 0 ↔ d_C(x) ≤ sSup ((∂ φ) 0)`.
    by_cases hgt : Metric.infDist x C > sSup ((∂ φ) 0)
    · let d : ℝ := Metric.infDist x C
      let r : ℝ := Prox[φ, hφ] d
      have hradial :
          IsProxPoint (distanceProfile C φ) x
            (P_C x + (r / d) • (x - P_C x)) :=
        radial_candidate_isProxPoint_distanceProfile_of_gt_threshold_of_exists_pos_memEffectiveDomain
          (C := C) hC_nonempty hC_closed hC_convex φ hφ heven hpos_dom hgt
      have hzero_le_sup : 0 ≤ sSup ((∂ φ) 0) := by
        exact
          (subdifferentialZero_mem_iff_le_sSup_of_exists_pos_memEffectiveDomain
            φ hφ heven hpos_dom (d := 0) (by simp)).1
            (zero_mem_subdifferential_zero_of_even φ hφ heven)
      have hd_pos : 0 < d := lt_of_le_of_lt hzero_le_sup hgt
      have hd_ne : d ≠ 0 := ne_of_gt hd_pos
      have hprox_conj : Prox[φ∗[hφ], gammaZeroConjugate_mem_gammaZero hφ] d = d - r := by
        rw [conjugate_proximityOperator_eq_sub_proximityOperator (g := φ) (hg := hφ) d]
      have hpoint_eq :
          x +
              ((Prox[φ∗[hφ], gammaZeroConjugate_mem_gammaZero hφ] d) / d) •
                (P_C x - x) =
            P_C x + (r / d) • (x - P_C x) := by
        rw [hprox_conj]
        have hcoeff : (d - r) / d = 1 - r / d := by
          field_simp [hd_ne]
        rw [hcoeff]
        calc
          x + (1 - r / d) • (P_C x - x)
              = x + ((1 : ℝ) • (P_C x - x) - (r / d) • (P_C x - x)) := by
                  rw [sub_smul]
          _ = x + (P_C x - x) - (r / d) • (P_C x - x) := by
                rw [one_smul, sub_eq_add_neg, sub_eq_add_neg]
                abel_nf
          _ = (x + (P_C x - x)) + -((r / d) • (P_C x - x)) := by
                abel_nf
          _ = P_C x - (r / d) • (P_C x - x) := by
                have hv : x + (P_C x - x) = P_C x := by
                  abel_nf
                simpa [sub_eq_add_neg] using
                  congrArg (fun z ↦ z + -((r / d) • (P_C x - x))) hv
          _ = P_C x + (r / d) • (x - P_C x) := by
                have hsub : P_C x - x = -(x - P_C x) := by
                  abel
                rw [sub_eq_add_neg, hsub, smul_neg]
                simp
      simpa [d, r, hgt, hpoint_eq] using hradial
    · -- The repaired threshold bridge reduces the low branch directly to the projection case.
      have hd_mem : Metric.infDist x C ∈ (∂ φ) 0 := by
        exact
          (subdifferentialZero_mem_iff_le_sSup_of_exists_pos_memEffectiveDomain
            φ hφ heven hpos_dom (Metric.infDist_nonneg (x := x) (s := C))).2
            (not_lt.mp hgt)
      have hproj :
          IsProxPoint (distanceProfile C φ) x (P_C x) :=
        projectionPoint_isProxPoint_distanceProfile_of_mem_subdifferential_zero
          (C := C) hC_nonempty hC_closed hC_convex φ hφ heven hd_mem
      simpa [hgt] using hproj

/-- Canonical bridge for Proposition 24.27: once `distanceProfile C φ ∈ Γ₀(H)` is supplied as an
explicit hypothesis, the unique proximity operator agrees with the same piecewise formula. -/
theorem prox_distanceProfile_eq_piecewise
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ)
    (hdiff : DifferentiableOn ℝ (fun t : ℝ ↦ (φ t : EReal).toReal) (({0} : Set ℝ)ᶜ))
    (hγ : distanceProfile C φ ∈ Γ₀(H))
    (x : H) :
    Prox[distanceProfile C φ, hγ] x =
      if Metric.infDist x C > sSup ((∂ φ) 0) then
        x +
          ((Prox[φ∗[hφ], gammaZeroConjugate_mem_gammaZero hφ] (Metric.infDist x C)) /
              Metric.infDist x C) •
            (P_C x - x)
      else
        P_C x := by
  simpa using
    (eq_proximityOperator_of_isProxPoint
      (distanceProfile C φ)
      (hasUniqueProxPoint_of_mem_gammaZero (distanceProfile C φ) hγ)
      (distanceProfile_piecewise_isProxPoint
        hC_nonempty hC_closed hC_convex φ hφ heven hdiff x)).symm

end BasicProperties

end

end ERealFunction
