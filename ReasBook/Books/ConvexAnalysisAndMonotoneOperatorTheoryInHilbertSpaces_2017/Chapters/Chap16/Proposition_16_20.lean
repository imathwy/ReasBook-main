import Mathlib
import Mathlib.Data.List.TFAE
import BauschkeLean.Chap01.Text_1_0_9
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap11.Definition_11_11
import BauschkeLean.Chap11.Proposition_11_14
import BauschkeLean.Chap08.Proposition_8_37
import BauschkeLean.Chap12.Corollary_12_18
import BauschkeLean.Chap13.Corollary_13_40
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section BoundednessAndSubdifferentialRegularity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Proposition 16 20: subgradients of `f.toEReal` can be read as ordinary real
affine-minorant inequalities. -/
lemma subgradient_real_inequality_of_mem_toEReal_subdifferential
    (f : H → ℝ) {x u y : H} (hu : u ∈ (∂ f.toEReal) x) :
    inner ℝ (y - x) u + f x ≤ f y := by
  -- Route correction: isolate the `EReal`-to-`ℝ` descent once so the later Lipschitz proofs do
  -- not keep re-elaborating the coercion step inline.
  have htest :
      (inner ℝ (y - x) u : EReal) + (f x : EReal) ≤ (f y : EReal) :=
    (mem_subdifferential_iff (f := f.toEReal) (x := x) (u := u)).1 hu y
  -- The real-valued coercion rewrites the subgradient inequality back to `ℝ`.
  exact EReal.coe_le_coe_iff.mp <| by
    simpa [Function.toEReal_apply, EReal.coe_add] using htest

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 16 20: a Lipschitz bound on a bounded set forces the image of that set
to be bounded. -/
lemma bounded_image_of_lipschitzOnWith_real
    (f : H → ℝ) {B : Set H} (hB : Bornology.IsBounded B)
    {β : NNReal} (hLip : LipschitzOnWith β f B) :
    Bornology.IsBounded (f '' B) := by
  -- If the source set is empty the image is empty, so the only work is the nonempty case.
  by_cases hBempty : B.Nonempty
  · rcases hBempty with ⟨x₀, hx₀⟩
    rcases hB.subset_ball x₀ with ⟨R, hR⟩
    refine
      (Metric.isBounded_closedBall :
        Bornology.IsBounded (Metric.closedBall (f x₀) (β * R))).subset ?_
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxR : x ∈ Metric.ball x₀ R := hR hx
    have hdist : dist (f x) (f x₀) ≤ β * dist x x₀ := hLip.dist_le_mul x hx x₀ hx₀
    have hxR' : dist x x₀ ≤ R := by
      simpa [Metric.mem_ball] using hxR.le
    rw [Metric.mem_closedBall]
    exact le_trans hdist (mul_le_mul_of_nonneg_left hxR' β.2)
  · have hB' : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hBempty
    simp [hB']

omit [CompleteSpace H] in
/-- Helper for Proposition 16 20: the standard test point
`x + (‖u‖ + 1)⁻¹ • u` stays inside the ball with radius enlarged by one. -/
lemma buffer_test_point_mem_ball
    {x₀ x u : H} {R : ℝ}
    (hx : x ∈ Metric.ball x₀ R) :
    x + ((‖u‖ + 1 : ℝ)⁻¹) • u ∈ Metric.ball x₀ (R + 1) := by
  let t : ℝ := (‖u‖ + 1)⁻¹
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht_mul_lt_one : t * ‖u‖ < 1 := by
    have hden : 0 < ‖u‖ + 1 := by
      positivity
    -- The buffered step has size strictly smaller than `1`.
    dsimp [t]
    simpa [div_eq_mul_inv, mul_comm] using
      (div_lt_one hden).2 (by linarith [norm_nonneg u])
  have hstep : dist (x + t • u) x = t * ‖u‖ := by
    -- The displacement from `x` to the test point is exactly `t • u`.
    rw [dist_eq_norm]
    have hsub : x + t • u - x = t • u := by
      abel_nf
    rw [hsub, norm_smul, Real.norm_of_nonneg ht_nonneg]
  rw [Metric.mem_ball] at hx ⊢
  -- Triangle inequality combines the original radius `R` with the unit-size buffer.
  calc
    dist (x + t • u) x₀ ≤ dist (x + t • u) x + dist x x₀ := dist_triangle _ _ _
    _ = t * ‖u‖ + dist x x₀ := by rw [hstep]
    _ < 1 + R := by linarith
    _ = R + 1 := by ring

/-- Helper for Proposition 16 20: once the common factor `((a + 1)⁻¹) * a` is known to be
positive, the buffered-ball scalar inequality cancels to `a ≤ β`. -/
lemma norm_le_of_inv_add_one_mul_sq_le
    {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (hineq : ((a + 1)⁻¹) * a ^ 2 ≤ β * (((a + 1)⁻¹) * a)) :
    a ≤ β := by
  by_cases ha0 : a = 0
  · -- The degenerate case reduces to the nonnegativity of `β`.
    simpa [ha0] using hβ
  have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
  let c : ℝ := ((a + 1)⁻¹) * a
  have hc_pos : 0 < c := by
    -- The cancellation factor is strictly positive for `a > 0`.
    dsimp [c]
    positivity
  have hscaled : c * a ≤ c * β := by
    -- Rewrite both sides so the common positive factor appears explicitly.
    dsimp [c]
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hineq
  exact le_of_mul_le_mul_left hscaled hc_pos

omit [CompleteSpace H] in
/-- Helper for Proposition 16 20: a subgradient on a ball where `f` is Lipschitz has norm at most
the Lipschitz constant after enlarging the ball by one unit. -/
lemma norm_le_of_mem_subdifferential_of_lipschitzOn_buffer_ball
    (f : H → ℝ) {x₀ x u : H} {R : ℝ} {β : NNReal}
    (hx : x ∈ Metric.ball x₀ R)
    (hLip : LipschitzOnWith β f (Metric.ball x₀ (R + 1)))
    (hu : u ∈ (∂ f.toEReal) x) :
    ‖u‖ ≤ β := by
  let t : ℝ := (‖u‖ + 1)⁻¹
  let y : H := x + t • u
  have hy : y ∈ Metric.ball x₀ (R + 1) := by
    -- The source proof uses the buffered test point `y` so both inequalities live on one ball.
    simpa [y, t] using buffer_test_point_mem_ball (x := x) (x₀ := x₀) (u := u) (R := R) hx
  have hx_buffer : x ∈ Metric.ball x₀ (R + 1) := by
    -- The original point also lies in the enlarged ball.
    rw [Metric.mem_ball] at hx ⊢
    linarith
  have hy_sub : y - x = t • u := by
    -- This isolates the common displacement used by the subgradient and Lipschitz estimates.
    dsimp [y]
    abel_nf
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have hsubgrad :
      t * ‖u‖ ^ 2 + f x ≤ f y := by
    -- Rewrite the real subgradient inequality at the buffered test point into scalar form.
    have htest :=
      subgradient_real_inequality_of_mem_toEReal_subdifferential (f := f) (u := u) (y := y) hu
    rw [hy_sub, real_inner_smul_left, real_inner_self_eq_norm_sq] at htest
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using htest
  have hdist : dist y x = t * ‖u‖ := by
    -- The metric displacement has the same scalar factor as the inner-product term above.
    rw [dist_eq_norm, hy_sub, norm_smul, Real.norm_of_nonneg ht_nonneg]
  have hLip_real :
      f y - f x ≤ β * dist y x := by
    -- The Lipschitz bound controls the signed gap by the corresponding absolute-value bound.
    have hdist' : dist (f y) (f x) ≤ β * dist y x := hLip.dist_le_mul y hy x hx_buffer
    have habs : |f y - f x| ≤ β * dist y x := by
      simpa [dist_eq_norm, Real.norm_eq_abs, sub_eq_add_neg] using hdist'
    exact le_trans (le_abs_self (f y - f x)) habs
  have hscaled :
      t * ‖u‖ ^ 2 ≤ β * (t * ‖u‖) := by
    -- Comparing the subgradient lower bound with the Lipschitz upper bound produces the common
    -- factor inequality that the scalar helper can cancel.
    have hleft : t * ‖u‖ ^ 2 ≤ f y - f x := by
      linarith
    have hright : f y - f x ≤ β * (t * ‖u‖) := by
      simpa [hdist] using hLip_real
    exact le_trans hleft hright
  exact norm_le_of_inv_add_one_mul_sq_le
    (a := ‖u‖) (β := β) (norm_nonneg u) β.2 <| by
      simpa [t, pow_two, mul_assoc, mul_left_comm, mul_comm] using hscaled

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 16 20: a real upper bound on a metric ball gives a finite `EReal`
supremum for the image of that ball. -/
lemma finite_sup_ball_lt_top_of_real_upper_bound
    (f : H → ℝ) {x₀ : H} {ρ M : ℝ}
    (hM : ∀ y ∈ Metric.ball x₀ ρ, f y ≤ M) :
    sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ) < ⊤ := by
  have hsSup_le :
      sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ) ≤ M := by
    -- Every point of the image lies below the same real bound `M`.
    refine sSup_le ?_
    intro a ha
    rcases ha with ⟨y, hy, rfl⟩
    change ((f y : ℝ) : EReal) ≤ (M : EReal)
    exact_mod_cast hM y hy
  exact lt_of_le_of_lt hsSup_le (EReal.coe_lt_top M)

omit [CompleteSpace H] in
/-- Helper for Proposition 16 20: coercing a convex real-valued function through `toEReal`
preserves convexity on its full effective domain. -/
lemma convexOn_toEReal_of_convexOn_univ
    (f : H → ℝ) (hconv : _root_.ConvexOn ℝ Set.univ f) :
    ConvexOn f.toEReal (effectiveDomain f.toEReal) := by
  refine ⟨?_, ?_, ?_⟩
  · -- A real-valued function is finite everywhere after the canonical `toEReal` coercion.
    simp [Function.effectiveDomain_toEReal]
  · -- Effective-domain membership is therefore automatic.
    simp [Function.effectiveDomain_toEReal]
  · intro x hx y hy a ha0 ha1
    -- Rewrite the convexity inequality back to the original real-valued statement.
    have hreal :
        f (a • x + (1 - a) • y) ≤ a * f x + (1 - a) * f y := by
      simpa [smul_eq_mul] using
        hconv.2 (by simp : x ∈ Set.univ) (by simp : y ∈ Set.univ) ha0.le
          (sub_nonneg.mpr ha1.le) (by linarith)
    change ((f (a • x + (1 - a) • y) : ℝ) : EReal) ≤
      ((a * f x + (1 - a) * f y : ℝ) : EReal)
    exact_mod_cast hreal

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 16 20: continuity of a real-valued function upgrades every point to a
continuity point on the effective domain of its `toEReal` coercion. -/
lemma continuousAtOnEffectiveDomain_toEReal_of_continuous
    (f : H → ℝ) (hcont : Continuous f) (x : H) :
    ContinuousAtOnEffectiveDomain f.toEReal x := by
  refine ⟨by simp [Function.effectiveDomain_toEReal], ?_⟩
  -- The effective domain is all of `H`, so this is just ordinary continuity at `x`.
  simpa [Function.effectiveDomain_toEReal, Function.toEReal_apply] using
    hcont.continuousAt.continuousWithinAt

omit [CompleteSpace H] in
/-- Helper for Proposition 16 20: a continuous convex real-valued function on all of `H`
canonically defines an element of `Γ₀(H)` after applying `toEReal`. -/
lemma real_toEReal_mem_gammaZero_of_continuous_convexOn_univ
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f) :
    f.toEReal ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  constructor
  · simpa [Function.toEReal_apply] using
      (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
  · refine ⟨by simp [Function.effectiveDomain_toEReal], subset_rfl, ?_⟩
    intro x hx y hy a ha0 ha1
    have hreal :
        f (a • x + (1 - a) • y) ≤ a * f x + (1 - a) * f y := by
      simpa [smul_eq_mul] using
        hconv.2 (by simp) (by simp) ha0.le (sub_nonneg.mpr ha1.le) (by linarith)
    have hcast :
        ((f (a • x + (1 - a) • y) : ℝ) : EReal) ≤
          ((a * f x + (1 - a) * f y : ℝ) : EReal) := by
      exact_mod_cast hreal
    simpa [Function.toEReal_apply, EReal.coe_mul, EReal.coe_add] using hcast

omit [CompleteSpace H] in
/-- Helper for Proposition 16 20: a uniform upper bound on the doubled ball controls the
oscillation on the inner ball, hence the real image of the inner ball is bounded. -/
lemma bounded_image_of_upper_bound_on_buffer_ball
    (f : H → ℝ) (hconv : _root_.ConvexOn ℝ Set.univ f)
    {x₀ : H} {R M : ℝ} (hR : 0 < R)
    (hM : ∀ y ∈ Metric.ball x₀ (2 * R), f y ≤ M) :
    Bornology.IsBounded (f '' Metric.ball x₀ R) := by
  let η : EReal := sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ (2 * R))
  let C : ℝ := (1 / 2 : ℝ) * (η.toReal - (f x₀ : EReal).toReal)
  have hconv_toEReal : ConvexOn f.toEReal (effectiveDomain f.toEReal) :=
    convexOn_toEReal_of_convexOn_univ f hconv
  have hx₀_dom : x₀ ∈ effectiveDomain f.toEReal := by
    simp [Function.effectiveDomain_toEReal]
  have hη : η < ⊤ := by
    -- The pointwise real upper bound on the larger ball gives a finite `EReal` supremum there.
    simpa [η] using finite_sup_ball_lt_top_of_real_upper_bound f hM
  have htwoR : 0 < 2 * R := by
    positivity
  have hhalf0 : 0 < (1 / 2 : ℝ) := by norm_num
  have hhalf1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hhalf_twoR : (1 / 2 : ℝ) * (2 * R) = R := by ring
  have hC_nonneg : 0 ≤ C := by
    have hx₀_ball : x₀ ∈ Metric.ball x₀ ((1 / 2 : ℝ) * (2 * R)) := by
      have hhalf_twoR' : 0 < (1 / 2 : ℝ) * (2 * R) := by
        simpa [hhalf_twoR] using hR
      exact Metric.mem_ball_self hhalf_twoR'
    have hosc :=
      oscillation_bound_on_smaller_ball
        (f := f.toEReal) (x := x₀) hconv_toEReal htwoR hx₀_dom hη hhalf0 hhalf1
        hx₀_ball
        (by simp [Function.effectiveDomain_toEReal])
    -- Evaluating the oscillation estimate at the center shows the radius is nonnegative.
    simpa [C, η, Function.toEReal_apply] using hosc
  have hsubset :
      f '' Metric.ball x₀ R ⊆ Metric.closedBall (f x₀) C := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have hosc :=
      oscillation_bound_on_smaller_ball
        (f := f.toEReal) (x := x) hconv_toEReal htwoR hx₀_dom hη hhalf0 hhalf1
        (by simpa [Metric.mem_ball, hhalf_twoR] using hx)
        (by simp [Function.effectiveDomain_toEReal])
    -- The oscillation estimate is exactly the closed-ball membership around `f x₀`.
    simpa [Metric.mem_closedBall, Real.dist_eq, C, η, Function.toEReal_apply] using hosc
  exact Metric.isBounded_closedBall.subset hsubset

omit [CompleteSpace H] in
/-- Helper for Proposition 16 20: bounded subgradients on a set force a Lipschitz estimate on that
set once every point admits a subgradient. -/
lemma lipschitzOnWith_of_subdifferentiable_and_image_subset_closedBall
    (f : H → ℝ) {B : Set H} {β : NNReal}
    (hsub : ∀ x ∈ B, SubdifferentiableAt f.toEReal x)
    (hImg :
      SetValuedOperator.image (∂ f.toEReal) B ⊆ Metric.closedBall (0 : H) β) :
    LipschitzOnWith β f B := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  have hx_dom : x ∈ SetValuedOperator.dom (∂ f.toEReal) :=
    (subdifferentiableAt_iff_mem_dom (f := f.toEReal) (x := x)).1 (hsub x hx)
  have hy_dom : y ∈ SetValuedOperator.dom (∂ f.toEReal) :=
    (subdifferentiableAt_iff_mem_dom (f := f.toEReal) (x := y)).1 (hsub y hy)
  rcases (SetValuedOperator.mem_dom_iff (A := ∂ f.toEReal) (x := x)).1 hx_dom with ⟨u, hu⟩
  rcases (SetValuedOperator.mem_dom_iff (A := ∂ f.toEReal) (x := y)).1 hy_dom with ⟨v, hv⟩
  have hu_img : u ∈ SetValuedOperator.image (∂ f.toEReal) B := by
    exact (SetValuedOperator.mem_image (∂ f.toEReal) B u).2 ⟨x, hx, hu⟩
  have hv_img : v ∈ SetValuedOperator.image (∂ f.toEReal) B := by
    exact (SetValuedOperator.mem_image (∂ f.toEReal) B v).2 ⟨y, hy, hv⟩
  have hu_norm : ‖u‖ ≤ β := by
    have hu_ball : u ∈ Metric.closedBall (0 : H) β := hImg hu_img
    -- Membership in the closed ball centered at `0` is exactly the required norm bound.
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu_ball
  have hv_norm : ‖v‖ ≤ β := by
    have hv_ball : v ∈ Metric.closedBall (0 : H) β := hImg hv_img
    -- The same closed-ball rewriting applies to the second endpoint subgradient.
    simpa [Metric.mem_closedBall, dist_eq_norm] using hv_ball
  have hxu :
      ⟪y - x, u⟫_ℝ + f x ≤ f y :=
    subgradient_real_inequality_of_mem_toEReal_subdifferential (f := f) (u := u) (y := y) hu
  have hyv :
      ⟪x - y, v⟫_ℝ + f y ≤ f x :=
    subgradient_real_inequality_of_mem_toEReal_subdifferential (f := f) (u := v) (y := x) hv
  have hxy :
      f x - f y ≤ β * ‖x - y‖ := by
    have hinner_lower : -(β * ‖x - y‖) ≤ ⟪y - x, u⟫_ℝ := by
      have hinner_abs : |⟪y - x, u⟫_ℝ| ≤ β * ‖x - y‖ := by
        calc
          |⟪y - x, u⟫_ℝ| ≤ ‖y - x‖ * ‖u‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖y - x‖ * β := by
            exact mul_le_mul_of_nonneg_left hu_norm (norm_nonneg _)
          _ = β * ‖x - y‖ := by rw [norm_sub_rev, mul_comm]
      exact le_trans (neg_le_neg hinner_abs) (neg_abs_le _)
    have hsub : f x + -(β * ‖x - y‖) ≤ f y := by
      calc
        f x + -(β * ‖x - y‖) ≤ f x + ⟪y - x, u⟫_ℝ := by
          simpa [add_comm] using add_le_add_left hinner_lower (f x)
        _ ≤ f y := by simpa [add_comm] using hxu
    linarith
  have hyx :
      f y - f x ≤ β * ‖x - y‖ := by
    have hinner_lower : -(β * ‖x - y‖) ≤ ⟪x - y, v⟫_ℝ := by
      have hinner_abs : |⟪x - y, v⟫_ℝ| ≤ β * ‖x - y‖ := by
        calc
          |⟪x - y, v⟫_ℝ| ≤ ‖x - y‖ * ‖v‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖x - y‖ * β := by
            exact mul_le_mul_of_nonneg_left hv_norm (norm_nonneg _)
          _ = β * ‖x - y‖ := by rw [mul_comm]
      exact le_trans (neg_le_neg hinner_abs) (neg_abs_le _)
    have hsub : f y + -(β * ‖x - y‖) ≤ f x := by
      calc
        f y + -(β * ‖x - y‖) ≤ f y + ⟪x - y, v⟫_ℝ := by
          simpa [add_comm] using add_le_add_left hinner_lower (f y)
        _ ≤ f x := by simpa [add_comm] using hyv
    linarith
  have habs : |f x - f y| ≤ β * ‖x - y‖ := (abs_sub_le_iff.2 ⟨hxy, hyx⟩)
  -- The paired one-sided bounds are exactly the absolute-value estimate for a real Lipschitz map.
  simpa [dist_eq_norm, Real.norm_eq_abs, sub_eq_add_neg] using habs

/-- Helper for Proposition 16 20: the biconjugate of the packaged Fenchel conjugate evaluates back
to the original real-valued function. -/
lemma gammaZeroConjugate_biconjugate_apply
    (f : H → ℝ) (hf : f.toEReal ∈ Γ₀(H)) (x : H) :
    ((f.toEReal∗[hf]).asEReal∗ x) = (f x : EReal) := by
  -- Evaluate the Fenchel--Moreau identity pointwise at `x`.
  simpa [Function.asEReal, Function.toEReal_apply, gammaZeroConjugate_apply] using
    congrFun (biconjugate_eq_of_mem_gammaZero hf) x

omit [CompleteSpace H] in
/-- Helper for Proposition 16 20: every `Γ₀(H)` function admits a global affine lower bound in the
norm with nonnegative slope. -/
lemma exists_linear_lower_bound_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    ∃ R C : ℝ, 0 ≤ R ∧ ∀ x : H, (((-R * ‖x‖ - C : ℝ) : EReal) ≤ (f x : EReal)) := by
  rcases hf.2.nonempty with ⟨p, hp⟩
  let ξ : ℝ := (f p : EReal).toReal - 1
  have hp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp)
  have hp_bot : (f p : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
  have hξ_lt_fp : (ξ : EReal) < (f p : EReal) := by
    rw [show (f p : EReal) = (((f p : EReal).toReal : ℝ) : EReal) by
      symm
      exact EReal.coe_toReal hp_top hp_bot]
    exact_mod_cast (show ξ < (f p : EReal).toReal by
      dsimp [ξ]
      linarith)
  have hopen : IsOpen (f.asEReal ⁻¹' Set.Ioi (ξ : EReal)) := hf.1.isOpen_preimage (ξ : EReal)
  have hp_mem : p ∈ f.asEReal ⁻¹' Set.Ioi (ξ : EReal) := by
    simpa [Function.asEReal] using hξ_lt_fp
  rcases Metric.isOpen_iff.mp hopen p hp_mem with ⟨r, hr_pos, hr_subset⟩
  let δ : ℝ := r / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    linarith
  refine ⟨|δ⁻¹|, 1 + ‖p‖ / δ - (f p : EReal).toReal, abs_nonneg _, ?_⟩
  intro x
  by_cases hx : x ∈ effectiveDomain f
  · have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    by_cases hnear : ‖x - p‖ < δ
    · have hball : x ∈ Metric.ball p r := by
        have : ‖x - p‖ < r := by
          dsimp [δ] at hnear
          linarith
        simpa [Metric.mem_ball, dist_eq_norm] using this
      have hξ_lt_fx : (ξ : EReal) < (f x : EReal) := hr_subset hball
      have hbound_real :
          -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) ≤ ξ := by
        dsimp [ξ]
        have hnonneg : 0 ≤ δ⁻¹ * ‖x‖ + ‖p‖ / δ := by
          positivity
        linarith
      have hbound_ereal :
          (((-δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) : ℝ) : EReal)) ≤
            (ξ : EReal) := by
        exact_mod_cast hbound_real
      have hbound_abs :
          (((-|δ⁻¹| * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) : ℝ) : EReal)) ≤
            (((-δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) : ℝ) : EReal)) := by
        have hreal : -|δ⁻¹| * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) ≤
            -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) := by
          have hmul : -|δ⁻¹| * ‖x‖ ≤ -δ⁻¹ * ‖x‖ := by
            have hneg : -|δ⁻¹| ≤ -δ⁻¹ := by
              nlinarith [le_abs_self (δ⁻¹)]
            exact mul_le_mul_of_nonneg_right hneg (norm_nonneg _)
          linarith
        exact_mod_cast hreal
      exact le_trans hbound_abs (le_trans hbound_ereal hξ_lt_fx.le)
    · have hfar : δ ≤ ‖x - p‖ := le_of_not_gt hnear
      have hxp_pos : 0 < ‖x - p‖ := lt_of_lt_of_le hδ_pos hfar
      let t : ℝ := δ / ‖x - p‖
      let y : H := t • x + (1 - t) • p
      have ht_pos : 0 < t := by
        dsimp [t]
        exact div_pos hδ_pos hxp_pos
      have ht_le_one : t ≤ 1 := by
        dsimp [t]
        exact (div_le_iff₀ hxp_pos).2 (by simpa [one_mul] using hfar)
      have hy_sub : y - p = t • (x - p) := by
        dsimp [y]
        calc
          t • x + (1 - t) • p - p = t • x + ((1 - t) • p - p) := by abel
          _ = t • x + ((1 - t) • p - (1 : ℝ) • p) := by simp
          _ = t • x + ((1 - t - 1) • p) := by rw [← sub_smul]
          _ = t • x + (-t) • p := by ring_nf
          _ = t • x - t • p := by rw [sub_eq_add_neg, neg_smul]
          _ = t • (x - p) := by rw [smul_sub]
      have hy_ball : y ∈ Metric.ball p r := by
        have hnorm : ‖y - p‖ < r := by
          calc
            ‖y - p‖ = ‖t • (x - p)‖ := by rw [hy_sub]
            _ = |t| * ‖x - p‖ := norm_smul t (x - p)
            _ = t * ‖x - p‖ := by rw [abs_of_pos ht_pos]
            _ = δ := by
                  dsimp [t]
                  field_simp [hxp_pos.ne']
            _ < r := by
                  dsimp [δ]
                  linarith
        simpa [Metric.mem_ball, dist_eq_norm] using hnorm
      have hξ_lt_fy : (ξ : EReal) < (f y : EReal) := hr_subset hy_ball
      have hconv :
          (f y : EReal) ≤ (t : EReal) * (f x : EReal) + ((1 - t : ℝ) : EReal) * (f p : EReal) := by
        by_cases ht_one : t = 1
        · simp [y, ht_one]
        · have ht_lt_one : t < 1 := lt_of_le_of_ne ht_le_one ht_one
          simpa [y] using hf.2.ineq (x := x) hx (y := p) hp (α := t) ht_pos ht_lt_one
      have hterm1_ne_top : (t : EReal) * (f x : EReal) ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨Or.inl (EReal.coe_ne_bot t), Or.inl ?_, Or.inl (EReal.coe_ne_top t), Or.inr hx_top⟩
        exact_mod_cast ht_pos.le
      have hterm2_ne_top : ((1 - t : ℝ) : EReal) * (f p : EReal) ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨Or.inl (EReal.coe_ne_bot (1 - t)), Or.inl ?_,
          Or.inl (EReal.coe_ne_top (1 - t)), Or.inr hp_top⟩
        exact_mod_cast sub_nonneg.mpr ht_le_one
      have hright_ne_top :
          (t : EReal) * (f x : EReal) + ((1 - t : ℝ) : EReal) * (f p : EReal) ≠ ⊤ :=
        EReal.add_ne_top hterm1_ne_top hterm2_ne_top
      have hy_top : (f y : EReal) ≠ ⊤ := by
        intro hy_top
        have : (⊤ : EReal) ≤
            (t : EReal) * (f x : EReal) + ((1 - t : ℝ) : EReal) * (f p : EReal) := by
          simpa [hy_top] using hconv
        exact hright_ne_top (top_unique this)
      have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
      have hξ_lt_fy_real : ξ < (f y : EReal).toReal := by
        rw [← EReal.coe_toReal hy_top hy_bot] at hξ_lt_fy
        exact EReal.coe_lt_coe_iff.1 hξ_lt_fy
      have hconv_real :
          (f y : EReal).toReal ≤ t * (f x : EReal).toReal + (1 - t) * (f p : EReal).toReal := by
        have hconv_cast :
            (((f y : EReal).toReal : ℝ) : EReal) ≤
              (t : EReal) * (((f x : EReal).toReal : ℝ) : EReal) +
                ((1 - t : ℝ) : EReal) * (((f p : EReal).toReal : ℝ) : EReal) := by
          simpa [EReal.coe_toReal hx_top hx_bot, EReal.coe_toReal hy_top hy_bot,
            EReal.coe_toReal hp_top hp_bot] using hconv
        exact EReal.coe_le_coe_iff.1 (by simpa [EReal.coe_mul, EReal.coe_add] using hconv_cast)
      have hfx_real :
          -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) < (f x : EReal).toReal := by
        have hdist : ‖x - p‖ ≤ ‖x‖ + ‖p‖ := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_sub_le x p
        have hmain : (f p : EReal).toReal - 1 / t < (f x : EReal).toReal := by
          have haux : ξ < t * (f x : EReal).toReal + (1 - t) * (f p : EReal).toReal :=
            lt_of_lt_of_le hξ_lt_fy_real hconv_real
          have hsub : -1 < t * ((f x : EReal).toReal - (f p : EReal).toReal) := by
            dsimp [ξ] at haux
            linarith
          have hdiv : -1 / t < (f x : EReal).toReal - (f p : EReal).toReal := by
            exact (div_lt_iff₀ ht_pos).2 (by simpa [mul_comm] using hsub)
          have hmain_shift :
              (f p : EReal).toReal + (-1 / t) <
                (f p : EReal).toReal + ((f x : EReal).toReal - (f p : EReal).toReal) :=
            add_lt_add_right hdiv (f p : EReal).toReal
          calc
            (f p : EReal).toReal - 1 / t = (f p : EReal).toReal + (-1 / t) := by ring
            _ < (f p : EReal).toReal + ((f x : EReal).toReal - (f p : EReal).toReal) := hmain_shift
            _ = (f x : EReal).toReal := by ring
        have ht_inv : 1 / t = ‖x - p‖ / δ := by
          dsimp [t]
          field_simp [hxp_pos.ne', hδ_pos.ne']
        rw [ht_inv] at hmain
        have hratio : ‖x - p‖ / δ ≤ ‖x‖ / δ + ‖p‖ / δ := by
          have := div_le_div_of_nonneg_right hdist hδ_pos.le
          simpa [add_div] using this
        have hleft_le :
            (f p : EReal).toReal - 1 - (‖x‖ / δ + ‖p‖ / δ) ≤
              (f p : EReal).toReal - ‖x - p‖ / δ := by
          linarith
        have hfinal :
            (f p : EReal).toReal - 1 - (‖x‖ / δ + ‖p‖ / δ) < (f x : EReal).toReal :=
          lt_of_le_of_lt hleft_le hmain
        have hrewrite :
            -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) =
              (f p : EReal).toReal - 1 - (‖x‖ / δ + ‖p‖ / δ) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
        rw [hrewrite]
        exact hfinal
      have hfx_ereal :
          (((-δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) : ℝ) : EReal)) <
            (f x : EReal) := by
        rw [show (f x : EReal) = (((f x : EReal).toReal : ℝ) : EReal) by
          symm
          exact EReal.coe_toReal hx_top hx_bot]
        exact_mod_cast hfx_real
      have hbound_abs :
          (((-|δ⁻¹| * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) : ℝ) : EReal)) ≤
            (((-δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) : ℝ) : EReal)) := by
        have hreal : -|δ⁻¹| * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) ≤
            -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) := by
          have hmul : -|δ⁻¹| * ‖x‖ ≤ -δ⁻¹ * ‖x‖ := by
            have hneg : -|δ⁻¹| ≤ -δ⁻¹ := by
              nlinarith [le_abs_self (δ⁻¹)]
            exact mul_le_mul_of_nonneg_right hneg (norm_nonneg _)
          linarith
        exact_mod_cast hreal
      exact le_trans hbound_abs hfx_ereal.le
  · have hx_top : (f x : EReal) = ⊤ := by
      apply le_antisymm le_top
      apply not_lt.mp
      intro hxtop
      exact hx (mem_effectiveDomain_iff.mpr hxtop)
    simp [hx_top]

omit [CompleteSpace H] in
/-- Helper for Proposition 16 20: for `Γ₀(H)` functions, supercoercivity is equivalent to bounded
Fenchel conjugate values on every bounded set. -/
theorem supercoercive_iff_conjugate_boundedOnEveryBoundedSet
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    Supercoercive f.asEReal ↔
      ∀ B : Set H, Bornology.IsBounded B →
        ∃ M : ℝ, ∀ u ∈ B, f.asEReal∗ u ≤ M := by
  constructor
  · intro hsuper B hB
    rcases exists_linear_lower_bound_of_mem_gammaZero hf with ⟨L, C, hL_nonneg, hlower⟩
    rcases hB.subset_closedBall (0 : H) with ⟨R, hR⟩
    let ρ : ℝ := max R 0 + 1
    rw [supercoercive_iff_tendsto_norm_atTop, EReal.tendsto_nhds_top_iff_real] at hsuper
    have hquot :
        ∀ᶠ x : H in Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop,
          (ρ : EReal) < f.asEReal x / ‖x‖ := hsuper ρ
    rcases Filter.mem_comap.1 hquot with ⟨s, hs, hs_subset⟩
    rcases Filter.mem_atTop_sets.1 hs with ⟨R0, hR0⟩
    let S : ℝ := max R0 1
    have houtside :
        ∀ x : H, S ≤ ‖x‖ → (((ρ * ‖x‖ : ℝ) : EReal) ≤ f.asEReal x) := by
      intro x hx
      have hxR0 : R0 ≤ ‖x‖ := le_trans (le_max_left _ _) hx
      have hxone : (1 : ℝ) ≤ ‖x‖ := le_trans (le_max_right _ _) hx
      have hxmem : ‖x‖ ∈ s := hR0 _ hxR0
      have hquotx : (ρ : EReal) < f.asEReal x / ‖x‖ := hs_subset hxmem
      have hnorm_pos : (0 : EReal) < ‖x‖ := by
        exact_mod_cast lt_of_lt_of_le zero_lt_one hxone
      exact le_of_lt <| (EReal.lt_div_iff hnorm_pos (by simp)).1 hquotx
    let K : ℝ := S * R + L * S + C
    let M : ℝ := max 0 K
    refine ⟨M, ?_⟩
    intro u hu
    rw [conjugate_apply]
    refine iSup_le fun x ↦ ?_
    by_cases hxS : S ≤ ‖x‖
    · have huR : ‖u‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hR hu
      have hxu : ⟪x, u⟫_ℝ ≤ ρ * ‖x‖ := by
        calc
          ⟪x, u⟫_ℝ ≤ ‖x‖ * ‖u‖ := real_inner_le_norm x u
          _ ≤ ‖x‖ * R := by
            exact mul_le_mul_of_nonneg_left huR (norm_nonneg _)
          _ ≤ ‖x‖ * ρ := by
            have hRρ : R ≤ ρ := by
              dsimp [ρ]
              linarith [le_max_left R 0]
            exact mul_le_mul_of_nonneg_left hRρ (norm_nonneg _)
          _ = ρ * ‖x‖ := by ring
      have hpair : (((⟪x, u⟫_ℝ : ℝ) : EReal)) ≤ (((ρ * ‖x‖ : ℝ) : EReal)) := by
        exact_mod_cast hxu
      have hfx : (((ρ * ‖x‖ : ℝ) : EReal)) ≤ f.asEReal x := houtside x hxS
      have hdefect_nonpos : (((⟪x, u⟫_ℝ : ℝ) : EReal) - f.asEReal x) ≤ 0 := by
        exact (EReal.sub_nonpos).2 (le_trans hpair hfx)
      have hM_nonneg : (0 : EReal) ≤ M := by
        exact_mod_cast (le_max_left 0 K)
      exact le_trans hdefect_nonpos hM_nonneg
    · have hxS' : ‖x‖ ≤ S := le_of_not_ge hxS
      have huR : ‖u‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hR hu
      by_cases hx_top : f.asEReal x = ⊤
      · simp [hx_top]
      · have hx_bot : f.asEReal x ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < f.asEReal x from (f x).2)
        have hlower_real : -L * ‖x‖ - C ≤ (f.asEReal x).toReal := by
          have hlowerx : (((-L * ‖x‖ - C : ℝ) : EReal) ≤ f.asEReal x) := hlower x
          rw [show f.asEReal x = (((f.asEReal x).toReal : ℝ) : EReal) by
            symm
            exact EReal.coe_toReal hx_top hx_bot] at hlowerx
          exact_mod_cast hlowerx
        have hinner : ⟪x, u⟫_ℝ ≤ ‖x‖ * R := by
          calc
            ⟪x, u⟫_ℝ ≤ ‖x‖ * ‖u‖ := real_inner_le_norm x u
            _ ≤ ‖x‖ * R := by
              exact mul_le_mul_of_nonneg_left huR (norm_nonneg _)
        have hdefect_real : ⟪x, u⟫_ℝ - (f.asEReal x).toReal ≤ K := by
          have hdefect_aux :
              ⟪x, u⟫_ℝ - (f.asEReal x).toReal ≤ ‖x‖ * R + L * ‖x‖ + C := by
            linarith
          have hR_nonneg : 0 ≤ R := le_trans (norm_nonneg u) huR
          have hRS : ‖x‖ * R ≤ S * R := by
            exact mul_le_mul_of_nonneg_right hxS' hR_nonneg
          have hLS : L * ‖x‖ ≤ L * S := by
            exact mul_le_mul_of_nonneg_left hxS' hL_nonneg
          have haux :
              ‖x‖ * R + L * ‖x‖ + C ≤ K := by
            dsimp [K]
            linarith
          exact le_trans hdefect_aux haux
        have hdefect_cast :
            (((⟪x, u⟫_ℝ - (f.asEReal x).toReal : ℝ) : EReal)) ≤ (M : EReal) := by
          have hKM : K ≤ M := by
            dsimp [M]
            exact le_max_right 0 K
          exact_mod_cast (le_trans hdefect_real hKM)
        rw [show f.asEReal x = (((f.asEReal x).toReal : ℝ) : EReal) by
          symm
          exact EReal.coe_toReal hx_top hx_bot, ← EReal.coe_sub]
        exact hdefect_cast
  · intro hbounded
    rw [supercoercive_iff_tendsto_norm_atTop, EReal.tendsto_nhds_top_iff_real]
    intro ξ
    let α : NNReal := ⟨max ξ 0 + 1, by positivity⟩
    rcases hbounded (Metric.closedBall (0 : H) (α : ℝ)) Metric.isBounded_closedBall with
      ⟨M, hM⟩
    let S : ℝ := max 1 (|M| / ((α : ℝ) - ξ) + 1)
    have hS :
        ∀ᶠ x : H in Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop, S ≤ ‖x‖ := by
      exact
        (Filter.tendsto_comap :
          Filter.Tendsto (fun x : H ↦ ‖x‖)
            (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) Filter.atTop).eventually_ge_atTop S
    filter_upwards [hS] with x hx
    have hx_pos : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hx)
    let u : H := ((α : ℝ) / ‖x‖) • x
    have hu_mem : u ∈ Metric.closedBall (0 : H) (α : ℝ) := by
      have hu_norm : ‖u‖ = (α : ℝ) := by
        calc
          ‖u‖ = ‖((α : ℝ) / ‖x‖)‖ * ‖x‖ := by
            dsimp [u]
            rw [norm_smul, Real.norm_eq_abs]
          _ = (((α : ℝ) / ‖x‖) : ℝ) * ‖x‖ := by
            rw [Real.norm_of_nonneg]
            positivity
          _ = (α : ℝ) := by
            rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hx_pos.ne', mul_one]
      simp [Metric.mem_closedBall, dist_eq_norm, hu_norm]
    have hxu : ⟪x, u⟫_ℝ = (α : ℝ) * ‖x‖ := by
      calc
        ⟪x, u⟫_ℝ = ((α : ℝ) / ‖x‖) * ⟪x, x⟫_ℝ := by
          simp [u, real_inner_smul_right]
        _ = ((α : ℝ) / ‖x‖) * ‖x‖ ^ 2 := by
          rw [real_inner_self_eq_norm_sq]
        _ = (α : ℝ) * ‖x‖ := by
          field_simp [hx_pos.ne']
    by_cases hx_top : f.asEReal x = ⊤
    · have hnorm_pos : (0 : EReal) < ‖x‖ := by
        exact_mod_cast hx_pos
      rw [hx_top, EReal.top_div_of_pos_ne_top hnorm_pos (EReal.coe_ne_top ‖x‖)]
      simp
    · have hx_bot : f.asEReal x ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < f.asEReal x from (f x).2)
      have hconj :
          (((α : ℝ) * ‖x‖ : ℝ) : EReal) - f.asEReal x ≤ M := by
        calc
          (((α : ℝ) * ‖x‖ : ℝ) : EReal) - f.asEReal x =
              (((⟪x, u⟫_ℝ : ℝ) : EReal) - f.asEReal x) := by rw [hxu]
          _ ≤ f.asEReal∗ u := by
            exact le_iSup (fun y : H ↦ (((⟪y, u⟫_ℝ : ℝ) : EReal) - f.asEReal y)) x
          _ ≤ M := hM u hu_mem
      rw [show f.asEReal x = (((f.asEReal x).toReal : ℝ) : EReal) by
        symm
        exact EReal.coe_toReal hx_top hx_bot, ← EReal.coe_sub] at hconj
      have hconj_real : (α : ℝ) * ‖x‖ - (f.asEReal x).toReal ≤ M := by
        exact_mod_cast hconj
      have hαξ_pos : 0 < (α : ℝ) - ξ := by
        dsimp [α]
        linarith [le_max_left ξ 0]
      have htail : ξ * ‖x‖ + M < (α : ℝ) * ‖x‖ := by
        dsimp [S] at hx
        have habs_lt : |M| < ((α : ℝ) - ξ) * ‖x‖ := by
          have hdiv_lt : |M| / ((α : ℝ) - ξ) < ‖x‖ := by
            linarith [le_trans (le_max_right _ _) hx]
          simpa [mul_comm] using (div_lt_iff₀ hαξ_pos).1 hdiv_lt
        have hM_lt : M < ((α : ℝ) - ξ) * ‖x‖ := by
          exact lt_of_le_of_lt (le_abs_self M) habs_lt
        linarith
      have hfx_real : ξ * ‖x‖ < (f.asEReal x).toReal := by
        linarith
      have hfx :
          ((ξ : EReal) * ‖x‖) < f.asEReal x := by
        rw [show f.asEReal x = (((f.asEReal x).toReal : ℝ) : EReal) by
          symm
          exact EReal.coe_toReal hx_top hx_bot]
        exact_mod_cast hfx_real
      have hnorm_pos : (0 : EReal) < ‖x‖ := by
        exact_mod_cast hx_pos
      exact (EReal.lt_div_iff hnorm_pos (by simp)).2 (by simpa [mul_comm] using hfx)

/-- Helper for Proposition 16 20: the Fenchel conjugate of `f` is supercoercive exactly when `f`
is bounded above on every bounded set. -/
lemma supercoercive_conjugate_iff_upper_boundedOnEveryBoundedSet
    (f : H → ℝ) (hf : f.toEReal ∈ Γ₀(H)) :
    Supercoercive f.toEReal.asEReal∗ ↔
      ∀ B : Set H, Bornology.IsBounded B →
        ∃ M : ℝ, ∀ x ∈ B, (f x : EReal) ≤ M := by
  constructor
  · intro hsuper
    rcases
        (supercoercive_iff_conjugate_boundedOnEveryBoundedSet
          (f := f.toEReal∗[hf]) (hf := gammaZeroConjugate_mem_gammaZero hf)).1 hsuper with
      hbounded
    intro B hB
    rcases hbounded B hB with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro x hx
    have hx_conj : ((f.toEReal∗[hf]).asEReal∗ x) ≤ M := by
      simpa [gammaZeroConjugate_apply] using hM x hx
    rwa [gammaZeroConjugate_biconjugate_apply (f := f) (hf := hf)] at hx_conj
  · intro hbounded
    apply
      (supercoercive_iff_conjugate_boundedOnEveryBoundedSet
        (f := f.toEReal∗[hf]) (hf := gammaZeroConjugate_mem_gammaZero hf)).2
    intro B hB
    rcases hbounded B hB with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro x hx
    rw [gammaZeroConjugate_biconjugate_apply (f := f) (hf := hf)]
    exact hM x hx

omit [CompleteSpace H] in
/-- Helper for Proposition 16 20: on continuous convex real-valued functions, boundedness on every
bounded set is equivalent to a bounded-set Lipschitz estimate. -/
lemma boundedOnEveryBoundedSet_iff_lipschitzOnEveryBoundedSet_of_continuous_convex
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f) :
    (∀ B : Set H, Bornology.IsBounded B → Bornology.IsBounded (f '' B)) ↔
      (∀ B : Set H, Bornology.IsBounded B → ∃ β : NNReal, LipschitzOnWith β f B) := by
  let _ := hcont
  have hconv_toEReal : ConvexOn f.toEReal (effectiveDomain f.toEReal) :=
    convexOn_toEReal_of_convexOn_univ f hconv
  constructor
  · intro hbounded B hB
    by_cases hBempty : B.Nonempty
    · rcases hBempty with ⟨x₀, hx₀⟩
      rcases hB.subset_ball x₀ with ⟨R, hR⟩
      have hRpos : 0 < R := by
        simpa [Metric.mem_ball] using hR hx₀
      have hx₀_dom : x₀ ∈ effectiveDomain f.toEReal := by
        simp [Function.effectiveDomain_toEReal]
      have hball_dom : Metric.ball x₀ (2 * R) ⊆ effectiveDomain f.toEReal := by
        simp [Function.effectiveDomain_toEReal]
      have hbig_bounded :
          Bornology.IsBounded (((fun y ↦ (f.toEReal y : EReal).toReal) '' Metric.ball x₀ (2 * R)) :
            Set ℝ) := by
        -- Clause `(1)` applied to the doubled ball supplies the Chapter 8 bounded-image input.
        simpa [Function.toEReal_apply] using hbounded (Metric.ball x₀ (2 * R)) Metric.isBounded_ball
      let β : NNReal :=
        ⟨Metric.diam
            (((fun z ↦ (f.toEReal z : EReal).toReal) '' Metric.ball x₀ (2 * R)) : Set ℝ) / R,
          by positivity⟩
      refine ⟨β, LipschitzOnWith.of_dist_le_mul ?_⟩
      intro x hx y hy
      have hx_ball : x ∈ Metric.ball x₀ R := hR hx
      have hy_ball : y ∈ Metric.ball x₀ R := hR hy
      -- Route correction: prove the bounded-set Lipschitz estimate by restricting the Chapter 8
      -- doubled-ball theorem, instead of rebuilding the oscillation argument inline.
      simpa [β, dist_eq_norm, Real.norm_eq_abs, Function.toEReal_apply] using
        lipschitz_bound_on_ball_of_bounded_image
          (f := f.toEReal) hconv_toEReal hRpos hx₀_dom hball_dom hbig_bounded
          hx_ball hy_ball
          (by simp [Function.effectiveDomain_toEReal])
          (by simp [Function.effectiveDomain_toEReal])
    · have hB' : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hBempty
      refine ⟨0, LipschitzOnWith.of_dist_le_mul ?_⟩
      intro x hx y hy
      simp [hB'] at hx
  · intro hLip B hB
    rcases hLip B hB with ⟨β, hβ⟩
    -- A Lipschitz map sends bounded sets to bounded sets.
    exact bounded_image_of_lipschitzOnWith_real f hB hβ

/-- Helper for Proposition 16 20: on continuous convex real-valued functions, bounded-set
Lipschitz control is equivalent to everywhere subdifferentiability together with bounded
subdifferential image on bounded sets. -/
lemma lipschitzOnEveryBoundedSet_iff_subdifferential_boundedImage_of_continuous_convex
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f) :
    (∀ B : Set H, Bornology.IsBounded B → ∃ β : NNReal, LipschitzOnWith β f B) ↔
      ((∀ x : H, SubdifferentiableAt f.toEReal x) ∧
        ∀ B : Set H, Bornology.IsBounded B →
          Bornology.IsBounded (SetValuedOperator.image (∂ f.toEReal) B)) := by
  have hconv_toEReal : ConvexOn f.toEReal (effectiveDomain f.toEReal) :=
    convexOn_toEReal_of_convexOn_univ f hconv
  constructor
  · intro hLip
    refine ⟨?_, ?_⟩
    · intro x
      have hxcont : ContinuousAtOnEffectiveDomain f.toEReal x :=
        continuousAtOnEffectiveDomain_toEReal_of_continuous f hcont x
      -- Proposition 16.17(ii) supplies a nonempty subdifferential at every continuity point.
      rw [subdifferentiableAt_iff_mem_dom, SetValuedOperator.mem_dom_iff]
      exact
        (subdifferential_nonempty_and_weaklyCompact_of_continuousAtOnEffectiveDomain
          (f := f.toEReal) hconv_toEReal hxcont).1
    · intro B hB
      by_cases hBempty : B.Nonempty
      · rcases hBempty with ⟨x₀, hx₀⟩
        rcases hB.subset_ball x₀ with ⟨R, hR⟩
        have hRpos : 0 < R := by
          simpa [Metric.mem_ball] using hR hx₀
        rcases hLip (Metric.ball x₀ (R + 1)) Metric.isBounded_ball with ⟨β, hβ⟩
        have hsubset :
            SetValuedOperator.image (∂ f.toEReal) B ⊆ Metric.closedBall (0 : H) β := by
          intro u hu
          rcases (SetValuedOperator.mem_image _ _ _).1 hu with ⟨x, hxB, hux⟩
          have hx_ball : x ∈ Metric.ball x₀ R := hR hxB
          have hnorm : ‖u‖ ≤ β :=
            norm_le_of_mem_subdifferential_of_lipschitzOn_buffer_ball
              (f := f) hx_ball hβ hux
          -- The local buffered-ball estimate gives a uniform closed-ball bound for all
          -- subgradients over `B`.
          rw [Metric.mem_closedBall, dist_eq_norm]
          simpa using hnorm
        exact Metric.isBounded_closedBall.subset hsubset
      · have hB' : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hBempty
        simp [SetValuedOperator.image, hB']
  · rintro ⟨hsub, himage⟩ B hB
    by_cases hBempty : B.Nonempty
    · have hImg_bounded :
          Bornology.IsBounded (SetValuedOperator.image (∂ f.toEReal) B) := himage B hB
      obtain ⟨R, hR⟩ := hImg_bounded.subset_closedBall (0 : H)
      let β : NNReal := ⟨max R 0, by positivity⟩
      have hsubset :
          SetValuedOperator.image (∂ f.toEReal) B ⊆ Metric.closedBall (0 : H) β := by
        intro u hu
        have hu_ball : u ∈ Metric.closedBall (0 : H) R := hR hu
        rw [Metric.mem_closedBall, dist_eq_norm] at hu_ball ⊢
        exact le_trans hu_ball (le_max_left _ _)
      refine ⟨β, ?_⟩
      -- Once the whole subdifferential image sits in one closed ball, the previously packaged
      -- subgradient estimate gives the Lipschitz bound on `B`.
      exact
        lipschitzOnWith_of_subdifferentiable_and_image_subset_closedBall
          (f := f) (B := B) (β := β) (fun x hx ↦ hsub x) hsubset
    · have hB' : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hBempty
      refine ⟨0, LipschitzOnWith.of_dist_le_mul ?_⟩
      intro x hx y hy
      simp [hB'] at hx

/-- Helper for Proposition 16 20: on continuous convex real-valued functions, boundedness on every
bounded set is equivalent to supercoercivity of the Fenchel conjugate. -/
lemma boundedOnEveryBoundedSet_iff_supercoercive_conjugate_of_continuous_convex
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f) :
    (∀ B : Set H, Bornology.IsBounded B → Bornology.IsBounded (f '' B)) ↔
      Supercoercive f.toEReal.asEReal∗ := by
  let hf : f.toEReal ∈ Γ₀(H) := real_toEReal_mem_gammaZero_of_continuous_convexOn_univ f hcont hconv
  have hsuper :
      Supercoercive f.toEReal.asEReal∗ ↔
        ∀ B : Set H, Bornology.IsBounded B →
          ∃ M : ℝ, ∀ x ∈ B, (f x : EReal) ≤ M :=
    supercoercive_conjugate_iff_upper_boundedOnEveryBoundedSet f hf
  constructor
  · intro hbounded
    refine hsuper.2 ?_
    intro B hB
    obtain ⟨R, hR⟩ := (hbounded B hB).subset_closedBall (0 : ℝ)
    refine ⟨R, ?_⟩
    intro x hx
    have hx_ball : f x ∈ Metric.closedBall (0 : ℝ) R := hR ⟨x, hx, rfl⟩
    have hreal : f x ≤ R := by
      -- Membership in a real closed ball gives the upper bound needed for Proposition 14.15.
      simpa using (abs_le.mp <| by simpa [Metric.mem_closedBall, Real.dist_eq] using hx_ball).2
    exact_mod_cast hreal
  · intro hsupercoercive B hB
    have hupper :
        ∀ C : Set H, Bornology.IsBounded C →
          ∃ M : ℝ, ∀ x ∈ C, (f x : EReal) ≤ M :=
      hsuper.1 hsupercoercive
    by_cases hBempty : B.Nonempty
    · rcases hBempty with ⟨x₀, hx₀⟩
      rcases hB.subset_ball x₀ with ⟨R, hR⟩
      have hRpos : 0 < R := by
        simpa [Metric.mem_ball] using hR hx₀
      rcases hupper (Metric.ball x₀ (2 * R)) Metric.isBounded_ball with ⟨M, hM⟩
      have hM_real : ∀ y ∈ Metric.ball x₀ (2 * R), f y ≤ M := by
        intro y hy
        exact_mod_cast hM y hy
      have hball_bounded :
          Bornology.IsBounded (f '' Metric.ball x₀ R) :=
        bounded_image_of_upper_bound_on_buffer_ball (f := f) hconv hRpos hM_real
      exact hball_bounded.subset <| by
        intro z hz
        rcases hz with ⟨x, hx, rfl⟩
        exact ⟨x, hR hx, rfl⟩
    · have hB' : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hBempty
      simp [hB']

/-- Helper for Proposition 16 20: three chapter-level equivalence bridges package into the final
four-clause `TFAE`. -/
lemma tfae_of_three_bridges
    {P1 P2 P3 P4 : Prop}
    (h12 : P1 ↔ P2) (h23 : P2 ↔ P3) (h14 : P1 ↔ P4) :
    List.TFAE [P1, P2, P3, P4] := by
  -- Route correction: isolate the purely propositional `TFAE` packaging so the main theorem only
  -- records the source-faithful chapter bridges `(1↔2)`, `(2↔3)`, and `(1↔4)`.
  tfae_have 1 ↔ 2 := by
    exact h12
  tfae_have 2 ↔ 3 := by
    exact h23
  tfae_have 1 ↔ 4 := by
    exact h14
  tfae_finish

-- Proof sketch: combine the Chapter 8 local boundedness and local Lipschitz criteria for convex
-- real-valued functions on bounded balls with Proposition 16.17 for subdifferentials and
-- Proposition 14.15 for Fenchel conjugates. The finite-dimensional conclusion then follows from
-- the bounded-set Lipschitz theorem on closed bounded subsets together with the first
-- equivalence.
set_option linter.style.longLine false in
/-- Proposition 16 20: for a continuous convex real-valued function on a real Hilbert space, the
following are equivalent: boundedness on every bounded subset, Lipschitz continuity on every
bounded subset, global subdifferentiability with bounded subdifferential image on bounded sets, and
supercoercivity of the Fenchel conjugate. -/
theorem continuous_convex_tfae_boundedOnEveryBoundedSet_lipschitzOnEveryBoundedSet_subdifferential_boundedImage_supercoercive_conjugate
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f) :
    List.TFAE
      [∀ B : Set H, Bornology.IsBounded B → Bornology.IsBounded (f '' B),
        ∀ B : Set H, Bornology.IsBounded B → ∃ β : NNReal, LipschitzOnWith β f B,
        (∀ x : H, SubdifferentiableAt f.toEReal x) ∧
          ∀ B : Set H, Bornology.IsBounded B →
            Bornology.IsBounded (SetValuedOperator.image (∂ f.toEReal) B),
        Supercoercive f.toEReal.asEReal∗] := by
  let P1 : Prop := ∀ B : Set H, Bornology.IsBounded B → Bornology.IsBounded (f '' B)
  let P2 : Prop := ∀ B : Set H, Bornology.IsBounded B → ∃ β : NNReal, LipschitzOnWith β f B
  let P3 : Prop := (∀ x : H, SubdifferentiableAt f.toEReal x) ∧
      ∀ B : Set H, Bornology.IsBounded B →
        Bornology.IsBounded (SetValuedOperator.image (∂ f.toEReal) B)
  let P4 : Prop := Supercoercive f.toEReal.asEReal∗
  have h12 : P1 ↔ P2 :=
    boundedOnEveryBoundedSet_iff_lipschitzOnEveryBoundedSet_of_continuous_convex
      f hcont hconv
  have h23 : P2 ↔ P3 :=
    lipschitzOnEveryBoundedSet_iff_subdifferential_boundedImage_of_continuous_convex
      f hcont hconv
  have h14 : P1 ↔ P4 :=
    boundedOnEveryBoundedSet_iff_supercoercive_conjugate_of_continuous_convex
      f hcont hconv
  have htfae : List.TFAE [P1, P2, P3, P4] := by
    -- Package the already-proved chapter bridges through the standalone propositional helper.
    exact tfae_of_three_bridges h12 h23 h14
  simpa [P1, P2, P3, P4] using htfae

end BoundednessAndSubdifferentialRegularity

section FiniteDimensionalBoundedness

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

-- Proof sketch: Corollary 8.40 first promotes convexity on `Set.univ` to continuity, so the
-- finite-dimensional conclusion does not need continuity as primitive data. Corollary 8.41 then
-- gives a Lipschitz constant for `f` on the closure of any bounded set, and a Lipschitz map sends
-- bounded sets to bounded sets.
/-- In finite dimension, a convex real-valued function is bounded on every bounded subset of the
ambient real normed space. -/
theorem boundedOnEveryBoundedSet_of_convex_finiteDimensional
    (f : H → ℝ) (hconv : _root_.ConvexOn ℝ Set.univ f) (B : Set H)
    (hB : Bornology.IsBounded B) :
    Bornology.IsBounded (f '' B) := by
  have hcont : Continuous f :=
    hconv.locallyLipschitz.continuous
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  have hcompact : IsCompact (closure B) := by
    simpa [isClosed_closure.closure_eq] using hB.isCompact_closure
  have himage_compact : IsCompact (f '' closure B) := hcompact.image hcont
  -- In finite dimension, bounded sets have compact closure, and continuous images of compact sets
  -- are compact, hence bounded.
  exact himage_compact.isBounded.subset <| by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, subset_closure hx, rfl⟩

end FiniteDimensionalBoundedness

end ERealFunction
