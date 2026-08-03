import Mathlib
import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap03.Theorem_3_16_2
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Theorem_16_3
import BauschkeLean.Chap16.Proposition_16_17
import BauschkeLean.Chap17.Proposition_17_2
import BauschkeLean.Chap17.Theorem_17_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section DirectionalDerivativesAndSubgradients

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (f : H → Set.Ioi (⊥ : EReal))

private theorem continuousAtOnEffectiveDomain_of_continuousPoint
    {x : H} (hxcont : ContinuousPoint f x) :
    ContinuousAtOnEffectiveDomain f x := by
  simpa [ContinuousPoint] using
    (ContinuousAtOnEffectiveDomain.of_continuousAtInEffectiveDomain hxcont)

-- Proof sketch: Proposition 16.17 gives that `∂ f(x)` is nonempty at a continuity point on the
-- effective domain. Proposition 16.4 supplies closedness and convexity, and Theorem 3.16.1 then
-- upgrades these properties to the Chebyshev condition needed for the metric projection.
/-- The subdifferential at a continuity point on the effective domain is a Chebyshev set. -/
theorem isChebyshev_subdifferential_of_continuousAtOnEffectiveDomain
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousPoint f x) :
    IsChebyshev ((∂ f) x) := by
  -- Proposition 16.17 gives a subgradient, and Proposition 16.4 supplies closedness/convexity.
  have hnonempty : ((∂ f) x).Nonempty :=
    (subdifferential_nonempty_and_weaklyCompact_of_continuousPoint f hconv hxcont).1
  exact isChebyshev_of_nonempty_isClosed_convex hnonempty
    (isClosed_subdifferential f x) (convex_subdifferential f x)

/-- The projection of `0` onto the subdifferential at a continuity point on the effective domain,
that is, the minimal-norm subgradient at `x`. -/
def minimalNormSubgradient
    (hconv : ConvexOn f (effectiveDomain f))
    (x : H) (hxcont : ContinuousPoint f x) : H :=
  projectionPoint ((∂ f) x)
    (isChebyshev_subdifferential_of_continuousAtOnEffectiveDomain f hconv hxcont) 0

-- Proof sketch: unfold `minimalNormSubgradient` and apply the defining best-approximation theorem
-- for `projectionPoint` on the Chebyshev set `(∂ f) x`.
/-- The minimal-norm subgradient is the best approximation of `0` from the subdifferential. -/
theorem minimalNormSubgradient_isBestApproximation_zero_of_continuousAtOnEffectiveDomain
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousPoint f x) :
    IsBestApproximation 0 ((∂ f) x) (minimalNormSubgradient f hconv x hxcont) := by
  -- Unfold the projector definition and apply the owner theorem for `projectionPoint`.
  simpa [minimalNormSubgradient] using
    projectionPoint_isBestApproximation ((∂ f) x)
      (isChebyshev_subdifferential_of_continuousAtOnEffectiveDomain f hconv hxcont) (0 : H)

-- Proof sketch: if the minimal-norm subgradient were `0`, then `0 ∈ (∂ f) x`. Fermat's rule
-- identifies zeros of the subdifferential with global minimizers, contradicting `x ∉ Argmin f`.
/-- A nonminimizer has a nonzero minimal-norm subgradient at every continuity point on the
effective domain. -/
theorem minimalNormSubgradient_ne_zero_of_continuousAtOnEffectiveDomain_of_not_mem_argmin
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousPoint f x)
    (hxnotmin : x ∉ Argmin f.asEReal) :
    minimalNormSubgradient f hconv x hxcont ≠ 0 := by
  -- If the projector were `0`, Fermat's rule would make `x` a global minimizer.
  have hu_mem : minimalNormSubgradient f hconv x hxcont ∈ (∂ f) x :=
    (minimalNormSubgradient_isBestApproximation_zero_of_continuousAtOnEffectiveDomain
      f hconv hxcont).1
  intro hu_zero
  have hzero_mem : (0 : H) ∈ (∂ f) x := by
    simpa [hu_zero] using hu_mem
  have hxmin : x ∈ Argmin f.asEReal := by
    rw [argmin_eq_zeros_subdifferential, SetValuedOperator.mem_zeros_iff]
    exact hzero_mem
  exact hxnotmin hxmin

/-- The normalized negative minimal-norm subgradient, i.e. the steepest descent direction
associated with `f` at `x`. -/
def steepestDescentDirection
    (hconv : ConvexOn f (effectiveDomain f))
    (x : H) (hxcont : ContinuousPoint f x) : H :=
  let u := minimalNormSubgradient f hconv x hxcont;
  -(‖u‖)⁻¹ • u

-- Proof sketch: write the steepest descent direction as `-(‖u‖)⁻¹ • u` with
-- `u = minimalNormSubgradient ...`. The previous theorem gives `u ≠ 0`, so
-- `‖(‖u‖)⁻¹ • u‖ = ‖u‖⁻¹ * ‖u‖ = 1`.
/-- For a nonminimizer, the steepest descent direction has norm `1`. -/
theorem norm_steepestDescentDirection_eq_one_of_continuousAtOnEffectiveDomain_of_not_mem_argmin
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousPoint f x)
    (hxnotmin : x ∉ Argmin f.asEReal) :
    ‖steepestDescentDirection f hconv x hxcont‖ = 1 := by
  let u := minimalNormSubgradient f hconv x hxcont
  have hu_ne : u ≠ 0 := by
    -- The normalization is legitimate because the minimal-norm subgradient is nonzero.
    intro hu_zero
    exact
      (minimalNormSubgradient_ne_zero_of_continuousAtOnEffectiveDomain_of_not_mem_argmin
        f hconv hxcont hxnotmin) (by simpa [u] using hu_zero)
  have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have hnorm_ne : ‖u‖ ≠ 0 := hnorm_pos.ne'
  -- Compute the norm of the normalized negative projector explicitly.
  calc
    ‖steepestDescentDirection f hconv x hxcont‖ = ‖(-(‖u‖)⁻¹) • u‖ := by
      simp [steepestDescentDirection, u]
    _ = ‖(-‖u‖⁻¹ : ℝ)‖ * ‖u‖ := by
      rw [norm_smul]
    _ = ‖u‖⁻¹ * ‖u‖ := by
      rw [Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hnorm_pos)]
    _ = 1 := by
      rw [inv_mul_cancel₀ hnorm_ne]

/-- Helper for Proposition 17 22: the minimal-norm subgradient belongs to the subdifferential. -/
theorem minimalNormSubgradient_mem_subdifferential_of_continuousAtOnEffectiveDomain
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousPoint f x) :
    minimalNormSubgradient f hconv x hxcont ∈ (∂ f) x := by
  -- The best-approximation characterization includes membership in the target set.
  exact
    (minimalNormSubgradient_isBestApproximation_zero_of_continuousAtOnEffectiveDomain
      f hconv hxcont).1

/-- Helper for Proposition 17 22: every subgradient pairs with the minimal-norm subgradient at
least by its squared norm. -/
theorem sq_norm_minimalNormSubgradient_le_inner_of_mem_subdifferential
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousPoint f x)
    {v : H} (hv : v ∈ (∂ f) x) :
    ‖minimalNormSubgradient f hconv x hxcont‖ ^ 2 ≤
      ⟪v, minimalNormSubgradient f hconv x hxcont⟫_ℝ := by
  let u := minimalNormSubgradient f hconv x hxcont
  have hu_char :
      u ∈ (∂ f) x ∧
        ∀ y ∈ (∂ f) x, ⟪y - u, (0 : H) - u⟫_ℝ ≤ 0 := by
    -- Theorem 3.16.2 rewrites the projection property into the standard variational inequality.
    exact
      (isBestApproximation_iff_mem_and_inner_sub_right_nonpos
        (convex_subdifferential f x)).mp <|
        by
          simpa [u] using
            minimalNormSubgradient_isBestApproximation_zero_of_continuousAtOnEffectiveDomain
              f hconv hxcont
  have hnonpos : ⟪v - u, (0 : H) - u⟫_ℝ ≤ 0 := hu_char.2 v hv
  -- Expanding the projection inequality isolates the key lower bound on `⟪v, u⟫`.
  rw [zero_sub, inner_sub_left, inner_neg_right, inner_neg_right,
    real_inner_self_eq_norm_sq] at hnonpos
  nlinarith

/-- Helper for Proposition 17 22: at a continuity point on the effective domain, every
subgradient gives a lower bound on the directional derivative through the support-function
representation. -/
theorem inner_le_directionalDerivative_of_mem_subdifferential_of_continuousAtOnEffectiveDomain
    (hconv : ConvexOn f (effectiveDomain f))
    {x u y : H} (hxcont : ContinuousPoint f x)
    (hu : u ∈ (∂ f) x) :
    (⟪y, u⟫_ℝ : EReal) ≤ f′(x; y) := by
  have hdir :
      f′(x; y) = σ[(∂ f) x] y := by
    exact congrArg (fun g : H → EReal ↦ g y)
      (directionalDerivative_eq_supportFunction_subdifferential_of_continuousAtOnEffectiveDomain
        f hconv (continuousAtOnEffectiveDomain_of_continuousPoint f hxcont))
  -- The support function is the supremum over the inner products with subgradients.
  calc
    (⟪y, u⟫_ℝ : EReal) = (⟪u, y⟫_ℝ : EReal) := by rw [real_inner_comm]
    _ ≤ σ[(∂ f) x] y := by
      rw [supportFunction_eq_sSup_image]
      exact (isLUB_sSup _).1 (Set.mem_image_of_mem (fun v : H ↦ (⟪v, y⟫_ℝ : EReal)) hu)
    _ = f′(x; y) := hdir.symm

/-- Helper for Proposition 17 22: the steepest descent direction pairs with the minimal-norm
subgradient to give the negative norm. -/
theorem real_inner_steepestDescentDirection_minimalNormSubgradient_eq_neg_norm
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousPoint f x)
    (hxnotmin : x ∉ Argmin f.asEReal) :
    ⟪steepestDescentDirection f hconv x hxcont,
      minimalNormSubgradient f hconv x hxcont⟫_ℝ =
        -‖minimalNormSubgradient f hconv x hxcont‖ := by
  let u := minimalNormSubgradient f hconv x hxcont
  have hu_ne : u ≠ 0 := by
    -- The nonminimizer assumption rules out the zero projector.
    intro hu_zero
    exact
      (minimalNormSubgradient_ne_zero_of_continuousAtOnEffectiveDomain_of_not_mem_argmin
        f hconv hxcont hxnotmin) (by simpa [u] using hu_zero)
  have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have hnorm_ne : ‖u‖ ≠ 0 := hnorm_pos.ne'
  -- Rewrite the inner product through the scalar multiple defining the descent direction.
  calc
    ⟪steepestDescentDirection f hconv x hxcont, u⟫_ℝ = ⟪(-(‖u‖)⁻¹) • u, u⟫_ℝ := by
      simp [steepestDescentDirection, u]
    _ = (-(‖u‖)⁻¹ : ℝ) * ⟪u, u⟫_ℝ := by
      rw [real_inner_smul_left]
    _ = (-(‖u‖)⁻¹ : ℝ) * ‖u‖ ^ 2 := by
      rw [real_inner_self_eq_norm_sq]
    _ = -‖u‖ := by
      rw [pow_two]
      field_simp [hnorm_ne]

/-- Helper for Proposition 17 22: every closed-unit-ball direction makes angle at least
`-‖u‖` with the minimal-norm subgradient `u`. -/
theorem neg_norm_minimalNormSubgradient_le_inner_of_mem_closedBall
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hxcont : ContinuousPoint f x)
    (hy : y ∈ Metric.closedBall (0 : H) 1) :
    -‖minimalNormSubgradient f hconv x hxcont‖ ≤
      ⟪y, minimalNormSubgradient f hconv x hxcont⟫_ℝ := by
  let u := minimalNormSubgradient f hconv x hxcont
  have hy_norm : ‖y‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hy
  have habs : |⟪y, u⟫_ℝ| ≤ ‖y‖ * ‖u‖ := abs_real_inner_le_norm y u
  have hmul : ‖y‖ * ‖u‖ ≤ ‖u‖ := by
    nlinarith [norm_nonneg u, hy_norm]
  -- Cauchy-Schwarz gives the lower bound after passing through the absolute value.
  exact neg_le_of_abs_le (le_trans habs hmul)

/-- Helper for Proposition 17 22: the steepest descent direction attains directional derivative
value `-‖u‖`, where `u` is the minimal-norm subgradient. -/
theorem directionalDerivative_steepestDescentDirection_eq_neg_norm_minimalNormSubgradient
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousPoint f x)
    (hxnotmin : x ∉ Argmin f.asEReal) :
    f′(x; steepestDescentDirection f hconv x hxcont) =
      (-‖minimalNormSubgradient f hconv x hxcont‖ : EReal) := by
  let u := minimalNormSubgradient f hconv x hxcont
  let z := steepestDescentDirection f hconv x hxcont
  have hx : x ∈ effectiveDomain f :=
    (continuousAtOnEffectiveDomain_of_continuousPoint f hxcont).mem_effectiveDomain
  have hu_mem : u ∈ (∂ f) x := by
    simpa [u] using
      minimalNormSubgradient_mem_subdifferential_of_continuousAtOnEffectiveDomain
        f hconv hxcont
  have hz_lower :
      (-‖u‖ : EReal) ≤ f′(x; z) := by
    -- The minimal-norm subgradient itself gives the matching lower bound.
    have hinner_le :
        (⟪z, u⟫_ℝ : EReal) ≤ f′(x; z) :=
      inner_le_directionalDerivative_of_mem_subdifferential_of_continuousAtOnEffectiveDomain
        f hconv hxcont hu_mem
    have hz_inner : (⟪z, u⟫_ℝ : EReal) = (-‖u‖ : EReal) := by
      exact_mod_cast
        real_inner_steepestDescentDirection_minimalNormSubgradient_eq_neg_norm
          f hconv hxcont hxnotmin
    simpa [hz_inner] using hinner_le
  rcases exists_subgradient_eq_directionalDerivative_of_continuousAtOnEffectiveDomain
      f hconv (continuousAtOnEffectiveDomain_of_continuousPoint f hxcont) z with
    ⟨v, hv, hvdir⟩
  have hv_lower :
      ‖u‖ ^ 2 ≤ ⟪v, u⟫_ℝ := by
    simpa [u] using
      sq_norm_minimalNormSubgradient_le_inner_of_mem_subdifferential
        f hconv hxcont hv
  have hu_ne : u ≠ 0 := by
    -- The steepest descent direction uses a genuine normalization.
    intro hu_zero
    exact
      (minimalNormSubgradient_ne_zero_of_continuousAtOnEffectiveDomain_of_not_mem_argmin
        f hconv hxcont hxnotmin) (by simpa [u] using hu_zero)
  have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have hv_upper_real : ⟪z, v⟫_ℝ ≤ -‖u‖ := by
    -- The projection inequality forces every attaining subgradient to give at most `-‖u‖`.
    have hinner_formula :
        ⟪z, v⟫_ℝ = (-(‖u‖)⁻¹ : ℝ) * ⟪v, u⟫_ℝ := by
      calc
        ⟪z, v⟫_ℝ = ⟪steepestDescentDirection f hconv x hxcont, v⟫_ℝ := by
          rfl
        _ = ⟪(-(‖u‖)⁻¹ : ℝ) • u, v⟫_ℝ := by
          simp [steepestDescentDirection, u]
        _ = (-(‖u‖)⁻¹ : ℝ) * ⟪u, v⟫_ℝ := by
          rw [real_inner_smul_left]
        _ = (-(‖u‖)⁻¹ : ℝ) * ⟪v, u⟫_ℝ := by
          rw [real_inner_comm]
    rw [hinner_formula]
    have hscaled :
        ‖u‖ ≤ ‖u‖⁻¹ * ⟪v, u⟫_ℝ := by
      have hscaled' :
          ‖u‖⁻¹ * ‖u‖ ^ 2 ≤ ‖u‖⁻¹ * ⟪v, u⟫_ℝ := by
        exact mul_le_mul_of_nonneg_left hv_lower (inv_nonneg.mpr hnorm_pos.le)
      have hleft : ‖u‖⁻¹ * ‖u‖ ^ 2 = ‖u‖ := by
        rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hnorm_pos.ne', one_mul]
      simpa [hleft] using hscaled'
    have hneg : -(‖u‖⁻¹ * ⟪v, u⟫_ℝ) ≤ -‖u‖ := neg_le_neg hscaled
    simpa [neg_mul] using hneg
  have hz_upper : f′(x; z) ≤ (-‖u‖ : EReal) := by
    -- Cast the real upper bound back to the directional derivative value.
    rw [hvdir]
    exact EReal.coe_le_coe hv_upper_real
  exact le_antisymm hz_upper hz_lower

/-- Helper for Proposition 17 22: a closed-unit-ball direction attaining the minimal directional
derivative value must equal the steepest descent direction. -/
theorem eq_steepestDescentDirection_of_mem_closedBall_of_directionalDerivative_eq_neg_norm
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hxcont : ContinuousPoint f x)
    (hxnotmin : x ∉ Argmin f.asEReal)
    (hy : y ∈ Metric.closedBall (0 : H) 1)
    (hyval :
      f′(x; y) = (-‖minimalNormSubgradient f hconv x hxcont‖ : EReal)) :
    y = steepestDescentDirection f hconv x hxcont := by
  let u := minimalNormSubgradient f hconv x hxcont
  let z := steepestDescentDirection f hconv x hxcont
  have hu_mem : u ∈ (∂ f) x := by
    simpa [u] using
      minimalNormSubgradient_mem_subdifferential_of_continuousAtOnEffectiveDomain
        f hconv hxcont
  have hzu_norm : ‖z‖ = 1 := by
    simpa [z] using
      norm_steepestDescentDirection_eq_one_of_continuousAtOnEffectiveDomain_of_not_mem_argmin
        f hconv hxcont hxnotmin
  have hy_inner_lower : (-‖u‖ : EReal) ≤ (⟪y, u⟫_ℝ : EReal) := by
    -- Closed-ball vectors satisfy the Cauchy-Schwarz lower bound against `u`.
    exact EReal.coe_le_coe <|
      by simpa [u] using
        neg_norm_minimalNormSubgradient_le_inner_of_mem_closedBall f hconv hxcont hy
  have hy_inner_upper : (⟪y, u⟫_ℝ : EReal) ≤ (-‖u‖ : EReal) := by
    -- The subgradient inequality and the assumed minimizing value trap the inner product.
    have hdir_lower :
        (⟪y, u⟫_ℝ : EReal) ≤ f′(x; y) :=
      inner_le_directionalDerivative_of_mem_subdifferential_of_continuousAtOnEffectiveDomain
        f hconv hxcont hu_mem
    simpa [hyval] using hdir_lower
  have hy_inner_eq : ⟪y, u⟫_ℝ = -‖u‖ := by
    exact EReal.coe_eq_coe_iff.mp (le_antisymm hy_inner_upper hy_inner_lower)
  have hyz_inner : ⟪y, z⟫_ℝ = 1 := by
    -- Normalize by `‖u‖` and substitute the equality `⟪y, u⟫ = -‖u‖`.
    have hu_ne : u ≠ 0 := by
      intro hu_zero
      exact
        (minimalNormSubgradient_ne_zero_of_continuousAtOnEffectiveDomain_of_not_mem_argmin
          f hconv hxcont hxnotmin) (by simpa [u] using hu_zero)
    have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
    have hnorm_ne : ‖u‖ ≠ 0 := hnorm_pos.ne'
    calc
      ⟪y, z⟫_ℝ = ⟪y, (-(‖u‖)⁻¹ : ℝ) • u⟫_ℝ := by
        calc
          ⟪y, z⟫_ℝ = ⟪y, steepestDescentDirection f hconv x hxcont⟫_ℝ := by
            rfl
          _ = ⟪y, (-(‖u‖)⁻¹ : ℝ) • u⟫_ℝ := by
            simp [steepestDescentDirection, u]
      _ = (-(‖u‖)⁻¹ : ℝ) * ⟪y, u⟫_ℝ := by
        rw [real_inner_smul_right]
      _ = (-(‖u‖)⁻¹ : ℝ) * (-‖u‖) := by rw [hy_inner_eq]
      _ = 1 := by
        field_simp [hnorm_ne]
  have hy_norm_sq_le : ‖y‖ ^ 2 ≤ 1 := by
    have hy_norm : ‖y‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    nlinarith [norm_nonneg y, hy_norm]
  have hyz_sq : ‖y - z‖ ^ 2 ≤ 0 := by
    -- Expanding the squared distance shows it is forced to vanish.
    rw [norm_sub_sq_real, hyz_inner, hzu_norm]
    nlinarith
  have hyz_zero : y - z = 0 := by
    apply norm_eq_zero.mp
    exact sq_eq_zero_iff.mp <| le_antisymm hyz_sq (sq_nonneg ‖y - z‖)
  exact sub_eq_zero.mp hyz_zero

-- Proof sketch: Theorem 17.18 rewrites `f′(x; ·)` as the support function of
-- `(∂ f) x`. The projection characterization of `u := minimalNormSubgradient ...` gives
-- `max ⟪-u, (∂ f) x - u⟫ = 0`, so the normalized vector
-- `z := steepestDescentDirection ...` attains the value `-‖u‖` on the support function. Every
-- `y ∈ closedBall 0 1` satisfies `⟪y, u⟫ ≥ -‖u‖` by Cauchy--Schwarz, hence no smaller directional
-- derivative value is possible; equality forces `y = z`.
/-- Proposition 17 22: if `x` is a continuity point on the effective domain of a convex function
but not a global minimizer, then the steepest descent direction obtained by normalizing the
negative metric projection of `0` onto `(∂ f) x` is the unique minimizer of `f′(x; ·)` on the
closed unit ball. -/
theorem argminOn_closedUnitBall_directionalDerivative_eq_singleton_steepestDescentDirection
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousPoint f x)
    (hxnotmin : x ∉ Argmin f.asEReal) :
    Argmin[Metric.closedBall 0 1] (f′(x; ·)) =
      {steepestDescentDirection f hconv x hxcont} := by
  let u := minimalNormSubgradient f hconv x hxcont
  let z := steepestDescentDirection f hconv x hxcont
  have hz_value :
      f′(x; z) = (-‖u‖ : EReal) := by
    simpa [u, z] using
      directionalDerivative_steepestDescentDirection_eq_neg_norm_minimalNormSubgradient
        f hconv hxcont hxnotmin
  have hz_ball : z ∈ Metric.closedBall (0 : H) 1 := by
    -- The candidate is feasible because its norm is exactly `1`.
    have hz_norm : ‖z‖ = 1 := by
      simpa [z] using
        norm_steepestDescentDirection_eq_one_of_continuousAtOnEffectiveDomain_of_not_mem_argmin
          f hconv hxcont hxnotmin
    simp [Metric.mem_closedBall, dist_eq_norm, hz_norm]
  have hu_mem : u ∈ (∂ f) x := by
    simpa [u] using
      minimalNormSubgradient_mem_subdifferential_of_continuousAtOnEffectiveDomain
        f hconv hxcont
  ext y
  constructor
  · intro hy
    rcases mem_argminOn_iff.mp hy with ⟨hy_ball, hy_min⟩
    rw [isMinOn_iff] at hy_min
    have hy_lower : (-‖u‖ : EReal) ≤ f′(x; y) := by
      -- Every feasible direction has directional derivative at least `-‖u‖`.
      have hy_inner_lower : (-‖u‖ : EReal) ≤ (⟪y, u⟫_ℝ : EReal) := by
        exact EReal.coe_le_coe <|
          by simpa [u] using
            neg_norm_minimalNormSubgradient_le_inner_of_mem_closedBall
              f hconv hxcont hy_ball
      have hy_inner_upper : (⟪y, u⟫_ℝ : EReal) ≤ f′(x; y) :=
        inner_le_directionalDerivative_of_mem_subdifferential_of_continuousAtOnEffectiveDomain
          f hconv hxcont hu_mem
      exact le_trans hy_inner_lower hy_inner_upper
    have hy_value : f′(x; y) = (-‖u‖ : EReal) := by
      -- A minimizer must meet the candidate value, so the lower bound is sharp.
      have hy_upper : f′(x; y) ≤ (-‖u‖ : EReal) := by
        simpa [hz_value] using hy_min z hz_ball
      exact le_antisymm hy_upper hy_lower
    rw [Set.mem_singleton_iff]
    exact
      eq_steepestDescentDirection_of_mem_closedBall_of_directionalDerivative_eq_neg_norm
        f hconv hxcont hxnotmin hy_ball (by simpa [u] using hy_value)
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    refine mem_argminOn_iff.mpr ?_
    refine ⟨hz_ball, ?_⟩
    rw [isMinOn_iff]
    intro y hy_ball
    -- Compare every feasible direction to the candidate through the common lower bound `-‖u‖`.
    have hy_lower : (-‖u‖ : EReal) ≤ f′(x; y) := by
      have hy_inner_lower : (-‖u‖ : EReal) ≤ (⟪y, u⟫_ℝ : EReal) := by
        exact EReal.coe_le_coe <|
          by simpa [u] using
            neg_norm_minimalNormSubgradient_le_inner_of_mem_closedBall
              f hconv hxcont hy_ball
      have hy_inner_upper : (⟪y, u⟫_ℝ : EReal) ≤ f′(x; y) :=
        inner_le_directionalDerivative_of_mem_subdifferential_of_continuousAtOnEffectiveDomain
          f hconv hxcont hu_mem
      exact le_trans hy_inner_lower hy_inner_upper
    calc
      f′(x; z) = (-‖u‖ : EReal) := hz_value
      _ ≤ f′(x; y) := hy_lower

end DirectionalDerivativesAndSubgradients

end

end ERealFunction
