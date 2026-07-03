import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_61 (from Chap10) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (f : E → ℝ) (Lf : NNReal)

/- Definition 10.61 is recall-only. The non-Euclidean gradient method keeps the same source-facing
whole-space minimization setup as Definition 10.4.1; the only change is that the ambient norm on
`E` need not be Euclidean.

Domain sampling identifies the existing owners already used in the chapter:
- `unconstrained_problem_solutions` from Chapter 8 for the unconstrained minimization problem;
- `mem_unconstrained_problem_solutions_iff` for its companion minimizer characterization;
- `is_l_smooth_on` from Chapter 5 for the `L_f`-smoothness assumption;
- `is_l_smooth_on_iff` for the derivative-Lipschitz characterization of that assumption.

The primitive data here are only the objective `f` and the smoothness parameter `Lf`; the
problem and smoothness clauses are derived by direct reuse of the existing owners, so this file
should not keep a separate wrapper around the generic smoothness predicate alone. -/

/- Definition 10.61: the unconstrained problem `min {f(x) | x ∈ E}` is the Chapter 8 owner
`unconstrained_problem_solutions f`. -/
#check unconstrained_problem_solutions f

/- Definition 10.61: the standing non-Euclidean smoothness assumption is the whole-space
specialization `is_l_smooth_on f Set.univ Lf` of the Chapter 5 owner predicate. -/
#check is_l_smooth_on f Set.univ Lf

end

/-! ### Lemma_10_61 (from Chap10) -/
noncomputable section

universe u

open Metric

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The set `Λ_a` of primal counterparts of a dual vector `a`: the unit-ball points where the
pairing with `a` attains the operator norm. This is equivalent to the source's zero/nonzero
case split, but keeps only the canonical primitive data on the continuous dual. -/
def primalCounterparts (a : E →L[ℝ] ℝ) : Set E :=
  { x : E | ‖x‖ ≤ 1 ∧ a x = ‖a‖ }

end

notation "Λ[" a "]" => primalCounterparts a

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Lemma 10.61: a maximizer of a real linear functional on the symmetric closed unit
ball controls the absolute value of that functional everywhere on the ball. -/
lemma norm_apply_le_of_isMaxOn_closedBall
    {a : E →L[ℝ] ℝ} {x0 x : E}
    (_hx0 : x0 ∈ closedBall (0 : E) 1)
    (hmax : IsMaxOn a (closedBall (0 : E) 1) x0)
    (hx : x ∈ closedBall (0 : E) 1) :
    ‖a x‖ ≤ a x0 := by
  rw [isMaxOn_iff] at hmax
  have hnegx : -x ∈ closedBall (0 : E) 1 := by
    -- The closed unit ball is symmetric, so `-x` stays admissible.
    rw [mem_closedBall_zero_iff] at hx ⊢
    simpa [norm_neg] using hx
  have hx_le : a x ≤ a x0 :=
    hmax x hx
  have hnegx_le : -a x ≤ a x0 := by
    -- Evaluating at `-x` converts the maximizing inequality into the opposite-sign bound.
    simpa using hmax (-x) hnegx
  have hleft : -a x0 ≤ a x := by
    linarith
  have habs_le : |a x| ≤ a x0 :=
    abs_le.mpr ⟨hleft, hx_le⟩
  simpa [Real.norm_eq_abs] using habs_le

/-- Helper for Lemma 10.61: a maximizer of a real linear functional on the closed unit ball
attains at least the operator norm of that functional. -/
lemma norm_le_apply_of_isMaxOn_closedBall
    {a : E →L[ℝ] ℝ} {x0 : E}
    (hx0 : x0 ∈ closedBall (0 : E) 1)
    (hmax : IsMaxOn a (closedBall (0 : E) 1) x0) :
    ‖a‖ ≤ a x0 := by
  rw [isMaxOn_iff] at hmax
  have hzero_mem : (0 : E) ∈ closedBall (0 : E) 1 := by
    -- The origin is in the closed unit ball, so maximality makes `a x0` nonnegative.
    simp
  have hx0_nonneg : 0 ≤ a x0 := by
    simpa using hmax 0 hzero_mem
  have hbound : ∀ x : E, ‖a x‖ ≤ a x0 * ‖x‖ := by
    intro x
    by_cases hx : x = 0
    · -- The zero vector contributes the trivial bound.
      subst hx
      simp
    · have hnormx_ne : ‖x‖ ≠ 0 :=
        norm_ne_zero_iff.mpr hx
      let y : E := ‖x‖⁻¹ • x
      have hy_norm : ‖y‖ = 1 := by
        -- The normalized vector lies on the unit sphere.
        dsimp [y]
        calc
          ‖‖x‖⁻¹ • x‖ = ‖‖x‖⁻¹‖ * ‖x‖ := norm_smul _ _
          _ = ‖x‖⁻¹ * ‖x‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg]
            positivity
          _ = 1 := by
            rw [inv_mul_cancel₀ hnormx_ne]
      have hy_mem : y ∈ closedBall (0 : E) 1 := by
        -- Normalize `x` onto the unit sphere to use maximality on the unit ball.
        rw [mem_closedBall_zero_iff]
        exact hy_norm.le
      have hy_bound : ‖a y‖ ≤ a x0 :=
        norm_apply_le_of_isMaxOn_closedBall hx0 (isMaxOn_iff.mpr hmax) hy_mem
      have hx_eq : x = ‖x‖ • y := by
        -- Undo the normalization so the global operator-norm bound can be recovered.
        dsimp [y]
        rw [smul_smul, mul_inv_cancel₀ hnormx_ne, one_smul]
      calc
        ‖a x‖ = ‖a (‖x‖ • y)‖ := by
          exact congrArg (fun z ↦ ‖a z‖) hx_eq
        _ = ‖‖x‖ • a y‖ := by
          rw [map_smul]
        _ = ‖‖x‖‖ * ‖a y‖ := norm_smul _ _
        _ = ‖x‖ * ‖a y‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          exact norm_nonneg _
        _ ≤ ‖x‖ * a x0 := by
          exact mul_le_mul_of_nonneg_left hy_bound (norm_nonneg _)
        _ = a x0 * ‖x‖ := by
          rw [mul_comm]
  exact a.opNorm_le_bound hx0_nonneg hbound

-- Proof sketch: unfold `primalCounterparts`, rewrite unit-ball membership as `mem_closedBall`,
-- and express the maximizer condition by `isMaxOn_iff`. The forward implication uses the operator
-- norm bound `a v ≤ ‖a‖` on the closed unit ball. For the converse, the maximality hypothesis on
-- `aDagger` bounds `a` on every normalized vector and therefore forces `‖a‖ ≤ a aDagger`.
/-- A vector belongs to `Λ[a]` exactly when it lies in the closed unit ball and maximizes `a`
over that ball. -/
theorem mem_Λ_iff
    {a : E →L[ℝ] ℝ} {aDagger : E} :
    aDagger ∈ Λ[a] ↔
      aDagger ∈ closedBall (0 : E) 1 ∧ IsMaxOn a (closedBall (0 : E) 1) aDagger := by
  constructor
  · intro haDagger
    rcases haDagger with ⟨haDagger_norm, haDagger_eq⟩
    constructor
    · -- Rewrite the defining norm bound as closed-ball membership.
      rwa [mem_closedBall_zero_iff]
    · -- The defining norm attainment forces `aDagger` to maximize `a` on the closed unit ball.
      rw [isMaxOn_iff]
      intro x hx
      have hx_norm : ‖x‖ ≤ 1 := by
        rwa [mem_closedBall_zero_iff] at hx
      calc
        a x ≤ ‖a x‖ := le_abs_self _
        _ ≤ ‖a‖ := by
          simpa [Real.norm_eq_abs] using a.unit_le_opNorm x hx_norm
        _ = a aDagger := haDagger_eq.symm
  · rintro ⟨haDagger_ball, hmax⟩
    have haDagger_norm : ‖aDagger‖ ≤ 1 := by
      rwa [mem_closedBall_zero_iff] at haDagger_ball
    have hupper : a aDagger ≤ ‖a‖ := by
      -- The unit-ball bound gives the easy inequality `a aDagger ≤ ‖a‖`.
      have hnorm : ‖a aDagger‖ ≤ ‖a‖ :=
        a.unit_le_opNorm aDagger haDagger_norm
      exact (le_abs_self (a aDagger)).trans <| by
        simpa [Real.norm_eq_abs] using hnorm
    have hlower : ‖a‖ ≤ a aDagger :=
      norm_le_apply_of_isMaxOn_closedBall haDagger_ball hmax
    -- Combine the norm bound and maximality lower bound to recover the defining equality.
    constructor
    · exact haDagger_norm
    · exact le_antisymm hupper hlower

-- Proof sketch: unfold `primalCounterparts a`. The equality `a a† = ‖a‖` together with the
-- operator-norm inequality forces `‖a‖ ≤ ‖a‖ * ‖a†‖`; since `a ≠ 0`, the norm is positive, so
-- `1 ≤ ‖a†‖`. Combined with the defining bound `‖a†‖ ≤ 1`, this gives `‖a†‖ = 1`.
/-- Lemma 10.61 (1): if `a ≠ 0`, every primal counterpart `a† ∈ Λ_a` has norm `1`. -/
theorem norm_eq_one_of_mem_primalCounterparts
    {a : E →L[ℝ] ℝ} (ha : a ≠ 0) {aDagger : E}
    (haDagger : aDagger ∈ Λ[a]) :
    ‖aDagger‖ = 1 := by
  rcases haDagger with ⟨haDagger_norm, haDagger_eq⟩
  have hnorma_pos : 0 < ‖a‖ :=
    norm_pos_iff.mpr ha
  have hnorma_le : ‖a‖ ≤ ‖a‖ * ‖aDagger‖ := by
    -- Rewrite the norm-attainment equation into an operator-norm lower bound.
    calc
      ‖a‖ = ‖a aDagger‖ := by
        rw [haDagger_eq, Real.norm_eq_abs, abs_of_nonneg]
        exact norm_nonneg _
      _ ≤ ‖a‖ * ‖aDagger‖ := a.le_opNorm aDagger
  have hone_le : 1 ≤ ‖aDagger‖ := by
    -- Strictly shrinking `aDagger` would contradict the attained operator norm.
    by_contra hone_le
    have hlt : ‖aDagger‖ < 1 :=
      lt_of_not_ge hone_le
    have hmul_lt : ‖a‖ * ‖aDagger‖ < ‖a‖ := by
      simpa [mul_one] using mul_lt_mul_of_pos_left hlt hnorma_pos
    exact not_lt_of_ge hnorma_le hmul_lt
  exact le_antisymm haDagger_norm hone_le

-- Proof sketch: after substituting `a = 0`, the equality clause in `primalCounterparts a` becomes
-- `0 = ‖0‖`, hence is automatic. Membership therefore reduces to `‖x‖ ≤ 1`, which is
-- exactly membership in the closed unit ball `closedBall (0 : E) 1`.
/-- Lemma 10.61 (2): if `a = 0`, then `Λ_a` is the closed unit ball `B_{‖·‖}[0,1]`. -/
theorem primalCounterparts_eq_closedBall_of_eq_zero
    {a : E →L[ℝ] ℝ} (ha : a = 0) :
    Λ[a] = closedBall (0 : E) 1 := by
  ext x
  constructor
  · intro hx
    -- When `a = 0`, the owner condition keeps only the closed-ball bound.
    rw [mem_closedBall_zero_iff]
    rw [ha] at hx
    exact hx.1
  · intro hx
    -- Conversely, every point of the closed unit ball satisfies the trivial zero-functional clause.
    rw [primalCounterparts, ha]
    constructor
    · simpa [mem_closedBall_zero_iff] using hx
    · simp

-- Proof sketch: the equality `a a† = ‖a‖` is part of the defining condition of
-- `primalCounterparts a`.
/-- Lemma 10.61 (3): every primal counterpart `a† ∈ Λ_a` satisfies
`⟨a, a†⟩ = ‖a‖_*`, written here as `a a† = ‖a‖`. -/
theorem apply_eq_norm_of_mem_primalCounterparts
    {a : E →L[ℝ] ℝ} {aDagger : E}
    (haDagger : aDagger ∈ Λ[a]) :
    a aDagger = ‖a‖ := by
  -- Unfold the owner definition and read off the norm-attainment equality.
  exact haDagger.2

end

/-! ### Proposition_10_61 (from Chap10) -/
noncomputable section

open WithLp (ofLp toLp)
open scoped BigOperators

section

variable {n : ℕ}

local notation "E₂" => EuclideanSpace ℝ (Fin n)
local notation "E" => WithLp (⊤ : ENNReal) (Fin n → ℝ)
local notation "E*" => WithLp (1 : ENNReal) (Fin n → ℝ)
local notation "coordToLinf" => (fun z : E₂ ↦ toLp (⊤ : ENNReal) (ofLp z))

/- Proposition 10.61 is a `bridge/view` item in the chapter's non-Euclidean duality API. The
Chapter 10 source-facing owner is `Λ[a]` from Lemma 10.61 / Definition 10.64. Domain sampling in
the surrounding `ℓ∞/ℓ¹` pair identifies:
- `lpPairingDual` and `lpPairingDual_apply` from Proposition 1.9 as the canonical owner for the
  coordinate functional represented by an `ℓ¹` vector on `WithLp (⊤ : ENNReal)`;
- `LinearMap.toContinuousLinearMap` as the canonical bridge from that finite-dimensional linear
  functional to the continuous-dual owner used by `Λ[·]`;
- `euclideanSubdifferentialAt` as the Chapter 3 owner on the Euclidean coordinate model, with
  `subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints` and
  `l1CoordinateSubgradientVectors` giving its coordinatewise `ℓ¹` sign-cube companion;
- `primalCounterparts_eq_preimage_subdifferentialAt_norm` from Definition 10.64 as the chapter
  bridge from `Λ[·]` to the canonical subdifferential owner.

The primitive data are only the coefficient vector `a : E*`, so the public statement should stay
on `Λ[LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))]` rather than
introducing a second local name for the same functional. The Euclidean point `toLp 2 (ofLp a)` and
the coordinate transport `coordToLinf` are derived bridge data. The first theorem therefore uses
the Chapter 3 owner `euclideanSubdifferentialAt`, and the coordinatewise sign-cube description is
kept as a companion theorem. -/

-- Proof sketch: use `primalCounterparts_eq_preimage_subdifferentialAt_norm` to identify
-- `Λ[LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))]` with the
-- subdifferential of the `ℓ¹` norm in the `ℓ∞/ℓ¹` dual pair, then transport that owner set along
-- the canonical `WithLp` equivalence between the Euclidean coordinate model `E₂` and the primal
-- `ℓ∞` model `E`.
/-- Helper for Proposition 10.61: a point of the `ℓ∞` unit ball has all coordinates in
`[-1, 1]`. -/
lemma abs_le_one_of_linf_norm_le_one
    {x : E} (hx : ‖x‖ ≤ 1) :
    ∀ i, |x i| ≤ 1 := by
  -- Rewrite the `WithLp` norm as the ambient sup norm on coordinates.
  have hx' : ‖ofLp x‖ ≤ 1 := by
    simpa using hx
  intro i
  have hcoord_nnnorm : ‖ofLp x i‖₊ ≤ ‖ofLp x‖₊ := by
    rw [Pi.nnnorm_def]
    exact Finset.le_sup (f := fun b => ‖ofLp x b‖₊) (Finset.mem_univ i)
  have hcoord : ‖ofLp x i‖ ≤ ‖ofLp x‖ := by
    exact_mod_cast hcoord_nnnorm
  simpa [Real.norm_eq_abs] using hcoord.trans hx'

/-- Helper for Proposition 10.61: coordinatewise bounds by `1` put an `ℓ∞` vector in the unit
ball. -/
lemma linf_norm_le_one_of_abs_le_one
    {x : E} (hx : ∀ i, |x i| ≤ 1) :
    ‖x‖ ≤ 1 := by
  -- Reassemble the sup-norm bound from the coordinate inequalities.
  have hx'_nnnorm : ‖ofLp x‖₊ ≤ 1 := by
    rw [Pi.nnnorm_def]
    refine Finset.sup_le_iff.mpr ?_
    intro i hi
    have hcoord : ‖ofLp x i‖ ≤ 1 := by
      simpa [Real.norm_eq_abs] using hx i
    exact_mod_cast hcoord
  have hx' : ‖ofLp x‖ ≤ 1 := by
    exact_mod_cast hx'_nnnorm
  simpa using hx'

/-- Helper for Proposition 10.61: `Real.sign` recovers the absolute value by multiplication. -/
lemma real_sign_mul_self
    (t : ℝ) :
    Real.sign t * t = |t| := by
  -- Split by the sign of the scalar and reduce to the defining formulas for `Real.sign`.
  rcases lt_trichotomy t 0 with hneg | rfl | hpos
  · simp [Real.sign_of_neg hneg, abs_of_neg hneg]
  · simp
  · simp [Real.sign_of_pos hpos, abs_of_pos hpos]

/-- Helper for Proposition 10.61: the operator norm of the `ℓ∞/ℓ¹` coordinate pairing equals the
`ℓ¹` norm of its coefficient vector. -/
lemma lpPairingDual_top_norm_eq_l1_norm
    (a : E*) :
    ‖LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))‖ = ‖a‖ := by
  -- Proposition 1.9 computes the same norm through the chapter dual-norm owner.
  simpa [dualNorm] using
    dualNorm_lpPairingDual_eq_conjugate_lp_norm ENNReal.HolderConjugate.top_one (ofLp a)

/-- Helper for Proposition 10.61: membership in the transported Euclidean image can be rewritten
using the inverse coordinate transport. -/
lemma mem_image_coordToLinf_iff
    (S : Set E₂) {x : E} :
    x ∈ coordToLinf '' S ↔ toLp 2 (ofLp x) ∈ S := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa
  · intro hx
    refine ⟨toLp 2 (ofLp x), hx, ?_⟩
    simp

/-- Helper for Proposition 10.61: the Chapter 10 owner `Λ_a` for the `ℓ∞/ℓ¹` pairing is exactly
the coordinatewise sign cube. -/
lemma mem_primalCounterparts_lpPairingDual_top_iff
    (a : E*) {x : E} :
    x ∈ Λ[LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))] ↔
      (∀ i, a i ≠ 0 → x i = Real.sign (a i)) ∧
        ∀ i, a i = 0 → |x i| ≤ 1 := by
  constructor
  · intro hx
    rcases hx with ⟨hx_norm, hx_pairing⟩
    -- Control every coordinate of `x` by the `ℓ∞` unit-ball hypothesis.
    have hx_coord : ∀ i, |x i| ≤ 1 :=
      abs_le_one_of_linf_norm_le_one hx_norm
    have hsum :
        ∑ i, x i * a i = ∑ i, |a i| := by
      -- Rewrite the attained pairing and the dual norm in explicit coordinate form.
      calc
        ∑ i, x i * a i =
            LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a)) x := by
              simp [lpPairingDual_apply, dotProduct]
        _ = ‖LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))‖ :=
              hx_pairing
        _ = ‖a‖ := lpPairingDual_top_norm_eq_l1_norm a
        _ = ∑ i, |a i| := by
              simpa [Real.norm_eq_abs] using (PiLp.norm_eq_of_L1 a)
    have hterm_le : ∀ i, x i * a i ≤ |a i| := by
      intro i
      calc
        x i * a i ≤ |x i * a i| := le_abs_self _
        _ = |x i| * |a i| := by rw [abs_mul]
        _ ≤ 1 * |a i| := mul_le_mul_of_nonneg_right (hx_coord i) (abs_nonneg _)
        _ = |a i| := by ring
    refine ⟨?_, ?_⟩
    · intro i hai
      -- Equality of the total sums forces equality in each nonzero coordinate term.
      have hterm_eq : x i * a i = |a i| := by
        refine le_antisymm (hterm_le i) ?_
        by_contra hlt
        have hsum_lt :
            ∑ j, x j * a j < ∑ j, |a j| := by
          refine Finset.sum_lt_sum (fun j _ ↦ hterm_le j) ?_
          exact ⟨i, Finset.mem_univ i, lt_of_not_ge hlt⟩
        exact hsum_lt.ne hsum
      -- Compare the attained product with the canonical sign identity `sign(a_i) * a_i = |a_i|`.
      exact mul_right_cancel₀ hai (hterm_eq.trans (real_sign_mul_self (a i)).symm)
    · intro i hai
      exact hx_coord i
  · rintro ⟨hsign, hzero⟩
    have hx_coord : ∀ i, |x i| ≤ 1 := by
      intro i
      by_cases hai : a i = 0
      · exact hzero i hai
      · rw [hsign i hai]
        rcases lt_or_gt_of_ne hai with hneg | hpos
        · simp [Real.sign_of_neg hneg]
        · simp [Real.sign_of_pos hpos]
    have hx_norm : ‖x‖ ≤ 1 :=
      linf_norm_le_one_of_abs_le_one hx_coord
    have hx_pairing :
        LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a)) x =
          ‖LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))‖ := by
      -- Evaluate the pairing coordinatewise and substitute the sign constraints.
      calc
        LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a)) x =
            ∑ i, x i * a i := by
              simp [lpPairingDual_apply, dotProduct]
        _ = ∑ i, |a i| := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hai : a i = 0
              · simp [hai]
              · rw [hsign i hai, real_sign_mul_self]
        _ = ‖a‖ := by
              simpa [Real.norm_eq_abs] using (PiLp.norm_eq_of_L1 a).symm
        _ = ‖LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))‖ := by
              rw [lpPairingDual_top_norm_eq_l1_norm]
    exact ⟨hx_norm, hx_pairing⟩

/-- Bridge/view form of Proposition 10.61: for a coefficient vector `a` in the `ℓ∞/ℓ¹` coordinate
dual pair, the source set `Λ_a` is the canonical transport of Chapter 3's Euclidean
subdifferential owner for the `ℓ¹` norm from the coordinate model to the primal `ℓ∞` model. -/
theorem primalCounterparts_lpPairingDual_top_eq_image_euclideanSubdifferentialAt_l1
    (a : E*) :
    Λ[LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))] =
      coordToLinf ''
        euclideanSubdifferentialAt (fun y : E₂ ↦ ‖toLp 1 fun i ↦ y i‖) (toLp 2 (ofLp a)) := by
  ext z
  -- Compare both sides through the same coordinatewise sign constraints.
  calc
    z ∈ Λ[LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))] ↔
        (∀ i, a i ≠ 0 → z i = Real.sign (a i)) ∧
          ∀ i, a i = 0 → |z i| ≤ 1 :=
      mem_primalCounterparts_lpPairingDual_top_iff a
    _ ↔ toLp 2 (ofLp z) ∈
        euclideanSubdifferentialAt (fun y : E₂ ↦ ‖toLp 1 fun i ↦ y i‖) (toLp 2 (ofLp a)) := by
          simp [subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints,
            mem_l1CoordinateSubgradientVectors_iff]
    _ ↔ z ∈
        coordToLinf ''
          euclideanSubdifferentialAt (fun y : E₂ ↦ ‖toLp 1 fun i ↦ y i‖) (toLp 2 (ofLp a)) :=
      (mem_image_coordToLinf_iff
        (euclideanSubdifferentialAt (fun y : E₂ ↦ ‖toLp 1 fun i ↦ y i‖) (toLp 2 (ofLp a)))).symm

-- Proof sketch: combine the transported-owner theorem above with
-- `subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints`. Under the `coordToLinf`
-- transport, Euclidean coordinates are exactly the original `Fin n → ℝ` coordinates, so the
-- right-hand side becomes the familiar coordinatewise sign-cube formula.
/-- Proposition 10.61: after unpacking the transported Chapter 3 owner
`euclideanSubdifferentialAt`, the source set `Λ_a` is the coordinatewise sign cube
`{z : ℝ^n | z_i = sgn(a_i)` on the nonzero coordinates of `a`, and `|z_j| ≤ 1` on the zero
coordinates}. In the textbook nonzero case, this is the usual description of
`∂ h(a)` for `h(x) = ‖x‖₁`. -/
theorem primalCounterparts_lpPairingDual_top_eq_coordinatewise_sign_cube
    (a : E*) :
    Λ[LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp a))] =
      { z : E |
          (∀ i, a i ≠ 0 → z i = Real.sign (a i)) ∧
            ∀ i, a i = 0 → |z i| ≤ 1 } := by
  ext z
  -- The source owner is already characterized by the coordinatewise sign-cube conditions.
  exact mem_primalCounterparts_lpPairingDual_top_iff a

end
