import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_6_2_1 (from Chap06) -/
universe u

noncomputable section

variable {E : Type u} [NormedAddCommGroup E]

/- Proposition 6.2.1 is `source-facing` in the Chapter 6 proximal-operator API. Domain sampling in
the minimal closure identifies the owner abstractions already upstream:

- `prox[...]` and `proximal_objective` from Definition 6.1 as the `core/canonical` owners,
- `mem_proximal_mapping_iff` as the canonical minimizer-set view,
- `prox_add_const` as the owner-level theorem showing additive real constants are derived data for
  proximal mappings.

The public source-facing data are only the constant value `c` and the base point `x`. The
zero-objective computation is the canonical special case of that source-facing statement, so it
should appear as a small companion theorem rather than as a parallel wrapper API. -/

-- Proof sketch: rewrite proximal membership for the zero function as global minimality of the
-- quadratic term. Evaluating at `x` forces the quadratic value at `u` to vanish, hence `u = x`;
-- conversely, the quadratic term is always nonnegative, so `x` is a minimizer.
/-- The proximal mapping of the zero function is the singleton containing the base point. -/
theorem prox_zero_eq_singleton (x : E) :
    prox[0] x = {x} := by
  rw [Set.eq_singleton_iff_unique_mem]
  constructor
  · rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
    intro y
    have hy : 0 ≤ (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
      positivity
    have hy' : (0 : EReal) ≤ ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
      exact_mod_cast hy
    simpa [proximal_objective] using hy'
  · intro u hu
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
    have hux' : ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) ≤ 0 := by
      simpa [proximal_objective] using hu x
    have hux : (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) ≤ 0 := by
      exact_mod_cast hux'
    have hnonneg : 0 ≤ (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) := by
      positivity
    have hnorm_sq : ‖u - x‖ ^ (2 : ℕ) = 0 := by
      have hquad : (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) = 0 := le_antisymm hux hnonneg
      nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_of_pow_eq_zero hnorm_sq))

-- Proof sketch: remove the additive constant from the objective via the owner theorem
-- `prox_add_const`, then apply the zero-function computation above.
/-- Proposition 6.2.1: if `f` is the constant function with value `c`, then the proximal mapping
at `x` is the singleton `{x}`. Equivalently, the proximal operator of a constant function is the
identity map. -/
@[simp]
theorem prox_const_eq_singleton (c : ℝ) (x : E) :
    prox[fun _ ↦ (c : EReal)] x = {x} := by
  calc
    prox[fun _ ↦ (c : EReal)] x = prox[0] x := by
      simpa using congrFun (prox_add_const (0 : E → EReal) c) x
    _ = {x} := prox_zero_eq_singleton x

end

/-! ### Definition_6_2 (from Chap06) -/
noncomputable section

open SignType

section

variable {α : Type*} [Ring α] [LinearOrder α]

/- Definition 6.2 is `source-facing`: domain sampling against
`Mathlib.Data.Sign.Defs`, `Mathlib.Data.Sign.Basic`, and
`Mathlib.Algebra.Order.Group.PosPart` shows that the primitive scalar ingredients are already the
canonical upstream owners `sign` and `(·)⁺`. The new owner here is therefore only the
soft-thresholding map built from those generic ordered-ring primitives, while its piecewise
description remains derived API. -/

/-- Definition 6.2: the soft thresholding function with parameter `λ` is the map
`y ↦ (|y| - λ)⁺ * sign y`. -/
def soft_thresholding (lam : α) : α → α :=
  fun y ↦ (|y| - lam)⁺ * sign y

/-- Textbook notation for the soft thresholding operator. -/
notation "𝒯[" l "]" => soft_thresholding l

-- Proof sketch: unfold `soft_thresholding`; the statement is exactly the defining positive-part
-- and sign formula, so it follows by definitional reduction.
/-- Evaluating the soft-thresholding operator gives its defining positive-part/sign formula. -/
@[simp] theorem soft_thresholding_apply (lam y : α) :
    𝒯[lam] y = (|y| - lam)⁺ * sign y := rfl

end

section

variable {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]

-- Proof sketch: assume `0 ≤ λ` and split into the three regimes `λ ≤ y`, `|y| < λ`, and
-- `y ≤ -λ`. In each regime, simplify `( |y| - λ )⁺` and `sign y` to obtain the displayed
-- branch value.
/-- For a nonnegative threshold, soft thresholding has the usual three-branch piecewise
presentation. -/
theorem soft_thresholding_eq_piecewise {lam : α} (hlam : 0 ≤ lam) (y : α) :
    𝒯[lam] y =
      if lam ≤ y then y - lam else if |y| < lam then 0 else y + lam := by
  by_cases hly : lam ≤ y
  · have hy : 0 ≤ y := le_trans hlam hly
    by_cases hy0 : y = 0
    · have hlam0 : lam = 0 := le_antisymm (hy0 ▸ hly) hlam
      simp [soft_thresholding, hy0, hlam0]
    · have hyne : 0 ≠ y := by
        intro h0
        exact hy0 h0.symm
      have hypos : 0 < y := lt_of_le_of_ne hy hyne
      simp [soft_thresholding, hly, abs_of_nonneg hy, sign_pos hypos]
  · by_cases habs : |y| < lam
    · simp [soft_thresholding, hly, habs, posPart_of_nonpos (sub_nonpos.mpr habs.le)]
    · have hlamabs : lam ≤ |y| := le_of_not_gt habs
      have hyneg : y < 0 := by
        by_contra hy_nonneg
        exact hly (by simpa [abs_of_nonneg (le_of_not_gt hy_nonneg)] using hlamabs)
      have hyabs : |y| = -y := abs_of_neg hyneg
      have hneg : lam ≤ -y := by simpa [hyabs] using hlamabs
      calc
        𝒯[lam] y = (-y - lam) * (-1 : α) := by
          simp [soft_thresholding, hyabs, sign_neg hyneg,
            posPart_of_nonneg (sub_nonneg.mpr hneg)]
        _ = -(-y - lam) := by simp
        _ = y + lam := by abel_nf
        _ = if lam ≤ y then y - lam else if |y| < lam then 0 else y + lam := by
          simp [hly, habs]

end

/-! ### Example_6_2 (from Chap06) -/
noncomputable section

/- Example 6.2 is `source-facing` in the scalar proximal-operator API. The owner abstraction is
`prox[...]` from Definition 6.1. Its nontrivial scalar penalties are already owned upstream by the
Chapter 6 declaration `hardThresholdPenalty` together with the Chapter 2 owner `l0Indicator`; this
file now uses that `EReal`-valued owner directly rather than keeping parallel lifted copies. -/

/- Example 6.2 (1): the zero penalty is the specialization `c = 0` of Proposition 6.2.1. -/
recall prox_const_eq_singleton

-- Proof sketch: this is exactly the owner-level hard-thresholding computation from Example 6.10.
/- Example 6.2 (2): if `0 ≤ λ`, then the proximal mapping of the negative origin spike returns
`{0}` below the threshold `√(2 λ)`, `{x}` above the threshold, and both points at the tie case.
This exact source-facing proximal formula is already owned by Example 6.10's canonical theorem
`prox_hardThresholdPenalty_eq_hardThresholding`, so this file reuses that theorem directly rather
than keeping a duplicate renamed wrapper. -/
recall prox_hardThresholdPenalty_eq_hardThresholding

private theorem proximal_objective_positive_origin_spike_at_origin (lam : ℝ) :
    proximal_objective (hardThresholdPenalty (-lam)) 0 0 = (lam : EReal) := by
  rw [proximal_objective, hardThresholdPenalty_zero (-lam)]
  simp

private theorem proximal_objective_positive_origin_spike_at_zero_of_ne_zero
    (lam : ℝ) {u : ℝ} (hu : u ≠ 0) :
    proximal_objective (hardThresholdPenalty (-lam)) 0 u =
      ((((1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  rw [proximal_objective, hardThresholdPenalty_of_ne_zero (-lam) hu]
  simp

private theorem proximal_objective_positive_origin_spike_self
    (lam x : ℝ) (hx : x ≠ 0) :
    proximal_objective (hardThresholdPenalty (-lam)) x x = 0 := by
  rw [proximal_objective, hardThresholdPenalty_of_ne_zero (-lam) hx]
  simp

private theorem proximal_objective_positive_origin_spike_at_zero
    (lam x : ℝ) :
    proximal_objective (hardThresholdPenalty (-lam)) x 0 =
      (((lam + (1 / 2 : ℝ) * x ^ (2 : ℕ)) : ℝ) : EReal) := by
  rw [proximal_objective, hardThresholdPenalty_zero (-lam)]
  simp [pow_two]

private theorem proximal_objective_positive_origin_spike_of_ne_zero
    (lam x y : ℝ) (hy : y ≠ 0) :
    proximal_objective (hardThresholdPenalty (-lam)) x y =
      ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  rw [proximal_objective, hardThresholdPenalty_of_ne_zero (-lam) hy]
  simp

-- Proof sketch: unfold `prox` and compare the proximal objective at `u = x` and `u = 0`.
-- If `x ≠ 0`, the point `u = x` has value `0`, while `u = 0` has the larger value
-- `λ + x^2 / 2`, so `{x}` is the minimizer set. If `x = 0`, the infimum value `0` is approached
-- along nonzero `u → 0` but is not attained, because the value at `u = 0` is `λ > 0`.
/-- Example 6.2 (3): for `λ > 0`, the proximal mapping of the positive origin spike, written
canonically as `hardThresholdPenalty (-λ)`, returns `{x}` away from the origin and is empty at the
origin. -/
theorem prox_positive_origin_spike_eq_piecewise (lam : ℝ) (hlam : 0 < lam) (x : ℝ) :
    prox[hardThresholdPenalty (-lam)] x = if x = 0 then ∅ else {x} := by
  by_cases hx : x = 0
  · subst x
    ext u
    simpa using
      (show u ∈ prox[hardThresholdPenalty (-lam)] 0 ↔ False from by
        constructor
        · intro hu
          rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
          by_cases hu0 : u = 0
          · subst u
            let v : ℝ := min 1 lam
            have hvpos : 0 < v := by
              dsimp [v]
              exact lt_min zero_lt_one hlam
            have hvne : v ≠ 0 := hvpos.ne'
            have hvsq_lt : (1 / 2 : ℝ) * v ^ (2 : ℕ) < lam := by
              dsimp [v]
              by_cases hlam_le_one : lam ≤ 1
              · rw [min_eq_right hlam_le_one]
                nlinarith
              · rw [min_eq_left (le_of_lt (lt_of_not_ge hlam_le_one))]
                nlinarith
            have hvlt : proximal_objective (hardThresholdPenalty (-lam)) 0 v <
                proximal_objective (hardThresholdPenalty (-lam)) 0 0 := by
              have hvnorm : ‖v‖ = v := by
                exact abs_of_pos hvpos
              have hvlt' :
                  (((1 / 2 : ℝ) * ‖v‖ ^ (2 : ℕ) : ℝ) : EReal) < (lam : EReal) := by
                rw [hvnorm]
                exact_mod_cast hvsq_lt
              rw [proximal_objective_positive_origin_spike_at_zero_of_ne_zero lam hvne,
                proximal_objective_positive_origin_spike_at_origin]
              exact hvlt'
            exact (not_le_of_gt hvlt) (hu v)
          · have hhalf_ne : u / 2 ≠ 0 := by
              intro hhalf
              apply hu0
              linarith
            have hhalf_lt :
                proximal_objective (hardThresholdPenalty (-lam)) 0 (u / 2) <
                  proximal_objective (hardThresholdPenalty (-lam)) 0 u := by
              have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
              have hhalf_lt' :
                  ((1 / 2 : ℝ) * ‖u / 2‖ ^ (2 : ℕ) : ℝ) < (1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) := by
                have hnorm_two : ‖(2 : ℝ)‖ = 2 := by norm_num
                rw [norm_div, hnorm_two, pow_two, pow_two]
                have hu_sq_pos : 0 < ‖u‖ * ‖u‖ := by positivity
                nlinarith
              have hhalf_lt'' :
                  ((((1 / 2 : ℝ) * ‖u / 2‖ ^ (2 : ℕ)) : ℝ) : EReal) <
                    ((((1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
                exact_mod_cast hhalf_lt'
              rw [proximal_objective_positive_origin_spike_at_zero_of_ne_zero lam hhalf_ne,
                proximal_objective_positive_origin_spike_at_zero_of_ne_zero lam hu0]
              exact hhalf_lt''
            exact (not_le_of_gt hhalf_lt) (hu (u / 2))
        · intro hu
          exact False.elim hu)
  · ext u
    simpa [hx] using
      (show u ∈ prox[hardThresholdPenalty (-lam)] x ↔ u = x from by
        constructor
        · intro hu
          rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
          have hux :
              proximal_objective (hardThresholdPenalty (-lam)) x u ≤
                proximal_objective (hardThresholdPenalty (-lam)) x x := hu x
          have hxx : proximal_objective (hardThresholdPenalty (-lam)) x x = 0 :=
            proximal_objective_positive_origin_spike_self lam x hx
          rw [hxx] at hux
          by_cases hu0 : u = 0
          · subst u
            have hpos' : 0 < lam + (1 / 2 : ℝ) * x ^ (2 : ℕ) := by
              have hx_sq_pos : 0 < x ^ (2 : ℕ) := sq_pos_of_ne_zero hx
              nlinarith
            have hpos : 0 < proximal_objective (hardThresholdPenalty (-lam)) x 0 := by
              have hposE : (0 : EReal) < (((lam + (1 / 2 : ℝ) * x ^ (2 : ℕ)) : ℝ) : EReal) := by
                exact_mod_cast hpos'
              rw [proximal_objective_positive_origin_spike_at_zero]
              exact hposE
            exact False.elim ((not_le_of_gt hpos) hux)
          · have hu_obj :
                proximal_objective (hardThresholdPenalty (-lam)) x u =
                  ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
              rw [proximal_objective_positive_origin_spike_of_ne_zero lam x u hu0]
            have hu_nonneg : 0 ≤ proximal_objective (hardThresholdPenalty (-lam)) x u := by
              rw [hu_obj]
              have hu_nonneg' : 0 ≤ (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) := by
                positivity
              exact_mod_cast hu_nonneg'
            have huzero :
                proximal_objective (hardThresholdPenalty (-lam)) x u = 0 :=
              le_antisymm hux hu_nonneg
            rw [hu_obj] at huzero
            have hu_eq_zero : (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) = 0 := by
              exact_mod_cast huzero
            have hnorm_sq : ‖u - x‖ ^ (2 : ℕ) = 0 := by
              nlinarith
            exact sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_of_pow_eq_zero hnorm_sq))
        · intro hu
          subst u
          rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
          have hxx : proximal_objective (hardThresholdPenalty (-lam)) x x = 0 :=
            proximal_objective_positive_origin_spike_self lam x hx
          intro y
          by_cases hy : y = 0
          · rw [hxx,
              show proximal_objective (hardThresholdPenalty (-lam)) x y =
                  (((lam + (1 / 2 : ℝ) * x ^ (2 : ℕ)) : ℝ) : EReal) by
                    subst y
                    rw [proximal_objective_positive_origin_spike_at_zero]]
            have hy_nonneg' : 0 ≤ lam + (1 / 2 : ℝ) * x ^ (2 : ℕ) := by
              positivity
            exact_mod_cast hy_nonneg'
          · rw [hxx,
              show proximal_objective (hardThresholdPenalty (-lam)) x y =
                  ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) : ℝ) : EReal) by
                    rw [proximal_objective_positive_origin_spike_of_ne_zero lam x y hy]]
            have hy_nonneg' : 0 ≤ (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
              positivity
            exact_mod_cast hy_nonneg')

end

/-! ### Proposition_6_2_2 (from Chap06) -/
universe u

noncomputable section

open scoped RealInnerProductSpace

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 6.2.2 is `source-facing` in the Chapter 6 proximal API. Domain sampling in the
minimal closure identifies the upstream owner abstractions:

- `prox[...]` and `proximal_objective` from Definition 6.1 as the `core/canonical` owners,
- `prox_eq_of_proximal_objective_eq_pos_mul_add_const` as the canonical objective-comparison API,
- `prox_add_const` as the owner-level theorem showing additive real constants are derived data,
- `prox_const_eq_singleton` from Proposition 6.2.1 as the constant-function computation,
- mathlib's `innerSL ℝ a` as the canonical owner of the rank-one functional `u ↦ ⟪a, u⟫`.

The primitive source-facing data for the proximal formula are only the linear coefficient `a` and
the base point `x`. The affine offset `b` is derived API because `prox_add_const` already removes
finite real constants from the objective. The completed-square constant is also derived proof data,
so the refinement should keep the normalized linear theorem as the main entry and recover the
affine `+ b` form only as a thin companion. -/

-- Proof sketch: rewrite the proximal objective for `u ↦ ⟪a, u⟫` as the proximal objective of a
-- constant function at the shifted base point `x - a` by completing the square, then conclude
-- with the owner comparison theorem plus Proposition 6.2.1.
/-- Proposition 6.2.2: for the linear functional `u ↦ ⟪a, u⟫_ℝ`, the proximal mapping at `x` is
the singleton `{x - a}`. Equivalently, the proximal operator of this rank-one functional
translates `x` by `-a`. -/
theorem prox_inner_eq_singleton_sub (a x : E) :
    prox[fun u ↦ ((⟪a, u⟫ : ℝ) : EReal)] x = {x - a} := by
  let x' : E := x - a
  let c : ℝ := ⟪a, x⟫ - (1 / 2 : ℝ) * ‖a‖ ^ (2 : ℕ)
  have hobjective (u : E) :
      proximal_objective (fun v ↦ ((⟪a, v⟫ : ℝ) : EReal)) x u =
        ((1 : ℝ) : EReal) * proximal_objective (fun _ ↦ (c : EReal)) x' u + (0 : EReal) := by
    simpa [proximal_objective] using
      (show (((⟪a, u⟫ : ℝ) + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) : ℝ) : EReal) =
          (((c : ℝ) + (1 / 2 : ℝ) * ‖u - x'‖ ^ (2 : ℕ) : ℝ) : EReal) from by
        exact_mod_cast show
          (⟪a, u⟫ : ℝ) + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) =
            c + (1 / 2 : ℝ) * ‖u - x'‖ ^ (2 : ℕ) by
          dsimp [c, x']
          rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real x a, inner_sub_right]
          rw [real_inner_comm a u, real_inner_comm x a]
          ring)
  calc
    prox[fun u ↦ ((⟪a, u⟫ : ℝ) : EReal)] x = prox[fun _ ↦ (c : EReal)] x' := by
      exact prox_eq_of_proximal_objective_eq_pos_mul_add_const zero_lt_one hobjective
    _ = {x'} := prox_const_eq_singleton c x'
    _ = {x - a} := by simp [x']

-- Proof sketch: remove the additive constant from the affine objective with `prox_add_const`, then
-- apply the normalized linear computation above.
/-- For the affine function `u ↦ ⟪a, u⟫_ℝ + b`, the proximal mapping at `x` is still the singleton
`{x - a}`; the additive constant is derived data and does not affect `prox`. -/
theorem prox_inner_add_const_eq_singleton_sub (a x : E) (b : ℝ) :
    prox[fun u ↦ ((⟪a, u⟫ + b : ℝ) : EReal)] x = {x - a} := by
  have hconst :
      prox[fun u ↦ ((⟪a, u⟫ + b : ℝ) : EReal)] x =
        prox[fun u ↦ ((⟪a, u⟫ : ℝ) : EReal)] x := by
    change prox[fun u ↦ (Real.toEReal ∘ innerSL ℝ a) u + (b : EReal)] x =
      prox[Real.toEReal ∘ innerSL ℝ a] x
    simpa [Function.comp, innerSL_apply_apply, EReal.coe_add] using
      congrFun (prox_add_const (Real.toEReal ∘ innerSL ℝ a) b) x
  calc
    prox[fun u ↦ ((⟪a, u⟫ + b : ℝ) : EReal)] x =
        prox[fun u ↦ ((⟪a, u⟫ : ℝ) : EReal)] x := hconst
    _ = {x - a} := prox_inner_eq_singleton_sub a x

end

/-! ### Text_6_2 (from Chap06) -/
variable {E : Type*} [NormedAddCommGroup E]

/- Text 6.2 is `bridge/view` in the proximal/projection domain. Domain sampling in the minimal
semantic closure shows that the relevant owner-level declarations are:
1. Chapter 2's `extendedIndicator`,
2. Chapter 6's `prox` / `prox[...]`,
3. Chapter 6's source-facing projection owner `projection_mapping`,
4. the bridge theorem `prox_extendedIndicator_eq_projection_mapping`.
The target file therefore reuses the existing chapter owner `P[C]` rather than keeping a parallel
squared-distance wrapper. -/
recall projection_mapping

/- Text 6.2: for a nonempty set `C`, the proximal mapping of the indicator function `δ_C`
coincides with the set-valued projection mapping `P_C`; in the Euclidean textbook setting, this
is the orthogonal projection operator. -/
recall prox_extendedIndicator_eq_projection_mapping

/-! ### Proposition_6_2_3 (from Chap06) -/
open Matrix
open scoped RealInnerProductSpace

noncomputable section

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "E" => EuclideanSpace ℝ ι

/- Proposition 6.2.3 is `source-facing` in the Euclidean proximal domain.

- `core/canonical`: the Chapter 6 proximal owner `prox[...]`;
- `bridge/view`: the Chapter 5 coordinate owner `quadratic_affine_function_on_lp (2 : ENNReal)`
  and mathlib's Euclidean matrix action `Matrix.toEuclideanLin`;
- primitive data: the matrix `A`, the Euclidean linear coefficient `b`, and the base point `x`.

The coordinate model from Chapter 5 remains the canonical construction of the quadratic-affine
function, but the public proposition should expose only the intrinsic Euclidean surface. The bridge
lemma below keeps the coordinate realization internal by rewriting
`quadratic_affine_function_on_lp (2 : ENNReal) A b.ofLp 0` as the Euclidean quadratic
`y ↦ (1 / 2) ⟪A.toEuclideanLin y, y⟫ + ⟪b, y⟫`. -/

/-- The Chapter 5 coordinate quadratic owner at `p = 2` is the intrinsic Euclidean quadratic
`y ↦ (1 / 2) ⟪A.toEuclideanLin y, y⟫ + ⟪b, y⟫`. -/
@[simp] theorem quadratic_affine_function_on_lp_two_apply_eq
    (A : Matrix ι ι ℝ) (b x : E) :
    quadratic_affine_function_on_lp (2 : ENNReal) A b.ofLp 0 x =
      (1 / 2 : ℝ) * ⟪A.toEuclideanLin x, x⟫ + ⟪b, x⟫ := by
  have hAx : ⟪A.toEuclideanLin x, x⟫ = x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) := by
    change ⟪((A.toLpLin 2 2) : WithLp 2 (ι → ℝ) →ₗ[ℝ] E) x, x⟫ = _
    simpa [Matrix.toLpLin_apply] using EuclideanSpace.inner_toLp_toLp (A *ᵥ x.ofLp) x.ofLp
  have hbx : ⟪b, x⟫ = x.ofLp ⬝ᵥ b.ofLp := by
    simpa using (EuclideanSpace.inner_eq_star_dotProduct b x)
  rw [quadratic_affine_function_on_lp_apply, quadratic_affine_function_apply, hAx, hbx]
  simp [dotProduct_comm]

/-- Helper for Proposition 6.2.3: the candidate proximal point obtained by solving the shifted
normal equation `(A + I) u = x - b`. -/
noncomputable def quadratic_prox_center (A : Matrix ι ι ℝ) (b x : E) : E :=
  ((A + 1)⁻¹).toEuclideanLin (x - b)

/-- Helper for Proposition 6.2.3: the real-valued proximal objective of the quadratic
`y ↦ (1 / 2) ⟪A y, y⟫ + ⟪b, y⟫` at the base point `x`. -/
def quadratic_penalized_value (A : Matrix ι ι ℝ) (b x y : E) : ℝ :=
  (1 / 2 : ℝ) * ⟪A.toEuclideanLin y, y⟫ + ⟪b, y⟫ + (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)

/-- Helper for Proposition 6.2.3: the nonnegative quadratic error term produced by recentering the
proximal objective at the canonical point `quadratic_prox_center A b x`. -/
def quadratic_prox_error (A : Matrix ι ι ℝ) (z : E) : ℝ :=
  (1 / 2 : ℝ) * ⟪A.toEuclideanLin z, z⟫ + (1 / 2 : ℝ) * ‖z‖ ^ (2 : ℕ)

-- The inverse formula is the textbook normal equation `(A + I) u = x - b`, transported through
-- `Matrix.toEuclideanLin`.
/-- Helper for Proposition 6.2.3: the shifted inverse point solves the normal equation
`(A + I) u = x - b`. -/
lemma shifted_inverse_solves_quadratic_normal_equation
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (b x : E) :
    (A + 1).toEuclideanLin (quadratic_prox_center A b x) = x - b := by
  -- Positive semidefiniteness of `A` makes `A + I` positive definite, hence invertible.
  have hpd : (A + 1).PosDef := by
    simpa [add_comm] using
      (Matrix.PosDef.add_posSemidef (A := (1 : Matrix ι ι ℝ)) (B := A) Matrix.PosDef.one hA)
  letI := hpd.isUnit.invertible
  -- Push the Euclidean equality to coordinates, where it is the standard matrix identity
  -- `(A + I) (A + I)⁻¹ = I`.
  ext i
  have hEq :
      (((A + 1).toEuclideanLin (quadratic_prox_center A b x)).ofLp) i = ((x - b).ofLp) i := by
    rw [quadratic_prox_center, Matrix.ofLp_toEuclideanLin_apply, Matrix.ofLp_toEuclideanLin_apply]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  simpa using hEq

-- Completing the square around the normal-equation solution rewrites the proximal objective as
-- its center value plus a purely quadratic error term.
/-- Helper for Proposition 6.2.3: recentering the quadratic proximal objective at
`quadratic_prox_center A b x` produces the center value plus the quadratic error
`quadratic_prox_error A z`. -/
lemma quadratic_penalized_value_center_add_error
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (b x z : E) :
    quadratic_penalized_value A b x (quadratic_prox_center A b x + z) =
      quadratic_penalized_value A b x (quadratic_prox_center A b x) + quadratic_prox_error A z := by
  let u : E := quadratic_prox_center A b x
  -- Rewrite the linear term using the normal equation satisfied by `u`.
  have hu : (A + 1).toEuclideanLin u = x - b := by
    simpa [u] using shifted_inverse_solves_quadratic_normal_equation A hA b x
  have hu' : A.toEuclideanLin u + u = x - b := by
    simpa [Matrix.toEuclideanLin.map_add, u] using hu
  -- Symmetry of `A` identifies the two mixed quadratic terms.
  have hsymmetric : (A.toEuclideanLin).IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff).2 hA.1
  have hzsymm : ⟪A.toEuclideanLin z, u⟫ = ⟪A.toEuclideanLin u, z⟫ := by
    calc
      ⟪A.toEuclideanLin z, u⟫ = ⟪z, A.toEuclideanLin u⟫ := hsymmetric z u
      _ = ⟪A.toEuclideanLin u, z⟫ := by simp [real_inner_comm]
  have hu_inner : ⟪A.toEuclideanLin u, z⟫ + ⟪u, z⟫ = ⟪x - b, z⟫ := by
    simpa [inner_add_left] using congrArg (fun w : E => ⟪w, z⟫) hu'
  have hu_inner' : ⟪A.toEuclideanLin u, z⟫ + ⟪u, z⟫ = ⟪x, z⟫ - ⟪b, z⟫ := by
    simpa [inner_sub_left] using hu_inner
  have hsub : u + z - x = (u - x) + z := by
    abel_nf
  unfold quadratic_penalized_value quadratic_prox_error
  rw [LinearMap.map_add, inner_add_left, inner_add_right, inner_add_right, inner_add_right, hsub,
    norm_add_sq_real]
  have hcross : ⟪A.toEuclideanLin u, z⟫ + ⟪A.toEuclideanLin z, u⟫ + 2 * ⟪u - x, z⟫ + 2 * ⟪b, z⟫ = 0 := by
    -- After the symmetry rewrite, the mixed terms cancel exactly by the normal equation.
    rw [inner_sub_left]
    nlinarith [hu_inner', hzsymm]
  nlinarith [hcross]

-- Positive semidefiniteness of `A` makes the recentered error term nonnegative.
/-- Helper for Proposition 6.2.3: the quadratic error term from the completed-square identity is
always nonnegative. -/
lemma quadratic_prox_error_nonneg
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (z : E) :
    0 ≤ quadratic_prox_error A z := by
  have hpositive : (A.toEuclideanLin).IsPositive :=
    (Matrix.isPositive_toEuclideanLin_iff).2 hA
  unfold quadratic_prox_error
  -- Each summand is nonnegative: the first by positivity of `A`, the second by being a norm
  -- square.
  have hquad : 0 ≤ ⟪A.toEuclideanLin z, z⟫ := by
    simpa [real_inner_comm] using hpositive.inner_nonneg_right z
  have hnorm : 0 ≤ ‖z‖ ^ (2 : ℕ) := sq_nonneg ‖z‖
  nlinarith

-- Proof sketch: first pass from the Chapter 5 coordinate owner to the intrinsic Euclidean formula
-- using `quadratic_affine_function_on_lp_two_apply_eq`. Completing the square then centers the
-- proximal objective at `((A + 1)⁻¹).toEuclideanLin (x - b)`. Since `hA` is positive semidefinite,
-- `A + 1` is positive definite and therefore invertible, so this Euclidean point is well-defined
-- and yields the unique minimizer.
/-- Proposition 6.2.3: for the Euclidean quadratic
`y ↦ (1 / 2) ⟪A.toEuclideanLin y, y⟫ + ⟪b, y⟫` on `EuclideanSpace ℝ ι`, hence on `ℝ^n` when
`ι = Fin n`, the proximal mapping at `x` is the singleton obtained by applying the inverse
Euclidean linear map `((A + 1)⁻¹).toEuclideanLin` to `x - b`. -/
theorem prox_quadratic_affine_function_eq_singleton
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (b x : E) :
    prox[fun y : E ↦ (((1 / 2 : ℝ) * ⟪A.toEuclideanLin y, y⟫ + ⟪b, y⟫ : ℝ) : EReal)] x =
      {((A + 1)⁻¹).toEuclideanLin (x - b)} := by
  let f : E → EReal :=
    fun y : E ↦ (((1 / 2 : ℝ) * ⟪A.toEuclideanLin y, y⟫ + ⟪b, y⟫ : ℝ) : EReal)
  let u : E := quadratic_prox_center A b x
  have hu_min : u ∈ prox[f] x := by
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
    intro y
    change ((quadratic_penalized_value A b x u : ℝ) : EReal) ≤
      ((quadratic_penalized_value A b x y : ℝ) : EReal)
    -- Recenter the objective at `u`; the remaining error term is nonnegative.
    have hz : y = u + (y - u) := by
      abel_nf
    rw [hz, quadratic_penalized_value_center_add_error A hA b x (y - u)]
    have hnonneg : 0 ≤ quadratic_prox_error A (y - u) :=
      quadratic_prox_error_nonneg A hA (y - u)
    exact_mod_cast le_add_of_nonneg_right hnonneg
  rw [Set.eq_singleton_iff_unique_mem]
  constructor
  · simpa [f, u, quadratic_prox_center] using hu_min
  · intro y hy
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hy
    -- Compare the minimizing inequalities in both directions to force the quadratic error to
    -- vanish.
    have hyuE := hy u
    change ((quadratic_penalized_value A b x y : ℝ) : EReal) ≤
      ((quadratic_penalized_value A b x u : ℝ) : EReal) at hyuE
    have hyu : quadratic_penalized_value A b x y ≤ quadratic_penalized_value A b x u := by
      exact_mod_cast hyuE
    have huy : quadratic_penalized_value A b x u ≤ quadratic_penalized_value A b x y := by
      have hz : y = u + (y - u) := by
        abel_nf
      rw [hz, quadratic_penalized_value_center_add_error A hA b x (y - u)]
      have hnonneg : 0 ≤ quadratic_prox_error A (y - u) :=
        quadratic_prox_error_nonneg A hA (y - u)
      exact le_add_of_nonneg_right hnonneg
    have hEq : quadratic_penalized_value A b x y = quadratic_penalized_value A b x u :=
      le_antisymm hyu huy
    have hz : y = u + (y - u) := by
      abel_nf
    rw [hz, quadratic_penalized_value_center_add_error A hA b x (y - u)] at hEq
    have herror_zero : quadratic_prox_error A (y - u) = 0 := by
      linarith
    have hnorm_sq : ‖y - u‖ ^ (2 : ℕ) = 0 := by
      have hnonneg : 0 ≤ ⟪A.toEuclideanLin (y - u), y - u⟫ := by
        have hpositive : (A.toEuclideanLin).IsPositive :=
          (Matrix.isPositive_toEuclideanLin_iff).2 hA
        simpa [real_inner_comm] using hpositive.inner_nonneg_right (y - u)
      unfold quadratic_prox_error at herror_zero
      nlinarith
    have hzero : y - u = 0 := by
      exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero hnorm_sq)
    have hy_eq_u : y = u := sub_eq_zero.mp hzero
    simpa [u, quadratic_prox_center] using hy_eq_u

end
