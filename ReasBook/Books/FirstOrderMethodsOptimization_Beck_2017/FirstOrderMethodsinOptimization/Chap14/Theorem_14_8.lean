import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap11.Lemma_11_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap14.Algorithm_14_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E1 : Type u} {E2 : Type u}
variable [NormedAddCommGroup E1] [NormedSpace ℝ E1]
variable [NormedAddCommGroup E2] [NormedSpace ℝ E2]

/- `prompt_add/` is absent in this workspace, so the owner review is done against the nearby
Chapter 11 recurrence lemmas, Algorithm 14.8, Lemma 14.4, and the Chapter 14 convex-rate owners.

Theorem 14.8 is `source-facing`: it gives the two-block `O(1 / k)` estimate for the objective gap
along the explicit block sequences `x₁^k` and `x₂^k` for the pair objective from
Algorithm 14.8. Domain sampling against the nearby Chapter 14 files identifies the relevant
owners:
- `two_block_alternating_minimization_objective` and
  `two_block_alternating_minimization_objective_blocks` from Algorithm 14.8 for the source-level
  objective `F(x₁, x₂) = f(x₁, x₂) + g₁(x₁) + g₂(x₂)`;
- `ConvexOn ℝ Set.univ f` from the nearby Chapter 14 rate files for the real-valued smooth term,
  together with the frozen-slice `is_l_smooth_on` assumptions from Lemma 14.4;
- `is_convex_function` only for the extended-real penalty terms `g₁` and `g₂`;
- `is_two_block_alternating_minimization_trajectory` from Algorithm 14.8 as the source-facing
  owner for the generated pair iterates, with
  `is_two_block_alternating_minimization_trajectory_toTrajectory` retained as the canonical bridge
  to `is_alternating_minimization_trajectory` on
  `two_block_alternating_minimization_block_iterate` once the initial pair lies in
  `effective_domain F`; and
- `nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence` from
  Lemma 11.7 only as the proof-level scalar recurrence bridge.

Layer triage:
- `source-facing`: the theorem below, stated directly for the two-block objective and the
  Algorithm 14.8 trajectory including the textbook initialization clause for `x₂⁰`;
- `core/canonical`: the Algorithm 14.8 objective owner together with the Chapter 14
  block-vector trajectory owner and the canonical convexity owner `ConvexOn ℝ Set.univ f` for the
  smooth term;
- `bridge/view`: the explicit initial-domain witness together with
  `is_two_block_alternating_minimization_trajectory_toTrajectory`, and the scalar recurrence on the
  objective-gap sequence, both used internally rather than as public theorem inputs. -/

variable {f : E1 × E2 → ℝ} {g1 : E1 → EReal} {g2 : E2 → EReal}
variable {x1 : ℕ → E1} {x2 : ℕ → E2} {xStar : E1 × E2} {FOpt : ℝ}
variable {L1 L2 R : PosReal}

local notation "F" => two_block_alternating_minimization_objective f.toExtendedReal g1 g2
local notation "x[" k "]" => (x1 k, x2 k)

-- Proof sketch: set
-- `a k = (F x[k]).toReal - FOpt` and use the source-facing Algorithm 14.8 trajectory
-- hypothesis together with the extra initial-domain bridge `hx0 : x[0] ∈ effective_domain F` to
-- obtain the canonical block-vector trajectory via
-- `is_two_block_alternating_minimization_trajectory_toTrajectory`. Then derive the needed slice
-- convexity and full-objective convexity data from the canonical convexity owner
-- `ConvexOn ℝ Set.univ f`, the penalty regularity, the frozen-slice smoothness assumptions, and
-- the initial-sublevel-radius hypothesis to prove the Chapter 14 quadratic recurrence
-- `a k - a (k + 1) ≥ (1 / γ) * a (k + 1)^2`
-- `γ = 2 * min (L₁, L₂) * R^2`. The stated quadratic recurrence is then
-- `nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence`
-- yields
-- `a k ≤ max {((1 / 2)^((k - 1) / 2)) * a 0, 4γ / (k - 1)}` for every `k ≥ 2`. Since
-- `4γ = 8 * min (L₁, L₂) * R^2`, this is exactly the displayed estimate.
/-- Helper for Theorem 14.8: a convex differentiable real-valued function on the whole Banach
space satisfies the first-order support inequality in `fderiv` form. -/
lemma convex_real_support_univ_fderiv
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} {x y : E}
    (hφ_convex : ConvexOn ℝ Set.univ φ)
    (hφ_diff : DifferentiableAt ℝ φ x) :
    φ y ≥ φ x + fderiv ℝ φ x (y - x) := by
  let line : ℝ → E := AffineMap.lineMap x y
  let ψ : ℝ → ℝ := fun t ↦ φ (line t)
  have hψ_convex : ConvexOn ℝ Set.univ ψ := by
    -- Restrict the ambient convex function to the affine line from `x` to `y`.
    simpa [ψ, line] using
      hφ_convex.comp_affineMap (AffineMap.lineMap (k := ℝ) x y)
  have hψ_deriv : HasDerivAt ψ (fderiv ℝ φ x (y - x)) 0 := by
    -- Differentiate the line restriction at the base point and identify the direction `y - x`.
    have hbase : HasFDerivAt φ (fderiv ℝ φ x) (line 0) := by
      simpa [line] using hφ_diff.hasFDerivAt
    have hline : HasDerivAt line (y - x) 0 := by
      simpa [line] using
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ)))
    simpa [ψ, line] using HasFDerivAt.comp_hasDerivAt (x := 0) hbase hline
  have hsecant :
      fderiv ℝ φ x (y - x) ≤ slope ψ 0 1 := by
    -- Convexity bounds the derivative at the left endpoint by the secant slope.
    exact hψ_convex.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hψ_deriv
  have hsecant' :
      fderiv ℝ φ x (y - x) ≤ φ y - φ x := by
    simpa [ψ, line, slope] using hsecant
  linarith

/-- Helper for Theorem 14.8: the current second block is always an exact minimizer of the current
`x₂`-subproblem, with the `k = 0` case coming from the initialization clause. -/
lemma two_block_current_x2_objective_is_min_on
    (htraj : is_two_block_alternating_minimization_trajectory f.toExtendedReal g1 g2 x1 x2)
    (n : ℕ) :
    IsMinOn
      (two_block_alternating_minimization_x2_objective f.toExtendedReal g1 g2 (x1 n))
      Set.univ
      (x2 n) := by
  -- Split off the initialization case from the recursive update case.
  cases n with
  | zero =>
      simpa using htraj.initial
  | succ n =>
      simpa [Nat.succ_eq_add_one] using htraj.step_x2 n

/-- Helper for Theorem 14.8: every outer iterate stays in the effective domain of `F`, and the
objective never exceeds its initial value. -/
lemma two_block_iterates_mem_effective_domain_and_initial_sublevel
    (htraj : is_two_block_alternating_minimization_trajectory f.toExtendedReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F) :
    ∀ n : ℕ, x[n] ∈ effective_domain F ∧ F x[n] ≤ F x[0] := by
  intro n
  induction n with
  | zero =>
      -- The initial pair is finite by hypothesis, and its value equals itself.
      exact ⟨hx0, le_rfl⟩
  | succ n ihn =>
      let xHalf := two_block_alternating_minimization_half_step x1 x2 n
      have hhalf_le : F xHalf ≤ F x[n] := by
        -- Compare the exact `x₁`-update against the old first block on the frozen `x₂^n` slice.
        have hmin := (isMinOn_iff.mp (htraj.step_x1 n)) (x1 n) (by simp)
        simpa [xHalf, two_block_alternating_minimization_half_step] using hmin
      have hhalf_mem : xHalf ∈ effective_domain F := by
        -- Finite descent from the current iterate keeps the half-step finite.
        refine mem_effective_domain.mpr ?_
        exact lt_of_le_of_lt hhalf_le (mem_effective_domain.mp ihn.1)
      have hnext_le_half : F x[n + 1] ≤ F xHalf := by
        -- Compare the exact `x₂`-update against the old second block on the frozen `x₁^{n+1}`
        -- slice.
        have hmin := (isMinOn_iff.mp (htraj.step_x2 n)) (x2 n) (by simp)
        simpa [xHalf, two_block_alternating_minimization_half_step] using hmin
      have hnext_mem : x[n + 1] ∈ effective_domain F := by
        -- The next iterate inherits finiteness from the half-step it improves.
        refine mem_effective_domain.mpr ?_
        exact lt_of_le_of_lt hnext_le_half (mem_effective_domain.mp hhalf_mem)
      have hnext_le_zero : F x[n + 1] ≤ F x[0] := by
        exact le_trans hnext_le_half (le_trans hhalf_le ihn.2)
      exact ⟨hnext_mem, hnext_le_zero⟩

/-- Helper for Theorem 14.8: each half-step also stays in the effective domain and in the initial
sublevel set. -/
lemma two_block_half_step_mem_effective_domain_and_initial_sublevel
    (htraj : is_two_block_alternating_minimization_trajectory f.toExtendedReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    two_block_alternating_minimization_half_step x1 x2 n ∈ effective_domain F ∧
      F (two_block_alternating_minimization_half_step x1 x2 n) ≤ F x[0] := by
  let xHalf := two_block_alternating_minimization_half_step x1 x2 n
  have hiter :=
    two_block_iterates_mem_effective_domain_and_initial_sublevel
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2) htraj hx0 n
  have hhalf_le : F xHalf ≤ F x[n] := by
    -- The exact first-block minimizer cannot exceed the old first block value on the same slice.
    have hmin := (isMinOn_iff.mp (htraj.step_x1 n)) (x1 n) (by simp)
    simpa [xHalf, two_block_alternating_minimization_half_step] using hmin
  have hhalf_mem : xHalf ∈ effective_domain F := by
    -- Finite descent from the current iterate keeps the half-step finite.
    refine mem_effective_domain.mpr ?_
    exact lt_of_le_of_lt hhalf_le (mem_effective_domain.mp hiter.1)
  have hhalf_le_zero : F xHalf ≤ F x[0] := by
    exact le_trans hhalf_le hiter.2
  exact ⟨hhalf_mem, hhalf_le_zero⟩

/-- Helper for Theorem 14.8: every iterate objective gap is nonnegative because each iterate is
finite and `xStar` globally minimizes `F`. -/
lemma two_block_objective_gap_nonneg
    (hg1_proper : IsProperExtendedRealFunction g1)
    (hg2_proper : IsProperExtendedRealFunction g2)
    (htraj : is_two_block_alternating_minimization_trajectory f.toExtendedReal g1 g2 x1 x2)
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal))
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    0 ≤ (F x[n]).toReal - FOpt := by
  have hiter :=
    two_block_iterates_mem_effective_domain_and_initial_sublevel
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2) htraj hx0 n
  have hFx_bot : F x[n] ≠ ⊥ := by
    -- The smooth term is real-valued, and the proper penalties never take the value `-∞`.
    rw [two_block_alternating_minimization_objective_apply, EReal.add_ne_bot_iff,
      EReal.add_ne_bot_iff]
    exact ⟨⟨by simp [Function.toExtendedReal], hg1_proper.ne_bot (x1 n)⟩, hg2_proper.ne_bot (x2 n)⟩
  have hFx_coe :
      (((F x[n]).toReal : ℝ) : EReal) = F x[n] := by
    exact EReal.coe_toReal (mem_effective_domain.mp hiter.1).ne hFx_bot
  have hlowerE : (FOpt : EReal) ≤ F x[n] := by
    -- Compare the global minimizer `xStar` against the current iterate.
    have hmin := (isMinOn_iff.mp hxStar) x[n] (by simp)
    simpa [hFOpt] using hmin
  have hlowerE' : (FOpt : EReal) ≤ (((F x[n]).toReal : ℝ) : EReal) := by
    rwa [← hFx_coe] at hlowerE
  have hlower : FOpt ≤ (F x[n]).toReal := by
    exact_mod_cast hlowerE'
  linarith

/-- Helper for Theorem 14.8: the source proof reduces the theorem to a Chapter 14 quadratic
recurrence and then to the Chapter 11 scalar recurrence estimate. -/
lemma two_block_objective_gap_le_of_quadratic_recurrence
    (γ : PosReal)
    (hγ :
      4 * (γ : ℝ) ≤ 8 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ)))
    (ha_nonneg : ∀ n : ℕ, 0 ≤ (F x[n]).toReal - FOpt)
    (hstep :
      ∀ n : ℕ,
        ((F x[n]).toReal - FOpt) - ((F x[n + 1]).toReal - FOpt) ≥
          (1 / (γ : ℝ)) * (((F x[n + 1]).toReal - FOpt) ^ (2 : ℕ)))
    (k : ℕ) (hk : 2 ≤ k) :
    (F x[k]).toReal - FOpt ≤
      max
        (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) *
          ((F x[0]).toReal - FOpt))
        ((8 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ))) / ((k - 1 : ℕ) : ℝ)) := by
  -- Apply Lemma 11.7 directly to the two-block objective-gap sequence.
  have hmain :=
    _root_.nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence
      (a := fun n ↦ (F x[n]).toReal - FOpt)
      (γ := γ)
      ha_nonneg
      hstep
      hk
  -- Then enlarge the sublinear branch using the coefficient comparison `hγ`.
  have hsub :
      4 * (γ : ℝ) / ((k - 1 : ℕ) : ℝ) ≤
        (8 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ))) / ((k - 1 : ℕ) : ℝ) := by
    exact div_le_div_of_nonneg_right hγ (by positivity)
  exact hmain.trans (max_le_max le_rfl hsub)

/-- Helper for Theorem 14.8: properness of the penalty terms rules out the value `-∞` for the
two-block objective at every point. -/
lemma two_block_objective_ne_bot
    (hg1_proper : IsProperExtendedRealFunction g1)
    (hg2_proper : IsProperExtendedRealFunction g2)
    (y : E1 × E2) :
    F y ≠ ⊥ := by
  rcases y with ⟨y1, y2⟩
  -- The smooth term is real-valued, and proper penalties never attain `-∞`.
  rw [two_block_alternating_minimization_objective_apply, EReal.add_ne_bot_iff,
    EReal.add_ne_bot_iff]
  exact ⟨⟨by simp [Function.toExtendedReal], hg1_proper.ne_bot y1⟩, hg2_proper.ne_bot y2⟩

/-- Helper for Theorem 14.8: on the effective domain, the objective is exactly the coercion of its
real value. -/
lemma two_block_objective_eq_coe_toReal_of_mem_effective_domain
    (hg1_proper : IsProperExtendedRealFunction g1)
    (hg2_proper : IsProperExtendedRealFunction g2)
    {y : E1 × E2} (hy : y ∈ effective_domain F) :
    (((F y).toReal : ℝ) : EReal) = F y := by
  -- Combine effective-domain finiteness with the global non-`⊥` fact.
  exact
    EReal.coe_toReal
      (mem_effective_domain.mp hy).ne
      (two_block_objective_ne_bot (f := f) (g1 := g1) (g2 := g2) hg1_proper hg2_proper y)

/-- Helper for Theorem 14.8: the exact second-block update makes the next objective gap no larger
than the half-step objective gap. -/
lemma two_block_next_iterate_objective_gap_le_half_step_gap
    (hg1_proper : IsProperExtendedRealFunction g1)
    (hg2_proper : IsProperExtendedRealFunction g2)
    (htraj : is_two_block_alternating_minimization_trajectory f.toExtendedReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    (F x[n + 1]).toReal - FOpt ≤
      (F (two_block_alternating_minimization_half_step x1 x2 n)).toReal - FOpt := by
  let xHalf := two_block_alternating_minimization_half_step x1 x2 n
  have hhalf :=
    two_block_half_step_mem_effective_domain_and_initial_sublevel
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2) htraj hx0 n
  have hnext_le_half : F x[n + 1] ≤ F xHalf := by
    -- Compare the exact `x₂`-update against the previous second block on the frozen half-step
    -- slice.
    have hmin := (isMinOn_iff.mp (htraj.step_x2 n)) (x2 n) (by simp)
    simpa [xHalf, two_block_alternating_minimization_half_step] using hmin
  have hnext_real_le_half_real :
      (F x[n + 1]).toReal ≤ (F xHalf).toReal := by
    -- Convert the EReal descent inequality to a real inequality using finiteness of the
    -- half-step objective and global non-`⊥` for the current iterate.
    exact
      EReal.toReal_le_toReal
        hnext_le_half
        (two_block_objective_ne_bot
          (f := f) (g1 := g1) (g2 := g2) hg1_proper hg2_proper x[n + 1])
        (mem_effective_domain.mp hhalf.1).ne
  linarith

/-- Helper for Theorem 14.8: exact minimization of the current second-block slice identifies the
first-block partial infimum at `x₁^n` with the current objective value. -/
lemma two_block_x1_partial_infimum_eq_current_value
    (htraj : is_two_block_alternating_minimization_trajectory f.toExtendedReal g1 g2 x1 x2)
    (n : ℕ) :
    let phi1 : E1 → EReal := fun y1 ↦ sInf (Set.range (fun z2 : E2 ↦ F (y1, z2)))
    phi1 (x1 n) = F x[n] := by
  let phi1 : E1 → EReal := fun y1 ↦ sInf (Set.range (fun z2 : E2 ↦ F (y1, z2)))
  have hmin :
      IsMinOn
        (two_block_alternating_minimization_x2_objective f.toExtendedReal g1 g2 (x1 n))
        Set.univ
        (x2 n) :=
    two_block_current_x2_objective_is_min_on
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2) htraj n
  apply le_antisymm
  · -- The current second block supplies one witness in the fiber defining `phi1`.
    exact sInf_le ⟨x2 n, by simp⟩
  · -- Exact `x₂`-minimality shows that every other fiber value lies above `F x[n]`.
    refine le_sInf ?_
    rintro _ ⟨z2, rfl⟩
    simpa [phi1] using (isMinOn_iff.mp hmin) z2 (by simp)

/-- Helper for Theorem 14.8: the same first-block partial infimum equals the optimal value at
`xStar.1`. -/
lemma two_block_x1_partial_infimum_eq_optimal_value
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal)) :
    let phi1 : E1 → EReal := fun y1 ↦ sInf (Set.range (fun z2 : E2 ↦ F (y1, z2)))
    phi1 xStar.1 = (FOpt : EReal) := by
  let phi1 : E1 → EReal := fun y1 ↦ sInf (Set.range (fun z2 : E2 ↦ F (y1, z2)))
  apply le_antisymm
  · -- The optimal pair contributes the witness `xStar.2` in the fiber over `xStar.1`.
    calc
      phi1 xStar.1 ≤ F (xStar.1, xStar.2) := by
        exact sInf_le ⟨xStar.2, by simp⟩
      _ = (FOpt : EReal) := hFOpt
  · -- Global minimality bounds every point in that fiber below by `FOpt`, hence also its infimum.
    refine le_sInf ?_
    rintro _ ⟨z2, rfl⟩
    have hmin := (isMinOn_iff.mp hxStar) (xStar.1, z2) (by simp)
    simpa [hFOpt, phi1] using hmin

/-- Helper for Theorem 14.8: exact minimization of the current first-block slice identifies the
second-block partial infimum at `x₂^n` with the half-step objective value. -/
lemma two_block_x2_partial_infimum_eq_current_value
    (htraj : is_two_block_alternating_minimization_trajectory f.toExtendedReal g1 g2 x1 x2)
    (n : ℕ) :
    let xHalf := two_block_alternating_minimization_half_step x1 x2 n
    let phi2 : E2 → EReal := fun y2 ↦ sInf (Set.range (fun z1 : E1 ↦ F (z1, y2)))
    phi2 (x2 n) = F xHalf := by
  let xHalf := two_block_alternating_minimization_half_step x1 x2 n
  let phi2 : E2 → EReal := fun y2 ↦ sInf (Set.range (fun z1 : E1 ↦ F (z1, y2)))
  have hmin :
      IsMinOn
        (two_block_alternating_minimization_x1_objective f.toExtendedReal g1 g2 (x2 n))
        Set.univ
        (x1 (n + 1)) := by
    simpa [Nat.succ_eq_add_one] using htraj.step_x1 n
  apply le_antisymm
  · -- The updated first block supplies one witness in the fiber defining `phi2`.
    exact sInf_le ⟨x1 (n + 1), by simp [two_block_alternating_minimization_half_step]⟩
  · -- Exact `x₁`-minimality keeps all other fiber values above the half-step objective.
    refine le_sInf ?_
    rintro _ ⟨z1, rfl⟩
    simpa [phi2, xHalf, two_block_alternating_minimization_half_step] using
      (isMinOn_iff.mp hmin) z1 (by simp)

/-- Helper for Theorem 14.8: the second-block partial infimum equals the optimal value at
`xStar.2`. -/
lemma two_block_x2_partial_infimum_eq_optimal_value
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal)) :
    let phi2 : E2 → EReal := fun y2 ↦ sInf (Set.range (fun z1 : E1 ↦ F (z1, y2)))
    phi2 xStar.2 = (FOpt : EReal) := by
  let phi2 : E2 → EReal := fun y2 ↦ sInf (Set.range (fun z1 : E1 ↦ F (z1, y2)))
  apply le_antisymm
  · -- The optimal pair contributes the witness `xStar.1` in the fiber over `xStar.2`.
    calc
      phi2 xStar.2 ≤ F (xStar.1, xStar.2) := by
        exact sInf_le ⟨xStar.1, by simp⟩
      _ = (FOpt : EReal) := hFOpt
  · -- Global minimality bounds the entire fiber below by `FOpt`, hence also its infimum.
    refine le_sInf ?_
    rintro _ ⟨z1, rfl⟩
    have hmin := (isMinOn_iff.mp hxStar) (z1, xStar.2) (by simp)
    simpa [hFOpt, phi2] using hmin

/-- Helper for Theorem 14.8: if the full objective is finite at `y`, then the first penalty term
is also finite there. -/
lemma two_block_first_penalty_eq_coe_toReal_of_mem_effective_domain
    (hg1_proper : IsProperExtendedRealFunction g1)
    (hg2_proper : IsProperExtendedRealFunction g2)
    {y : E1 × E2} (hy : y ∈ effective_domain F) :
    (((g1 y.1).toReal : ℝ) : EReal) = g1 y.1 := by
  rcases y with ⟨y1, y2⟩
  have hg1_ne_top : g1 y1 ≠ ⊤ := by
    -- A top-valued active penalty would force the whole objective to be `⊤`, contradicting
    -- effective-domain membership.
    intro hg1_top
    have hFy_top : F (y1, y2) = ⊤ := by
      calc
        F (y1, y2) = (((f (y1, y2) : ℝ) : EReal) + ⊤) + g2 y2 := by
          simp [two_block_alternating_minimization_objective_apply, hg1_top]
        _ = ⊤ + g2 y2 := by
          rw [EReal.add_top_of_ne_bot (by simp)]
        _ = ⊤ := by
          rw [EReal.top_add_of_ne_bot (hg2_proper.ne_bot y2)]
    exact (mem_effective_domain.mp hy).ne hFy_top
  exact EReal.coe_toReal hg1_ne_top (hg1_proper.ne_bot y1)

/-- Helper for Theorem 14.8: if the full objective is finite at `y`, then the second penalty term
is also finite there. -/
lemma two_block_second_penalty_eq_coe_toReal_of_mem_effective_domain
    (hg1_proper : IsProperExtendedRealFunction g1)
    (hg2_proper : IsProperExtendedRealFunction g2)
    {y : E1 × E2} (hy : y ∈ effective_domain F) :
    (((g2 y.2).toReal : ℝ) : EReal) = g2 y.2 := by
  rcases y with ⟨y1, y2⟩
  have hg2_ne_top : g2 y2 ≠ ⊤ := by
    -- A top-valued inactive penalty would also force the whole objective to be `⊤`.
    intro hg2_top
    have hFy_top : F (y1, y2) = ⊤ := by
      calc
        F (y1, y2) = (((f (y1, y2) : ℝ) : EReal) + g1 y1) + ⊤ := by
          simp [two_block_alternating_minimization_objective_apply, hg2_top, add_assoc]
        _ = ⊤ := by
          have hleft_ne_bot :
              (((f (y1, y2) : ℝ) : EReal) + g1 y1) ≠ ⊥ := by
            exact (EReal.add_ne_bot_iff).2 ⟨by simp [Function.toExtendedReal], hg1_proper.ne_bot y1⟩
          rw [EReal.add_top_of_ne_bot hleft_ne_bot]
    exact (mem_effective_domain.mp hy).ne hFy_top
  exact EReal.coe_toReal hg2_ne_top (hg2_proper.ne_bot y2)

/-- Helper for Theorem 14.8: once the current outer iterate is finite, the inactive marginal
`η₁(y₁) = inf_z₂ (f(y₁, z₂) + g₂(z₂))` is attained at the current second block. -/
lemma two_block_x1_inactive_marginal_eq_current_value
    (hg1_proper : IsProperExtendedRealFunction g1)
    (hg2_proper : IsProperExtendedRealFunction g2)
    (htraj : is_two_block_alternating_minimization_trajectory f.toExtendedReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    let eta1 : E1 → EReal :=
      fun y1 ↦ sInf (Set.range (fun z2 : E2 ↦ (((f (y1, z2) : ℝ) : EReal)) + g2 z2))
    eta1 (x1 n) = (((f (x1 n, x2 n) : ℝ) : EReal)) + g2 (x2 n) := by
  let eta1 : E1 → EReal :=
    fun y1 ↦ sInf (Set.range (fun z2 : E2 ↦ (((f (y1, z2) : ℝ) : EReal)) + g2 z2))
  have hiter :=
    two_block_iterates_mem_effective_domain_and_initial_sublevel
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2) htraj hx0 n
  have hg1_coe :
      (((g1 (x1 n)).toReal : ℝ) : EReal) = g1 (x1 n) :=
    two_block_first_penalty_eq_coe_toReal_of_mem_effective_domain
      (f := f) (g1 := g1) (g2 := g2) hg1_proper hg2_proper hiter.1
  have hmin :
      IsMinOn
        (two_block_alternating_minimization_x2_objective f.toExtendedReal g1 g2 (x1 n))
        Set.univ
        (x2 n) :=
    two_block_current_x2_objective_is_min_on
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2) htraj n
  apply le_antisymm
  · -- The current inactive block provides a witness in the marginal fiber.
    exact sInf_le ⟨x2 n, by simp [eta1]⟩
  · -- Exact `x₂`-minimality lets us cancel the finite active penalty from both slice values.
    refine le_sInf ?_
    rintro _ ⟨z2, rfl⟩
    have hslice : F x[n] ≤ F (x1 n, z2) := by
      simpa using (isMinOn_iff.mp hmin) z2 (by simp)
    have hcancel :
        ((((f (x1 n, x2 n) : ℝ) : EReal) + g2 (x2 n)) +
            (((g1 (x1 n)).toReal : ℝ) : EReal)) ≤
          ((((f (x1 n, z2) : ℝ) : EReal) + g2 z2) +
            (((g1 (x1 n)).toReal : ℝ) : EReal)) := by
      simpa [two_block_alternating_minimization_objective_apply, hg1_coe,
        add_assoc, add_left_comm, add_comm] using hslice
    exact
      (EReal.addLECancellable_coe ((g1 (x1 n)).toReal)).add_le_add_iff_right.mp hcancel

/-- Helper for Theorem 14.8: the optimal second block gives an upper witness for the inactive
first-block marginal `η₁`. -/
lemma two_block_x1_inactive_marginal_le_optimal_witness :
    let eta1 : E1 → EReal :=
      fun y1 ↦ sInf (Set.range (fun z2 : E2 ↦ (((f (y1, z2) : ℝ) : EReal)) + g2 z2))
    eta1 xStar.1 ≤ (((f xStar : ℝ) : EReal)) + g2 xStar.2 := by
  let eta1 : E1 → EReal :=
    fun y1 ↦ sInf (Set.range (fun z2 : E2 ↦ (((f (y1, z2) : ℝ) : EReal)) + g2 z2))
  -- Insert the optimal inactive block as one witness in the marginal fiber.
  exact sInf_le ⟨xStar.2, by simp [eta1]⟩

/-- Helper for Theorem 14.8: reattaching the active penalty to `η₁(x₁^n)` recovers the full
current objective value. -/
lemma two_block_x1_inactive_marginal_add_active_penalty_eq_current_objective
    (hg1_proper : IsProperExtendedRealFunction g1)
    (hg2_proper : IsProperExtendedRealFunction g2)
    (htraj : is_two_block_alternating_minimization_trajectory f.toExtendedReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    let eta1 : E1 → EReal :=
      fun y1 ↦ sInf (Set.range (fun z2 : E2 ↦ (((f (y1, z2) : ℝ) : EReal)) + g2 z2))
    eta1 (x1 n) + g1 (x1 n) = F x[n] := by
  let eta1 : E1 → EReal :=
    fun y1 ↦ sInf (Set.range (fun z2 : E2 ↦ (((f (y1, z2) : ℝ) : EReal)) + g2 z2))
  have heta' :
      eta1 (x1 n) = (((f (x1 n, x2 n) : ℝ) : EReal)) + g2 (x2 n) := by
    simpa [eta1] using
      two_block_x1_inactive_marginal_eq_current_value
        (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2)
        hg1_proper hg2_proper htraj hx0 n
  have heta :=
    heta'
  -- Add back the active penalty after the exact inactive minimization identity.
  calc
    eta1 (x1 n) + g1 (x1 n)
        = ((((f (x1 n, x2 n) : ℝ) : EReal)) + g2 (x2 n)) + g1 (x1 n) := by
            rw [heta]
    _ = F x[n] := by
      simp [two_block_alternating_minimization_objective_apply, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 14.8: reattaching the active penalty to the optimal witness for `η₁`
compares the marginal value against `F_opt`. -/
lemma two_block_x1_inactive_marginal_add_active_penalty_le_optimal_value
    (hFOpt : F xStar = (FOpt : EReal)) :
    let eta1 : E1 → EReal :=
      fun y1 ↦ sInf (Set.range (fun z2 : E2 ↦ (((f (y1, z2) : ℝ) : EReal)) + g2 z2))
    eta1 xStar.1 + g1 xStar.1 ≤ (FOpt : EReal) := by
  let eta1 : E1 → EReal :=
    fun y1 ↦ sInf (Set.range (fun z2 : E2 ↦ (((f (y1, z2) : ℝ) : EReal)) + g2 z2))
  have heta' :
      eta1 xStar.1 ≤ (((f xStar : ℝ) : EReal)) + g2 xStar.2 := by
    simpa [eta1] using
      two_block_x1_inactive_marginal_le_optimal_witness
        (f := f) (g2 := g2) (xStar := xStar)
  have heta :=
    heta'
  -- Add back the active penalty and rewrite to the full objective at `xStar`.
  calc
    eta1 xStar.1 + g1 xStar.1
        ≤ ((((f xStar : ℝ) : EReal)) + g2 xStar.2) + g1 xStar.1 := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_right heta (g1 xStar.1)
    _ = F xStar := by
      have hxStar_eta : xStar = (xStar.1, xStar.2) := by
        cases xStar
        rfl
      rw [show ((((f xStar : ℝ) : EReal)) + g2 xStar.2) + g1 xStar.1 =
          (((f xStar : ℝ) : EReal)) + (g1 xStar.1 + g2 xStar.2) by
            rw [add_assoc, add_comm (g2 xStar.2) (g1 xStar.1)]]
      rw [hxStar_eta, two_block_alternating_minimization_objective_apply]
      simp [Function.toExtendedReal, add_assoc]
    _ = (FOpt : EReal) := hFOpt

/-- Helper for Theorem 14.8: once the half-step is finite, the inactive marginal
`η₂(y₂) = inf_z₁ (f(z₁, y₂) + g₁(z₁))` is attained at the updated first block. -/
lemma two_block_x2_inactive_marginal_eq_current_value
    (hg1_proper : IsProperExtendedRealFunction g1)
    (hg2_proper : IsProperExtendedRealFunction g2)
    (htraj : is_two_block_alternating_minimization_trajectory f.toExtendedReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    let eta2 : E2 → EReal :=
      fun y2 ↦ sInf (Set.range (fun z1 : E1 ↦ (((f (z1, y2) : ℝ) : EReal)) + g1 z1))
    eta2 (x2 n) = (((f (x1 (n + 1), x2 n) : ℝ) : EReal)) + g1 (x1 (n + 1)) := by
  let eta2 : E2 → EReal :=
    fun y2 ↦ sInf (Set.range (fun z1 : E1 ↦ (((f (z1, y2) : ℝ) : EReal)) + g1 z1))
  have hhalf :=
    two_block_half_step_mem_effective_domain_and_initial_sublevel
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2) htraj hx0 n
  have hg2_coe :
      (((g2 (x2 n)).toReal : ℝ) : EReal) = g2 (x2 n) := by
    simpa [two_block_alternating_minimization_half_step] using
      two_block_second_penalty_eq_coe_toReal_of_mem_effective_domain
        (f := f) (g1 := g1) (g2 := g2) hg1_proper hg2_proper hhalf.1
  have hmin :
      IsMinOn
        (two_block_alternating_minimization_x1_objective f.toExtendedReal g1 g2 (x2 n))
        Set.univ
        (x1 (n + 1)) := by
    simpa [Nat.succ_eq_add_one] using htraj.step_x1 n
  apply le_antisymm
  · -- The updated first block is a witness in the second marginal fiber.
    exact sInf_le ⟨x1 (n + 1), by simp [eta2]⟩
  · -- Exact `x₁`-minimality lets us cancel the finite inactive penalty `g₂(x₂^n)`.
    refine le_sInf ?_
    rintro _ ⟨z1, rfl⟩
    have hslice :
        F (x1 (n + 1), x2 n) ≤ F (z1, x2 n) := by
      simpa [Nat.succ_eq_add_one, two_block_alternating_minimization_half_step] using
        (isMinOn_iff.mp hmin) z1 (by simp)
    have hcancel :
        ((((f (x1 (n + 1), x2 n) : ℝ) : EReal) + g1 (x1 (n + 1))) +
            (((g2 (x2 n)).toReal : ℝ) : EReal)) ≤
          ((((f (z1, x2 n) : ℝ) : EReal) + g1 z1) +
            (((g2 (x2 n)).toReal : ℝ) : EReal)) := by
      simpa [two_block_alternating_minimization_objective_apply, hg2_coe,
        add_assoc, add_left_comm, add_comm] using hslice
    exact
      (EReal.addLECancellable_coe ((g2 (x2 n)).toReal)).add_le_add_iff_right.mp hcancel

/-- Helper for Theorem 14.8: the optimal first block gives an upper witness for the inactive
second-block marginal `η₂`. -/
lemma two_block_x2_inactive_marginal_le_optimal_witness :
    let eta2 : E2 → EReal :=
      fun y2 ↦ sInf (Set.range (fun z1 : E1 ↦ (((f (z1, y2) : ℝ) : EReal)) + g1 z1))
    eta2 xStar.2 ≤ (((f xStar : ℝ) : EReal)) + g1 xStar.1 := by
  let eta2 : E2 → EReal :=
    fun y2 ↦ sInf (Set.range (fun z1 : E1 ↦ (((f (z1, y2) : ℝ) : EReal)) + g1 z1))
  -- Insert the optimal active block as one witness in the marginal fiber.
  exact sInf_le ⟨xStar.1, by simp [eta2]⟩

/-- Helper for Theorem 14.8: reattaching the inactive penalty to `η₂(x₂^n)` recovers the
half-step objective value. -/
lemma two_block_x2_inactive_marginal_add_inactive_penalty_eq_half_step_objective
    (hg1_proper : IsProperExtendedRealFunction g1)
    (hg2_proper : IsProperExtendedRealFunction g2)
    (htraj : is_two_block_alternating_minimization_trajectory f.toExtendedReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    let eta2 : E2 → EReal :=
      fun y2 ↦ sInf (Set.range (fun z1 : E1 ↦ (((f (z1, y2) : ℝ) : EReal)) + g1 z1))
    eta2 (x2 n) + g2 (x2 n) = F (two_block_alternating_minimization_half_step x1 x2 n) := by
  let eta2 : E2 → EReal :=
    fun y2 ↦ sInf (Set.range (fun z1 : E1 ↦ (((f (z1, y2) : ℝ) : EReal)) + g1 z1))
  have heta' :
      eta2 (x2 n) = (((f (x1 (n + 1), x2 n) : ℝ) : EReal)) + g1 (x1 (n + 1)) := by
    simpa [eta2] using
      two_block_x2_inactive_marginal_eq_current_value
        (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2)
        hg1_proper hg2_proper htraj hx0 n
  have heta :=
    heta'
  -- Add back the frozen second-block penalty after the exact inactive minimization identity.
  calc
    eta2 (x2 n) + g2 (x2 n)
        = ((((f (x1 (n + 1), x2 n) : ℝ) : EReal)) + g1 (x1 (n + 1))) + g2 (x2 n) := by
            rw [heta]
    _ = F (two_block_alternating_minimization_half_step x1 x2 n) := by
      simp [two_block_alternating_minimization_objective_apply,
        two_block_alternating_minimization_half_step, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 14.8: reattaching the inactive penalty to the optimal witness for `η₂`
compares that marginal value against `F_opt`. -/
lemma two_block_x2_inactive_marginal_add_inactive_penalty_le_optimal_value
    (hFOpt : F xStar = (FOpt : EReal)) :
    let eta2 : E2 → EReal :=
      fun y2 ↦ sInf (Set.range (fun z1 : E1 ↦ (((f (z1, y2) : ℝ) : EReal)) + g1 z1))
    eta2 xStar.2 + g2 xStar.2 ≤ (FOpt : EReal) := by
  let eta2 : E2 → EReal :=
    fun y2 ↦ sInf (Set.range (fun z1 : E1 ↦ (((f (z1, y2) : ℝ) : EReal)) + g1 z1))
  have heta' :
      eta2 xStar.2 ≤ (((f xStar : ℝ) : EReal)) + g1 xStar.1 := by
    simpa [eta2] using
      two_block_x2_inactive_marginal_le_optimal_witness
        (f := f) (g1 := g1) (xStar := xStar)
  have heta :=
    heta'
  -- Add back the inactive penalty and rewrite to the full objective at `xStar`.
  calc
    eta2 xStar.2 + g2 xStar.2
        ≤ ((((f xStar : ℝ) : EReal)) + g1 xStar.1) + g2 xStar.2 := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_right heta (g2 xStar.2)
    _ = F xStar := by
      have hxStar_eta : xStar = (xStar.1, xStar.2) := by
        cases xStar
        rfl
      rw [show ((((f xStar : ℝ) : EReal)) + g1 xStar.1) + g2 xStar.2 =
          (((f xStar : ℝ) : EReal)) + (g1 xStar.1 + g2 xStar.2) by
            rw [add_assoc]]
      rw [hxStar_eta, two_block_alternating_minimization_objective_apply]
      simp [Function.toExtendedReal, add_assoc]
    _ = (FOpt : EReal) := hFOpt

/-- Helper for Theorem 14.8: once a pair objective has a supporting affine lower bound at an
attained fiber minimizer, the same support inequality descends to the partial infimum. -/
lemma partial_infimum_support_of_attained_pair_support
    {E : Type u} {V : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {H : E × V → EReal} {x0 : E} {v0 : V} {g : Module.Dual ℝ E}
    (hattained :
      sInf (Set.range (fun v : V ↦ H (x0, v))) = H (x0, v0))
    (hsupport :
      ∀ y : E, ∀ v : V, H (y, v) ≥ H (x0, v0) + (g (y - x0) : EReal)) :
    ∀ y : E,
      sInf (Set.range (fun v : V ↦ H (y, v))) ≥
        sInf (Set.range (fun v : V ↦ H (x0, v))) + (g (y - x0) : EReal) := by
  intro y
  -- Rewrite the base fiber infimum through the attained minimizer before descending the support
  -- inequality to the entire target fiber.
  rw [hattained]
  refine le_sInf ?_
  rintro _ ⟨v, rfl⟩
  -- Every point in the `y`-fiber lies above the same supporting affine lower bound.
  exact hsupport y v

/-- Helper for Theorem 14.8: the source equation `(14.35)` is the `x₁`-half-step quadratic gap
estimate. -/
lemma two_block_x1_half_step_quadratic_gap
    (hg1_proper : IsProperExtendedRealFunction g1)
    (hg1_convex : is_convex_function g1)
    (hg2_proper : IsProperExtendedRealFunction g2)
    (htraj : is_two_block_alternating_minimization_trajectory f.toExtendedReal g1 g2 x1 x2)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_x1_smooth :
      ∀ z2 : E2, is_l_smooth_on (fun y1 ↦ f (y1, z2)) Set.univ (PosReal.toNNReal L1))
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal))
    (hx0 : x[0] ∈ effective_domain F)
    (hR :
      ∀ ⦃y : E1 × E2⦄,
        F y ≤ F x[0] →
        ‖y - xStar‖ ≤ (R : ℝ))
    (n : ℕ) :
    let xHalf := two_block_alternating_minimization_half_step x1 x2 n
    ((F x[n]).toReal - FOpt) - ((F xHalf).toReal - FOpt) ≥
      (1 / (2 * (L1 : ℝ) * ((R : ℝ) ^ (2 : ℕ)))) *
        (((F xHalf).toReal - FOpt) ^ (2 : ℕ)) := by
  -- Route correction: isolate the source `(14.35)` half-step estimate as its own blocker so the
  -- final recurrence can be completed from textbook algebra alone.
  let _ := hg1_proper
  let _ := hg1_convex
  let _ := hg2_proper
  let _ := htraj
  let _ := hf_convex
  let _ := hf_x1_smooth
  let _ := hxStar
  let _ := hFOpt
  let _ := hx0
  let _ := hR
  have heta_current :=
    two_block_x1_inactive_marginal_add_active_penalty_eq_current_objective
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2)
      hg1_proper hg2_proper htraj hx0 n
  have heta_opt :=
    two_block_x1_inactive_marginal_add_active_penalty_le_optimal_value
      (f := f) (g1 := g1) (g2 := g2) (xStar := xStar) (FOpt := FOpt) hFOpt
  let _ := heta_current
  let _ := heta_opt
  -- Route correction: the stalled full-objective marginal `phi1` route is replaced by the source
  -- inactive marginal `eta1(y1) = inf_z2 (f(y1, z2) + g2 z2)`, whose current-value and
  -- optimal-witness identities are now proved above.
  -- TODO: the remaining source-faithful blocker is now only the pair-support theorem for
  -- `H1(y1, z2) = ((f (y1, z2) : ℝ) : EReal) + g2 z2` at `(x1 n, x2 n)`.
  -- After proving
  -- `H1 (y1, z2) ≥ H1 (x1 n, x2 n) +
  --    (fderiv ℝ (fun y1 ↦ f (y1, x2 n)) (x1 n) (y1 - x1 n) : EReal)`,
  -- `partial_infimum_support_of_attained_pair_support` descends it to the needed `eta1`
  -- inequality, and `heta_current` plus `heta_opt` finish the existing smooth/radius algebra.
  sorry

/-- Helper for Theorem 14.8: the source equation `(14.36)` contributes the `x₂`-next-step
quadratic gap estimate. -/
lemma two_block_x2_next_step_quadratic_gap
    (hg1_proper : IsProperExtendedRealFunction g1)
    (hg2_proper : IsProperExtendedRealFunction g2)
    (hg2_convex : is_convex_function g2)
    (htraj : is_two_block_alternating_minimization_trajectory f.toExtendedReal g1 g2 x1 x2)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_x2_smooth :
      ∀ z1 : E1, is_l_smooth_on (fun y2 ↦ f (z1, y2)) Set.univ (PosReal.toNNReal L2))
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal))
    (hx0 : x[0] ∈ effective_domain F)
    (hR :
      ∀ ⦃y : E1 × E2⦄,
        F y ≤ F x[0] →
        ‖y - xStar‖ ≤ (R : ℝ))
    (n : ℕ) :
    let xHalf := two_block_alternating_minimization_half_step x1 x2 n
    ((F xHalf).toReal - FOpt) - ((F x[n + 1]).toReal - FOpt) ≥
      (1 / (2 * (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ)))) *
        (((F x[n + 1]).toReal - FOpt) ^ (2 : ℕ)) := by
  -- Route correction: isolate the symmetric `x₂` source inequality before the final `min` step.
  let _ := hg1_proper
  let _ := hg2_proper
  let _ := hg2_convex
  let _ := htraj
  let _ := hf_convex
  let _ := hf_x2_smooth
  let _ := hxStar
  let _ := hFOpt
  let _ := hx0
  let _ := hR
  have heta_current :=
    two_block_x2_inactive_marginal_add_inactive_penalty_eq_half_step_objective
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2)
      hg1_proper hg2_proper htraj hx0 n
  have heta_opt :=
    two_block_x2_inactive_marginal_add_inactive_penalty_le_optimal_value
      (f := f) (g1 := g1) (g2 := g2) (xStar := xStar) (FOpt := FOpt) hFOpt
  let _ := heta_current
  let _ := heta_opt
  -- Route correction: the symmetric `phi2` route is replaced by the source inactive marginal
  -- `eta2(y2) = inf_z1 (f(z1, y2) + g1 z1)`, with the exact attainment and optimal witness
  -- identities already normalized above.
  -- TODO: the remaining source-faithful blocker is now only the symmetric pair-support theorem
  -- for `H2(z1, y2) = ((f (z1, y2) : ℝ) : EReal) + g1 z1` at
  -- `(x1 (n + 1), x2 n)`.
  -- Once
  -- `H2 (z1, y2) ≥ H2 (x1 (n + 1), x2 n) +
  --    (fderiv ℝ (fun y2 ↦ f (x1 (n + 1), y2)) (x2 n) (y2 - x2 n) : EReal)`
  -- is available, `partial_infimum_support_of_attained_pair_support` gives the required `eta2`
  -- support step and the existing reattachment/smoothness algebra closes `(14.36)`.
  sorry

/-- Helper for Theorem 14.8: the source proof's real work is the quadratic one-step recurrence
for the two-block objective-gap sequence. -/
lemma two_block_objective_gap_quadratic_recurrence
    (hg1_proper : IsProperExtendedRealFunction g1)
    (hg1_convex : is_convex_function g1)
    (hg2_proper : IsProperExtendedRealFunction g2)
    (hg2_convex : is_convex_function g2)
    (htraj : is_two_block_alternating_minimization_trajectory f.toExtendedReal g1 g2 x1 x2)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_x1_smooth :
      ∀ z2 : E2, is_l_smooth_on (fun y1 ↦ f (y1, z2)) Set.univ (PosReal.toNNReal L1))
    (hf_x2_smooth :
      ∀ z1 : E1, is_l_smooth_on (fun y2 ↦ f (z1, y2)) Set.univ (PosReal.toNNReal L2))
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal))
    (hx0 : x[0] ∈ effective_domain F)
    (hR :
      ∀ ⦃y : E1 × E2⦄,
        F y ≤ F x[0] →
        ‖y - xStar‖ ≤ (R : ℝ))
    (n : ℕ) :
    ((F x[n]).toReal - FOpt) - ((F x[n + 1]).toReal - FOpt) ≥
      (1 / (2 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ)))) *
        (((F x[n + 1]).toReal - FOpt) ^ (2 : ℕ)) := by
  let xHalf := two_block_alternating_minimization_half_step x1 x2 n
  let gapHalf : ℝ := (F xHalf).toReal - FOpt
  let gapNext : ℝ := (F x[n + 1]).toReal - FOpt
  let c1 : ℝ := 1 / (2 * (L1 : ℝ) * ((R : ℝ) ^ (2 : ℕ)))
  let c2 : ℝ := 1 / (2 * (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ)))
  have hhalf :
      ((F x[n]).toReal - FOpt) - gapHalf ≥
        c1 * (gapHalf ^ (2 : ℕ)) := by
    -- This is the source half-step estimate `(14.35)`.
    simpa [xHalf, gapHalf, c1] using
      two_block_x1_half_step_quadratic_gap
        (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2)
        (xStar := xStar) (FOpt := FOpt) (L1 := L1) (R := R)
        hg1_proper hg1_convex hg2_proper htraj hf_convex hf_x1_smooth hxStar hFOpt hx0 hR n
  have hnext :
      gapHalf - gapNext ≥
        c2 * (gapNext ^ (2 : ℕ)) := by
    -- This is the source next-step estimate on the second block.
    simpa [xHalf, gapHalf, gapNext, c2] using
      two_block_x2_next_step_quadratic_gap
        (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2)
        (xStar := xStar) (FOpt := FOpt) (L2 := L2) (R := R)
        hg1_proper hg2_proper hg2_convex htraj hf_convex hf_x2_smooth hxStar hFOpt hx0 hR n
  have hgap_next_nonneg : 0 ≤ gapNext := by
    -- The next iterate is feasible and lies above the optimal value.
    simpa [gapNext] using
      two_block_objective_gap_nonneg
        (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2)
        (xStar := xStar) (FOpt := FOpt)
        hg1_proper hg2_proper htraj hxStar hFOpt hx0 (n + 1)
  have hgap_next_le_half : gapNext ≤ gapHalf := by
    -- Exact `x₂` minimization makes the next-step gap no larger than the half-step gap.
    simpa [xHalf, gapHalf, gapNext] using
      two_block_next_iterate_objective_gap_le_half_step_gap
        (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2)
        (FOpt := FOpt) hg1_proper hg2_proper htraj hx0 n
  have hgap_half_nonneg : 0 ≤ gapHalf := by
    linarith
  have hc1_nonneg : 0 ≤ c1 := by
    have hL1_pos : 0 < (L1 : ℝ) := PosReal.coe_pos L1
    have hR_sq_pos : 0 < ((R : ℝ) ^ (2 : ℕ)) := by
      simpa [pow_two] using sq_pos_of_pos (PosReal.coe_pos R)
    have hden_pos : 0 < 2 * (L1 : ℝ) * ((R : ℝ) ^ (2 : ℕ)) := by
      exact mul_pos (mul_pos (by norm_num) hL1_pos) hR_sq_pos
    dsimp [c1]
    exact one_div_nonneg.mpr hden_pos.le
  have hsecond_drop_nonneg : 0 ≤ gapHalf - gapNext := by
    linarith
  have hsq_next_le_half : gapNext ^ (2 : ℕ) ≤ gapHalf ^ (2 : ℕ) := by
    nlinarith
  have hfrom_x1 :
      ((F x[n]).toReal - FOpt) - gapNext ≥
        c1 * (gapNext ^ (2 : ℕ)) := by
    -- Replace the half-step gap in `(14.35)` by the smaller next-step gap.
    have hdecomp :
        ((F x[n]).toReal - FOpt) - gapNext =
          (((F x[n]).toReal - FOpt) - gapHalf) + (gapHalf - gapNext) := by
      ring
    rw [hdecomp]
    nlinarith
  have hcoef1_nonneg : 0 ≤ c1 * (gapHalf ^ (2 : ℕ)) := by
    nlinarith
  have hfirst_drop_nonneg :
      0 ≤ ((F x[n]).toReal - FOpt) - gapHalf := by
    linarith
  have hfrom_x2 :
      ((F x[n]).toReal - FOpt) - gapNext ≥
        c2 * (gapNext ^ (2 : ℕ)) := by
    -- Add the nonnegative first-block decrease to the `x₂` estimate.
    have hdecomp :
        ((F x[n]).toReal - FOpt) - gapNext =
          (((F x[n]).toReal - FOpt) - gapHalf) + (gapHalf - gapNext) := by
      ring
    rw [hdecomp]
    nlinarith
  by_cases hL : (L1 : ℝ) ≤ (L2 : ℝ)
  · -- If `L₁` is the smaller Lipschitz constant, the `x₁` estimate already has the target
    -- coefficient.
    have htarget :
        ((F x[n]).toReal - FOpt) - ((F x[n + 1]).toReal - FOpt) ≥
          c1 * (((F x[n + 1]).toReal - FOpt) ^ (2 : ℕ)) := by
      simpa [gapNext] using hfrom_x1
    simpa [c1, min_eq_left hL] using htarget
  · -- Otherwise `L₂ < L₁`, so the symmetric `x₂` estimate is the sharper one.
    have hL' : (L2 : ℝ) ≤ (L1 : ℝ) := le_of_lt (lt_of_not_ge hL)
    have htarget :
        ((F x[n]).toReal - FOpt) - ((F x[n + 1]).toReal - FOpt) ≥
          c2 * (((F x[n + 1]).toReal - FOpt) ^ (2 : ℕ)) := by
      simpa [gapNext] using hfrom_x2
    simpa [c2, min_eq_right hL'] using htarget

/-- Helper for Theorem 14.8: the source proof reduces the theorem to a Chapter 14 quadratic
recurrence and then to the Chapter 11 scalar recurrence estimate. -/
lemma two_block_objective_gap_le_max_geometric_or_sublinear_core
    (hg1_proper : IsProperExtendedRealFunction g1)
    (hg1_convex : is_convex_function g1)
    (hg2_proper : IsProperExtendedRealFunction g2)
    (hg2_convex : is_convex_function g2)
    (htraj : is_two_block_alternating_minimization_trajectory f.toExtendedReal g1 g2 x1 x2)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_x1_smooth :
      ∀ z2 : E2, is_l_smooth_on (fun y1 ↦ f (y1, z2)) Set.univ (PosReal.toNNReal L1))
    (hf_x2_smooth :
      ∀ z1 : E1, is_l_smooth_on (fun y2 ↦ f (z1, y2)) Set.univ (PosReal.toNNReal L2))
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal))
    (hx0 : x[0] ∈ effective_domain F)
    (hR :
      ∀ ⦃y : E1 × E2⦄,
        F y ≤ F x[0] →
        ‖y - xStar‖ ≤ (R : ℝ))
    (k : ℕ) (hk : 2 ≤ k) :
    (F x[k]).toReal - FOpt ≤
      max
        (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) *
          ((F x[0]).toReal - FOpt))
        ((8 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ))) / ((k - 1 : ℕ) : ℝ)) := by
  let γ : PosReal := ⟨2 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ)), by
    have hmin_pos : 0 < min (L1 : ℝ) (L2 : ℝ) := by
      exact lt_min (PosReal.coe_pos L1) (PosReal.coe_pos L2)
    have hR_pos : 0 < (R : ℝ) ^ (2 : ℕ) := by
      simpa [pow_two] using sq_pos_of_pos (PosReal.coe_pos R)
    exact mul_pos (mul_pos (by norm_num) hmin_pos) hR_pos⟩
  have hγ :
      4 * (γ : ℝ) ≤ 8 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ)) := by
    have hγ_eq :
        4 * (γ : ℝ) = 8 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ)) := by
      dsimp [γ]
      ring
    exact hγ_eq.le
  have hgap_nonneg :
      ∀ n : ℕ, 0 ≤ (F x[n]).toReal - FOpt := by
    -- Each iterate is finite and lies above the optimal value.
    intro n
    exact
      two_block_objective_gap_nonneg
        (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2)
        (xStar := xStar) (FOpt := FOpt)
        hg1_proper hg2_proper htraj hxStar hFOpt hx0 n
  have hstep :
      ∀ n : ℕ,
        ((F x[n]).toReal - FOpt) - ((F x[n + 1]).toReal - FOpt) ≥
          (1 / (γ : ℝ)) * (((F x[n + 1]).toReal - FOpt) ^ (2 : ℕ)) := by
    -- This is the remaining source-faithful Chapter 14 recurrence step.
    intro n
    simpa [γ] using
      two_block_objective_gap_quadratic_recurrence
        (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2)
        (xStar := xStar) (FOpt := FOpt) (L1 := L1) (L2 := L2) (R := R)
        hg1_proper hg1_convex hg2_proper hg2_convex
        htraj hf_convex hf_x1_smooth hf_x2_smooth hxStar hFOpt hx0 hR n
  exact
    two_block_objective_gap_le_of_quadratic_recurrence
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2)
      (FOpt := FOpt) (L1 := L1) (L2 := L2) (R := R)
      γ hγ hgap_nonneg hstep k hk

/-- Theorem 14.8: if the penalties `g₁` and `g₂` are proper, closed, and convex, the smooth term
`f : E₁ × E₂ → ℝ` is convex, each frozen one-block slice of `f` is `L₁`- or `L₂`-smooth,
`(x₁^k, x₂^k)` is generated by the exact two-block
alternating-minimization method from Algorithm 14.8, `xStar` is an optimal point with
`F(xStar) = F_opt`, the initial pair `x^0 = (x₁^0, x₂^0)` lies in `dom(F)`, and every point of
the initial sublevel set `{y | F(y) ≤ F(x^0)}` stays within distance `R` of `xStar`, then for
every `k ≥ 2` the objective gap is
bounded by the maximum of the geometric term
`(1 / 2)^((k - 1) / 2) (F(x^0) - F_opt)` and the sublinear term
`8 min {L₁, L₂} R^2 / (k - 1)`, where `R` is the initial-sublevel radius `R_{F(x^0)}`. -/
theorem two_block_alternating_minimization_objective_gap_le_max_geometric_or_sublinear
    (hg1_proper : IsProperExtendedRealFunction g1)
    (hg1_closed : LowerSemicontinuous g1)
    (hg1_convex : is_convex_function g1)
    (hg2_proper : IsProperExtendedRealFunction g2)
    (hg2_closed : LowerSemicontinuous g2)
    (hg2_convex : is_convex_function g2)
    (htraj : is_two_block_alternating_minimization_trajectory f.toExtendedReal g1 g2 x1 x2)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_x1_smooth :
      ∀ z2 : E2, is_l_smooth_on (fun y1 ↦ f (y1, z2)) Set.univ (PosReal.toNNReal L1))
    (hf_x2_smooth :
      ∀ z1 : E1, is_l_smooth_on (fun y2 ↦ f (z1, y2)) Set.univ (PosReal.toNNReal L2))
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal))
    (hx0 : x[0] ∈ effective_domain F)
    (hR :
      ∀ ⦃y : E1 × E2⦄,
        F y ≤ F x[0] →
        ‖y - xStar‖ ≤ (R : ℝ))
    (k : ℕ) (hk : 2 ≤ k) :
    (F x[k]).toReal - FOpt ≤
      max
        (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) *
          ((F x[0]).toReal - FOpt))
        ((8 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ))) / ((k - 1 : ℕ) : ℝ)) := by
  -- These regularity assumptions are exactly the remaining inputs to the open recurrence lemma.
  let _ := hg1_closed
  let _ := hg1_convex
  let _ := hg2_closed
  let _ := hg2_convex
  -- Reduce the theorem to the scalar recurrence from the textbook proof.
  exact
    two_block_objective_gap_le_max_geometric_or_sublinear_core
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2)
      (xStar := xStar) (FOpt := FOpt) (L1 := L1) (L2 := L2) (R := R)
      hg1_proper hg1_convex hg2_proper hg2_convex
      htraj hf_convex hf_x1_smooth hf_x2_smooth hxStar hFOpt hx0 hR k hk

end
