import Mathlib
import BauschkeLean.Chap02.Corollary_2_15
import BauschkeLean.Chap02.Lemma_2_46
import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap03.Theorem_3_16_2
import BauschkeLean.Chap08.Corollary_8_39
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap05.Definition_5_1
import BauschkeLean.Chap05.Proposition_5_4
import BauschkeLean.Chap05.Proposition_5_7
import BauschkeLean.Chap10.Definition_10_7
import BauschkeLean.Chap10.Proposition_10_8
import BauschkeLean.Chap11.Corollary_11_30
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap11.Definition_11_11

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction Filter
open scoped Topology

universe u

section

variable {H : Type u} [NormedAddCommGroup H]

/- Proposition 11.18: the source-facing owner is the extended-real limsup squared-distance
objective attached to a sequence `zₙ`. This keeps the correct `+∞` behavior for unbounded
sequences, while boundedness is used later only for the finite real-valued bridge. -/
/-- The asymptotic-center objective attached to a sequence `zₙ`, namely
`x ↦ limsup ‖x - zₙ‖²`, viewed in `EReal`. -/
noncomputable def asymptoticCenterObjective (zₙ : ℕ → H) : H → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    ⟨Filter.limsup (fun n ↦ ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) atTop, by
      have hnonneg :
          (0 : EReal) ≤
            Filter.limsup (fun n ↦ ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) atTop := by
        refine Filter.le_limsup_of_le (by isBoundedDefault) ?_
        intro b hb
        rcases Filter.eventually_atTop.1 hb with ⟨N, hN⟩
        have hN_nonneg : (0 : EReal) ≤ ((‖x - zₙ N‖ ^ (2 : ℕ) : ℝ) : EReal) := by
          exact_mod_cast (show 0 ≤ ‖x - zₙ N‖ ^ (2 : ℕ) by positivity)
        exact le_trans hN_nonneg (hN N le_rfl)
      exact lt_of_lt_of_le (by simp) hnonneg⟩

/-- For a bounded sequence, the asymptotic-center objective is finite everywhere. -/
theorem asymptoticCenterObjective_lt_top
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) (x : H) :
    (asymptoticCenterObjective zₙ x : EReal) < ⊤ := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hzₙ_bdd
  have hR_nonneg : 0 ≤ R := by
    exact le_trans (norm_nonneg _) (hR (zₙ 0) (Set.mem_range_self 0))
  -- A uniform norm bound on `zₙ` gives a uniform bound on every squared-distance term.
  have hle :
      ∀ᶠ n in atTop, ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal) ≤ (((‖x‖ + R) ^ (2 : ℕ) : ℝ) : EReal) :=
    Filter.Eventually.of_forall fun n ↦ by
      have hz : ‖zₙ n‖ ≤ R := by
        simpa using hR (zₙ n) (Set.mem_range_self n)
      have hnorm : ‖x - zₙ n‖ ≤ ‖x‖ + R := by
        calc
          ‖x - zₙ n‖ ≤ ‖x‖ + ‖zₙ n‖ := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_sub_le x (zₙ n)
          _ ≤ ‖x‖ + R := by
            linarith
      exact_mod_cast
        (show ‖x - zₙ n‖ ^ (2 : ℕ) ≤ (‖x‖ + R) ^ (2 : ℕ) by
          have hsum_nonneg : 0 ≤ ‖x‖ + R := add_nonneg (norm_nonneg _) hR_nonneg
          nlinarith [hnorm, norm_nonneg (x - zₙ n), hsum_nonneg])
  -- The limsup is therefore bounded by a finite real, so it cannot be `⊤`.
  have hlimsup_le :
      Filter.limsup (fun n ↦ ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) atTop ≤
        (((‖x‖ + R) ^ (2 : ℕ) : ℝ) : EReal) := by
    exact Filter.limsup_le_of_le (hf := by isBoundedDefault) hle
  change Filter.limsup (fun n ↦ ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) atTop < ⊤
  exact lt_of_le_of_lt hlimsup_le (EReal.coe_lt_top _)

/-- Any global minimizer of the indicator-augmented asymptotic-center objective lies in the
constraint set. -/
private theorem mem_constraint_of_mem_argmin_addIndicator_asymptoticCenterObjective
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {C : Set H}
    (hC_nonempty : C.Nonempty) {z : H}
    (hz : z ∈ Argmin ((asymptoticCenterObjective zₙ + ι[C]).asEReal)) :
    z ∈ C := by
  rcases hC_nonempty with ⟨y, hyC⟩
  have hzmin :
      IsMinOn ((asymptoticCenterObjective zₙ + ι[C]).asEReal) Set.univ z :=
    mem_argmin_iff.1 hz
  have hzy : ((asymptoticCenterObjective zₙ + ι[C]).asEReal) z ≤
      ((asymptoticCenterObjective zₙ + ι[C]).asEReal) y :=
    (isMinOn_univ_iff).1 hzmin y
  -- A feasible comparison point has finite objective value because the indicator vanishes on `C`.
  have hy_lt_top : ((asymptoticCenterObjective zₙ + ι[C]).asEReal) y < ⊤ := by
    simpa [hyC] using asymptoticCenterObjective_lt_top hzₙ_bdd y
  by_contra hzC
  have hz_eq_top : ((asymptoticCenterObjective zₙ + ι[C]).asEReal) z = ⊤ := by
    have hz_ne_bot : (asymptoticCenterObjective zₙ z : EReal) ≠ ⊥ :=
      ne_of_gt (asymptoticCenterObjective zₙ z).2
    simpa [hzC] using EReal.add_top_of_ne_bot hz_ne_bot
  have : (⊤ : EReal) ≤ ((asymptoticCenterObjective zₙ + ι[C]).asEReal) y := by
    simpa [hz_eq_top] using hzy
  exact not_le_of_gt hy_lt_top this

section RealHilbert

variable [InnerProductSpace ℝ H]

/-- Helper for Proposition 11 18: weak convergence in the first slot and strong convergence in
the second slot imply convergence of the real inner product. -/
private theorem tendsto_inner_of_tendsto_toWeakSpace_of_tendsto
    [CompleteSpace H]
    (xSeq uSeq : ℕ → H) (x u : H)
    (hx :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hu : Tendsto uSeq atTop (𝓝 u)) :
    Tendsto (fun n ↦ inner ℝ (xSeq n) (uSeq n)) atTop (𝓝 (inner ℝ x u)) := by
  -- Route correction: the earlier completeness-bound route was wrong here; instead we follow the
  -- Chapter 2 proof directly by splitting off the strongly convergent perturbation `uSeq n - u`.
  have hxSeq_bdd : Bornology.IsBounded (Set.range xSeq) := bounded_range_of_tendsto_weakly hx
  obtain ⟨R, hR⟩ := hxSeq_bdd.subset_closedBall (0 : H)
  have hR_norm : ∀ n, ‖xSeq n‖ ≤ R := by
    intro n
    simpa [Metric.mem_closedBall, dist_eq_norm] using hR (Set.mem_range_self n)
  have hu_sub : Tendsto (fun n ↦ uSeq n - u) atTop (𝓝 (0 : H)) := by
    have hsub : Tendsto (fun n ↦ uSeq n - u) atTop (𝓝 (u - u)) :=
      hu.sub tendsto_const_nhds
    simpa using hsub
  have hsmall_bound :
      ∀ n, ‖inner ℝ (xSeq n) (uSeq n - u)‖ ≤ R * ‖uSeq n - u‖ := by
    intro n
    calc
      ‖inner ℝ (xSeq n) (uSeq n - u)‖ ≤ ‖xSeq n‖ * ‖uSeq n - u‖ := abs_real_inner_le_norm _ _
      _ ≤ R * ‖uSeq n - u‖ := by
        exact mul_le_mul_of_nonneg_right (hR_norm n) (norm_nonneg _)
  have hsmall_bound_tendsto : Tendsto (fun n ↦ R * ‖uSeq n - u‖) atTop (𝓝 0) := by
    simpa using hu_sub.norm.const_mul R
  have hsmall :
      Tendsto (fun n ↦ inner ℝ (xSeq n) (uSeq n - u)) atTop (𝓝 0) := by
    exact squeeze_zero_norm hsmall_bound hsmall_bound_tendsto
  have hfixed : Tendsto (fun n ↦ inner ℝ (xSeq n) u) atTop (𝓝 (inner ℝ x u)) := by
    simpa using ((weakSpace_continuous_inner_right u).tendsto (toWeakSpace ℝ H x)).comp hx
  have hsum :
      Tendsto
        (fun n ↦ inner ℝ (xSeq n) (uSeq n - u) + inner ℝ (xSeq n) u)
        atTop (𝓝 (0 + inner ℝ x u)) :=
    hsmall.add hfixed
  convert hsum using 1
  · funext n
    rw [← inner_add_right, sub_add_cancel]
  · simp

/-- Helper for Proposition 11 18: translating the affine-combination squared-norm identity by a
base point `z` yields the textbook expansion for squared distances to `z`. -/
private theorem sqNorm_sub_affine_combination_add_weighted_norm_sub_sq
    (x y z : H) (α : ℝ) :
    ‖(α • x + (1 - α) • y) - z‖ ^ (2 : ℕ) + α * (1 - α) * ‖x - y‖ ^ (2 : ℕ) =
      α * ‖x - z‖ ^ (2 : ℕ) + (1 - α) * ‖y - z‖ ^ (2 : ℕ) := by
  have htranslate :
      α • (x - z) + (1 - α) • (y - z) = (α • x + (1 - α) • y) - z := by
    rw [smul_sub, smul_sub]
    calc
      α • x - α • z + ((1 - α) • y - (1 - α) • z)
          = α • x + (1 - α) • y - (α • z + (1 - α) • z) := by
            abel
      _ = (α • x + (1 - α) • y) - z := by
            rw [← add_smul, show α + (1 - α) = (1 : ℝ) by ring, one_smul]
  -- Translate the standard affine-combination identity by the base point `z`.
  simpa [htranslate] using
    norm_sq_affine_combination_add_weighted_norm_sub_sq (x - z) (y - z) α

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 11 18: boundedness of the orbit gives a uniform upper bound on each
fixed-base squared-distance sequence, which is the exact `limsup` boundedness input needed later.
-/
private theorem sqdist_sequence_isBoundedUnder
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) (x : H) :
    Filter.IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ)
      (fun n ↦ ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hzₙ_bdd
  have hR_nonneg : 0 ≤ R := by
    exact le_trans (norm_nonneg _) (hR (zₙ 0) (Set.mem_range_self 0))
  refine Filter.isBoundedUnder_of_eventually_le (a := (((‖x‖ + R) ^ (2 : ℕ) : ℝ) : EReal)) ?_
  refine Filter.Eventually.of_forall fun n ↦ ?_
  have hz : ‖zₙ n‖ ≤ R := by
    simpa using hR (zₙ n) (Set.mem_range_self n)
  have hnorm : ‖x - zₙ n‖ ≤ ‖x‖ + R := by
    calc
      ‖x - zₙ n‖ ≤ ‖x‖ + ‖zₙ n‖ := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_sub_le x (zₙ n)
      _ ≤ ‖x‖ + R := by
        linarith
  exact_mod_cast
    (show ‖x - zₙ n‖ ^ (2 : ℕ) ≤ (‖x‖ + R) ^ (2 : ℕ) by
      have hsum_nonneg : 0 ≤ ‖x‖ + R := add_nonneg (norm_nonneg _) hR_nonneg
      nlinarith [hnorm, norm_nonneg (x - zₙ n), hsum_nonneg])

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 11 18: every squared-distance sequence is nonnegative, so it is
frequently bounded below by `0` and therefore cobounded for `Filter.limsup`. -/
private theorem sqdist_sequence_isCoboundedUnder
    {zₙ : ℕ → H} (x : H) :
    Filter.IsCoboundedUnder (· ≤ ·) (atTop : Filter ℕ)
      (fun n ↦ ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
  -- Every squared norm is nonnegative, so `0` is a frequent lower bound for the sequence.
  exact Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
    (Frequently.of_forall fun n ↦ by
      exact_mod_cast (show 0 ≤ ‖x - zₙ n‖ ^ (2 : ℕ) by positivity))

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 11 18: the weighted squared-distance sequence satisfies the exact
`limsup` Jensen bound needed for the asymptotic-center objective. -/
private theorem limsup_weighted_sqdist_jensen_le
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) (x y : H)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    Filter.limsup
        (fun n ↦
          (((α * ‖x - zₙ n‖ ^ (2 : ℕ) + (1 - α) * ‖y - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)))
        atTop ≤
      (α : EReal) *
          Filter.limsup (fun n ↦ ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) atTop +
        (1 - α : EReal) *
          Filter.limsup (fun n ↦ ((‖y - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) atTop := by
  let u : ℕ → EReal := fun n ↦ ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)
  let v : ℕ → EReal := fun n ↦ ((‖y - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)
  have hu_bdd : Filter.IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ) u := by
    simpa [u] using sqdist_sequence_isBoundedUnder hzₙ_bdd x
  have hv_bdd : Filter.IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ) v := by
    simpa [v] using sqdist_sequence_isBoundedUnder hzₙ_bdd y
  have hscaled_u_bddAbove :
      Filter.IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ) (fun n ↦ (α : EReal) * u n) := by
    rcases hu_bdd.eventually_le with ⟨U, hU⟩
    refine Filter.isBoundedUnder_of_eventually_le (a := (α : EReal) * U) ?_
    exact hU.mono fun n hn ↦ mul_le_mul_of_nonneg_left hn (by exact_mod_cast hα0)
  have hscaled_v_bddAbove :
      Filter.IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ) (fun n ↦ (1 - α : EReal) * v n) := by
    rcases hv_bdd.eventually_le with ⟨V, hV⟩
    refine Filter.isBoundedUnder_of_eventually_le (a := (1 - α : EReal) * V) ?_
    exact hV.mono fun n hn ↦ mul_le_mul_of_nonneg_left hn (by exact_mod_cast sub_nonneg.mpr hα1)
  have hscaled_u_bddBelow :
      Filter.IsBoundedUnder (· ≥ ·) (atTop : Filter ℕ) (fun n ↦ (α : EReal) * u n) := by
    refine Filter.isBoundedUnder_of_eventually_ge (a := 0) ?_
    exact Filter.Eventually.of_forall fun n ↦ by
      exact mul_nonneg (by exact_mod_cast hα0) (by simp [u])
  have hscaled_v_nonneg : 0 ≤ᶠ[atTop] fun n ↦ (1 - α : EReal) * v n := by
    exact Filter.Eventually.of_forall fun n ↦ by
      exact mul_nonneg (by exact_mod_cast sub_nonneg.mpr hα1) (by simp [v])
  have hscaled_u_nonneg : 0 ≤ᶠ[atTop] fun n ↦ (α : EReal) * u n := by
    exact Filter.Eventually.of_forall fun n ↦ by
      exact mul_nonneg (by exact_mod_cast hα0) (by simp [u])
  have hscaled_u_ne_bot : Filter.limsup (fun n ↦ (α : EReal) * u n) atTop ≠ ⊥ := by
    have hnonneg :
        (0 : EReal) ≤ Filter.limsup (fun n ↦ (α : EReal) * u n) atTop := by
      exact le_of_eq_of_le (Filter.limsup_const 0).symm
        (Filter.limsup_le_limsup hscaled_u_nonneg (by isBoundedDefault) hscaled_u_bddAbove)
    exact ne_of_gt (lt_of_lt_of_le (by simp) hnonneg)
  have hscaled_v_ne_bot : Filter.limsup (fun n ↦ (1 - α : EReal) * v n) atTop ≠ ⊥ := by
    have hnonneg :
        (0 : EReal) ≤ Filter.limsup (fun n ↦ (1 - α : EReal) * v n) atTop := by
      exact le_of_eq_of_le (Filter.limsup_const 0).symm
        (Filter.limsup_le_limsup hscaled_v_nonneg (by isBoundedDefault) hscaled_v_bddAbove)
    exact ne_of_gt (lt_of_lt_of_le (by simp) hnonneg)
  have h_add_le :
      Filter.limsup (fun n ↦ (α : EReal) * u n + (1 - α : EReal) * v n) atTop ≤
        Filter.limsup (fun n ↦ (α : EReal) * u n) atTop +
          Filter.limsup (fun n ↦ (1 - α : EReal) * v n) atTop := by
    -- Route correction: keep the source `Example 8.19` architecture and separate the add and
    -- scalar limsup transports, but use the specialized `EReal` add lemma to avoid the generic
    -- `whnf` blow-up seen in the previous route.
    exact EReal.limsup_add_le (u := fun n ↦ (α : EReal) * u n) (v := fun n ↦ (1 - α : EReal) * v n)
      (f := atTop) (Or.inl hscaled_u_ne_bot) (Or.inr hscaled_v_ne_bot)
  have h_mul_u :
      Filter.limsup (fun n ↦ (α : EReal) * u n) atTop =
        (α : EReal) * Filter.limsup u atTop := by
    simpa using
      (EReal.limsup_const_mul_of_nonneg_of_ne_top
        (f := atTop) (u := u) (c := (α : EReal)) (by exact_mod_cast hα0)
        (by exact EReal.coe_ne_top α))
  have h_mul_v :
      Filter.limsup (fun n ↦ (1 - α : EReal) * v n) atTop =
        (1 - α : EReal) * Filter.limsup v atTop := by
    simpa using
      (EReal.limsup_const_mul_of_nonneg_of_ne_top
        (f := atTop) (u := v) (c := (1 - α : EReal))
        (by exact_mod_cast sub_nonneg.mpr hα1) (by exact EReal.coe_ne_top (1 - α)))
  have h_final :
      Filter.limsup (fun n ↦ (α : EReal) * u n + (1 - α : EReal) * v n) atTop ≤
        (α : EReal) * Filter.limsup u atTop + (1 - α : EReal) * Filter.limsup v atTop := by
    exact h_add_le.trans (by simp [h_mul_u, h_mul_v])
  -- The weighted real sequence is exactly the sum of the two scaled squared-distance sequences.
  simpa [u, v, EReal.coe_add, EReal.coe_mul] using h_final

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 11 18: the constant correction term in the source squared-distance
identity passes through `Filter.limsup` for bounded squared-distance sequences. -/
private theorem limsup_const_add_sqdist_eq
    {zₙ : ℕ → H} (x : H) (c : ℝ) :
    Filter.limsup
        (fun n ↦ (((c : ℝ) : EReal) + ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)))
        atTop =
      ((c : ℝ) : EReal) + asymptoticCenterObjective zₙ x := by
  let u : ℕ → EReal := fun n ↦ ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)
  let cE : EReal := ((c : ℝ) : EReal)
  have hc_ne_bot : Filter.limsup (fun _ : ℕ ↦ cE) atTop ≠ ⊥ := by
    simp [cE]
  have hc_ne_top : Filter.limsup (fun _ : ℕ ↦ cE) atTop ≠ ⊤ := by
    simp [cE]
  have hle :
      Filter.limsup (fun n ↦ cE + u n) atTop ≤ cE + Filter.limsup u atTop := by
    -- The finite constant is neither `⊥` nor `⊤`, so the `EReal` limsup add inequality applies.
    simpa [u, cE] using
      (EReal.limsup_add_le (f := atTop) (u := fun _ : ℕ ↦ cE) (v := u)
        (Or.inl hc_ne_bot) (Or.inl hc_ne_top))
  have hge :
      cE + Filter.limsup u atTop ≤ Filter.limsup (fun n ↦ cE + u n) atTop := by
    -- Reversing the roles and using `liminf` of the constant sequence gives the opposite
    -- inequality, which is the source textbook constant-shift identity.
    simpa [u, cE, add_comm, add_left_comm, add_assoc] using
      (EReal.le_limsup_add (f := atTop) (u := u) (v := fun _ : ℕ ↦ cE))
  exact le_antisymm hle hge

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 11 18: a reverse-triangle estimate gives the source quadratic lower
bound on each squared-distance term once `‖x‖` dominates the uniform radius `R`. -/
private theorem sqdist_quadratic_lower_bound_of_norm_large
    {zₙ : ℕ → H} {R : ℝ} (hR_nonneg : 0 ≤ R) (hR : ∀ n : ℕ, ‖zₙ n‖ ≤ R) {x : H}
    (hx_large : 2 * R ≤ ‖x‖) :
    ∀ n : ℕ, ‖x‖ * (‖x‖ - 2 * R) ≤ ‖x - zₙ n‖ ^ (2 : ℕ) := by
  intro n
  have hz : ‖zₙ n‖ ≤ R := hR n
  have hnorm_sub : ‖x‖ ≤ ‖x - zₙ n‖ + R := by
    -- Rewrite `x` as `(x - zₙ n) + zₙ n` and apply the triangle inequality.
    calc
      ‖x‖ = ‖(x - zₙ n) + zₙ n‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - zₙ n‖ + ‖zₙ n‖ := norm_add_le _ _
      _ ≤ ‖x - zₙ n‖ + R := by linarith
  have hshift_nonneg : 0 ≤ ‖x‖ - R := by
    linarith
  have hshift_sq :
      (‖x‖ - R) ^ 2 ≤ ‖x - zₙ n‖ ^ 2 := by
    -- Squaring preserves the lower bound because both sides are nonnegative.
    nlinarith [hnorm_sub, hshift_nonneg, norm_nonneg (x - zₙ n)]
  -- Drop the extra nonnegative `R^2` term from `(‖x‖ - R)^2`.
  calc
    ‖x‖ * (‖x‖ - 2 * R) ≤ (‖x‖ - R) ^ 2 := by
      nlinarith [sq_nonneg R]
    _ ≤ ‖x - zₙ n‖ ^ (2 : ℕ) := by
      simpa [pow_two] using hshift_sq

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 11 18: once `‖x‖` is large compared with a uniform radius for `zₙ`,
the normalized asymptotic-center objective is bounded below by the affine function
`‖x‖ - 2R`. -/
private theorem asymptoticCenterObjective_div_norm_lower_bound
    {zₙ : ℕ → H} {R : ℝ} (hR : ∀ n : ℕ, ‖zₙ n‖ ≤ R) {x : H}
    (hx_norm : (1 : ℝ) ≤ ‖x‖) (hx_large : 2 * R ≤ ‖x‖) :
    (((‖x‖ - 2 * R : ℝ) : EReal) ≤ (asymptoticCenterObjective zₙ x : EReal) / ‖x‖) := by
  have hR_nonneg : 0 ≤ R := by
    exact le_trans (norm_nonneg _) (hR 0)
  have hsq_bdd :
      Filter.IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ)
        (fun n ↦ ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
    refine Filter.isBoundedUnder_of_eventually_le (a := (((‖x‖ + R) ^ (2 : ℕ) : ℝ) : EReal)) ?_
    refine Filter.Eventually.of_forall fun n ↦ ?_
    have hz : ‖zₙ n‖ ≤ R := hR n
    have hnorm : ‖x - zₙ n‖ ≤ ‖x‖ + R := by
      -- The same uniform radius bound controls the squared-distance sequence from above.
      calc
        ‖x - zₙ n‖ ≤ ‖x‖ + ‖zₙ n‖ := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_sub_le x (zₙ n)
        _ ≤ ‖x‖ + R := by
          linarith
    exact_mod_cast
      (show ‖x - zₙ n‖ ^ (2 : ℕ) ≤ (‖x‖ + R) ^ (2 : ℕ) by
        have hsum_nonneg : 0 ≤ ‖x‖ + R := add_nonneg (norm_nonneg _) hR_nonneg
        nlinarith [hnorm, norm_nonneg (x - zₙ n), hsum_nonneg])
  have hquad :
      (((‖x‖ * (‖x‖ - 2 * R) : ℝ) : EReal)) ≤ asymptoticCenterObjective zₙ x := by
    -- Pass the pointwise quadratic lower bound through `Filter.limsup`.
    change (((‖x‖ * (‖x‖ - 2 * R) : ℝ) : EReal)) ≤
      Filter.limsup (fun n ↦ ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) atTop
    refine Filter.le_limsup_of_le hsq_bdd ?_
    intro b hb
    rcases Filter.eventually_atTop.1 hb with ⟨N, hN⟩
    have hN_quad :
        (((‖x‖ * (‖x‖ - 2 * R) : ℝ) : EReal)) ≤
          ((‖x - zₙ N‖ ^ (2 : ℕ) : ℝ) : EReal) := by
      exact_mod_cast
        sqdist_quadratic_lower_bound_of_norm_large hR_nonneg hR hx_large N
    exact le_trans hN_quad (hN N le_rfl)
  have hnorm_pos : (0 : EReal) < ‖x‖ := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hx_norm
  have hmul_le :
      ((((‖x‖ - 2 * R : ℝ) : EReal) * ‖x‖)) ≤ asymptoticCenterObjective zₙ x := by
    -- Repackage the quadratic lower bound in the form expected by `EReal.le_div_iff_mul_le`.
    calc
      (((‖x‖ - 2 * R : ℝ) : EReal) * ‖x‖) =
          (((((‖x‖ - 2 * R) * ‖x‖ : ℝ)) : EReal)) := by
            rw [← EReal.coe_mul]
      _ = (((‖x‖ * (‖x‖ - 2 * R) : ℝ) : EReal)) := by
            congr 1
            ring
      _ ≤ asymptoticCenterObjective zₙ x := hquad
  -- Divide by the positive norm to reach the normalized lower bound.
  exact (EReal.le_div_iff_mul_le hnorm_pos (by simp)).2 hmul_le

/-- Helper for Proposition 11 18: the bounded `EReal` owner satisfies the real Jensen inequality
with the quadratic correction term kept on the left-hand side. -/
private theorem asymptoticCenterObjective_toReal_jensen_bound
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) (x y : H)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (asymptoticCenterObjective zₙ (α • x + (1 - α) • y) : EReal).toReal +
        α * (1 - α) * ‖x - y‖ ^ (2 : ℕ) ≤
      α * (asymptoticCenterObjective zₙ x : EReal).toReal +
        (1 - α) * (asymptoticCenterObjective zₙ y : EReal).toReal := by
  let w : H := α • x + (1 - α) • y
  let δ : ℝ := α * (1 - α) * ‖x - y‖ ^ (2 : ℕ)
  have h_fun :
      (fun n ↦ (((δ : ℝ) : EReal) + ((‖w - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))) =
        fun n ↦
          (((α * ‖x - zₙ n‖ ^ (2 : ℕ) + (1 - α) * ‖y - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
    -- Rewrite the pointwise Hilbert identity into the exact sequence equality used by `limsup`.
    funext n
    have hsq :
        δ + ‖w - zₙ n‖ ^ (2 : ℕ) =
          α * ‖x - zₙ n‖ ^ (2 : ℕ) + (1 - α) * ‖y - zₙ n‖ ^ (2 : ℕ) := by
      simpa [w, δ, add_comm, add_left_comm, add_assoc] using
        sqNorm_sub_affine_combination_add_weighted_norm_sub_sq x y (zₙ n) α
    rw [← EReal.coe_add]
    exact_mod_cast hsq
  have h_ereal :
      ((δ : ℝ) : EReal) + asymptoticCenterObjective zₙ w ≤
        (α : EReal) * asymptoticCenterObjective zₙ x +
          (1 - α : EReal) * asymptoticCenterObjective zₙ y := by
    -- Pass the left constant shift through `limsup`, then apply the weighted Jensen `limsup`
    -- inequality that was already isolated above.
    calc
      ((δ : ℝ) : EReal) + asymptoticCenterObjective zₙ w =
          Filter.limsup
            (fun n ↦ (((δ : ℝ) : EReal) + ((‖w - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)))
            atTop := by
              symm
              simpa [w, δ] using limsup_const_add_sqdist_eq w δ
      _ = Filter.limsup
            (fun n ↦
              (((α * ‖x - zₙ n‖ ^ (2 : ℕ) + (1 - α) * ‖y - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)))
            atTop := by rw [h_fun]
      _ ≤
          (α : EReal) * Filter.limsup (fun n ↦ ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) atTop +
            (1 - α : EReal) *
              Filter.limsup (fun n ↦ ((‖y - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) atTop := by
                exact limsup_weighted_sqdist_jensen_le hzₙ_bdd x y hα0 hα1
      _ =
          (α : EReal) * asymptoticCenterObjective zₙ x +
            (1 - α : EReal) * asymptoticCenterObjective zₙ y := by
              simp [asymptoticCenterObjective]
  have hw_top : (asymptoticCenterObjective zₙ w : EReal) ≠ ⊤ :=
    ne_of_lt (asymptoticCenterObjective_lt_top hzₙ_bdd w)
  have hx_top : (asymptoticCenterObjective zₙ x : EReal) ≠ ⊤ :=
    ne_of_lt (asymptoticCenterObjective_lt_top hzₙ_bdd x)
  have hy_top : (asymptoticCenterObjective zₙ y : EReal) ≠ ⊤ :=
    ne_of_lt (asymptoticCenterObjective_lt_top hzₙ_bdd y)
  have hw_bot : (asymptoticCenterObjective zₙ w : EReal) ≠ ⊥ := by
    exact ne_of_gt (asymptoticCenterObjective zₙ w).2
  have hx_bot : (asymptoticCenterObjective zₙ x : EReal) ≠ ⊥ := by
    exact ne_of_gt (asymptoticCenterObjective zₙ x).2
  have hy_bot : (asymptoticCenterObjective zₙ y : EReal) ≠ ⊥ := by
    exact ne_of_gt (asymptoticCenterObjective zₙ y).2
  have hsub_cast : (1 - (α : EReal)) = (((1 - α : ℝ) : EReal)) := by
    exact_mod_cast (show (1 - α : ℝ) = 1 - α by ring)
  have h_ereal_coe :
      (((asymptoticCenterObjective zₙ w : EReal).toReal + δ : ℝ) : EReal) ≤
        (((α * (asymptoticCenterObjective zₙ x : EReal).toReal +
            (1 - α) * (asymptoticCenterObjective zₙ y : EReal).toReal : ℝ) : EReal)) := by
    -- Convert the finite objective values to `EReal` only at the end of the argument.
    calc
      (((asymptoticCenterObjective zₙ w : EReal).toReal + δ : ℝ) : EReal) =
          ((δ : ℝ) : EReal) + asymptoticCenterObjective zₙ w := by
            rw [EReal.coe_add, EReal.coe_toReal hw_top hw_bot, add_comm]
      _ ≤
          (α : EReal) * asymptoticCenterObjective zₙ x +
            (1 - α : EReal) * asymptoticCenterObjective zₙ y := h_ereal
      _ =
          (((α * (asymptoticCenterObjective zₙ x : EReal).toReal +
              (1 - α) * (asymptoticCenterObjective zₙ y : EReal).toReal : ℝ) : EReal)) := by
            rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul,
              EReal.coe_toReal hx_top hx_bot, EReal.coe_toReal hy_top hy_bot]
            rw [hsub_cast]
  exact_mod_cast h_ereal_coe

-- Proof sketch: boundedness makes the canonical `EReal` owner finite everywhere, so its `toReal`
-- bridge satisfies the pointwise identity
-- `‖α x + (1 - α) y - zₙ‖² = α ‖x - zₙ‖² + (1 - α) ‖y - zₙ‖² - α (1 - α) ‖x - y‖²`;
-- passing to `Filter.limsup` yields the real-valued source clause.
/-- Proposition 11 18 (1): clause (i). For a bounded sequence, the real-valued bridge of the
asymptotic-center objective is strongly convex on the whole Hilbert space with constant `2`. -/
theorem asymptoticCenterObjective_strongConvexOn_univ
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) :
    StrongConvexOn (Set.univ : Set H) (2 : ℝ)
      (fun x ↦ (asymptoticCenterObjective zₙ x : EReal).toReal) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hb_eq : b = 1 - a := by linarith
  subst b
  have ha_le_one : a ≤ 1 := by linarith
  have hjensen :=
    asymptoticCenterObjective_toReal_jensen_bound hzₙ_bdd x y ha ha_le_one
  -- Repackage the Jensen-gap inequality into mathlib's `StrongConvexOn` format.
  have hineq :
      (asymptoticCenterObjective zₙ (a • x + (1 - a) • y) : EReal).toReal ≤
        a * (asymptoticCenterObjective zₙ x : EReal).toReal +
          (1 - a) * (asymptoticCenterObjective zₙ y : EReal).toReal -
            a * (1 - a) * ((2 : ℝ) / 2 * ‖x - y‖ ^ (2 : ℕ)) := by
    linarith
  simpa [smul_eq_mul] using hineq

-- Proof sketch: boundedness identifies the effective domain of the canonical `EReal` owner with
-- the whole space, and the same Jensen-gap computation yields the chapter-10 strong-convexity
-- owner directly.
/-- For a bounded sequence, the canonical `EReal` asymptotic-center objective is strongly convex
with constant `2`. -/
theorem asymptoticCenterObjective_stronglyConvex
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) :
    ERealFunction.StronglyConvex (asymptoticCenterObjective zₙ) (2 : ℝ) := by
  have hdom_eq : effectiveDomain (asymptoticCenterObjective zₙ) = Set.univ := by
    ext x
    rw [mem_effectiveDomain_iff]
    constructor
    · intro _
      simp
    · intro _
      exact asymptoticCenterObjective_lt_top hzₙ_bdd x
  have hdom_nonempty : (effectiveDomain (asymptoticCenterObjective zₙ)).Nonempty := by
    refine ⟨0, ?_⟩
    -- Boundedness makes the owner finite at every point, so the effective domain is nonempty.
    simp [hdom_eq]
  -- Route correction: first establish strong convexity of the finite real bridge on `Set.univ`,
  -- then transfer it back to the canonical `]-∞,+∞]`-valued owner.
  exact StrongConvexOn.toStronglyConvex_effectiveDomain
    (by
      simpa [hdom_eq] using asymptoticCenterObjective_strongConvexOn_univ (zₙ := zₙ) hzₙ_bdd)
    (by norm_num) hdom_nonempty

/-- Helper for Proposition 11 18: coercing an everywhere-finite convex real-valued function
through `toEReal` preserves convexity on its full effective domain. -/
private theorem convexOn_toEReal_of_convexOn_univ
    (f : H → ℝ) (hconv : _root_.ConvexOn ℝ Set.univ f) :
    ConvexOn f.toEReal (effectiveDomain f.toEReal) := by
  refine ⟨?_, ?_, ?_⟩
  · -- A real-valued function stays finite everywhere after the canonical `toEReal` coercion.
    simp [Function.effectiveDomain_toEReal]
  · -- Effective-domain membership is therefore automatic.
    simp [Function.effectiveDomain_toEReal]
  · intro x hx y hy a ha0 ha1
    -- Rewrite the `EReal` Jensen step back to the original real-valued convexity inequality.
    have hreal :
        f (a • x + (1 - a) • y) ≤ a * f x + (1 - a) * f y := by
      simpa [smul_eq_mul] using
        hconv.2 (by simp : x ∈ Set.univ) (by simp : y ∈ Set.univ) ha0.le
          (sub_nonneg.mpr ha1.le) (by linarith)
    have hcast :
        ((f (a • x + (1 - a) • y) : ℝ) : EReal) ≤
          ((a * f x + (1 - a) * f y : ℝ) : EReal) := by
      exact_mod_cast hreal
    simpa [Function.toEReal_apply, EReal.coe_mul, EReal.coe_add] using hcast

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 11 18: for bounded sequences, coercing the finite real bridge back to
`EReal` recovers the original asymptotic-center objective pointwise. -/
private theorem asymptoticCenterObjective_eq_realBridge_toEReal
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) (x : H) :
    ((((asymptoticCenterObjective zₙ x : EReal).toReal : ℝ) : EReal)) =
      (asymptoticCenterObjective zₙ x : EReal) := by
  have hx_top : (asymptoticCenterObjective zₙ x : EReal) ≠ ⊤ :=
    (asymptoticCenterObjective_lt_top hzₙ_bdd x).ne
  have hx_bot : (asymptoticCenterObjective zₙ x : EReal) ≠ ⊥ :=
    ne_of_gt (asymptoticCenterObjective zₙ x).2
  -- Boundedness rules out `⊤`, and the subtype codomain rules out `⊥`, so `coe_toReal` applies.
  simpa using (EReal.coe_toReal hx_top hx_bot)

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 11 18: boundedness gives the exact finite-sup-ball witness required
by Corollary 8.39 for the bundled real bridge of the asymptotic-center objective. -/
private theorem asymptoticCenterObjective_realBridge_finiteSupBall
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) :
    ∃ x₀ : H, ∃ ρ : ℝ, 0 < ρ ∧
      sSup
          ((fun y : H ↦
              ((((asymptoticCenterObjective zₙ y : EReal).toReal : ℝ) : EReal))) ''
            Metric.ball x₀ ρ) < ⊤ := by
  obtain ⟨R, hR_range⟩ := isBounded_iff_forall_norm_le.mp hzₙ_bdd
  have hR : ∀ n : ℕ, ‖zₙ n‖ ≤ R := by
    intro n
    simpa using hR_range (zₙ n) (Set.mem_range_self n)
  have hR_nonneg : 0 ≤ R := by
    exact le_trans (norm_nonneg _) (hR 0)
  refine ⟨0, 1, by norm_num, ?_⟩
  have hsSup_le :
      sSup
          ((fun y : H ↦
              ((((asymptoticCenterObjective zₙ y : EReal).toReal : ℝ) : EReal))) ''
            Metric.ball (0 : H) 1) ≤
        (((1 + R) ^ (2 : ℕ) : ℝ) : EReal) := by
    refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy_norm_lt : ‖y‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hy
    have hy_norm_le : ‖y‖ ≤ 1 := hy_norm_lt.le
    have hobj_le :
        (asymptoticCenterObjective zₙ y : EReal) ≤ (((1 + R) ^ (2 : ℕ) : ℝ) : EReal) := by
      change
        Filter.limsup (fun n ↦ ((‖y - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) atTop ≤
          (((1 + R) ^ (2 : ℕ) : ℝ) : EReal)
      refine Filter.limsup_le_of_le (hf := by isBoundedDefault) ?_
      refine Filter.Eventually.of_forall fun n ↦ ?_
      have hz : ‖zₙ n‖ ≤ R := hR n
      have hnorm : ‖y - zₙ n‖ ≤ 1 + R := by
        calc
          ‖y - zₙ n‖ ≤ ‖y‖ + ‖zₙ n‖ := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_sub_le y (zₙ n)
          _ ≤ 1 + R := by
            linarith
      exact_mod_cast
        (show ‖y - zₙ n‖ ^ (2 : ℕ) ≤ (1 + R) ^ (2 : ℕ) by
          have hsum_nonneg : 0 ≤ 1 + R := by linarith
          nlinarith [hnorm, norm_nonneg (y - zₙ n), hsum_nonneg])
    calc
      ((((asymptoticCenterObjective zₙ y : EReal).toReal : ℝ) : EReal)) =
          (asymptoticCenterObjective zₙ y : EReal) := by
            exact asymptoticCenterObjective_eq_realBridge_toEReal hzₙ_bdd y
      _ ≤ (((1 + R) ^ (2 : ℕ) : ℝ) : EReal) := hobj_le
  exact lt_of_le_of_lt hsSup_le (EReal.coe_lt_top _)

/-- Helper for Proposition 11 18: boundedness makes the finite real bridge of the asymptotic-
center objective continuous on the whole Hilbert space. -/
private theorem continuous_asymptoticCenterObjective_realBridge
    [CompleteSpace H] {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) :
    Continuous (fun x : H ↦ (asymptoticCenterObjective zₙ x : EReal).toReal) := by
  let g : H → Set.Ioi (⊥ : EReal) :=
    (fun x : H ↦ (asymptoticCenterObjective zₙ x : EReal).toReal).toEReal
  have hstrong :
      StrongConvexOn (Set.univ : Set H) (2 : ℝ)
        (fun x : H ↦ (asymptoticCenterObjective zₙ x : EReal).toReal) :=
    asymptoticCenterObjective_strongConvexOn_univ (zₙ := zₙ) hzₙ_bdd
  have hconv_real :
      _root_.ConvexOn ℝ Set.univ
        (fun x : H ↦ (asymptoticCenterObjective zₙ x : EReal).toReal) := by
    -- Forget the positive quadratic term to retain ordinary convexity of the real bridge.
    simpa using (hstrong.mono (show (0 : ℝ) ≤ 2 by norm_num))
  have hconv : ConvexOn g (effectiveDomain g) := by
    -- Bundle the real bridge into the `]-∞,+∞]`-valued form required by Corollary 8.39.
    exact convexOn_toEReal_of_convexOn_univ _ hconv_real
  rw [continuous_iff_continuousAt]
  intro x
  have hx : x ∈ interior (effectiveDomain g) := by
    simp [g, Function.effectiveDomain_toEReal]
  obtain ⟨x₀, ρ₀, hρ₀, hsup₀⟩ :=
    asymptoticCenterObjective_realBridge_finiteSupBall hzₙ_bdd
  rcases
      convex_locallyLipschitzNear_on_interior_of_finiteSupBall (x₀ := x₀) g hconv
        ⟨ρ₀, hρ₀, hsup₀⟩ x hx with
    ⟨β, ρ, hρ, hball, hLip⟩
  have hcont :
      ContinuousAt (fun z : H ↦ (g z : EReal).toReal) x := by
    exact hLip.continuousOn.continuousAt (Metric.ball_mem_nhds x hρ)
  simpa [g, Function.toEReal_apply] using hcont

/-- Helper for Proposition 11 18: boundedness makes the canonical asymptotic-center objective
lower semicontinuous because its everywhere-finite real bridge is continuous on `Set.univ`. -/
private theorem asymptoticCenterObjective_lowerSemicontinuous
    [CompleteSpace H] {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) :
    LowerSemicontinuous (fun x : H ↦ (asymptoticCenterObjective zₙ x : EReal)) := by
  have hcont_real :
      Continuous (fun x : H ↦ (asymptoticCenterObjective zₙ x : EReal).toReal) :=
    continuous_asymptoticCenterObjective_realBridge hzₙ_bdd
  have hEq :
      (fun x : H ↦ ((((asymptoticCenterObjective zₙ x : EReal).toReal : ℝ) : EReal))) =
        fun x : H ↦ (asymptoticCenterObjective zₙ x : EReal) := by
    funext x
    exact asymptoticCenterObjective_eq_realBridge_toEReal hzₙ_bdd x
  -- Route correction: use continuity of the everywhere-finite real bridge on `Set.univ`, then
  -- rewrite the coerced bridge back to the original `EReal`-valued owner pointwise.
  rw [← hEq]
  exact (continuous_coe_real_ereal.comp hcont_real).lowerSemicontinuous

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 11 18: outside the constraint set, the indicator forces the sum to
`⊤`, so every lower level set of `f + ι[C]` is exactly the feasible lower level set of `f`. -/
private theorem lowerLevelSet_add_indicator_eq_inter
    {f : H → EReal} {C : Set H} (hbot : ∀ x ∉ C, f x ≠ ⊥) {η : ℝ} :
    lowerLevelSet (f + (ι[C]).asEReal) η = C ∩ lowerLevelSet f η := by
  -- The indicator contributes `0` on `C` and `⊤` off `C`, so only feasible points remain.
  ext x
  constructor
  · intro hx
    by_cases hxC : x ∈ C
    · refine ⟨hxC, ?_⟩
      simpa [mem_lowerLevelSet_iff, add_indicator_apply, indicator_apply, hxC] using hx
    · have hxle : (f + (ι[C]).asEReal) x ≤ (η : EReal) :=
        (mem_lowerLevelSet_iff (f + (ι[C]).asEReal) η x).1 hx
      have htop : (f + (ι[C]).asEReal) x = ⊤ := by
        simp [indicator_apply, hxC, EReal.add_top_of_ne_bot (hbot x hxC)]
      have : ¬ ((⊤ : EReal) ≤ (η : EReal)) := by
        simp
      rw [htop] at hxle
      exact False.elim <| this hxle
  · rintro ⟨hxC, hxlevel⟩
    refine (mem_lowerLevelSet_iff (f + (ι[C]).asEReal) η x).2 ?_
    simpa [mem_lowerLevelSet_iff, add_indicator_apply, indicator_apply, hxC] using
      (mem_lowerLevelSet_iff f η x).1 hxlevel

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 11 18: adding the indicator of a closed set preserves lower
semicontinuity. -/
private theorem lowerSemicontinuous_add_indicator_of_isClosed
    {f : H → EReal} {C : Set H} (hf : LowerSemicontinuous f) (hC_closed : IsClosed C)
    (hbot : ∀ x ∉ C, f x ≠ ⊥) :
    LowerSemicontinuous (f + (ι[C]).asEReal) := by
  -- Rewrite lower level sets as an intersection of the closed constraint set with the lower level
  -- set of `f`.
  rw [lowerSemicontinuous_iff_isClosed_lowerLevelSet]
  intro η
  rw [_root_.lowerLevelSet_add_indicator_eq_inter hbot]
  exact hC_closed.inter ((lowerSemicontinuous_iff_isClosed_lowerLevelSet f).1 hf η)

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 11 18: boundedness makes the asymptotic-center objective finite
everywhere, so after adding the indicator of `C` the effective domain is exactly `C`. -/
private theorem effectiveDomain_asymptoticCenterObjective_add_indicator_eq
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {C : Set H} :
    effectiveDomain (asymptoticCenterObjective zₙ + ι[C]) = C := by
  -- The base objective is finite at every point, so only the indicator determines feasibility.
  ext x
  rw [mem_effectiveDomain_pointwiseAdd_iff, effectiveDomain_indicator]
  constructor
  · intro hx
    exact hx.2
  · intro hxC
    exact ⟨mem_effectiveDomain_iff.mpr (asymptoticCenterObjective_lt_top hzₙ_bdd x), hxC⟩

omit [InnerProductSpace ℝ H] in
-- Proof sketch: boundedness of `zₙ` gives a quadratic lower bound on
-- `x ↦ limsup ‖x - zₙ‖²` as `‖x‖ → ∞`; dividing by `‖x‖` and sending `‖x‖` to infinity yields the
-- supercoercive growth condition.
/-- Proposition 11.18 (2): clause (ii). For a bounded sequence, the canonical `EReal`
asymptotic-center objective is supercoercive. -/
theorem asymptoticCenterObjective_supercoercive
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) :
    ERealFunction.Supercoercive (asymptoticCenterObjective zₙ).asEReal := by
  obtain ⟨R, hR_range⟩ := isBounded_iff_forall_norm_le.mp hzₙ_bdd
  have hR : ∀ n : ℕ, ‖zₙ n‖ ≤ R := by
    intro n
    simpa using hR_range (zₙ n) (Set.mem_range_self n)
  rw [ERealFunction.Supercoercive, EReal.tendsto_nhds_top_iff_real]
  intro ξ
  have htail :
      ∀ᶠ x in Bornology.cobounded H,
        max (1 : ℝ) (max (2 * R) (ξ + 2 * R + 1)) ≤ ‖x‖ := by
    simpa using
      (eventually_cobounded_le_norm (max (1 : ℝ) (max (2 * R) (ξ + 2 * R + 1))) :
        ∀ᶠ x in Bornology.cobounded H,
          max (1 : ℝ) (max (2 * R) (ξ + 2 * R + 1)) ≤ ‖x‖)
  filter_upwards [htail] with x hx
  have hx_norm : (1 : ℝ) ≤ ‖x‖ := by
    exact le_trans (le_max_left _ _) hx
  have hx_tail : max (2 * R) (ξ + 2 * R + 1) ≤ ‖x‖ := by
    exact le_trans (le_max_right _ _) hx
  have hx_large : 2 * R ≤ ‖x‖ := by
    exact le_trans (le_max_left _ _) hx_tail
  have hξ_real : ξ < ‖x‖ - 2 * R := by
    have hξ_tail : ξ + 2 * R + 1 ≤ ‖x‖ := by
      exact le_trans (le_max_right _ _) hx_tail
    linarith
  have hlower :=
    asymptoticCenterObjective_div_norm_lower_bound (zₙ := zₙ) hR hx_norm hx_large
  have hξ_cast : ((ξ : ℝ) : EReal) < ((‖x‖ - 2 * R : ℝ) : EReal) := by
    exact_mod_cast hξ_real
  -- The tail lower bound `‖x‖ - 2R` eventually dominates any prescribed real threshold `ξ`.
  exact lt_of_lt_of_le hξ_cast hlower

-- Proof sketch: combine the strong convexity and supercoercivity of the asymptotic-center
-- objective with convexity of the indicator `ι[C]` to obtain the corresponding bridge facts for
-- the indicator-augmented objective `f + ι_C`.
/-- Proposition 11.18 (3): clause (iii). For a nonempty convex set `C`, the indicator-augmented
asymptotic-center objective `f + ι[C]` is strongly convex with constant `2`. -/
theorem asymptoticCenterObjective_addIndicator_stronglyConvex
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {C : Set H}
    (hC_nonempty : C.Nonempty) (hC_convex : Convex ℝ C) :
    ERealFunction.StronglyConvex (asymptoticCenterObjective zₙ + ι[C]) (2 : ℝ) := by
  have hdom_eq :
      effectiveDomain (asymptoticCenterObjective zₙ + ι[C]) = C :=
    effectiveDomain_asymptoticCenterObjective_add_indicator_eq hzₙ_bdd
  have hstrong_on_C :
      StrongConvexOn C (2 : ℝ)
        (fun x ↦ ((asymptoticCenterObjective zₙ + ι[C]) x : EReal).toReal) := by
    refine ⟨hC_convex, ?_⟩
    intro x hx y hy a b ha hb hab
    have hxy : a • x + b • y ∈ C := hC_convex hx hy ha hb hab
    have hbase :
        (asymptoticCenterObjective zₙ (a • x + b • y) : EReal).toReal ≤
          a • (asymptoticCenterObjective zₙ x : EReal).toReal +
            b • (asymptoticCenterObjective zₙ y : EReal).toReal -
              a * b * ((2 : ℝ) / 2 * ‖x - y‖ ^ (2 : ℕ)) := by
      exact
        (asymptoticCenterObjective_strongConvexOn_univ (zₙ := zₙ) hzₙ_bdd).2
          (x := x) (by simp) (y := y) (by simp) ha hb hab
    -- On feasible points, the indicator vanishes, so the constrained real bridge matches the base
    -- bridge and inherits the same strong-convexity inequality.
    simpa [add_indicator_apply, indicator_apply, hx, hy, hxy] using hbase
  have hdom_nonempty : (effectiveDomain (asymptoticCenterObjective zₙ + ι[C])).Nonempty := by
    rcases hC_nonempty with ⟨x, hx⟩
    exact ⟨x, by simpa [hdom_eq] using hx⟩
  -- Route correction: rather than manipulating the `EReal` Jensen gap of the sum directly, first
  -- transfer the feasible-point real bridge on `C`, then package it back through the effective
  -- domain equality.
  exact StrongConvexOn.toStronglyConvex_effectiveDomain
    (f := asymptoticCenterObjective zₙ + ι[C])
    (by simpa [hdom_eq] using hstrong_on_C)
    (by norm_num)
    hdom_nonempty

omit [InnerProductSpace ℝ H] in
-- Proof sketch: adding the indicator `ι[C]` only increases the objective pointwise, so the
-- supercoercive growth from clause (ii) is preserved by the constrained objective.
/-- Proposition 11.18 (3): clause (iii). For any constraint set `C`, the indicator-augmented
asymptotic-center objective `f + ι[C]` remains supercoercive. -/
theorem asymptoticCenterObjective_addIndicator_supercoercive
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {C : Set H} :
    ERealFunction.Supercoercive ((asymptoticCenterObjective zₙ + ι[C]).asEReal) := by
  have hbase :
      ERealFunction.Supercoercive (asymptoticCenterObjective zₙ).asEReal :=
    asymptoticCenterObjective_supercoercive hzₙ_bdd
  rw [ERealFunction.Supercoercive, EReal.tendsto_nhds_top_iff_real] at hbase ⊢
  intro ξ
  have htail :
      ∀ᶠ x in Bornology.cobounded H,
        (ξ : EReal) < (asymptoticCenterObjective zₙ x : EReal) / ‖x‖ :=
    hbase ξ
  filter_upwards [htail] with x hx
  have hpointwise :
      (asymptoticCenterObjective zₙ x : EReal) ≤
        ((asymptoticCenterObjective zₙ + ι[C]).asEReal x) := by
    by_cases hxC : x ∈ C
    · -- On the constraint set, the indicator vanishes and the two objectives agree.
      simp [indicator_apply, hxC]
    · have hx_ne_bot : (asymptoticCenterObjective zₙ x : EReal) ≠ ⊥ :=
        ne_of_gt (asymptoticCenterObjective zₙ x).2
      -- Outside the constraint set, the indicator forces the sum to `⊤`.
      simp [indicator_apply, hxC, EReal.add_top_of_ne_bot hx_ne_bot]
  have hquot_le :
      (asymptoticCenterObjective zₙ x : EReal) / ‖x‖ ≤
        ((asymptoticCenterObjective zₙ + ι[C]).asEReal x) / ‖x‖ := by
    exact EReal.div_le_div_right_of_nonneg (by exact_mod_cast norm_nonneg x) hpointwise
  exact lt_of_lt_of_le hx hquot_le

section CompleteSpace

variable [CompleteSpace H]

-- Proof sketch: apply the existence theory for strongly convex supercoercive constrained
-- objectives to the indicator-augmented bridge `f + ι_C`.
private theorem existsUnique_mem_argmin_addIndicator_asymptoticCenterObjective
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {C : Set H}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ∃! z : H, z ∈ Argmin ((asymptoticCenterObjective zₙ + ι[C]).asEReal) := by
  have hobjective_lsc :
      LowerSemicontinuous (fun x : H ↦ (asymptoticCenterObjective zₙ x : EReal)) :=
    asymptoticCenterObjective_lowerSemicontinuous hzₙ_bdd
  have hnot_bot : ∀ x ∉ C, (asymptoticCenterObjective zₙ).asEReal x ≠ ⊥ :=
    fun x _ ↦ ne_of_gt (asymptoticCenterObjective zₙ x).2
  have hsum_lsc :
      LowerSemicontinuous ((asymptoticCenterObjective zₙ + ι[C]).asEReal) :=
    _root_.lowerSemicontinuous_add_indicator_of_isClosed hobjective_lsc hC_closed hnot_bot
  have hsum_conv :
      ConvexOn (asymptoticCenterObjective zₙ + ι[C])
        (effectiveDomain (asymptoticCenterObjective zₙ + ι[C])) := by
    -- Strong convexity of the constrained objective implies ordinary convexity on its domain.
    exact
      (asymptoticCenterObjective_addIndicator_stronglyConvex
        hzₙ_bdd hC_nonempty hC_convex).uniformlyConvex.convexOn
  have hsum_gamma : asymptoticCenterObjective zₙ + ι[C] ∈ Γ₀(H) := by
    -- Package the constrained objective into `Γ₀(H)` once lower semicontinuity and convexity are
    -- both available.
    rw [mem_gammaZero_iff]
    exact ⟨hsum_lsc, hsum_conv⟩
  have hsum_coe :
      Coercive ((asymptoticCenterObjective zₙ + ι[C]).asEReal) :=
    coercive_of_supercoercive
      (asymptoticCenterObjective_addIndicator_supercoercive (zₙ := zₙ) hzₙ_bdd)
  have hsum_strict : StrictlyConvex (asymptoticCenterObjective zₙ + ι[C]) :=
    (asymptoticCenterObjective_addIndicator_stronglyConvex
      hzₙ_bdd hC_nonempty hC_convex).uniformlyConvex.strictlyConvex
  -- The complete-space uniqueness theorem now applies to the constrained asymptotic-center
  -- objective.
  exact existsUnique_mem_argmin_of_mem_gammaZero_of_coercive_of_strictlyConvex
    hsum_gamma hsum_coe hsum_strict

/-- Proposition 11.18 (3): clause (iii). For a nonempty closed convex set `C`, the
asymptotic-center objective has a unique minimizer on `C`. -/
theorem existsUnique_mem_argminOn_asymptoticCenterObjective
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {C : Set H}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ∃! z : H, z ∈ Argmin[C] (asymptoticCenterObjective zₙ).asEReal := by
  have hnot_bot : ∀ x ∉ C, (asymptoticCenterObjective zₙ).asEReal x ≠ ⊥ :=
    fun x _ ↦ ne_of_gt (asymptoticCenterObjective zₙ x).2
  rcases
      existsUnique_mem_argmin_addIndicator_asymptoticCenterObjective
        hzₙ_bdd hC_nonempty hC_closed hC_convex with
    ⟨z, hz, huniq⟩
  refine ⟨z, ?_, ?_⟩
  · rw [argminOn_eq_inter_argmin_add_indicator (asymptoticCenterObjective zₙ).asEReal C hnot_bot]
    exact ⟨mem_constraint_of_mem_argmin_addIndicator_asymptoticCenterObjective
      hzₙ_bdd hC_nonempty hz, hz⟩
  · intro w hw
    rw [argminOn_eq_inter_argmin_add_indicator
      (asymptoticCenterObjective zₙ).asEReal C hnot_bot] at hw
    exact huniq w hw.2

/-- The canonical asymptotic center of `zₙ` relative to `C`. -/
noncomputable def asymptoticCenter
    (zₙ : ℕ → H) (C : Set H) (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ))
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) : H :=
  (existsUnique_mem_argminOn_asymptoticCenterObjective
    hzₙ_bdd hC_nonempty hC_closed hC_convex).choose

-- Proof sketch: unfold `asymptoticCenter` as the chosen witness of the unique constrained
-- minimizer theorem.
/-- The canonical asymptotic center belongs to the minimizer set of the asymptotic-center
objective over `C`. -/
theorem asymptoticCenter_mem_argminOn
    {zₙ : ℕ → H} {C : Set H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ))
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    asymptoticCenter zₙ C hzₙ_bdd hC_nonempty hC_closed hC_convex ∈
      Argmin[C] (asymptoticCenterObjective zₙ).asEReal := by
  exact
    (existsUnique_mem_argminOn_asymptoticCenterObjective
      hzₙ_bdd hC_nonempty hC_closed hC_convex).choose_spec.1

/-- Any constrained minimizer of the asymptotic-center objective is the canonical asymptotic
center. -/
theorem eq_asymptoticCenter_of_mem_argminOn
    {zₙ : ℕ → H} {C : Set H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ))
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) {z : H}
    (hz : z ∈ Argmin[C] (asymptoticCenterObjective zₙ).asEReal) :
    z = asymptoticCenter zₙ C hzₙ_bdd hC_nonempty hC_closed hC_convex := by
  exact ExistsUnique.unique
    (existsUnique_mem_argminOn_asymptoticCenterObjective
      hzₙ_bdd hC_nonempty hC_closed hC_convex)
    hz
    (asymptoticCenter_mem_argminOn hzₙ_bdd hC_nonempty hC_closed hC_convex)

omit [CompleteSpace H] in
/-- Helper for Proposition 11 18: expanding `‖x - y‖²` around a base point `z` isolates the
weakly vanishing cross term used in clause (iv). -/
private theorem sqNorm_sub_eq_sqNorm_sub_add_cross_add_sqNorm
    (x y z : H) :
    ‖x - y‖ ^ (2 : ℕ) =
      ‖x - z‖ ^ (2 : ℕ) + 2 * inner ℝ (x - z) (z - y) + ‖z - y‖ ^ (2 : ℕ) := by
  have hdecomp : x - y = (x - z) + (z - y) := by
    abel
  -- Expand `x - y` through the intermediate point `z` and apply the real polarization identity.
  calc
    ‖x - y‖ ^ (2 : ℕ) = ‖(x - z) + (z - y)‖ ^ (2 : ℕ) := by rw [hdecomp]
    _ = ‖x - z‖ ^ (2 : ℕ) + 2 * inner ℝ (x - z) (z - y) + ‖z - y‖ ^ (2 : ℕ) := by
          simpa using norm_add_sq_real (x - z) (z - y)

/-- Helper for Proposition 11 18: the weakly convergent cross term in the source square expansion
tends to `0`. -/
private theorem cross_term_tendsto_zero_of_tendsto_weakly
    {zₙ : ℕ → H} {x z : H}
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (zₙ n)) atTop (𝓝 (toWeakSpace ℝ H z))) :
    Tendsto (fun n ↦ (2 : ℝ) * inner ℝ (x - z) (z - zₙ n)) atTop (𝓝 0) := by
  have hsub :
      Tendsto (fun n ↦ toWeakSpace ℝ H (z - zₙ n)) atTop
        (𝓝 ((toWeakSpace ℝ H z) - (toWeakSpace ℝ H z))) := by
    -- Subtract the weak limit from the sequence to move the vanishing statement to the origin.
    have hzconst :
        Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ H z) atTop (𝓝 (toWeakSpace ℝ H z)) :=
      tendsto_const_nhds
    simpa [sub_eq_add_neg] using hzconst.sub hweak
  have hsub_zero :
      Tendsto (fun n ↦ toWeakSpace ℝ H (z - zₙ n)) atTop (𝓝 (toWeakSpace ℝ H (0 : H))) := by
    simpa using hsub
  have hinner :
      Tendsto (fun n ↦ inner ℝ (z - zₙ n) (x - z)) atTop (𝓝 (inner ℝ (0 : H) (x - z))) := by
    simpa using ((weakSpace_continuous_inner_right (H := H) (x - z)).tendsto
      (toWeakSpace ℝ H (0 : H))).comp hsub_zero
  -- Rewrite the inner product into the source order and multiply by the fixed scalar `2`.
  simpa [real_inner_comm] using hinner.const_mul (2 : ℝ)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 11 18: once the vanishing cross term is smaller than `1` in absolute
value, the perturbed squared-distance sequence is bounded below by `-1`. -/
private theorem eventually_neg_one_le_sqdist_cross
    {zₙ : ℕ → H} {z : H} {c : ℕ → ℝ}
    (hc : Tendsto c atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      (((-1 : ℝ) : EReal)) ≤
        (((c n : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
  have hc_lower : ∀ᶠ n in atTop, (-1 : ℝ) < c n := by
    exact hc (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 0))
  -- Once the perturbation is above `-1`, the nonnegative squared-distance term preserves the bound.
  filter_upwards [hc_lower] with n hn
  have hsq_nonneg : (0 : EReal) ≤ ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    exact_mod_cast (show 0 ≤ ‖z - zₙ n‖ ^ (2 : ℕ) by positivity)
  have hc_le : (((-1 : ℝ) : EReal)) ≤ ((c n : ℝ) : EReal) := by
    exact_mod_cast hn.le
  exact le_trans hc_le (le_add_of_nonneg_right hsq_nonneg)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 11 18: the perturbed squared-distance sequence stays bounded above once
the orbit is bounded and the cross term tends to `0`. -/
private theorem sqdist_cross_isBoundedUnder
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {z : H} {c : ℕ → ℝ}
    (hc : Tendsto c atTop (𝓝 0)) :
    Filter.IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ)
      (fun n ↦ (((c n : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))) := by
  have hc_upper : ∀ᶠ n in atTop, c n < 1 := by
    exact hc (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hsq_bdd : Filter.IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ)
      (fun n ↦ ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) := sqdist_sequence_isBoundedUnder hzₙ_bdd z
  rcases hsq_bdd.eventually_le with ⟨U, hU⟩
  refine Filter.isBoundedUnder_of_eventually_le (a := ((1 : ℝ) : EReal) + U) ?_
  filter_upwards [hc_upper, hU] with n hn hsq
  have hc_le : ((c n : ℝ) : EReal) ≤ ((1 : ℝ) : EReal) := by
    exact_mod_cast hn.le
  exact add_le_add hc_le hsq

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 11 18: the perturbed squared-distance sequence remains cobounded below,
which is the lower-side `limsup` input needed for the epsilon sandwich. -/
private theorem sqdist_cross_isCoboundedUnder
    {zₙ : ℕ → H} {z : H} {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0)) :
    Filter.IsCoboundedUnder (· ≤ ·) (atTop : Filter ℕ)
      (fun n ↦ (((c n : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))) := by
  exact Filter.IsCoboundedUnder.of_frequently_ge (a := (((-1 : ℝ) : EReal)))
    (eventually_neg_one_le_sqdist_cross (zₙ := zₙ) (z := z) hc).frequently

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 11 18: if the cross perturbation is eventually at most `ε`, then the
perturbed `limsup` is at most `ε` above the unperturbed asymptotic-center value. -/
private theorem limsup_sqdist_cross_le_eps
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {z : H} {c : ℕ → ℝ}
    (hc : Tendsto c atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    Filter.limsup
        (fun n ↦ (((c n : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))) atTop ≤
      ((ε : ℝ) : EReal) + asymptoticCenterObjective zₙ z := by
  have hc_upper : ∀ᶠ n in atTop, c n < ε := by
    exact hc (Iio_mem_nhds hε)
  have hcross_cobdd :
      Filter.IsCoboundedUnder (· ≤ ·) (atTop : Filter ℕ)
        (fun n ↦ (((c n : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))) :=
    sqdist_cross_isCoboundedUnder (zₙ := zₙ) (z := z) hc
  have hcmp_bdd :
      Filter.IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ)
        (fun n ↦ (((ε : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))) := by
    rcases (sqdist_sequence_isBoundedUnder (zₙ := zₙ) hzₙ_bdd z).eventually_le with ⟨U, hU⟩
    refine Filter.isBoundedUnder_of_eventually_le (a := ((ε : ℝ) : EReal) + U) ?_
    exact hU.mono fun n hn ↦ by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hn (((ε : ℝ) : EReal))
  have hcompare :
      ∀ᶠ n in atTop,
        (((c n : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) ≤
          (((ε : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
    filter_upwards [hc_upper] with n hn
    have hc_le : ((c n : ℝ) : EReal) ≤ ((ε : ℝ) : EReal) := by
      exact_mod_cast hn.le
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_right hc_le (((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))
  -- Compare the perturbed sequence to the constant-shifted squared-distance sequence.
  calc
    Filter.limsup
        (fun n ↦ (((c n : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))) atTop
      ≤ Filter.limsup
          (fun n ↦ (((ε : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))) atTop := by
            exact Filter.limsup_le_limsup hcompare hcross_cobdd hcmp_bdd
    _ = ((ε : ℝ) : EReal) + asymptoticCenterObjective zₙ z := by
          simpa using limsup_const_add_sqdist_eq z ε

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 11 18: if the cross perturbation is eventually bounded below by `-ε`,
then the unperturbed asymptotic-center value is at most `ε` above the perturbed `limsup`. -/
private theorem limsup_sqdist_le_eps_add_cross
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {z : H} {c : ℕ → ℝ}
    (hc : Tendsto c atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    asymptoticCenterObjective zₙ z ≤
      ((ε : ℝ) : EReal) +
        Filter.limsup
          (fun n ↦ (((c n : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))) atTop := by
  have hc_lower : ∀ᶠ n in atTop, -ε < c n := by
    exact hc (Ioi_mem_nhds (by linarith : (-ε : ℝ) < 0))
  have hcross_bdd :
      Filter.IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ)
        (fun n ↦ (((c n : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))) :=
    sqdist_cross_isBoundedUnder (zₙ := zₙ) hzₙ_bdd (z := z) hc
  have hcmp_cobdd :
      Filter.IsCoboundedUnder (· ≤ ·) (atTop : Filter ℕ)
        (fun n ↦ ((((-ε : ℝ) : EReal)) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))) := by
    refine Filter.IsCoboundedUnder.of_frequently_ge (a := (((-ε : ℝ) : EReal))) ?_
    exact Frequently.of_forall fun n ↦ by
      have hsq_nonneg : (0 : EReal) ≤ ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal) := by
        exact_mod_cast (show 0 ≤ ‖z - zₙ n‖ ^ (2 : ℕ) by positivity)
      simpa using le_add_of_nonneg_right hsq_nonneg
  have hcompare :
      ∀ᶠ n in atTop,
        ((((-ε : ℝ) : EReal)) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) ≤
          (((c n : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
    filter_upwards [hc_lower] with n hn
    have hc_le : (((-ε : ℝ) : EReal)) ≤ ((c n : ℝ) : EReal) := by
      exact_mod_cast hn.le
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_right hc_le (((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))
  have hshift :
      (((-ε : ℝ) : EReal) + asymptoticCenterObjective zₙ z) ≤
        Filter.limsup
          (fun n ↦ (((c n : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))) atTop := by
    have hconst :
        Filter.limsup
            (fun n ↦ ((((-ε : ℝ) : EReal)) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))) atTop =
          (((-ε : ℝ) : EReal) + asymptoticCenterObjective zₙ z) := by
      simpa using limsup_const_add_sqdist_eq z (-ε)
    calc
      (((-ε : ℝ) : EReal) + asymptoticCenterObjective zₙ z)
        =
          Filter.limsup
            (fun n ↦ ((((-ε : ℝ) : EReal)) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))) atTop := by
              exact hconst.symm
      _ ≤ Filter.limsup
            (fun n ↦ (((c n : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))) atTop := by
              exact Filter.limsup_le_limsup hcompare hcmp_cobdd hcross_bdd
  have hadd :
      ((ε : ℝ) : EReal) + (((((-ε : ℝ) : EReal)) + asymptoticCenterObjective zₙ z)) ≤
        ((ε : ℝ) : EReal) +
          Filter.limsup
            (fun n ↦ (((c n : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))) atTop :=
    by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hshift (((ε : ℝ) : EReal))
  have hcancel :
      ((ε : ℝ) : EReal) + ((((-ε : ℝ) : EReal)) + asymptoticCenterObjective zₙ z) =
        asymptoticCenterObjective zₙ z := by
    calc
      ((ε : ℝ) : EReal) + ((((-ε : ℝ) : EReal)) + asymptoticCenterObjective zₙ z) =
          ((((ε + -ε : ℝ)) : EReal) + asymptoticCenterObjective zₙ z) := by
            rw [← add_assoc, ← EReal.coe_add]
      _ = asymptoticCenterObjective zₙ z := by
            norm_num
  -- Cancel the finite shift `ε + (-ε)` on the left-hand side.
  calc
    asymptoticCenterObjective zₙ z =
        ((ε : ℝ) : EReal) + ((((-ε : ℝ) : EReal)) + asymptoticCenterObjective zₙ z) := by
          exact hcancel.symm
    _ ≤
        ((ε : ℝ) : EReal) +
          Filter.limsup
            (fun n ↦ (((c n : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))) atTop := hadd

/-- Helper for Proposition 11 18: weak convergence splits the asymptotic-center objective into the
squared distance to the weak limit plus the value at the limit. -/
private theorem asymptoticCenterObjective_formula_of_tendsto_weakly
    {zₙ : ℕ → H} {z : H}
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (zₙ n)) atTop (𝓝 (toWeakSpace ℝ H z))) :
    ∀ x : H,
      (asymptoticCenterObjective zₙ x : EReal) =
        ((‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal) + asymptoticCenterObjective zₙ z := by
  let hzₙ_bdd : Bornology.IsBounded (Set.range zₙ) := bounded_range_of_tendsto_weakly hweak
  intro x
  let c : ℕ → ℝ := fun n ↦ (2 : ℝ) * inner ℝ (x - z) (z - zₙ n)
  let u : ℕ → EReal :=
    fun n ↦ (((c n : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))
  have hc : Tendsto c atTop (𝓝 0) :=
    cross_term_tendsto_zero_of_tendsto_weakly (zₙ := zₙ) (x := x) hweak
  have hu_bdd :
      Filter.IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ) u := by
    simpa [u] using sqdist_cross_isBoundedUnder (zₙ := zₙ) hzₙ_bdd (z := z) hc
  have hu_cobdd :
      Filter.IsCoboundedUnder (· ≤ ·) (atTop : Filter ℕ) u := by
    simpa [u] using sqdist_cross_isCoboundedUnder (zₙ := zₙ) (z := z) hc
  have hshift :
      Filter.limsup
          (fun n ↦ (((‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal) + u n)) atTop =
        ((‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal) + Filter.limsup u atTop := by
    let cE : EReal := ((‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal)
    have hc_ne_bot : Filter.limsup (fun _ : ℕ ↦ cE) atTop ≠ ⊥ := by
      simpa [cE] using (EReal.coe_ne_bot (‖x - z‖ ^ (2 : ℕ) : ℝ))
    have hc_ne_top : Filter.limsup (fun _ : ℕ ↦ cE) atTop ≠ ⊤ := by
      simpa [cE] using (EReal.coe_ne_top (‖x - z‖ ^ (2 : ℕ) : ℝ))
    have hle :
        Filter.limsup (fun n ↦ cE + u n) atTop ≤ cE + Filter.limsup u atTop := by
      simpa [cE] using
        (EReal.limsup_add_le (f := atTop) (u := fun _ : ℕ ↦ cE) (v := u)
          (Or.inl hc_ne_bot) (Or.inl hc_ne_top))
    have hge :
        cE + Filter.limsup u atTop ≤ Filter.limsup (fun n ↦ cE + u n) atTop := by
      simpa [cE, add_comm, add_left_comm, add_assoc] using
        (EReal.le_limsup_add (f := atTop) (u := u) (v := fun _ : ℕ ↦ cE))
    exact le_antisymm hle hge
  have hsq :
      (fun n ↦ ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) =
        fun n ↦ (((‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal) + u n) := by
    funext n
    have hsq_real :
        ‖x - zₙ n‖ ^ (2 : ℕ) =
          ‖x - z‖ ^ (2 : ℕ) + (c n + ‖z - zₙ n‖ ^ (2 : ℕ)) := by
      simpa [c, add_assoc, add_left_comm, add_comm] using
        sqNorm_sub_eq_sqNorm_sub_add_cross_add_sqNorm x (zₙ n) z
    calc
      ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)
        = (((‖x - z‖ ^ (2 : ℕ) + (c n + ‖z - zₙ n‖ ^ (2 : ℕ)) : ℝ) : EReal)) := by
            exact_mod_cast hsq_real
      _ =
          (((‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal) +
            ((((c n + ‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)))) := by
              rw [EReal.coe_add]
      _ =
          (((‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal) +
            (((c n : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))) := by
              rw [EReal.coe_add]
  have hobjective_eq :
      (asymptoticCenterObjective zₙ x : EReal) =
        ((‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal) + Filter.limsup u atTop := by
    -- Move the fixed squared-distance term outside the `limsup`.
    change
      Filter.limsup (fun n ↦ ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) atTop =
        ((‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal) + Filter.limsup u atTop
    rw [hsq, hshift]
  have hlimsup_ge_neg_one : (((-1 : ℝ) : EReal)) ≤ Filter.limsup u atTop := by
    refine Filter.le_limsup_of_le hu_bdd ?_
    intro b hb
    rcases ((eventually_neg_one_le_sqdist_cross (zₙ := zₙ) (z := z) hc).and hb).exists with
      ⟨n, hn⟩
    exact le_trans hn.1 hn.2
  have hlimsup_bot : Filter.limsup u atTop ≠ ⊥ := by
    exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe (-1)) hlimsup_ge_neg_one)
  have hlimsup_top : Filter.limsup u atTop ≠ ⊤ := by
    have hbound :
        Filter.limsup u atTop ≤
          ((1 : ℝ) : EReal) + asymptoticCenterObjective zₙ z := by
      simpa [u] using
        limsup_sqdist_cross_le_eps (zₙ := zₙ) hzₙ_bdd (z := z) hc (by norm_num : (0 : ℝ) < 1)
    have htop_rhs :
        (((1 : ℝ) : EReal) + asymptoticCenterObjective zₙ z) < ⊤ := by
      exact EReal.add_lt_top (EReal.coe_ne_top 1) (asymptoticCenterObjective_lt_top hzₙ_bdd z).ne
    exact ne_of_lt (lt_of_le_of_lt hbound htop_rhs)
  have hz_top : (asymptoticCenterObjective zₙ z : EReal) ≠ ⊤ :=
    (asymptoticCenterObjective_lt_top hzₙ_bdd z).ne
  have hz_bot : (asymptoticCenterObjective zₙ z : EReal) ≠ ⊥ :=
    ne_of_gt (asymptoticCenterObjective zₙ z).2
  have htoReal_le :
      (Filter.limsup u atTop).toReal ≤ (asymptoticCenterObjective zₙ z : EReal).toReal := by
    apply le_iff_forall_pos_le_add.mpr
    intro ε hε
    have hε_ereal :
        Filter.limsup u atTop ≤ ((ε : ℝ) : EReal) + asymptoticCenterObjective zₙ z := by
      simpa [u] using limsup_sqdist_cross_le_eps (zₙ := zₙ) hzₙ_bdd (z := z) hc hε
    have hε_top :
        (((ε : ℝ) : EReal) + asymptoticCenterObjective zₙ z) ≠ ⊤ := by
      exact EReal.add_ne_top (EReal.coe_ne_top ε) hz_top
    -- Convert the `EReal` inequality to the finite real bridge to remove the `ε`-error.
    simpa [EReal.toReal_add, add_comm, add_left_comm, add_assoc, hz_top, hz_bot] using
      (EReal.toReal_le_toReal hε_ereal hlimsup_bot hε_top)
  have htoReal_ge :
      (asymptoticCenterObjective zₙ z : EReal).toReal ≤ (Filter.limsup u atTop).toReal := by
    apply le_iff_forall_pos_le_add.mpr
    intro ε hε
    have hε_ereal :
        asymptoticCenterObjective zₙ z ≤
          ((ε : ℝ) : EReal) + Filter.limsup u atTop := by
      simpa [u] using limsup_sqdist_le_eps_add_cross (zₙ := zₙ) hzₙ_bdd (z := z) hc hε
    have hε_top :
        (((ε : ℝ) : EReal) + Filter.limsup u atTop) ≠ ⊤ := by
      exact EReal.add_ne_top (EReal.coe_ne_top ε) hlimsup_top
    -- The reverse epsilon-sandwich gives the opposite real inequality.
    simpa [EReal.toReal_add, add_comm, add_left_comm, add_assoc, hlimsup_top, hlimsup_bot] using
      (EReal.toReal_le_toReal hε_ereal hz_bot hε_top)
  have hlimsup_eq : Filter.limsup u atTop = asymptoticCenterObjective zₙ z := by
    exact
      (EReal.toReal_eq_toReal hlimsup_top hlimsup_bot hz_top hz_bot).1
        (le_antisymm htoReal_le htoReal_ge)
  -- Reinsert the identified `limsup` to obtain the source formula.
  calc
    (asymptoticCenterObjective zₙ x : EReal) =
        ((‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal) + Filter.limsup u atTop := hobjective_eq
    _ =
        ((‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal) + asymptoticCenterObjective zₙ z := by
          rw [hlimsup_eq]

/-- Helper for Proposition 11 18: the metric projection minimizes any squared-distance objective
shifted by an additive `EReal` constant. -/
private theorem projectionPoint_mem_argminOn_sqNorm_add_const
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (z : H) (c : EReal) :
    projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) z ∈
      Argmin[C] (fun x : H ↦ ((‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal) + c) := by
  let p :=
    projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) z
  have hpC : p ∈ C := by
    simp [p]
  refine mem_argminOn_iff.mpr ⟨hpC, ?_⟩
  rw [isMinOn_iff]
  intro x hxC
  have hp_best : dist z p ≤ dist z x := by
    calc
      dist z p = Metric.infDist z C := by
        simpa [p] using
          (projectionPoint_isBestApproximation C
            (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) z).2
      _ ≤ dist z x := Metric.infDist_le_dist_of_mem hxC
  have hsq :
      ‖p - z‖ ^ (2 : ℕ) ≤ ‖x - z‖ ^ (2 : ℕ) := by
    have hnorm : ‖p - z‖ ≤ ‖x - z‖ := by
      simpa [dist_eq_norm, norm_sub_rev] using hp_best
    nlinarith [hnorm, norm_nonneg (p - z), norm_nonneg (x - z)]
  have hsq_ereal :
      (((‖p - z‖ ^ (2 : ℕ) : ℝ) : EReal)) ≤ (((‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
    exact_mod_cast hsq
  -- The additive constant `c` does not affect the projection minimizer.
  simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hsq_ereal c

-- Proof sketch: expand `‖x - zₙ‖²` around the weak limit `z`, pass to the limit superior using
-- weak convergence of the linear term, and then identify the unique minimizer on `C` with the
-- metric projection of `z` onto `C`.
/-- Proposition 11.18 (4): clause (iv). If `zₙ` converges weakly to `z`, then the asymptotic-center
objective splits as `‖x - z‖²` plus the constant `f(z)`, and the asymptotic center relative to `C`
is the metric projection of `z` onto `C`. -/
theorem asymptoticCenterObjective_formula_and_asymptoticCenter_eq_projectionPoint_of_tendsto_weakly
    {zₙ : ℕ → H} {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) {z : H}
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (zₙ n)) atTop (𝓝 (toWeakSpace ℝ H z))) :
    (∀ x : H,
        (asymptoticCenterObjective zₙ x : EReal) =
          ((‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal) + asymptoticCenterObjective zₙ z) ∧
      asymptoticCenter zₙ C (bounded_range_of_tendsto_weakly hweak)
        hC_nonempty hC_closed hC_convex =
        projectionPoint C (isChebyshev_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex) z := by
  constructor
  · exact asymptoticCenterObjective_formula_of_tendsto_weakly hweak
  · let hzₙ_bdd : Bornology.IsBounded (Set.range zₙ) := bounded_range_of_tendsto_weakly hweak
    let p :=
      projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) z
    have hp_arg_shift :
        p ∈ Argmin[C]
          (fun x : H ↦ ((‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal) + asymptoticCenterObjective zₙ z) := by
      simpa [p] using
        projectionPoint_mem_argminOn_sqNorm_add_const
          hC_nonempty hC_closed hC_convex z (asymptoticCenterObjective zₙ z)
    have hp_arg :
        p ∈ Argmin[C] (asymptoticCenterObjective zₙ).asEReal := by
      rcases mem_argminOn_iff.mp hp_arg_shift with ⟨hpC, hpmin⟩
      refine mem_argminOn_iff.mpr ⟨hpC, ?_⟩
      rw [isMinOn_iff] at hpmin ⊢
      intro x hxC
      -- Rewrite the constrained objective using the weak-limit formula proved just above.
      calc
        (asymptoticCenterObjective zₙ p : EReal) =
            ((‖p - z‖ ^ (2 : ℕ) : ℝ) : EReal) + asymptoticCenterObjective zₙ z := by
              simpa using asymptoticCenterObjective_formula_of_tendsto_weakly hweak p
        _ ≤ ((‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal) + asymptoticCenterObjective zₙ z := hpmin x hxC
        _ = (asymptoticCenterObjective zₙ x : EReal) := by
              symm
              simpa using asymptoticCenterObjective_formula_of_tendsto_weakly hweak x
    exact
      (eq_asymptoticCenter_of_mem_argminOn
        hzₙ_bdd hC_nonempty hC_closed hC_convex hp_arg).symm

-- Proof sketch: Proposition 5.7 gives strong convergence of the projection shadows `P_C zₙ` for a
-- Fejér-monotone sequence; the limit point is characterized as the unique minimizer of the
-- asymptotic-center objective on `C`.
omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 11 18: if the squared-distance sequence to `x` has a real limit, then
the `EReal` asymptotic-center objective at `x` is exactly that finite limit. -/
private theorem asymptoticCenterObjective_eq_coe_of_tendsto_sqdist
    {zₙ : ℕ → H} {x : H} {a : ℝ}
    (ha : Tendsto (fun n ↦ ‖zₙ n - x‖ ^ (2 : ℕ)) atTop (𝓝 a)) :
    (asymptoticCenterObjective zₙ x : EReal) = ((a : ℝ) : EReal) := by
  have hcoe :
      Tendsto (fun n ↦ ((‖zₙ n - x‖ ^ (2 : ℕ) : ℝ) : EReal)) atTop (𝓝 ((a : ℝ) : EReal)) := by
    exact continuous_coe_real_ereal.continuousAt.tendsto.comp ha
  change Filter.limsup (fun n ↦ ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) atTop = ((a : ℝ) : EReal)
  have hsymm :
      (fun n ↦ ((‖x - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) =
        fun n ↦ ((‖zₙ n - x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    funext n
    simp [norm_sub_rev]
  rw [hsymm]
  simpa using hcoe.limsup_eq

/-- Helper for Proposition 11 18: the strong limit of the Fejér projection shadows minimizes the
asymptotic-center objective against every feasible comparison point in `C`. -/
private theorem fejer_projection_limit_le_asymptoticCenterObjective_of_mem
    {zₙ : ℕ → H} {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hfejer : FejerMonotone C zₙ) {p : H} (hpC : p ∈ C)
    (hp : Tendsto
    (fun n ↦
        projectionPoint C (isChebyshev_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex) (zₙ n))
      atTop (𝓝 p)) :
    ∀ ⦃x : H⦄, x ∈ C →
      (asymptoticCenterObjective zₙ p : EReal) ≤ (asymptoticCenterObjective zₙ x : EReal) := by
  intro x hxC
  rcases exists_sqNorm_limits_of_fejerMonotone (C := C) zₙ hfejer hpC hxC with ⟨a, b, ha, hb⟩
  have hab_gap : a + ‖x - p‖ ^ (2 : ℕ) ≤ b := by
    simpa [add_comm, norm_sub_rev] using
      sqNorm_limit_add_sqNorm_le_limit_of_shadowLimit
        (C := C) hC_nonempty hC_closed hC_convex zₙ hp hxC ha hb
  have hab : a ≤ b := by
    have hnonneg : 0 ≤ ‖x - p‖ ^ (2 : ℕ) := by positivity
    nlinarith
  -- Identify the two `limsup` values with the corresponding real limits of squared distances.
  calc
    (asymptoticCenterObjective zₙ p : EReal) = ((a : ℝ) : EReal) := by
      exact asymptoticCenterObjective_eq_coe_of_tendsto_sqdist ha
    _ ≤ ((b : ℝ) : EReal) := by
      exact_mod_cast hab
    _ = (asymptoticCenterObjective zₙ x : EReal) := by
      exact (asymptoticCenterObjective_eq_coe_of_tendsto_sqdist hb).symm

/-- Helper for Proposition 11 18: the strong limit of the Fejér projection shadows is a
constrained minimizer of the asymptotic-center objective. -/
private theorem fejer_projection_limit_mem_argminOn_asymptoticCenterObjective
    {zₙ : ℕ → H} {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hfejer : FejerMonotone C zₙ) {p : H} (hpC : p ∈ C)
    (hp : Tendsto
    (fun n ↦
        projectionPoint C (isChebyshev_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex) (zₙ n))
      atTop (𝓝 p)) :
    p ∈ Argmin[C] (asymptoticCenterObjective zₙ).asEReal := by
  refine mem_argminOn_iff.mpr ⟨hpC, ?_⟩
  rw [isMinOn_iff]
  intro x hxC
  exact
    fejer_projection_limit_le_asymptoticCenterObjective_of_mem
      hC_nonempty hC_closed hC_convex hfejer hpC hp hxC

/-- Proposition 11.18 (5): clause (v). If `zₙ` is Fejér monotone with respect to `C`, then the
projection shadow sequence `P_C zₙ` converges strongly to the asymptotic center relative to `C`. -/
theorem tendsto_projectionPoint_to_asymptoticCenter_of_fejerMonotone
    {zₙ : ℕ → H} {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hfejer : FejerMonotone C zₙ) :
    Tendsto
      (fun n ↦
        projectionPoint C (isChebyshev_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex) (zₙ n))
      atTop (𝓝 (asymptoticCenter zₙ C (hfejer.isBounded hC_nonempty)
        hC_nonempty hC_closed hC_convex)) := by
  rcases exists_shadowLimit_of_fejerMonotone hC_nonempty hC_closed hC_convex zₙ hfejer with
    ⟨p, hpC, hp⟩
  have hp_arg :
      p ∈ Argmin[C] (asymptoticCenterObjective zₙ).asEReal :=
    fejer_projection_limit_mem_argminOn_asymptoticCenterObjective
      hC_nonempty hC_closed hC_convex hfejer hpC hp
  have hp_eq :
      p = asymptoticCenter zₙ C (hfejer.isBounded hC_nonempty)
        hC_nonempty hC_closed hC_convex :=
    eq_asymptoticCenter_of_mem_argminOn
      (hfejer.isBounded hC_nonempty) hC_nonempty hC_closed hC_convex hp_arg
  -- Uniqueness of the constrained minimizer identifies the shadow limit with the asymptotic center.
  simpa [hp_eq] using hp

-- Proof sketch: compare the asymptotic-center objective at `z_C` and at `T z_C` along the Picard
-- orbit `zₙ`; nonexpansiveness gives the inequality, and uniqueness of the minimizer forces
-- `T z_C = z_C`.
omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 11 18: applying a nonexpansive orbit map to a constrained minimizer
produces another constrained minimizer of the asymptotic-center objective. -/
private theorem orbit_image_mem_argminOn_asymptoticCenterObjective
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {C : Set H}
    {T : C → C} (hT : LipschitzWith 1 T) (hzₙ_mem : ∀ n, zₙ n ∈ C)
    (horbit : ∀ n, zₙ (n + 1) = T ⟨zₙ n, hzₙ_mem n⟩) {z : H}
    (hzC : z ∈ C) (hzmin : IsMinOn (asymptoticCenterObjective zₙ).asEReal C z) :
    (T ⟨z, hzC⟩ : H) ∈ Argmin[C] (asymptoticCenterObjective zₙ).asEReal := by
  let u : ℕ → EReal := fun n ↦ ((‖(T ⟨z, hzC⟩ : H) - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)
  let v : ℕ → EReal := fun n ↦ ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)
  have hu_shift_le : ∀ᶠ n in atTop, u (n + 1) ≤ v n := by
    refine Filter.Eventually.of_forall fun n ↦ ?_
    -- Compare the shifted orbit pointwise using nonexpansiveness of `T`.
    have hdist :
        ‖(T ⟨z, hzC⟩ : H) - zₙ (n + 1)‖ ≤ ‖z - zₙ n‖ := by
      simpa [Subtype.dist_eq, dist_eq_norm, horbit n, one_mul] using
        hT.dist_le_mul ⟨z, hzC⟩ ⟨zₙ n, hzₙ_mem n⟩
    change
      ((‖(T ⟨z, hzC⟩ : H) - zₙ (n + 1)‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)
    exact_mod_cast
      (show ‖(T ⟨z, hzC⟩ : H) - zₙ (n + 1)‖ ^ (2 : ℕ) ≤ ‖z - zₙ n‖ ^ (2 : ℕ) by
        nlinarith [hdist, norm_nonneg ((T ⟨z, hzC⟩ : H) - zₙ (n + 1)), norm_nonneg (z - zₙ n)])
  have hu_shift_cobdd :
      Filter.IsCoboundedUnder (· ≤ ·) (atTop : Filter ℕ) (fun n ↦ u (n + 1)) := by
    simpa [u] using
      sqdist_sequence_isCoboundedUnder
        (zₙ := fun n ↦ zₙ (n + 1)) ((T ⟨z, hzC⟩ : H))
  have hv_bdd :
      Filter.IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ) v := by
    simpa [v] using sqdist_sequence_isBoundedUnder hzₙ_bdd z
  have himage_le :
      (asymptoticCenterObjective zₙ (T ⟨z, hzC⟩) : EReal) ≤ asymptoticCenterObjective zₙ z := by
    -- Rewrite the image objective to the shifted tail, then compare with the minimizer tail.
    change Filter.limsup u atTop ≤ Filter.limsup v atTop
    rw [← Filter.limsup_nat_add u 1]
    exact Filter.limsup_le_limsup hu_shift_le hu_shift_cobdd hv_bdd
  refine mem_argminOn_iff.mpr ⟨(T ⟨z, hzC⟩).2, ?_⟩
  rw [isMinOn_iff]
  intro y hyC
  -- Compose the orbit inequality with the minimizing property of `z` on `C`.
  exact himage_le.trans ((isMinOn_iff.mp hzmin) y hyC)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 11 18: residual convergence yields a vanishing scalar error sequence
that controls the squared distance from `T z` to the orbit by the squared distance from `z`. -/
private theorem residual_sqdist_le_sqdist_add_error
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {C : Set H}
    {T : C → C} (hT : LipschitzWith 1 T) (hzₙ_mem : ∀ n, zₙ n ∈ C)
    (hres :
      Tendsto (fun n ↦ zₙ n - (T ⟨zₙ n, hzₙ_mem n⟩ : H)) atTop (𝓝 (0 : H))) {z : H}
    (hzC : z ∈ C) :
    ∃ c : ℕ → ℝ,
      Tendsto c atTop (𝓝 0) ∧
        ∀ n,
          ‖(T ⟨z, hzC⟩ : H) - zₙ n‖ ^ (2 : ℕ) ≤
            c n + ‖z - zₙ n‖ ^ (2 : ℕ) := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hzₙ_bdd
  let M : ℝ := ‖z‖ + R
  let r : ℕ → ℝ := fun n ↦ ‖zₙ n - (T ⟨zₙ n, hzₙ_mem n⟩ : H)‖
  let c : ℕ → ℝ := fun n ↦ 2 * M * r n + r n ^ (2 : ℕ)
  have hr : Tendsto r atTop (𝓝 0) := by
    -- The residual norms converge to `0` because the residual vectors do.
    simpa [r] using hres.norm
  have hc : Tendsto c atTop (𝓝 0) := by
    -- The quadratic error is built from sums and products of the vanishing residual norm.
    have hMr : Tendsto (fun n ↦ 2 * M * r n) atTop (𝓝 (2 * M * 0)) :=
      (hr.const_mul (2 * M))
    have hr_sq : Tendsto (fun n ↦ r n ^ (2 : ℕ)) atTop (𝓝 (0 ^ (2 : ℕ))) :=
      hr.pow 2
    simpa [c] using hMr.add hr_sq
  have hbound : ∀ n, ‖z - zₙ n‖ ≤ M := by
    intro n
    have hzₙ_norm : ‖zₙ n‖ ≤ R := by
      simpa using hR (zₙ n) (Set.mem_range_self n)
    -- The bounded orbit gives the fixed comparison radius `M = ‖z‖ + R`.
    calc
      ‖z - zₙ n‖ ≤ ‖z‖ + ‖zₙ n‖ := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_sub_le z (zₙ n)
      _ ≤ M := by
        dsimp [M]
        linarith
  refine ⟨c, hc, ?_⟩
  intro n
  let Tz : H := T ⟨z, hzC⟩
  let Tzₙ : H := T ⟨zₙ n, hzₙ_mem n⟩
  have hdist :
      ‖Tz - zₙ n‖ ≤ ‖z - zₙ n‖ + r n := by
    have hsplit : Tz - zₙ n = (Tz - Tzₙ) + (Tzₙ - zₙ n) := by
      simp [Tz, Tzₙ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    calc
      ‖Tz - zₙ n‖ = ‖(Tz - Tzₙ) + (Tzₙ - zₙ n)‖ := by rw [hsplit]
      _ ≤ ‖Tz - Tzₙ‖ + ‖Tzₙ - zₙ n‖ := norm_add_le _ _
      _ ≤ ‖z - zₙ n‖ + ‖Tzₙ - zₙ n‖ := by
            gcongr
            simpa [Tz, Tzₙ, Subtype.dist_eq, dist_eq_norm, one_mul] using
              hT.dist_le_mul ⟨z, hzC⟩ ⟨zₙ n, hzₙ_mem n⟩
      _ = ‖z - zₙ n‖ + r n := by
            simp [r, Tzₙ, norm_sub_rev]
  have hr_nonneg : 0 ≤ r n := norm_nonneg _
  have hz_nonneg : 0 ≤ ‖z - zₙ n‖ := norm_nonneg _
  have hT_nonneg : 0 ≤ ‖Tz - zₙ n‖ := norm_nonneg _
  -- Expand the square after the triangle estimate and absorb the mixed term with `‖z - zₙ n‖ ≤ M`.
  have hsq :
      ‖Tz - zₙ n‖ ^ (2 : ℕ) ≤ c n + ‖z - zₙ n‖ ^ (2 : ℕ) := by
    dsimp [c]
    nlinarith [hdist, hbound n, hr_nonneg, hz_nonneg, hT_nonneg]
  simpa [Tz] using hsq

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 11 18: for bounded sequences, an `ε`-family of upper bounds on the
asymptotic-center objective can be upgraded to an exact upper bound. -/
private theorem asymptoticCenterObjective_le_of_forall_pos_add
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {x y : H}
    (hxy : ∀ {ε : ℝ}, 0 < ε →
      (asymptoticCenterObjective zₙ x : EReal) ≤
        ((ε : ℝ) : EReal) + asymptoticCenterObjective zₙ y) :
    (asymptoticCenterObjective zₙ x : EReal) ≤ asymptoticCenterObjective zₙ y := by
  let fx : EReal := asymptoticCenterObjective zₙ x
  let fy : EReal := asymptoticCenterObjective zₙ y
  have hfx_top : fx ≠ ⊤ := by
    exact ne_of_lt (by simpa [fx] using asymptoticCenterObjective_lt_top hzₙ_bdd x)
  have hfy_top : fy ≠ ⊤ := by
    exact ne_of_lt (by simpa [fy] using asymptoticCenterObjective_lt_top hzₙ_bdd y)
  have hfx_bot : fx ≠ ⊥ := by
    simpa [fx] using ne_of_gt (asymptoticCenterObjective zₙ x).2
  have hfy_bot : fy ≠ ⊥ := by
    simpa [fy] using ne_of_gt (asymptoticCenterObjective zₙ y).2
  have hreal : fx.toReal ≤ fy.toReal := by
    -- Push the `EReal` epsilon-majorization down to `ℝ`, where the standard order lemma applies.
    refine _root_.le_of_forall_pos_le_add fun ε hε ↦ ?_
    have hε_bound : fx ≤ ((ε : ℝ) : EReal) + fy := by
      simpa [fx, fy] using hxy (ε := ε) hε
    have hsum_top : (((ε : ℝ) : EReal) + fy) ≠ ⊤ := by
      exact EReal.add_ne_top (EReal.coe_ne_top ε) hfy_top
    have hε_real :
        fx.toReal ≤ ((((ε : ℝ) : EReal) + fy).toReal) := by
      exact EReal.toReal_le_toReal hε_bound hfx_bot hsum_top
    -- Rewrite the finite sum back to the real addition `ε + fy.toReal`.
    rw [EReal.toReal_add (EReal.coe_ne_top ε) (EReal.coe_ne_bot ε) hfy_top hfy_bot] at hε_real
    simpa [add_comm, add_left_comm, add_assoc] using hε_real
  -- Lift the resulting real inequality back to `EReal`.
  have hcast : (((fx.toReal : ℝ) : EReal)) ≤ (((fy.toReal : ℝ) : EReal)) := by
    exact_mod_cast hreal
  simpa [fx, fy, EReal.coe_toReal hfx_top hfx_bot, EReal.coe_toReal hfy_top hfy_bot] using hcast

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 11 18: residual convergence transfers constrained minimality through a
nonexpansive self-map by comparing `T z` to `z` up to a vanishing quadratic error. -/
private theorem residual_image_mem_argminOn_asymptoticCenterObjective
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {C : Set H}
    {T : C → C} (hT : LipschitzWith 1 T) (hzₙ_mem : ∀ n, zₙ n ∈ C)
    (hres :
      Tendsto (fun n ↦ zₙ n - (T ⟨zₙ n, hzₙ_mem n⟩ : H)) atTop (𝓝 (0 : H))) {z : H}
    (hzC : z ∈ C) (hzmin : IsMinOn (asymptoticCenterObjective zₙ).asEReal C z) :
    (T ⟨z, hzC⟩ : H) ∈ Argmin[C] (asymptoticCenterObjective zₙ).asEReal := by
  rcases residual_sqdist_le_sqdist_add_error hzₙ_bdd hT hzₙ_mem hres hzC with ⟨c, hc, hsq⟩
  let Tz : H := T ⟨z, hzC⟩
  let u : ℕ → EReal :=
    fun n ↦ (((c n : ℝ) : EReal) + ((‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal))
  have hcompare :
      ∀ᶠ n in atTop,
        ((‖Tz - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal) ≤ u n := by
    refine Filter.Eventually.of_forall fun n ↦ ?_
    -- Translate the real perturbation estimate to the `EReal` sequence used by `limsup`.
    have hsqE :
        ((‖Tz - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
          ((c n + ‖z - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal) := by
      exact_mod_cast hsq n
    simpa [u, EReal.coe_add] using hsqE
  have hu_bdd :
      Filter.IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ) u := by
    simpa [u] using sqdist_cross_isBoundedUnder (zₙ := zₙ) hzₙ_bdd (z := z) hc
  have hv_cobdd :
      Filter.IsCoboundedUnder (· ≤ ·) (atTop : Filter ℕ)
        (fun n ↦ ((‖Tz - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
    simpa [Tz] using sqdist_sequence_isCoboundedUnder (zₙ := zₙ) Tz
  have himage_le_cross :
      (asymptoticCenterObjective zₙ Tz : EReal) ≤ Filter.limsup u atTop := by
    -- First compare the image tail to the perturbed tail termwise, then pass to `limsup`.
    change
      Filter.limsup (fun n ↦ ((‖Tz - zₙ n‖ ^ (2 : ℕ) : ℝ) : EReal)) atTop ≤
        Filter.limsup u atTop
    exact Filter.limsup_le_limsup hcompare hv_cobdd hu_bdd
  have himage_le :
      (asymptoticCenterObjective zₙ Tz : EReal) ≤ asymptoticCenterObjective zₙ z := by
    -- Remove the vanishing `ε`-error from the perturbed `limsup` estimate.
    refine asymptoticCenterObjective_le_of_forall_pos_add (zₙ := zₙ) hzₙ_bdd ?_
    intro ε hε
    exact le_trans himage_le_cross (by
      simpa [u] using limsup_sqdist_cross_le_eps (zₙ := zₙ) hzₙ_bdd (z := z) hc hε)
  refine mem_argminOn_iff.mpr ⟨(T ⟨z, hzC⟩).2, ?_⟩
  rw [isMinOn_iff]
  intro y hyC
  -- Compose the image inequality with the minimizing property of `z` on the constraint set.
  exact himage_le.trans ((isMinOn_iff.mp hzmin) y hyC)

/-- Proposition 11.18 (6): clause (vi). If `zₙ` is the orbit of a nonexpansive self-map `T : C →
C`, then the asymptotic center relative to `C` is an ambient fixed point of `T`. -/
theorem asymptoticCenter_mem_fixedPoints_of_orbit
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {C : Set H}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {T : C → C} (hT : LipschitzWith 1 T) (hzₙ_mem : ∀ n, zₙ n ∈ C)
    (horbit : ∀ n, zₙ (n + 1) = T ⟨zₙ n, hzₙ_mem n⟩) :
    asymptoticCenter zₙ C hzₙ_bdd hC_nonempty hC_closed hC_convex ∈
      Subtype.val '' Function.fixedPoints T := by
  let zC := asymptoticCenter zₙ C hzₙ_bdd hC_nonempty hC_closed hC_convex
  have hzC_arg :
      zC ∈ Argmin[C] (asymptoticCenterObjective zₙ).asEReal :=
    asymptoticCenter_mem_argminOn hzₙ_bdd hC_nonempty hC_closed hC_convex
  rcases mem_argminOn_iff.mp hzC_arg with ⟨hzC_mem, hzC_min⟩
  have himage_arg :
      (T ⟨zC, hzC_mem⟩ : H) ∈ Argmin[C] (asymptoticCenterObjective zₙ).asEReal :=
    orbit_image_mem_argminOn_asymptoticCenterObjective
      hzₙ_bdd hT hzₙ_mem horbit hzC_mem hzC_min
  have hzC_eq :
      zC = asymptoticCenter zₙ C hzₙ_bdd hC_nonempty hC_closed hC_convex :=
    eq_asymptoticCenter_of_mem_argminOn
      hzₙ_bdd hC_nonempty hC_closed hC_convex hzC_arg
  have himage_eq :
      (T ⟨zC, hzC_mem⟩ : H) =
        asymptoticCenter zₙ C hzₙ_bdd hC_nonempty hC_closed hC_convex :=
    eq_asymptoticCenter_of_mem_argminOn
      hzₙ_bdd hC_nonempty hC_closed hC_convex himage_arg
  let zFix : C := ⟨zC, hzC_mem⟩
  have hzFix : zFix ∈ Function.fixedPoints T := by
    rw [Function.mem_fixedPoints_iff]
    -- Uniqueness of the constrained minimizer forces `T zC = zC`.
    exact Subtype.ext (himage_eq.trans hzC_eq.symm)
  exact ⟨zFix, hzFix, rfl⟩

-- Proof sketch: compare `T z_C` to the sequence `zₙ` by inserting and subtracting `T zₙ`; the
-- residual convergence together with nonexpansiveness shows that `T z_C` is no larger for the
-- asymptotic-center objective than `z_C`, so uniqueness forces fixed-point membership.
/-- Proposition 11.18 (7): clause (vii). If `zₙ - T zₙ → 0` for a nonexpansive self-map `T : C →
C`, then the asymptotic center relative to `C` is an ambient fixed point of `T`. -/
theorem asymptoticCenter_mem_fixedPoints_of_residual_tendsto_zero
    {zₙ : ℕ → H} (hzₙ_bdd : Bornology.IsBounded (Set.range zₙ)) {C : Set H}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {T : C → C} (hT : LipschitzWith 1 T) (hzₙ_mem : ∀ n, zₙ n ∈ C)
    (hres :
      Tendsto (fun n ↦ zₙ n - (T ⟨zₙ n, hzₙ_mem n⟩ : H)) atTop (𝓝 (0 : H))) :
    asymptoticCenter zₙ C hzₙ_bdd hC_nonempty hC_closed hC_convex ∈
      Subtype.val '' Function.fixedPoints T := by
  let zC := asymptoticCenter zₙ C hzₙ_bdd hC_nonempty hC_closed hC_convex
  have hzC_arg :
      zC ∈ Argmin[C] (asymptoticCenterObjective zₙ).asEReal :=
    asymptoticCenter_mem_argminOn hzₙ_bdd hC_nonempty hC_closed hC_convex
  rcases mem_argminOn_iff.mp hzC_arg with ⟨hzC_mem, hzC_min⟩
  have himage_arg :
      (T ⟨zC, hzC_mem⟩ : H) ∈ Argmin[C] (asymptoticCenterObjective zₙ).asEReal :=
    residual_image_mem_argminOn_asymptoticCenterObjective
      hzₙ_bdd hT hzₙ_mem hres hzC_mem hzC_min
  have hzC_eq :
      zC = asymptoticCenter zₙ C hzₙ_bdd hC_nonempty hC_closed hC_convex :=
    eq_asymptoticCenter_of_mem_argminOn
      hzₙ_bdd hC_nonempty hC_closed hC_convex hzC_arg
  have himage_eq :
      (T ⟨zC, hzC_mem⟩ : H) =
        asymptoticCenter zₙ C hzₙ_bdd hC_nonempty hC_closed hC_convex :=
    eq_asymptoticCenter_of_mem_argminOn
      hzₙ_bdd hC_nonempty hC_closed hC_convex himage_arg
  let zFix : C := ⟨zC, hzC_mem⟩
  have hzFix : zFix ∈ Function.fixedPoints T := by
    rw [Function.mem_fixedPoints_iff]
    -- The residual-transfer minimizer comparison yields the same fixed-point conclusion.
    exact Subtype.ext (himage_eq.trans hzC_eq.symm)
  exact ⟨zFix, hzFix, rfl⟩

end CompleteSpace

end RealHilbert

end
