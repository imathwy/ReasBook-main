import BauschkeLean.Chap04.Proposition_4_9
import BauschkeLean.Chap04.Proposition_4_16
import BauschkeLean.Chap05.Corollary_5_24
import BauschkeLean.Chap29.Example_29_45
import BauschkeLean.Chap30.Corollary_30_2
import BauschkeLean.Chap30.Corollary_30_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators Topology InnerProductSpace

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section

variable {m : ℕ} {C : Fin m → Set H}
variable (hC_nonempty : (⋂ i, C i).Nonempty)
variable (hC_closed : ∀ i, IsClosed (C i)) (hC_convex : ∀ i, Convex ℝ (C i))

local notation "InterC" => ⋂ i, C i

local notation "hInter_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty
    (isClosed_iInter hC_closed) (convex_iInter hC_convex)

local notation "hFamily_cheb" =>
  family_isChebyshev_of_iInter_nonempty_closed_convex C hC_nonempty hC_closed hC_convex

local notation "H_univ" => (Set.univ : Set H)

/-- Helper for Example 30.4: any point of `C i` is fixed by the metric projector onto `C i`. -/
private theorem projectionPoint_eq_self_of_mem {i : Fin m} {z : H} (hz : z ∈ C i) :
    P[C i, hFamily_cheb i] z = z := by
  -- Turn the membership hypothesis into the defining best-approximation property.
  have hz_best : IsBestApproximation z (C i) z := by
    refine ⟨hz, ?_⟩
    simpa using (Metric.infDist_zero_of_mem_closure (subset_closure hz)).symm
  exact (eq_projectionPoint_of_isBestApproximation (C i) (hFamily_cheb i) hz_best).symm

/-- Helper for Example 30.4: the Halpern parameters `λₙ = 1 / (n + 2)` lie in `]0,1[`. -/
private theorem reciprocalHalpernParams_memIoo (n : ℕ) :
    ((n + 2 : ℝ)⁻¹) ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · -- Positivity is immediate from the positive denominator.
    positivity
  · -- The denominator is strictly larger than `1`, so its reciprocal is strictly smaller than `1`.
    have hlt : (1 : ℝ) < (n + 2 : ℝ) := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by
        positivity
      nlinarith
    simpa [one_div] using inv_lt_one_of_one_lt₀ hlt

/-- Helper for Example 30.4: the shifted harmonic partial sums
`∑_{n < N} 1 / (n + 2)` diverge to `+∞`. -/
private theorem reciprocalHalpernParams_sumDiverges :
    Tendsto (fun N ↦ (Finset.range N).sum (fun n ↦ ((n + 2 : ℝ)⁻¹))) atTop atTop := by
  -- This is exactly the harmonic-series divergence after shifting the index by `2`.
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg]
  · simpa [Nat.cast_add, one_div] using
      mt (summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ)) 2).mp
        Real.not_summable_one_div_natCast
  · intro n
    positivity

/-- Helper for Example 30.4: the successive differences of `λₙ = 1 / (n + 2)` form a summable
series. -/
private theorem reciprocalHalpernParams_successiveDiffSummable :
    Summable (fun n : ℕ ↦ |((n + 3 : ℝ)⁻¹) - ((n + 2 : ℝ)⁻¹)|) := by
  have hpSeries : Summable (fun n : ℕ ↦ 1 / ((n + 2 : ℝ) ^ 2)) := by
    -- Shift the convergent `p`-series with exponent `2`.
    simpa [Nat.cast_add] using
      (summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) 2).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ ↦ 1 / ((n + 2 : ℝ) ^ 2))
    (g := fun n : ℕ ↦ |((n + 3 : ℝ)⁻¹) - ((n + 2 : ℝ)⁻¹)|)
    (fun n ↦ by positivity) ?_ hpSeries
  intro n
  have htwo_pos : (0 : ℝ) < (n + 2 : ℝ) := by
    positivity
  have hthree_pos : (0 : ℝ) < (n + 3 : ℝ) := by
    positivity
  have hdiff :
      |((n + 3 : ℝ)⁻¹) - ((n + 2 : ℝ)⁻¹)| = 1 / ((n + 2 : ℝ) * (n + 3 : ℝ)) := by
    have hraw :
        ((n + 3 : ℝ)⁻¹) - ((n + 2 : ℝ)⁻¹) =
          -(1 / ((n + 2 : ℝ) * (n + 3 : ℝ))) := by
      field_simp [htwo_pos.ne', hthree_pos.ne']
      ring
    rw [hraw, abs_of_nonpos]
    · ring
    · have hnonneg : 0 ≤ 1 / ((n + 2 : ℝ) * (n + 3 : ℝ)) := by
        positivity
      exact neg_nonpos.mpr hnonneg
  have hmul_le :
      (n + 2 : ℝ) * (n + 2 : ℝ) ≤ (n + 2 : ℝ) * (n + 3 : ℝ) := by
    have hstep : (n + 2 : ℝ) ≤ n + 3 := by
      nlinarith
    exact mul_le_mul_of_nonneg_left hstep htwo_pos.le
  have hinv_le :
      1 / ((n + 2 : ℝ) * (n + 3 : ℝ)) ≤ 1 / ((n + 2 : ℝ) * (n + 2 : ℝ)) := by
    exact one_div_le_one_div_of_le (mul_pos htwo_pos htwo_pos) hmul_le
  calc
    |((n + 3 : ℝ)⁻¹) - ((n + 2 : ℝ)⁻¹)| = 1 / ((n + 2 : ℝ) * (n + 3 : ℝ)) := hdiff
    _ ≤ 1 / ((n + 2 : ℝ) * (n + 2 : ℝ)) := hinv_le
    _ = 1 / ((n + 2 : ℝ) ^ 2) := by rw [pow_two]

/-- Helper for Example 30.4: each metric projector `P[C i]` is `1 / 2`-averaged on `Set.univ`. -/
private theorem projectorAveragedWithHalfOnUniv (i : Fin m) :
    AveragedWith (1 / 2 : ℝ) (fun z : H_univ ↦ P[C i, hFamily_cheb i] z) := by
  cases m with
  | zero =>
      exact i.elim0
  | succ n =>
      let hC_nonempty' : ∀ j : Fin (n + 1), (C j).Nonempty := by
        intro j
        rcases hC_nonempty with ⟨z, hz⟩
        exact ⟨z, Set.mem_iInter.mp hz j⟩
      -- Reuse the Chapter 5 POCS projector-family owner instead of rebuilding the averaged proof.
      simpa [pocsProjectorFamilyOnUniv, pocsProjectorFamily] using
        pocs_projectorFamily_averagedWith_half_on_univ C hC_nonempty' hC_closed hC_convex i

omit [CompleteSpace H] in
/-- Helper for Example 30.4: every averaged map on `Set.univ` is nonexpansive. -/
private theorem lipschitzWithOneOfAveragedWithLocal {α : ℝ} {T : H_univ → H}
    (hT : AveragedWith α T) : LipschitzWith 1 T := by
  rcases averagedWith_iff.mp hT with ⟨hα, R, hR, hT_eq⟩
  have hα_nonneg : 0 ≤ α := hα.1.le
  have h_one_sub_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα.2.le
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hRxy : ‖R x - R y‖ ≤ ‖(x : H) - y‖ := by
    simpa [Subtype.dist_eq, dist_eq_norm] using hR.dist_le_mul x y
  have hxy :
      T x - T y = (1 - α) • ((x : H) - y) + α • (R x - R y) := by
    calc
      T x - T y
          = ((1 - α) • (x : H) + α • R x) - ((1 - α) • (y : H) + α • R y) := by
              rw [hT_eq]
      _ = (1 - α) • ((x : H) - y) + α • (R x - R y) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  simpa [Subtype.dist_eq, dist_eq_norm, one_mul] using
    calc
      ‖T x - T y‖ = ‖(1 - α) • ((x : H) - y) + α • (R x - R y)‖ := by
        rw [hxy]
      _ ≤ ‖(1 - α) • ((x : H) - y)‖ + ‖α • (R x - R y)‖ := norm_add_le _ _
      _ = (1 - α) * ‖(x : H) - y‖ + α * ‖R x - R y‖ := by
            rw [norm_smul, norm_smul]
            simp [Real.norm_eq_abs, abs_of_nonneg h_one_sub_nonneg, abs_of_nonneg hα_nonneg]
      _ ≤ (1 - α) * ‖(x : H) - y‖ + α * ‖(x : H) - y‖ := by
            nlinarith [hRxy, norm_nonneg ((x : H) - y)]
      _ = ‖(x : H) - y‖ := by
            ring

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Example 30.4: coercing a `Set.univ` finite composition recovers the ambient finite
composition. -/
@[simp] private theorem finiteComposition_univFamily_coe :
    ∀ {n : ℕ} (T : Fin n → H → H) (x : H_univ),
      ((finiteComposition (fun i ↦ fun y : H_univ ↦ ⟨T i y, Set.mem_univ _⟩) x : H_univ) : H) =
        finiteComposition T x
  | 0, _, _ => rfl
  | n + 1, T, x => by
      rw [finiteComposition_succ, finiteComposition_succ]
      exact congrArg (T 0) (finiteComposition_univFamily_coe (T := fun i ↦ T i.succ) (x := x))

/-- Helper for Example 30.4: the lifted projector family on `Set.univ` has a common fixed point
whenever `⋂ i, C i` is nonempty. -/
private theorem liftedProjectorFamily_fixedPoints_nonempty :
    Set.Nonempty
      (⋂ i,
        Function.fixedPoints
          (fun z : H_univ ↦
            (⟨P[C i, hFamily_cheb i] z, Set.mem_univ _⟩ : H_univ)) : Set H_univ) := by
  have hC_nonempty' := hC_nonempty
  rcases hC_nonempty with ⟨z, hz⟩
  refine ⟨⟨z, Set.mem_univ _⟩, ?_⟩
  rw [Set.mem_iInter]
  intro i
  rw [Function.mem_fixedPoints_iff]
  apply Subtype.ext
  -- Each point in the common intersection is fixed by every metric projector.
  have hzi : z ∈ C i := (Set.mem_iInter.mp hz) i
  exact
    projectionPoint_eq_self_of_mem
      (hC_nonempty := hC_nonempty') (hC_closed := hC_closed) (hC_convex := hC_convex)
      (i := i) hzi

/-- Helper for Example 30.4: the fixed points of the ambient cyclic projector composition are
exactly the common intersection `⋂ i, C i`. -/
private theorem fixedPoints_cyclicProjection_eq_iInter :
    Function.fixedPoints (finiteComposition (fun i ↦ P[C i, hFamily_cheb i])) = InterC := by
  let T : Fin m → H_univ → H_univ :=
    fun i z ↦ ⟨P[C i, hFamily_cheb i] z, Set.mem_univ _⟩
  have hAveraged : ∀ i, ∃ α, AveragedWith α (fun z : H_univ ↦ (T i z : H)) := by
    intro i
    refine ⟨(1 / 2 : ℝ), ?_⟩
    -- Reuse the projector averagedness on `Set.univ` for each factor.
    simpa [T] using
      projectorAveragedWithHalfOnUniv
        (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
        (i := i)
  have hfix_eq :
      Function.fixedPoints (finiteComposition T) = ⋂ i, Function.fixedPoints (T i) :=
    fixedPoints_finiteComposition_eq_iInter_fixedPoints_of_averagedWith
      (T := T) hAveraged
      (liftedProjectorFamily_fixedPoints_nonempty
        (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex))
  ext z
  constructor
  · intro hz
    have hz_univ :
        (⟨z, Set.mem_univ _⟩ : H_univ) ∈ Function.fixedPoints (finiteComposition T) := by
      rw [Function.mem_fixedPoints_iff] at hz ⊢
      apply Subtype.ext
      -- Coercing the lifted fixed-point equation recovers the ambient cyclic composition.
      simpa [T, finiteComposition_univFamily_coe] using hz
    have hz_iInter : (⟨z, Set.mem_univ _⟩ : H_univ) ∈ ⋂ i, Function.fixedPoints (T i) := by
      simpa [hfix_eq] using hz_univ
    rw [Set.mem_iInter]
    intro i
    have hz_fix_i : (⟨z, Set.mem_univ _⟩ : H_univ) ∈ Function.fixedPoints (T i) :=
      (Set.mem_iInter.mp hz_iInter) i
    rw [Function.mem_fixedPoints_iff] at hz_fix_i
    -- Fixed points of each projector are exactly the points of the corresponding set.
    have hz_eq : P[C i, hFamily_cheb i] z = z := congrArg Subtype.val hz_fix_i
    simpa [hz_eq] using projectionPoint_mem (C i) (hFamily_cheb i) z
  · intro hz
    have hz_iInter : (⟨z, Set.mem_univ _⟩ : H_univ) ∈ ⋂ i, Function.fixedPoints (T i) := by
      rw [Set.mem_iInter]
      intro i
      rw [Function.mem_fixedPoints_iff]
      apply Subtype.ext
      -- Membership in every `C i` makes the lifted projector family fix `z`.
      have hzi : z ∈ C i := (Set.mem_iInter.mp hz) i
      simpa [T] using
        (projectionPoint_eq_self_of_mem
          (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
          (i := i) hzi)
    have hz_univ : (⟨z, Set.mem_univ _⟩ : H_univ) ∈ Function.fixedPoints (finiteComposition T) := by
      simpa [hfix_eq] using hz_iInter
    rw [Function.mem_fixedPoints_iff] at hz_univ ⊢
    -- Coercing the lifted fixed-point equation returns the ambient cyclic fixed-point equation.
    simpa [T, finiteComposition_univFamily_coe] using congrArg Subtype.val hz_univ

/-- Helper for Example 30.4: the ambient cyclic projector composition is nonexpansive on
`Set.univ`. -/
private theorem cyclicProjection_lipschitzOnUniv :
    LipschitzOnWith 1 (finiteComposition (fun i ↦ P[C i, hFamily_cheb i])) Set.univ := by
  let T : Fin m → H_univ → H_univ :=
    fun i z ↦ ⟨P[C i, hFamily_cheb i] z, Set.mem_univ _⟩
  have hT_lip : ∀ i, LipschitzWith 1 (T i) := by
    intro i
    -- Each averaged projector factor is nonexpansive on `Set.univ`.
    exact
      lipschitzWithOneOfAveragedWithLocal
        (projectorAveragedWithHalfOnUniv
          (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
          (i := i))
  have hComp_lip : LipschitzWith 1 (finiteComposition T) :=
    lipschitzWith_finiteComposition T hT_lip
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro y hy z hz
  -- Restrict the lifted nonexpansive composition back to the ambient Hilbert space.
  simpa [T, Subtype.dist_eq, one_mul, finiteComposition_univFamily_coe] using
    hComp_lip.dist_le_mul ⟨y, hy⟩ ⟨z, hz⟩

/-- Helper for Example 30.4: the projection onto the cyclic composition fixed-point set is the
projection onto `⋂ i, C i`. -/
private theorem cyclicProjection_target_eq_projection_iInter (x : H)
    (hComp_cheb :
      IsChebyshev
        (fixedPointSetOn Set.univ (finiteComposition (fun i ↦ P[C i, hFamily_cheb i])))) :
    P[fixedPointSetOn Set.univ (finiteComposition (fun i ↦ P[C i, hFamily_cheb i])), hComp_cheb] x =
      P[InterC, hInter_cheb] x := by
  -- Replace the cyclic fixed-point target by the common intersection before projecting.
  apply eq_projectionPoint_of_isBestApproximation InterC hInter_cheb
  simpa [fixedPointSetOn_eq_inter_fixedPoints,
    fixedPoints_cyclicProjection_eq_iInter
      (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)] using
    projectionPoint_isBestApproximation
      (fixedPointSetOn Set.univ (finiteComposition (fun i ↦ P[C i, hFamily_cheb i])))
      hComp_cheb x

/- Source/core/bridge triage:
- `source-facing`: Example 30.4 states the two Halpern limits for weighted and cyclic projector
  families.
- `core/canonical`: the repository’s Chapter 30 Halpern owners are
  `halpern_iteration_tendsto_projection_iInter_fixedPointSetOn` and
  `halpern_iteration_tendsto_projection_commonFixedPoints_of_averaged_finiteComposition`.
- `bridge/view`: this file specializes those corollaries to the projector family
  `fun i ↦ P[C i, hFamily_cheb i]`, keeping the source-facing weighted-average operator
  `weighted_projection_average` and cyclic-composition operator `finiteComposition`.
-/

/-- Weighted-sequence half of Example 30.4: for a finite family `(C_i)_{i = 1}^m` of closed
convex subsets of a real Hilbert space with nonempty intersection, positive weights `ω_i` whose
sum is `1`, and `x, x₀ ∈ H`, the Halpern sequence generated by the weighted average
`∑ i, ω_i P_{C_i}` converges strongly to the metric projection of `x` onto `⋂ i, C_i`. -/
theorem halpern_weighted_projection_sequence_tendsto_projection_iInter
    (ω : Fin m → ℝ) (x x0 : H)
    (hω_pos : ∀ i, 0 < ω i) (hω_sum : ∑ i, ω i = 1) :
    Tendsto
      (halpernIteration (weighted_projection_average C ω hFamily_cheb)
        (fun n ↦ ((n + 2 : ℝ)⁻¹)) x x0)
      atTop
      (𝓝 (P[InterC, hInter_cheb] x)) := by
  let Proj : Fin m → H → H := fun i ↦ P[C i, hFamily_cheb i]
  have hProj_fixedPoints : ∀ i, Function.fixedPoints (Proj i) = C i := by
    intro i
    ext y
    rw [Function.mem_fixedPoints_iff]
    constructor
    · intro hy
      simpa [Proj, hy] using projectionPoint_mem (C i) (hFamily_cheb i) y
    · intro hy
      -- Membership in `C i` identifies the projector value with the point itself.
      simpa [Proj] using
        (projectionPoint_eq_self_of_mem
          (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
          (i := i) hy)
  have hProj_fixed : ∀ i, fixedPointSetOn Set.univ (Proj i) = C i := by
    intro i
    simp [fixedPointSetOn_eq_inter_fixedPoints, hProj_fixedPoints i]
  have hProj_iInter_cheb : IsChebyshev (⋂ i, fixedPointSetOn Set.univ (Proj i)) := by
    simpa [fixedPointSetOn_eq_inter_fixedPoints, hProj_fixedPoints] using hInter_cheb
  have hcor :
      Tendsto
        (halpernIteration (fun y ↦ ∑ i, ω i • Proj i y)
          (fun n ↦ ((n + 2 : ℝ)⁻¹)) x x0)
        atTop
        (𝓝 (P[⋂ i, fixedPointSetOn Set.univ (Proj i), hProj_iInter_cheb] x)) := by
    have hProj_nonexp : ∀ i, LipschitzOnWith 1 (Proj i) Set.univ := by
      intro i
      have hProj_lip : LipschitzWith 1 (fun z : H_univ ↦ Proj i z) :=
        lipschitzWithOneOfAveragedWithLocal
          (projectorAveragedWithHalfOnUniv
            (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
            (i := i))
      -- Restrict the global Lipschitz bound to `Set.univ`.
      refine LipschitzOnWith.of_dist_le_mul ?_
      intro y hy z hz
      simpa [Proj, Subtype.dist_eq, one_mul] using hProj_lip.dist_le_mul ⟨y, hy⟩ ⟨z, hz⟩
    have hProj_fix : (⋂ i, fixedPointSetOn Set.univ (Proj i)).Nonempty := by
      simpa [fixedPointSetOn_eq_inter_fixedPoints, hProj_fixedPoints] using hC_nonempty
    have hProj_maps : ∀ i, Set.MapsTo (Proj i) Set.univ Set.univ := by
      simp
    have hx_univ : x ∈ Set.univ := by
      trivial
    have hx0_univ : x0 ∈ Set.univ := by
      trivial
    have hlam_tendsto_zero :
        Tendsto (fun n : ℕ ↦ ((n + 2 : ℝ)⁻¹)) atTop (𝓝 (0 : ℝ)) := by
      have hshift : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
      -- The reciprocal of the shifted index still tends to zero.
      simpa [Nat.cast_add, one_div] using (tendsto_inv_atTop_zero.comp hshift)
    have hlam_successive_diff_summable :
        Summable (fun n : ℕ ↦ |(((n + 1 : ℕ) + 2 : ℝ)⁻¹) - ((n + 2 : ℝ)⁻¹)|) := by
      convert reciprocalHalpernParams_successiveDiffSummable using 1
      ext n
      norm_num [Nat.cast_add, add_assoc]
    -- Apply Corollary 30.2 to the concrete projector family.
    exact
      halpern_iteration_tendsto_projection_iInter_fixedPointSetOn
        isClosed_univ convex_univ
        hProj_nonexp
        hProj_fix
        hProj_maps
        hω_pos
        hω_sum
        hx_univ
        hx0_univ
        reciprocalHalpernParams_memIoo
        hlam_tendsto_zero
        reciprocalHalpernParams_sumDiverges
        hlam_successive_diff_summable
  have hProj_limit :
      P[⋂ i, fixedPointSetOn Set.univ (Proj i), hProj_iInter_cheb] x =
        P[InterC, hInter_cheb] x := by
    -- Identify the two projector targets through the fixed-point-set description.
    apply eq_projectionPoint_of_isBestApproximation InterC hInter_cheb
    simpa [fixedPointSetOn_eq_inter_fixedPoints, hProj_fixedPoints] using
      projectionPoint_isBestApproximation
        (⋂ i, fixedPointSetOn Set.univ (Proj i)) hProj_iInter_cheb x
  simpa [weighted_projection_average, Proj, fixedPointSetOn_eq_inter_fixedPoints,
    hProj_fixedPoints, hProj_limit] using hcor

/-- Example 30.4 (2): for a finite family `(C_i)_{i = 1}^m` of closed
convex subsets of a real Hilbert space with nonempty intersection, and `x, y₀ ∈ H`, the Halpern
sequence generated by the cyclic composition `P_{C_1} ⋯ P_{C_m}` converges strongly to the metric
projection of `x` onto `⋂ i, C_i`. -/
theorem halpern_cyclic_projection_sequence_tendsto_projection_iInter
    (x y0 : H) :
    Tendsto
      (halpernIteration (finiteComposition (fun i ↦ P[C i, hFamily_cheb i]))
        (fun n ↦ ((n + 2 : ℝ)⁻¹)) x y0)
      atTop
      (𝓝 (P[InterC, hInter_cheb] x)) := by
  classical
  have hlam_tendsto_zero :
      Tendsto (fun n : ℕ ↦ ((n + 2 : ℝ)⁻¹)) atTop (𝓝 (0 : ℝ)) := by
    have hshift : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    -- The same reciprocal parameter family tends to zero in the cyclic setting.
    simpa [Nat.cast_add, one_div] using (tendsto_inv_atTop_zero.comp hshift)
  let Proj : Fin m → H → H := fun i ↦ P[C i, hFamily_cheb i]
  have hComp_nonexp : LipschitzOnWith 1 (finiteComposition Proj) Set.univ := by
    -- Route correction: work directly with the ambient cyclic composition instead of the
    -- subtype-image target from Corollary 30.3.
    simpa [Proj] using
      cyclicProjection_lipschitzOnUniv
        (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
  have hFixEq : Function.fixedPoints (finiteComposition Proj) = InterC := by
    -- Public Corollary 4.51 identifies the cyclic fixed points with the common intersection.
    simpa [Proj] using
      fixedPoints_cyclicProjection_eq_iInter
        (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
  have hComp_fix_nonempty : (fixedPointSetOn Set.univ (finiteComposition Proj)).Nonempty := by
    simpa [fixedPointSetOn_eq_inter_fixedPoints, hFixEq] using hC_nonempty
  have hComp_closed_convex :
      IsClosed (fixedPointSetOn Set.univ (finiteComposition Proj)) ∧
        Convex ℝ (fixedPointSetOn Set.univ (finiteComposition Proj)) :=
    isClosed_and_convex_fixedPointSetOn_of_quasinonexpansive
      hComp_nonexp.quasinonexpansiveOn isClosed_univ convex_univ
  have hComp_cheb : IsChebyshev (fixedPointSetOn Set.univ (finiteComposition Proj)) :=
    isChebyshev_of_nonempty_isClosed_convex
      hComp_fix_nonempty hComp_closed_convex.1 hComp_closed_convex.2
  have hProjection :
      P[fixedPointSetOn Set.univ (finiteComposition Proj), hComp_cheb] x =
        P[InterC, hInter_cheb] x := by
    -- Once the fixed-point set is identified with `⋂ i, C i`, the projection target matches.
    simpa [Proj] using
      cyclicProjection_target_eq_projection_iInter
        (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
        x hComp_cheb
  have hlam_successive_diff_summable :
      Summable (fun n : ℕ ↦ |(((n + 1 : ℕ) + 2 : ℝ)⁻¹) - ((n + 2 : ℝ)⁻¹)|) := by
    convert reciprocalHalpernParams_successiveDiffSummable using 1
    ext n
    norm_num [Nat.cast_add, add_assoc]
  -- Apply Theorem 30.1 to the ambient cyclic projector composition on `Set.univ`.
  simpa only [Proj, hProjection] using
    (halpern_iteration_tendsto_projection_fixedPointSetOn
      (hD_closed := isClosed_univ) (hD_convex := convex_univ)
      (hT_nonexp := hComp_nonexp) (hFix_nonempty := hComp_fix_nonempty)
      (D := (Set.univ : Set H)) (T := finiteComposition Proj) (x := x) (x0 := y0)
      (lam := fun n ↦ ((n + 2 : ℝ)⁻¹))
      (by trivial)
      (by simp)
      (by trivial)
      reciprocalHalpernParams_memIoo
      hlam_tendsto_zero
      reciprocalHalpernParams_sumDiverges
      hlam_successive_diff_summable)

end

end
