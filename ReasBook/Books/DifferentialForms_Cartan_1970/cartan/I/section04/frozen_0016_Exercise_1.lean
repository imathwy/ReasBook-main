import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Topology PowerSeries PowerSeries.WithPiTopology

open Filter
open PowerSeries

variable {K : Type u}

section Metric

variable [Ring K]

/-- The distance on `K⟦X⟧` obtained from the order of the difference of two formal power series. -/
noncomputable def powerSeriesOrderDist (S T : K⟦X⟧) : ℝ :=
  let _ : DecidableEq K⟦X⟧ := Classical.decEq _
  if S = T then 0 else Real.exp (-((S - T).order.toNat : ℝ))

/-- `powerSeriesOrderDist` vanishes on the diagonal. -/
-- Proof sketch: after choosing classical decidable equality, the defining `if` reduces to its
-- diagonal branch.
theorem powerSeriesOrderDist_self (S : K⟦X⟧) :
    powerSeriesOrderDist S S = 0 := by
  -- The diagonal case is exactly the zero branch of the defining `if`.
  simp [powerSeriesOrderDist]

/-- `powerSeriesOrderDist` is symmetric. -/
-- Proof sketch: rewrite `T - S` as `-(S - T)` and use invariance of the order under negation.
theorem powerSeriesOrderDist_comm (S T : K⟦X⟧) :
    powerSeriesOrderDist S T = powerSeriesOrderDist T S := by
  by_cases h : S = T
  · -- On the diagonal, both distances are zero.
    subst h
    simp [powerSeriesOrderDist_self]
  · have h' : T ≠ S := fun hTS ↦ h hTS.symm
    have hsub : T - S = -(S - T) := by
      abel_nf
    -- Away from the diagonal, the orders of `S - T` and `T - S` agree.
    rw [powerSeriesOrderDist, if_neg h, powerSeriesOrderDist, if_neg h']
    rw [hsub, PowerSeries.order_neg]

/-- `powerSeriesOrderDist` vanishes exactly on the diagonal. -/
-- Proof sketch: away from the diagonal the exponential term is strictly positive, so distance zero
-- can only occur when the defining `if` takes the diagonal branch.
@[simp] theorem powerSeriesOrderDist_eq_zero {S T : K⟦X⟧} :
    powerSeriesOrderDist S T = 0 ↔ S = T := by
  constructor
  · intro hdist
    by_contra hne
    -- Off the diagonal, the exponential branch is strictly positive.
    rw [powerSeriesOrderDist, if_neg hne] at hdist
    have hpos : 0 < Real.exp (-((S - T).order.toNat : ℝ)) := Real.exp_pos _
    linarith
  · rintro rfl
    exact powerSeriesOrderDist_self S

/-- Helper for Exercise 1: `powerSeriesOrderDist` is always nonnegative. -/
-- Proof sketch: either we are on the diagonal and the distance is `0`, or we are on the
-- exponential branch, which is positive.
theorem powerSeriesOrderDist_nonneg (S T : K⟦X⟧) :
    0 ≤ powerSeriesOrderDist S T := by
  by_cases h : S = T
  · simp [powerSeriesOrderDist, h]
  · simpa [powerSeriesOrderDist, h] using le_of_lt (Real.exp_pos (-((S - T).order.toNat : ℝ)))

/-- Helper for Exercise 1: the order metric is non-archimedean. -/
-- Proof sketch: rewrite `S - U` as `(S - T) + (T - U)`, apply
-- `PowerSeries.min_order_le_order_add`, and translate the resulting order inequality through the
-- decreasing function `n ↦ exp (-n)`.
theorem powerSeriesOrderDist_nonarchimedean (S T U : K⟦X⟧) :
    powerSeriesOrderDist S U ≤ max (powerSeriesOrderDist S T) (powerSeriesOrderDist T U) := by
  by_cases hSU : S = U
  · -- When the endpoints agree, the left-hand side vanishes.
    subst hSU
    rw [powerSeriesOrderDist_self]
    exact le_trans (powerSeriesOrderDist_nonneg S T) (le_max_left _ _)
  · by_cases hST : S = T
    · -- If `S = T`, the estimate is immediate from the right-hand side.
      subst hST
      simpa [powerSeriesOrderDist_self] using
        (le_max_right (powerSeriesOrderDist T T) (powerSeriesOrderDist T U))
    · by_cases hTU : T = U
      · -- If `T = U`, the estimate is immediate from the right-hand side.
        subst hTU
        simpa [powerSeriesOrderDist_self] using
          (le_max_left (powerSeriesOrderDist S T) (powerSeriesOrderDist T T))
      · have hsum : S - U = (S - T) + (T - U) := by
          abel_nf
        have horder :
            min (S - T).order (T - U).order ≤ (S - U).order := by
          rw [hsum]
          exact PowerSeries.min_order_le_order_add (S - T) (T - U)
        have hST_top : (S - T).order ≠ ⊤ := by
          exact PowerSeries.order_eq_top.not.mpr (sub_ne_zero.mpr hST)
        have hTU_top : (T - U).order ≠ ⊤ := by
          exact PowerSeries.order_eq_top.not.mpr (sub_ne_zero.mpr hTU)
        have hSU_top : (S - U).order ≠ ⊤ := by
          exact PowerSeries.order_eq_top.not.mpr (sub_ne_zero.mpr hSU)
        have hmain :
            Real.exp (-((S - U).order.toNat : ℝ)) ≤
              max (Real.exp (-((S - T).order.toNat : ℝ)))
                (Real.exp (-((T - U).order.toNat : ℝ))) := by
          rcases le_total (S - T).order (T - U).order with hmin | hmin
          · have horderST : (S - T).order ≤ (S - U).order := by
              simpa [min_eq_left hmin] using horder
            have htoNatST : (S - T).order.toNat ≤ (S - U).order.toNat :=
              ENat.toNat_le_toNat horderST hSU_top
            have hminNat : (S - T).order.toNat ≤ (T - U).order.toNat :=
              ENat.toNat_le_toNat hmin hTU_top
            have hmax :
              max (Real.exp (-((S - T).order.toNat : ℝ)))
                  (Real.exp (-((T - U).order.toNat : ℝ))) =
                Real.exp (-((S - T).order.toNat : ℝ)) := by
              apply max_eq_left
              exact Real.exp_le_exp.mpr <| by
                exact neg_le_neg (show ((S - T).order.toNat : ℝ) ≤ (T - U).order.toNat by
                  exact_mod_cast hminNat)
            have hle :
                Real.exp (-((S - U).order.toNat : ℝ)) ≤
                  Real.exp (-((S - T).order.toNat : ℝ)) := by
              apply Real.exp_le_exp.mpr
              have hcast :
                  (((S - T).order.toNat : ℕ) : ℝ) ≤ (S - U).order.toNat := by
                exact_mod_cast htoNatST
              linarith
            simpa [hmax] using hle
          · have horderTU : (T - U).order ≤ (S - U).order := by
              simpa [min_eq_right hmin] using horder
            have htoNatTU : (T - U).order.toNat ≤ (S - U).order.toNat :=
              ENat.toNat_le_toNat horderTU hSU_top
            have hminNat : (T - U).order.toNat ≤ (S - T).order.toNat :=
              ENat.toNat_le_toNat hmin hST_top
            have hmax :
              max (Real.exp (-((S - T).order.toNat : ℝ)))
                  (Real.exp (-((T - U).order.toNat : ℝ))) =
                Real.exp (-((T - U).order.toNat : ℝ)) := by
              apply max_eq_right
              exact Real.exp_le_exp.mpr <| by
                exact neg_le_neg (show ((T - U).order.toNat : ℝ) ≤ (S - T).order.toNat by
                  exact_mod_cast hminNat)
            have hle :
                Real.exp (-((S - U).order.toNat : ℝ)) ≤
                  Real.exp (-((T - U).order.toNat : ℝ)) := by
              apply Real.exp_le_exp.mpr
              have hcast :
                  (((T - U).order.toNat : ℕ) : ℝ) ≤ (S - U).order.toNat := by
                exact_mod_cast htoNatTU
              linarith
            simpa [hmax] using hle
        -- After excluding the diagonal branches, the estimate is exactly `hmain`.
        simpa [powerSeriesOrderDist, hSU, hST, hTU] using hmain

/-- `powerSeriesOrderDist` satisfies the triangle inequality. -/
-- Proof sketch: use the non-archimedean estimate
-- `min (S - T).order (T - U).order ≤ (S - U).order`, then translate it through the monotonicity
-- of `x ↦ exp (-x)` and conclude with `max a b ≤ a + b`.
theorem powerSeriesOrderDist_triangle (S T U : K⟦X⟧) :
    powerSeriesOrderDist S U ≤ powerSeriesOrderDist S T + powerSeriesOrderDist T U := by
  -- First use the ultrametric bound coming from the order valuation.
  refine le_trans (powerSeriesOrderDist_nonarchimedean S T U) ?_
  -- Then dominate the maximum by the sum using nonnegativity of both terms.
  refine max_le_iff.mpr ?_
  constructor
  · exact le_add_of_nonneg_right (powerSeriesOrderDist_nonneg T U)
  · exact le_add_of_nonneg_left (powerSeriesOrderDist_nonneg S T)

/-- Exercise 1 (1): the exponential of minus the order of a difference gives a metric on
`K⟦X⟧`. -/
@[reducible] noncomputable def powerSeriesOrderMetric : MetricSpace K⟦X⟧ where
  dist := powerSeriesOrderDist
  dist_self := powerSeriesOrderDist_self
  dist_comm := powerSeriesOrderDist_comm
  dist_triangle := powerSeriesOrderDist_triangle
  eq_of_dist_eq_zero := powerSeriesOrderDist_eq_zero.mp

/-- The distance of `powerSeriesOrderMetric` is `powerSeriesOrderDist`. -/
@[simp] theorem powerSeriesOrderMetric_dist (S T : K⟦X⟧) :
    letI : MetricSpace K⟦X⟧ := powerSeriesOrderMetric
    dist S T = powerSeriesOrderDist S T := rfl

/-- Helper for Exercise 1: the distance between `S` and `T` only depends on `S - T`. -/
-- Proof sketch: after unfolding the definition, the two distances use the same order term
-- because `((S - T) - 0) = S - T`.
theorem powerSeriesOrderDist_sub_eq_zero (S T : K⟦X⟧) :
    powerSeriesOrderDist S T = powerSeriesOrderDist (S - T) 0 := by
  by_cases h : S = T
  · subst h
    simp [powerSeriesOrderDist_self]
  · have hsub : S - T ≠ 0 := sub_ne_zero.mpr h
    rw [powerSeriesOrderDist, if_neg h, powerSeriesOrderDist, if_neg hsub]
    simp

/-- Helper for Exercise 1: a metric ball for the order metric is exactly the cylinder where the
first coefficients agree. -/
-- Proof sketch: membership in the ball means the order of `T - S` is greater than `m`, which is
-- equivalent to vanishing of all coefficients below `m + 1`; rewriting those vanishing statements
-- gives agreement of the first `m + 1` coefficients of `T` and `S`.
theorem mem_ball_powerSeriesOrderDist_iff_coeff_eq (S T : K⟦X⟧) (m : ℕ) :
    letI : MetricSpace K⟦X⟧ := powerSeriesOrderMetric
    T ∈ Metric.ball S (Real.exp (-(m : ℝ))) ↔ ∀ n < m + 1, coeff n T = coeff n S := by
  letI : MetricSpace K⟦X⟧ := powerSeriesOrderMetric
  constructor
  · intro hball n hn
    by_cases hTS : T = S
    · -- On the diagonal, coefficient agreement is immediate.
      simpa [hTS]
    · have hdist : powerSeriesOrderDist T S < Real.exp (-(m : ℝ)) := by
        simpa [powerSeriesOrderMetric_dist] using hball
      rw [powerSeriesOrderDist, if_neg hTS] at hdist
      have horder : m < (T - S).order.toNat := by
        have hexp : -(((T - S).order.toNat : ℝ)) < -(m : ℝ) := Real.exp_lt_exp.mp hdist
        by_contra hnot
        have hle : (T - S).order.toNat ≤ m := Nat.not_lt.mp hnot
        have hcast : -(m : ℝ) ≤ -((T - S).order.toNat : ℝ) := by
          exact neg_le_neg (show ((T - S).order.toNat : ℝ) ≤ m by exact_mod_cast hle)
        linarith
      have hcoeff : coeff n (T - S) = 0 :=
        PowerSeries.coeff_of_lt_order_toNat n <|
          lt_of_le_of_lt (Nat.le_of_lt_succ hn) horder
      -- Vanishing of the `n`th coefficient of `T - S` is exactly coefficient agreement.
      exact sub_eq_zero.mp (by simpa using hcoeff)
  · intro hcoeff
    by_cases hTS : T = S
    · -- The diagonal point belongs to every positive-radius ball.
      simpa [hTS, powerSeriesOrderMetric_dist] using
        (Metric.mem_ball_self (x := S) (Real.exp_pos _))
    · have hvanish : ∀ n < m + 1, coeff n (T - S) = 0 := by
        intro n hn
        simpa [hcoeff n hn]
      have horder : ↑(m + 1) ≤ (T - S).order :=
        PowerSeries.nat_le_order (T - S) (m + 1) hvanish
      have horder_top : (T - S).order ≠ ⊤ := by
        exact PowerSeries.order_eq_top.not.mpr (sub_ne_zero.mpr hTS)
      have htoNat : m + 1 ≤ (T - S).order.toNat := ENat.toNat_le_toNat horder horder_top
      have hdist :
          powerSeriesOrderDist T S < Real.exp (-(m : ℝ)) := by
        rw [powerSeriesOrderDist, if_neg hTS]
        apply Real.exp_lt_exp.mpr
        have hcast : (m : ℝ) < (T - S).order.toNat := by
          exact_mod_cast lt_of_lt_of_le (Nat.lt_succ_self m) htoNat
        linarith
      simpa [powerSeriesOrderMetric_dist] using hdist

end Metric

section Topological

open PowerSeries.WithPiTopology

section RingTopology

variable [Ring K] [TopologicalSpace K] [DiscreteTopology K]

/-- Helper for Exercise 1: in the coefficientwise topology, fixing finitely many coefficients is a
neighborhood condition. -/
-- Proof sketch: prove this by induction on the number of constrained coefficients; each step adds
-- one more coefficient equality, which is the preimage of a singleton under a continuous
-- coefficient map.
theorem coeff_cylinder_mem_nhds (S : K⟦X⟧) (m : ℕ) :
    {T : K⟦X⟧ | ∀ n < m, coeff n T = coeff n S} ∈ 𝓝 S := by
  induction m with
  | zero =>
      -- With no coefficient conditions, the cylinder is the whole space.
      simpa using Filter.univ_mem
  | succ m ih =>
      have hprev :
          {T : K⟦X⟧ | ∀ n < m, coeff n T = coeff n S} ∈ 𝓝 S := ih
      have hcoeff :
          {T : K⟦X⟧ | coeff m T = coeff m S} ∈ 𝓝 S := by
        -- A singleton is open in the discrete coefficient space.
        have hpre :
            (fun T : K⟦X⟧ ↦ coeff m T) ⁻¹' ({coeff m S} : Set K) ∈ 𝓝 S := by
          refine ((PowerSeries.WithPiTopology.continuous_coeff K m).isOpen_preimage _ <|
            isOpen_discrete _).mem_nhds ?_
          simp
        simpa using hpre
      have hset :
          {T : K⟦X⟧ | ∀ n < m + 1, coeff n T = coeff n S} =
            {T : K⟦X⟧ | ∀ n < m, coeff n T = coeff n S} ∩
              {T : K⟦X⟧ | coeff m T = coeff m S} := by
        ext T
        constructor
        · intro hT
          constructor
          · intro n hn
            exact hT n (Nat.lt_succ_of_lt hn)
          · exact hT m (Nat.lt_succ_self m)
        · rintro ⟨hT, hm⟩ n hn
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hn) with hnm | rfl
          · exact hT n hnm
          · exact hm
      -- Finite intersections of coefficient cylinders stay in the neighborhood filter.
      rw [hset]
      exact inter_mem hprev hcoeff

/-- The order metric induces the canonical coefficientwise topology on `K⟦X⟧`. -/
theorem powerSeriesOrderMetric_toTopologicalSpace_eq :
    powerSeriesOrderMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      instTopologicalSpace K := by
  let tMetric : TopologicalSpace K⟦X⟧ :=
    powerSeriesOrderMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  change tMetric = instTopologicalSpace K
  letI : PseudoMetricSpace K⟦X⟧ := powerSeriesOrderMetric.toPseudoMetricSpace
  have hforward :
      @Continuous K⟦X⟧ K⟦X⟧
        tMetric
        (instTopologicalSpace K)
        id := by
    rw [continuous_iff_continuousAt]
    intro S
    rw [ContinuousAt]
    letI : TopologicalSpace K⟦X⟧ := instTopologicalSpace K
    show Filter.Tendsto id (@nhds K⟦X⟧ tMetric S) (𝓝 S)
    refine (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto
      (R := K) (f := id) (u := @nhds K⟦X⟧ tMetric S) (g := S)).2 ?_
    intro n
    have htarget :
        (𝓝 ((PowerSeries.coeff (R := K) n) (id S)) : Filter K) =
          pure ((PowerSeries.coeff (R := K) n) (id S)) := by
      simpa [nhds_discrete]
    rw [htarget, Filter.tendsto_pure]
    have hballmem :
        Metric.ball S (Real.exp (-(n : ℝ))) ∈ @nhds K⟦X⟧ tMetric S := by
      simpa [tMetric] using (Metric.ball_mem_nhds S (Real.exp_pos (-(n : ℝ))))
    refine Filter.mem_of_superset hballmem ?_
    intro T hT
    -- The ball/cylinder description turns metric closeness into equality of the `n`th coefficient.
    exact (mem_ball_powerSeriesOrderDist_iff_coeff_eq (S := S) (T := T) (m := n)).mp hT n
      (Nat.lt_succ_self n)
  have hback :
      @Continuous K⟦X⟧ K⟦X⟧
        (instTopologicalSpace K)
        tMetric
        id := by
    rw [continuous_def]
    intro s hs
    rw [show @IsOpen K⟦X⟧ (instTopologicalSpace K) s ↔
      ∀ x ∈ s, s ∈ @nhds K⟦X⟧ (instTopologicalSpace K) x from isOpen_iff_mem_nhds]
    intro S hS
    -- Metric openness provides a ball around `S`, which we then replace by a coefficient cylinder.
    have hsMetric :
        @IsOpen K⟦X⟧ powerSeriesOrderMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          s := by
      simpa [tMetric] using hs
    rcases Metric.isOpen_iff.mp hsMetric S hS with ⟨ε, hε, hεsub⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, Real.exp (-(m : ℝ)) < ε := by
      obtain ⟨m, hm⟩ := exists_nat_gt (-Real.log ε)
      refine ⟨m, ?_⟩
      calc
        Real.exp (-(m : ℝ)) < Real.exp (Real.log ε) := by
          apply Real.exp_lt_exp.mpr
          have hcast : (-Real.log ε) < (m : ℝ) := by exact_mod_cast hm
          linarith
        _ = ε := Real.exp_log hε
    have hball :
        {T : K⟦X⟧ | ∀ n < m + 1, coeff n T = coeff n S} ⊆ s := by
      intro T hT
      apply hεsub
      exact lt_trans
        ((mem_ball_powerSeriesOrderDist_iff_coeff_eq (S := S) (T := T) (m := m)).mpr hT)
        hm
    exact Filter.mem_of_superset (coeff_cylinder_mem_nhds (K := K) S (m + 1)) hball
  -- We compare the two topologies by proving that the identity map is continuous both ways.
  apply le_antisymm
  · exact continuous_id_iff_le.mp hforward
  · exact continuous_id_iff_le.mp hback

/- Exercise 1 (2) and (3): after `powerSeriesOrderMetric_toTopologicalSpace_eq`, continuity of
addition and multiplication is exactly the canonical topological-ring structure from
`PowerSeries.WithPiTopology`. -/
recall PowerSeries.WithPiTopology.instIsTopologicalRing

end RingTopology

section DenseRange

variable [CommSemiring K] [TopologicalSpace K] [DiscreteTopology K]

/- Exercise 1 (4): after `powerSeriesOrderMetric_toTopologicalSpace_eq`, density of the polynomial
inclusion is exactly `PowerSeries.WithPiTopology.denseRange_toPowerSeries`. -/
recall PowerSeries.WithPiTopology.denseRange_toPowerSeries

end DenseRange

section Derivative

variable [CommRing K] [TopologicalSpace K] [DiscreteTopology K]

/-- Exercise 1 (6): formal differentiation is continuous for the metric defined by
`powerSeriesOrderMetric`. -/
-- Proof sketch: first work in the canonical coefficientwise topology, where continuity follows
-- from `PowerSeries.coeff_derivative` and
-- `PowerSeries.WithPiTopology.continuous_coeff`; this is the topology identified with the metric
-- topology by `powerSeriesOrderMetric_toTopologicalSpace_eq`.
theorem powerSeriesOrderMetric_derivative_continuous :
    @Continuous K⟦X⟧ K⟦X⟧
      powerSeriesOrderMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      powerSeriesOrderMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (d⁄dX K : K⟦X⟧ → K⟦X⟧) := by
  letI : TopologicalSpace K⟦X⟧ := instTopologicalSpace K
  have hcont :
      @Continuous K⟦X⟧ K⟦X⟧ (instTopologicalSpace K) (instTopologicalSpace K)
        (d⁄dX K : K⟦X⟧ → K⟦X⟧) := by
    simp only [continuous_iff_continuousAt]
    intro S
    change Filter.Tendsto (d⁄dX K : K⟦X⟧ → K⟦X⟧) (𝓝 S) (𝓝 ((d⁄dX K) S))
    rw [tendsto_iff_coeff_tendsto]
    intro n
    have hcoeff : Continuous fun T : K⟦X⟧ ↦ coeff n ((d⁄dX K) T) := by
      simpa [coeff_derivative] using (continuous_coeff K (n + 1)).mul continuous_const
    exact hcoeff.continuousAt
  -- Route correction: rewrite both source and target topologies through the explicit metric topology.
  simpa [powerSeriesOrderMetric_toTopologicalSpace_eq (K := K)] using hcont

end Derivative

end Topological

section Uniform

open PowerSeries.WithPiTopology

variable [Ring K] [UniformSpace K] [DiscreteUniformity K]

/-- The order metric induces the canonical coefficientwise uniform structure on `K⟦X⟧`. -/
theorem powerSeriesOrderMetric_toUniformSpace_eq :
    powerSeriesOrderMetric.toPseudoMetricSpace.toUniformSpace =
      instUniformSpace K := by
  let uMetric : UniformSpace K⟦X⟧ := powerSeriesOrderMetric.toPseudoMetricSpace.toUniformSpace
  change uMetric = instUniformSpace K
  letI : PseudoMetricSpace K⟦X⟧ := powerSeriesOrderMetric.toPseudoMetricSpace
  -- Both uniformities come from subtraction and the neighborhood filter at `0`.
  apply UniformSpace.ext
  change @uniformity K⟦X⟧ uMetric = @uniformity K⟦X⟧ (instUniformSpace K)
  have hnhds :
      @nhds K⟦X⟧ uMetric.toTopologicalSpace 0 =
        @nhds K⟦X⟧ (instTopologicalSpace K) 0 := by
    simpa [uMetric] using congrArg (fun t : TopologicalSpace K⟦X⟧ => @nhds K⟦X⟧ t 0)
      (powerSeriesOrderMetric_toTopologicalSpace_eq (K := K))
  have hmetric :
      @uniformity K⟦X⟧ uMetric =
        comap (fun p : K⟦X⟧ × K⟦X⟧ ↦ p.1 - p.2)
          (((𝓝 (0 : ℝ)).comap fun q : K⟦X⟧ ↦ dist q 0)) := by
    calc
      @uniformity K⟦X⟧ uMetric =
          comap (fun p : K⟦X⟧ × K⟦X⟧ ↦ dist p.1 p.2) (𝓝 (0 : ℝ)) := by
            simpa [uMetric] using (Metric.uniformity_eq_comap_nhds_zero (α := K⟦X⟧))
      _ =
          comap (fun p : K⟦X⟧ × K⟦X⟧ ↦ p.1 - p.2)
            (((𝓝 (0 : ℝ)).comap fun q : K⟦X⟧ ↦ dist q 0)) := by
            rw [comap_comap]
            congr
            ext p
            simpa [powerSeriesOrderMetric_dist, powerSeriesOrderDist_sub_eq_zero]
  calc
    @uniformity K⟦X⟧ uMetric =
        comap (fun p : K⟦X⟧ × K⟦X⟧ ↦ p.1 - p.2)
          (((𝓝 (0 : ℝ)).comap fun q : K⟦X⟧ ↦ dist q 0)) := hmetric
    _ =
        comap (fun p : K⟦X⟧ × K⟦X⟧ ↦ p.1 - p.2)
          (@nhds K⟦X⟧ uMetric.toTopologicalSpace 0) := by
          -- The metric neighborhood filter at `0` is the pullback of `𝓝 0` along `q ↦ dist q 0`.
          simpa [uMetric] using congrArg
            (comap (fun p : K⟦X⟧ × K⟦X⟧ ↦ p.1 - p.2))
            (nhds_comap_dist (a := (0 : K⟦X⟧)))
    _ =
        comap (fun p : K⟦X⟧ × K⟦X⟧ ↦ p.1 - p.2)
          (@nhds K⟦X⟧ (instTopologicalSpace K) 0) := by
          rw [hnhds]
    _ = @uniformity K⟦X⟧ (instUniformSpace K) := by
          letI : UniformSpace K⟦X⟧ := instUniformSpace K
          simpa using (uniformity_eq_comap_nhds_zero_swapped K⟦X⟧).symm

/- Exercise 1 (5): after `powerSeriesOrderMetric_toUniformSpace_eq`, completeness is exactly the
canonical `PowerSeries.WithPiTopology.instCompleteSpace`. -/
recall PowerSeries.WithPiTopology.instCompleteSpace

end Uniform
