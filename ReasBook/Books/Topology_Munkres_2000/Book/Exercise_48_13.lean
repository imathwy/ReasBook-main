module

public import Topology_Munkres_2000.Book.Exercise_46_11
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Ordered
public import Mathlib.Topology.Defs.Basic

universe u v

public section

namespace FineContinuousMap

variable (X : Type u) (Y : Type v) [TopologicalSpace X] [MetricSpace Y]

open Filter
open scoped Topology

/-- Helper for Exercise 48.13: a positive fine ball contains a smaller positive fine ball,
with radius at most one third of the original radius, inside any prescribed dense open set. -/
private lemma exists_ball_refinement_of_open_dense
    (f : FineContinuousMap X Y) (δ : C(X, ℝ)) (hδ : ∀ x, 0 < δ x)
    (U : Set (FineContinuousMap X Y)) (hUOpen : IsOpen U) (hUDense : Dense U) :
    ∃ g : FineContinuousMap X Y, ∃ ε : C(X, ℝ),
      (∀ x, 0 < ε x) ∧ (∀ x, ε x ≤ δ x / 3) ∧
        g ∈ ball X Y f ((1 / 3 : ℝ) • δ) ∧ ball X Y g ε ⊆ U := by
  -- First intersect the dense open set with the one-third ball.
  have hThirdFactorPositive : (0 : ℝ) < 1 / 3 := by norm_num
  have hThirdPositive : ∀ x, 0 < ((1 / 3 : ℝ) • δ) x := by
    intro x
    rw [ContinuousMap.smul_apply]
    exact smul_pos hThirdFactorPositive (hδ x)
  have hThirdBallEq :
      ball X Y f ((1 / 3 : ℝ) • δ) = ball X Y f ((1 / 3 : ℝ) • δ) := rfl
  have hThirdBasis : ball X Y f ((1 / 3 : ℝ) • δ) ∈ basis X Y :=
    (mem_basis_iff X Y _).mpr
      ⟨f, (1 / 3 : ℝ) • δ, hThirdPositive, hThirdBallEq⟩
  have hThirdOpen : IsOpen (ball X Y f ((1 / 3 : ℝ) • δ)) :=
    (basis_isTopologicalBasis X Y).isOpen hThirdBasis
  have hfThird : f ∈ ball X Y f ((1 / 3 : ℝ) • δ) := by
    apply (mem_ball X Y f f ((1 / 3 : ℝ) • δ)).mpr
    intro x
    simpa only [dist_self] using hThirdPositive x
  obtain ⟨h, hhThird, hhU⟩ :=
    hUDense.inter_open_nonempty (ball X Y f ((1 / 3 : ℝ) • δ))
      hThirdOpen ⟨f, hfThird⟩
  have hhIntersection : h ∈ ball X Y f ((1 / 3 : ℝ) • δ) ∩ U :=
    ⟨hhThird, hhU⟩
  have hIntersectionOpen : IsOpen (ball X Y f ((1 / 3 : ℝ) • δ) ∩ U) :=
    hThirdOpen.inter hUOpen
  obtain ⟨V, hVBasis, hhV, hVSubset⟩ :=
    (basis_isTopologicalBasis X Y).exists_subset_of_mem_open
      hhIntersection hIntersectionOpen
  obtain ⟨g, ε₀, hε₀, rfl⟩ := (mem_basis_iff X Y V).mp hVBasis
  -- Intersect the extracted radius with the one-third radius to retain both containments.
  let ε : C(X, ℝ) := ε₀ ⊓ ((1 / 3 : ℝ) • δ)
  have hεPositive : ∀ x, 0 < ε x := by
    intro x
    simpa only [ε, ContinuousMap.inf_apply, lt_inf_iff] using
      And.intro (hε₀ x) (hThirdPositive x)
  have hεLe : ∀ x, ε x ≤ δ x / 3 := by
    intro x
    have hInf : ε₀ x ⊓ ((1 / 3 : ℝ) * δ x) ≤ (1 / 3 : ℝ) * δ x := inf_le_right
    have hThirdEq : (1 / 3 : ℝ) * δ x = δ x / 3 := by ring
    simpa only [ε, ContinuousMap.inf_apply, ContinuousMap.smul_apply, smul_eq_mul] using
      hInf.trans_eq hThirdEq
  have hgε : g ∈ ball X Y g ε := by
    apply (mem_ball X Y g g ε).mpr
    intro x
    simpa only [dist_self] using hεPositive x
  have hSmallSubset : ball X Y g ε ⊆ ball X Y g ε₀ := by
    have hεMapLe : ε ≤ ε₀ := by
      exact inf_le_left
    intro k hk
    apply (mem_ball X Y g k ε₀).mpr
    intro x
    exact lt_of_lt_of_le ((mem_ball X Y g k ε).mp hk x)
      (hεMapLe x)
  have hgIntersection : g ∈ ball X Y f ((1 / 3 : ℝ) • δ) ∩ U :=
    hVSubset (hSmallSubset hgε)
  refine ⟨g, ε, hεPositive, hεLe, hgIntersection.1, ?_⟩
  -- The smaller ball stays inside the extracted ball, hence inside the dense open set.
  exact fun k hk ↦ (hVSubset (hSmallSubset hk)).2

/-- Helper for Exercise 48.13: from a sequence of dense open sets, one can recursively choose
positive fine balls with one-third radius decay whose successor balls lie in the prescribed sets. -/
private lemma exists_nested_balls_in_denseOpen
    (U : ℕ → Set (FineContinuousMap X Y))
    (hUOpen : ∀ n, IsOpen (U n)) (hUDense : ∀ n, Dense (U n))
    (f₀ : FineContinuousMap X Y) (δ₀ : C(X, ℝ)) (hδ₀ : ∀ x, 0 < δ₀ x) :
    ∃ f : ℕ → FineContinuousMap X Y, ∃ δ : ℕ → C(X, ℝ),
      f 0 = f₀ ∧ δ 0 = δ₀ ∧ (∀ n x, 0 < δ n x) ∧
        (∀ n x, δ (n + 1) x ≤ δ n x / 3) ∧
        (∀ n, f (n + 1) ∈ ball X Y (f n) ((1 / 3 : ℝ) • δ n)) ∧
        (∀ n, ball X Y (f (n + 1)) (δ (n + 1)) ⊆ U n) := by
  classical
  -- Package precisely the center and positive radius that must be carried through recursion.
  let S := {p : FineContinuousMap X Y × C(X, ℝ) // ∀ x, 0 < p.2 x}
  have hTransition : ∀ n (s : S), ∃ t : S,
      (∀ x, t.1.2 x ≤ s.1.2 x / 3) ∧
        t.1.1 ∈ ball X Y s.1.1 ((1 / 3 : ℝ) • s.1.2) ∧
        ball X Y t.1.1 t.1.2 ⊆ U n := by
    intro n s
    obtain ⟨g, ε, hεPositive, hεLe, hgThird, hεSubset⟩ :=
      exists_ball_refinement_of_open_dense X Y s.1.1 s.1.2 s.2
        (U n) (hUOpen n) (hUDense n)
    let t : S := ⟨(g, ε), hεPositive⟩
    refine ⟨t, ?_, ?_, ?_⟩
    · simpa only [t] using hεLe
    · simpa only [t] using hgThird
    · simpa only [t] using hεSubset
  let s₀ : S := ⟨(f₀, δ₀), hδ₀⟩
  let next : ℕ → S → S := fun n s ↦ Classical.choose (hTransition n s)
  let s : ℕ → S := Nat.rec s₀ (fun n current ↦ next n current)
  let f : ℕ → FineContinuousMap X Y := fun n ↦ (s n).1.1
  let δ : ℕ → C(X, ℝ) := fun n ↦ (s n).1.2
  have hfZero : f 0 = f₀ := by rfl
  have hδZero : δ 0 = δ₀ := by rfl
  have hδPositive : ∀ n x, 0 < δ n x := by
    intro n x
    exact (s n).2 x
  have hsSucc : ∀ n, s (n + 1) = next n (s n) := by
    intro n
    rfl
  have hNextSpec : ∀ n,
      (∀ x, (next n (s n)).1.2 x ≤ (s n).1.2 x / 3) ∧
        (next n (s n)).1.1 ∈
          ball X Y (s n).1.1 ((1 / 3 : ℝ) • (s n).1.2) ∧
        ball X Y (next n (s n)).1.1 (next n (s n)).1.2 ⊆ U n := by
    intro n
    simpa only [next] using Classical.choose_spec (hTransition n (s n))
  have hδStep : ∀ n x, δ (n + 1) x ≤ δ n x / 3 := by
    intro n x
    simpa only [δ, hsSucc n] using (hNextSpec n).1 x
  have hfStep : ∀ n, f (n + 1) ∈ ball X Y (f n) ((1 / 3 : ℝ) • δ n) := by
    intro n
    simpa only [f, δ, hsSucc n] using (hNextSpec n).2.1
  have hBallSubset : ∀ n, ball X Y (f (n + 1)) (δ (n + 1)) ⊆ U n := by
    intro n
    simpa only [f, δ, hsSucc n] using (hNextSpec n).2.2
  -- Unpack the recursive state into the center and radius sequences used by the limit lemma.
  exact ⟨f, δ, hfZero, hδZero, hδPositive, hδStep, hfStep, hBallSubset⟩

/-- Helper for Exercise 48.13: radii that shrink by a factor of three are bounded by the
corresponding global geometric sequence. -/
private lemma radius_le_geometric {ι : Type*} (δ : ℕ → ι → ℝ)
    (hδZero : ∀ x, δ 0 x ≤ 1)
    (hδStep : ∀ n x, δ (n + 1) x ≤ δ n x / 3) :
    ∀ n x, δ n x ≤ (1 / 3 : ℝ) ^ n := by
  -- Induction propagates the initial unit bound through every one-third contraction.
  have hThreeNonnegative : (0 : ℝ) ≤ 3 := by norm_num
  intro n
  induction n with
  | zero =>
      intro x
      simpa only [pow_zero] using hδZero x
  | succ n ih =>
      intro x
      calc
        δ (n + 1) x ≤ δ n x / 3 := hδStep n x
        _ ≤ (1 / 3 : ℝ) ^ n / 3 :=
          div_le_div_of_nonneg_right (ih x) hThreeNonnegative
        _ = (1 / 3 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

/-- Helper for Exercise 48.13: the radius after a shifted number of contractions is bounded
by the starting radius times the shifted geometric factor. -/
private lemma radius_add_le_geometric {ι : Type*} (δ : ℕ → ι → ℝ)
    (hδStep : ∀ n x, δ (n + 1) x ≤ δ n x / 3) :
    ∀ n k x, δ (n + k) x ≤ δ n x / 3 ^ k := by
  -- Induction on the shift retains the original radius as the geometric coefficient.
  have hThreeNonnegative : (0 : ℝ) ≤ 3 := by norm_num
  intro n k
  induction k with
  | zero =>
      intro x
      simp only [Nat.add_zero, pow_zero, div_one]
      exact le_rfl
  | succ k ih =>
      intro x
      calc
        δ (n + (k + 1)) x = δ ((n + k) + 1) x := by rw [Nat.add_assoc]
        _ ≤ δ (n + k) x / 3 := hδStep (n + k) x
        _ ≤ (δ n x / 3 ^ k) / 3 :=
          div_le_div_of_nonneg_right (ih x) hThreeNonnegative
        _ = δ n x / 3 ^ (k + 1) := by rw [pow_succ]; ring

/-- Helper for Exercise 48.13: a pointwise limit of continuous maps is continuous when their
successive distances have a uniform geometric bound. -/
private lemma continuous_of_pointwise_tendsto_of_geometric_steps
    (F : ℕ → FineContinuousMap X Y) (g : X → Y) (C r : ℝ)
    (hrNonnegative : 0 ≤ r) (hrLtOne : r < 1)
    (hStep : ∀ n x, dist (F n x) (F (n + 1) x) ≤ C * r ^ n)
    (hTendsto : ∀ x, Tendsto (fun n ↦ F n x) atTop (𝓝 (g x))) :
    Continuous g := by
  -- The geometric tail theorem gives a pointwise estimate with a uniform scalar bound.
  have hTail : ∀ n x, dist (F n x) (g x) ≤ C * r ^ n / (1 - r) := by
    intro n x
    have hStepAt : ∀ k, dist (F k x) (F (k + 1) x) ≤ C * r ^ k := by
      intro k
      exact hStep k x
    exact dist_le_of_le_geometric_of_tendsto r C hrLtOne hStepAt (hTendsto x) n
  have hBoundTendsto :
      Tendsto (fun n ↦ C * r ^ n / (1 - r)) atTop (𝓝 0) := by
    have hPow := tendsto_pow_atTop_nhds_zero_of_lt_one hrNonnegative hrLtOne
    simpa only [mul_zero, zero_div] using (hPow.const_mul C).div_const (1 - r)
  have hUniform : TendstoUniformly (fun n x ↦ F n x) g atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    refine ((tendsto_order.mp hBoundTendsto).2 ε hε).mono ?_
    intro n hn x
    rw [dist_comm]
    exact lt_of_le_of_lt (hTail n x) hn
  -- Uniform convergence transports continuity from every approximating map to the limit.
  have hFrequentlyContinuous : ∃ᶠ n in atTop,
      Continuous (equivContinuousMap X Y (F n)) := by
    exact Frequently.of_forall fun n ↦ (equivContinuousMap X Y (F n)).continuous
  exact hUniform.continuous hFrequentlyContinuous

variable [CompleteSpace Y]

/-- Helper for Exercise 48.13: geometrically shrinking fine balls whose next centers lie in
one-third subballs have a common point. -/
private lemma nested_ball_iInter_nonempty
    (f : ℕ → FineContinuousMap X Y) (δ : ℕ → C(X, ℝ))
    (hδPositive : ∀ n x, 0 < δ n x)
    (hδZero : ∀ x, δ 0 x ≤ 1)
    (hδStep : ∀ n x, δ (n + 1) x ≤ δ n x / 3)
    (hfStep : ∀ n, f (n + 1) ∈ ball X Y (f n) ((1 / 3 : ℝ) • δ n)) :
    (⋂ n, ball X Y (f n) (δ n)).Nonempty := by
  -- Global geometric bounds make every pointwise sequence of centers Cauchy.
  have hRatioNonnegative : (0 : ℝ) ≤ 1 / 3 := by norm_num
  have hRatioLtOne : (1 / 3 : ℝ) < 1 := by norm_num
  have hThreeNonnegative : (0 : ℝ) ≤ 3 := by norm_num
  have hRadiusGlobal : ∀ n x, δ n x ≤ (1 / 3 : ℝ) ^ n :=
    radius_le_geometric (fun n x ↦ δ n x) hδZero hδStep
  have hCenterGlobal : ∀ n x,
      dist (f n x) (f (n + 1) x) ≤ (1 / 3 : ℝ) * (1 / 3 : ℝ) ^ n := by
    intro n x
    have hCenter :=
      (mem_ball X Y (f n) (f (n + 1)) ((1 / 3 : ℝ) • δ n)).mp
        (hfStep n) x
    have hCenterThird :
        dist (f n x) (f (n + 1) x) ≤ (1 / 3 : ℝ) * δ n x := by
      simpa only [ContinuousMap.smul_apply, smul_eq_mul] using le_of_lt hCenter
    have hCenterScale : (1 / 3 : ℝ) * δ n x = δ n x / 3 := by ring
    calc
      dist (f n x) (f (n + 1) x) ≤ δ n x / 3 :=
        hCenterThird.trans_eq hCenterScale
      _ ≤ (1 / 3 : ℝ) ^ n / 3 :=
        div_le_div_of_nonneg_right (hRadiusGlobal n x) hThreeNonnegative
      _ = (1 / 3 : ℝ) * (1 / 3 : ℝ) ^ n := by ring
  have hPointwiseCauchy : ∀ x, CauchySeq (fun n ↦ f n x) := by
    intro x
    have hCenterGlobalAt : ∀ n,
        dist (f n x) (f (n + 1) x) ≤ (1 / 3 : ℝ) * (1 / 3 : ℝ) ^ n := by
      intro n
      exact hCenterGlobal n x
    exact cauchySeq_of_le_geometric (1 / 3) (1 / 3) hRatioLtOne hCenterGlobalAt
  classical
  have hPointwiseConverges : ∀ x, ∃ y, Tendsto (fun n ↦ f n x) atTop (𝓝 y) := by
    intro x
    exact cauchySeq_tendsto_of_complete (hPointwiseCauchy x)
  choose g hgTendsto using hPointwiseConverges
  have hgContinuous : Continuous g :=
    continuous_of_pointwise_tendsto_of_geometric_steps X Y f g (1 / 3) (1 / 3)
      hRatioNonnegative hRatioLtOne hCenterGlobal hgTendsto
  let gContinuous : C(X, Y) := ⟨g, hgContinuous⟩
  let gFine : FineContinuousMap X Y := (equivContinuousMap X Y).symm gContinuous
  have hgFineMap : equivContinuousMap X Y gFine = gContinuous :=
    (equivContinuousMap X Y).apply_symm_apply gContinuous
  have hgMem : gFine ∈ ⋂ n, ball X Y (f n) (δ n) := by
    apply Set.mem_iInter.mpr
    intro n
    apply (mem_ball X Y (f n) gFine (δ n)).mpr
    intro x
    -- A shifted geometric tail is at most half the current radius, hence strictly internal.
    have hRadiusShift : ∀ k, δ (n + k) x ≤ δ n x / 3 ^ k :=
      fun k ↦ radius_add_le_geometric (fun m y ↦ δ m y) hδStep n k x
    have hShiftStep : ∀ k,
        dist (f (n + k) x) (f (n + (k + 1)) x) ≤
          (δ n x / 3) * (1 / 3 : ℝ) ^ k := by
      intro k
      have hCenter :=
        (mem_ball X Y (f (n + k)) (f (n + k + 1))
          ((1 / 3 : ℝ) • δ (n + k))).mp
          (hfStep (n + k)) x
      have hCenterThird :
          dist (f (n + k) x) (f (n + k + 1) x) ≤
            (1 / 3 : ℝ) * δ (n + k) x := by
        simpa only [ContinuousMap.smul_apply, smul_eq_mul] using le_of_lt hCenter
      have hCenterScale :
          (1 / 3 : ℝ) * δ (n + k) x = δ (n + k) x / 3 := by ring
      calc
        dist (f (n + k) x) (f (n + (k + 1)) x) =
            dist (f (n + k) x) (f (n + k + 1) x) := by rw [Nat.add_assoc]
        _ ≤ δ (n + k) x / 3 := hCenterThird.trans_eq hCenterScale
        _ ≤ (δ n x / 3 ^ k) / 3 :=
          div_le_div_of_nonneg_right (hRadiusShift k) hThreeNonnegative
        _ = (δ n x / 3) * (1 / 3 : ℝ) ^ k := by
          simp only [div_eq_mul_inv, ← inv_pow]
          ring
    have hShiftTendsto : Tendsto (fun k ↦ f (n + k) x) atTop (𝓝 (g x)) := by
      have hRightShift :=
        (Filter.tendsto_add_atTop_iff_nat (f := fun k ↦ f k x) n).mpr (hgTendsto x)
      simpa only [Nat.add_comm] using hRightShift
    have hTail := dist_le_of_le_geometric_of_tendsto₀
      (1 / 3) (δ n x / 3) hRatioLtOne hShiftStep hShiftTendsto
    have hTailHalf : dist (f n x) (g x) ≤ δ n x / 2 := by
      calc
        dist (f n x) (g x) = dist (f (n + 0) x) (g x) := by rw [Nat.add_zero]
        _ ≤ (δ n x / 3) / (1 - (1 / 3 : ℝ)) := hTail
        _ = δ n x / 2 := by ring
    have hgFineApply : gFine x = g x := by
      rw [← equivContinuousMap_apply X Y gFine x, hgFineMap]
      rfl
    rw [hgFineApply]
    exact lt_of_le_of_lt hTailHalf (half_lt_self (hδPositive n x))
  exact ⟨gFine, hgMem⟩

/-- Exercise 48.13. The continuous maps from `X` to `Y` with the fine topology form a Baire
space when `Y` is a complete metric space. -/
instance instBaireSpace : BaireSpace (FineContinuousMap X Y) := by
  -- It suffices to meet the countable intersection inside every nonempty fine basis ball.
  refine ⟨?_⟩
  intro U hUOpen hUDense
  apply (basis_isTopologicalBasis X Y).dense_iff.mpr
  intro O hOBasis _hONonempty
  obtain ⟨f₀, δ, hδPositive, rfl⟩ := (mem_basis_iff X Y O).mp hOBasis
  -- Shrink the initial radius by one so that the geometric sequence has a uniform majorant.
  let δ₀ : C(X, ℝ) := δ ⊓ 1
  have hOnePositive : (0 : ℝ) < 1 := by norm_num
  have hδ₀Positive : ∀ x, 0 < δ₀ x := by
    intro x
    simpa only [δ₀, ContinuousMap.inf_apply, ContinuousMap.one_apply, lt_inf_iff] using
      And.intro (hδPositive x) hOnePositive
  have hδ₀Bound : ∀ x, δ₀ x ≤ 1 := by
    intro x
    simpa only [δ₀, ContinuousMap.inf_apply, ContinuousMap.one_apply] using
      (inf_le_right : δ x ⊓ (1 : ℝ) ≤ 1)
  have hδ₀Le : ∀ x, δ₀ x ≤ δ x := by
    intro x
    simpa only [δ₀, ContinuousMap.inf_apply, ContinuousMap.one_apply] using
      (inf_le_left : δ x ⊓ (1 : ℝ) ≤ δ x)
  obtain ⟨f, ρ, hfZero, hρZero, hρPositive, hρStep, hfStep, hBallSubset⟩ :=
    exists_nested_balls_in_denseOpen X Y U hUOpen hUDense f₀ δ₀ hδ₀Positive
  have hρZeroBound : ∀ x, ρ 0 x ≤ 1 := by
    intro x
    rw [hρZero]
    exact hδ₀Bound x
  obtain ⟨g, hgBalls⟩ :=
    nested_ball_iInter_nonempty X Y f ρ hρPositive
      hρZeroBound hρStep hfStep
  -- The common point remains in the original ball and every selected successor ball.
  have hgInitialSmall : g ∈ ball X Y f₀ δ₀ := by
    rw [← hfZero, ← hρZero]
    exact Set.mem_iInter.mp hgBalls 0
  have hgInitial : g ∈ ball X Y f₀ δ := by
    apply (mem_ball X Y f₀ g δ).mpr
    intro x
    exact lt_of_lt_of_le ((mem_ball X Y f₀ g δ₀).mp hgInitialSmall x) (hδ₀Le x)
  have hgDenseSets : g ∈ ⋂ n, U n := by
    apply Set.mem_iInter.mpr
    intro n
    exact hBallSubset n (Set.mem_iInter.mp hgBalls (n + 1))
  exact ⟨g, hgInitial, hgDenseSets⟩

end FineContinuousMap
