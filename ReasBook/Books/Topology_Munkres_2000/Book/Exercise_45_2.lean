module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.UniformSpace.UniformConvergence

public section

open Filter

universe u v

/-- Exercise 45.2 (1). A finite family of continuous maps into a metric space is
equicontinuous. -/
theorem equicontinuous_of_finite
    {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y] {𝓕 : Set (X → Y)}
    (h𝓕 : 𝓕.Finite) (h_continuous : ∀ f ∈ 𝓕, Continuous f) :
    𝓕.Equicontinuous := by
  -- Regard the finite set as its finite subtype, then use the finite-family criterion.
  classical
  letI : Fintype 𝓕 := h𝓕.fintype
  exact equicontinuous_finite.mpr fun f ↦ h_continuous f f.property

/-- Helper for Exercise 45.2: a uniformly convergent sequence of continuous maps is
equicontinuous at each point. -/
lemma equicontinuousAt_of_tendstoUniformlySequence
    {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    {f : ℕ → X → Y} {g : X → Y} (h_continuous : ∀ n, Continuous (f n))
    (h_uniform : TendstoUniformly f g atTop) (x₀ : X) :
    EquicontinuousAt f x₀ := by
  -- Choose one index after which every function is uniformly close to the limit.
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hε6 : 0 < ε / 6 := by
    positivity
  obtain ⟨N, h_tail⟩ := eventually_atTop.mp
    (Metric.tendstoUniformly_iff.mp h_uniform (ε / 6) hε6)
  -- The finitely many functions through index `N` share one neighborhood at `x₀`.
  have h_head : Equicontinuous (fun j : Fin (N + 1) ↦ f j) := by
    rw [equicontinuous_finite]
    intro j
    exact h_continuous j
  have hε3 : 0 < ε / 3 := by
    positivity
  have h_head_eventually :
      ∀ᶠ x in nhds x₀, ∀ j : Fin (N + 1), dist (f j x₀) (f j x) < ε / 3 :=
    Metric.equicontinuousAt_iff_right.mp (h_head x₀) (ε / 3) hε3
  filter_upwards [h_head_eventually] with x hx i
  by_cases hi : i ≤ N
  · -- An index in the finite head is controlled directly by its common neighborhood.
    let j : Fin (N + 1) := ⟨i, Nat.lt_succ_iff.mpr hi⟩
    have hj := hx j
    simp only [j] at hj
    linarith
  · -- A tail index is compared to the fixed head term `f N` through the limit at both points.
    have hNi : N ≤ i := Nat.le_of_lt (Nat.lt_of_not_ge hi)
    have hi_x₀ := h_tail i hNi x₀
    have hi_x := h_tail i hNi x
    have hN_x₀ := h_tail N le_rfl x₀
    have hN_x := h_tail N le_rfl x
    have h_head_N : dist (f N x₀) (f N x) < ε / 3 :=
      hx ⟨N, Nat.lt_succ_self N⟩
    calc
      dist (f i x₀) (f i x) ≤ dist (f i x₀) (g x₀) + dist (g x₀) (f i x) :=
        dist_triangle _ _ _
      _ ≤ dist (f i x₀) (g x₀) +
          (dist (g x₀) (f N x₀) + dist (f N x₀) (f i x)) := by
        gcongr
        exact dist_triangle _ _ _
      _ ≤ dist (f i x₀) (g x₀) +
          (dist (g x₀) (f N x₀) +
            (dist (f N x₀) (f N x) + dist (f N x) (f i x))) := by
        gcongr
        exact dist_triangle _ _ _
      _ ≤ dist (f i x₀) (g x₀) +
          (dist (g x₀) (f N x₀) +
            (dist (f N x₀) (f N x) +
              (dist (f N x) (g x) + dist (g x) (f i x)))) := by
        gcongr
        exact dist_triangle _ _ _
      _ < ε := by
        rw [dist_comm (f i x₀) (g x₀), dist_comm (f N x) (g x)]
        linarith

/-- Exercise 45.2 (2). A uniformly convergent sequence of continuous maps into a
metric space is equicontinuous. -/
theorem equicontinuous_of_tendstoUniformly
    {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    {f : ℕ → X → Y} {g : X → Y} (h_continuous : ∀ n, Continuous (f n))
    (h_uniform : TendstoUniformly f g atTop) :
    Equicontinuous f := by
  -- Apply the pointwise finite-head/uniform-tail argument at every point.
  intro x₀
  exact equicontinuousAt_of_tendstoUniformlySequence h_continuous h_uniform x₀

/-- Helper for Exercise 45.2: a common derivative bound on a ball gives a common
Lipschitz bound there. -/
lemma familyLipschitzOn_ball_of_deriv_bound
    {𝓕 : Set (ℝ → ℝ)} (h_differentiable : ∀ f ∈ 𝓕, Differentiable ℝ f)
    {x₀ r : ℝ} {M : NNReal}
    (h_bound : ∀ f ∈ 𝓕, ∀ y ∈ Metric.ball x₀ r, ‖deriv f y‖₊ ≤ M) :
    ∀ f ∈ 𝓕, LipschitzOnWith M f (Metric.ball x₀ r) := by
  -- Apply the one-dimensional mean value theorem on the convex ball.
  intro f hf
  exact Convex.lipschitzOnWith_of_nnnorm_deriv_le
    (fun y _ ↦ (h_differentiable f hf).differentiableAt)
    (h_bound f hf) (convex_ball x₀ r)

/-- Helper for Exercise 45.2: a family with one Lipschitz constant on a neighborhood is
equicontinuous at the neighborhood's center. -/
lemma equicontinuousAt_of_common_lipschitzOn_nhds
    {ι : Type*} {F : ι → ℝ → ℝ} {s : Set ℝ} {x₀ : ℝ} {M : NNReal}
    (hs : s ∈ nhds x₀) (h_lipschitz : ∀ i, LipschitzOnWith M (F i) s) :
    EquicontinuousAt F x₀ := by
  -- Use the common linear modulus `M * dist x₀ x` on the given neighborhood.
  apply Metric.equicontinuousAt_of_continuity_modulus
    (fun x ↦ (M : ℝ) * dist x₀ x)
  · have h_modulus : ContinuousAt (fun x : ℝ ↦ (M : ℝ) * dist x₀ x) x₀ :=
      continuousAt_const.mul
        ((continuousAt_const : ContinuousAt (fun _ : ℝ ↦ x₀) x₀).dist continuousAt_id)
    have h_value : (fun x : ℝ ↦ (M : ℝ) * dist x₀ x) x₀ = 0 := by
      simp
    rw [← h_value]
    exact h_modulus
  · filter_upwards [hs] with x hx i
    exact (h_lipschitz i).dist_le_mul x₀ (mem_of_mem_nhds hs) x hx

/-- Exercise 45.2 (3). A family of differentiable real functions whose derivatives
are uniformly bounded on a neighborhood of each point is equicontinuous. -/
theorem equicontinuous_of_locally_bounded_deriv
    {𝓕 : Set (ℝ → ℝ)} (h_differentiable : ∀ f ∈ 𝓕, Differentiable ℝ f)
    (h_bound : ∀ x : ℝ, ∃ U ∈ nhds x, ∃ M : NNReal,
      ∀ f ∈ 𝓕, ∀ y ∈ U, ‖deriv f y‖₊ ≤ M) :
    𝓕.Equicontinuous := by
  -- At each point, shrink the supplied neighborhood to a ball and use the common Lipschitz bound.
  intro x₀
  obtain ⟨U, hU, M, hM⟩ := h_bound x₀
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  have h_lipschitz :
      ∀ f ∈ 𝓕, LipschitzOnWith M f (Metric.ball x₀ r) :=
    familyLipschitzOn_ball_of_deriv_bound h_differentiable
      (fun f hf y hy ↦ hM f hf y (hball hy))
  exact equicontinuousAt_of_common_lipschitzOn_nhds
    (F := fun f : 𝓕 ↦ (f : ℝ → ℝ)) (Metric.ball_mem_nhds x₀ hr)
    (fun f ↦ h_lipschitz f f.property)
