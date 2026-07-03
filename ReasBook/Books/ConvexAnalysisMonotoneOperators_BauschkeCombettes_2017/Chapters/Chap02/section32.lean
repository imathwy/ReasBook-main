import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_2_32_1 (from Chap02) -/
open scoped InnerProductSpace
open Filter

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Example 2.32.1: every fixed coordinate of an orthonormal sequence tends to `0`. -/
private lemma orthonormal_inner_right_tendsto_zero (x : ℕ → H) (hx : Orthonormal ℝ x) (u : H) :
    Tendsto (fun n ↦ ⟪x n, u⟫_ℝ) atTop (nhds 0) := by
  -- Bessel's inequality makes the squared coordinates summable, so they vanish at infinity.
  have hs : Summable (fun n ↦ ‖⟪x n, u⟫_ℝ‖ ^ 2) :=
    hx.inner_products_summable u
  have hs0 : Tendsto (fun n ↦ ‖⟪x n, u⟫_ℝ‖ ^ 2) atTop (nhds 0) :=
    hs.tendsto_atTop_zero
  -- Taking square roots recovers the norms of the coordinates.
  have hsqrt : Tendsto (fun n ↦ Real.sqrt (‖⟪x n, u⟫_ℝ‖ ^ 2)) atTop
      (nhds (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp hs0
  have hnorm : Tendsto (fun n ↦ ‖⟪x n, u⟫_ℝ‖) atTop (nhds 0) := by
    convert hsqrt using 1
    · ext n
      rw [Real.sqrt_sq]
      positivity
    · simp
  -- Norm convergence to `0` is equivalent to convergence to `0` in `ℝ`.
  exact (tendsto_zero_iff_norm_tendsto_zero).2 hnorm

/-- Example 2.32.1: an orthonormal sequence in a real Hilbert space converges weakly to `0`. -/
-- Proof sketch: for each `u : H`, Bessel's inequality implies that
-- `n ↦ ‖inner ℝ (x n) u‖ ^ 2` is summable, so `inner ℝ (x n) u → 0`. By the Hilbert-space
-- description of the weak topology from Remark 2.31, this is exactly convergence to `0` in
-- `WeakSpace ℝ H`.
theorem orthonormal_sequence_tendsto_zero_weakly (x : ℕ → H) (hx : Orthonormal ℝ x) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (nhds (0 : WeakSpace ℝ H)) := by
  simpa using
    (weakConvergence_iff_forall_tendsto_inner_right x (0 : H)).2
      fun u ↦ by simpa using orthonormal_inner_right_tendsto_zero x hx u

omit [CompleteSpace H] in
/-- An orthonormal sequence does not converge strongly to `0`. -/
-- Proof sketch: if `x` converged to `0` in norm, then `‖x n‖ → 0`; this contradicts the fact
-- that every term has norm `1`.
theorem orthonormal_sequence_not_tendsto_zero_strongly (x : ℕ → H) (hx : Orthonormal ℝ x) :
    ¬ Tendsto x atTop (nhds (0 : H)) := by
  intro hx0
  -- Strong convergence to `0` forces the norms to converge to `0`.
  have hnorm : Tendsto (fun n ↦ ‖x n‖) atTop (nhds 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).mp hx0
  -- Rewriting the norms with orthonormality turns this into the impossible limit `1 → 0`.
  have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 0) := by
    convert hnorm using 1
    ext n
    simp [hx.norm_eq_one]
  have hconst' : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hone : (0 : ℝ) = 1 :=
    tendsto_nhds_unique hconst hconst'
  norm_num at hone

omit [CompleteSpace H] in
/-- Helper for Example 2.32.1: distinct terms of an orthonormal sequence have squared distance `2`.
-/
private lemma orthonormal_norm_sub_sq_eq_two (x : ℕ → H) (hx : Orthonormal ℝ x) {m n : ℕ}
    (hmn : m ≠ n) :
    ‖x m - x n‖ ^ 2 = 2 := by
  -- Expand the squared norm and simplify the two norm terms and the cross term separately.
  rw [norm_sub_sq_real]
  have hm : ‖x m‖ = 1 := hx.norm_eq_one m
  have hn : ‖x n‖ = 1 := hx.norm_eq_one n
  have hinner : inner ℝ (x m) (x n) = 0 := hx.inner_eq_zero hmn
  nlinarith [hm, hn, hinner]

omit [CompleteSpace H] in
/-- An orthonormal sequence has no Cauchy subsequence. -/
-- Proof sketch: for distinct `m` and `n`, orthonormality gives
-- `‖x m - x n‖ ^ 2 = ‖x m‖ ^ 2 + ‖x n‖ ^ 2 = 2`, so distinct subsequence terms stay a fixed
-- positive distance apart and cannot satisfy the Cauchy criterion.
theorem orthonormal_sequence_not_exists_cauchy_subsequence (x : ℕ → H) (hx : Orthonormal ℝ x) :
    ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ CauchySeq (x ∘ φ) := by
  rintro ⟨φ, hφ, hcauchy⟩
  -- A Cauchy subsequence would eventually have all later terms within distance `1` of one anchor.
  rcases (Metric.cauchySeq_iff'.1 hcauchy) 1 zero_lt_one with ⟨N, hN⟩
  have hdist : dist ((x ∘ φ) (N + 1)) ((x ∘ φ) N) < 1 :=
    hN (N + 1) (Nat.le_succ N)
  -- Consecutive subsequence terms are still distinct, so orthonormality keeps them separated.
  have hsq : ‖x (φ (N + 1)) - x (φ N)‖ ^ 2 = 2 := by
    apply orthonormal_norm_sub_sq_eq_two x hx
    exact (hφ (Nat.lt_succ_self N)).ne'
  rw [dist_eq_norm] at hdist
  have hsq_lt : ‖x (φ (N + 1)) - x (φ N)‖ ^ 2 < 1 := by
    simpa using
      (pow_lt_pow_left₀ hdist (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0))
  linarith

/-! ### Example_2_32_2 (from Chap02) -/
open scoped Topology InnerProductSpace
open Filter

universe u

-- Proof sketch: the norm is continuous for the strong topology, so the unit sphere is the
-- preimage of the closed set `{1}` under `x ↦ ‖x‖`, hence strongly closed. For the weak statement,
-- choose an orthonormal sequence in the infinite-dimensional Hilbert space; each term lies on the
-- unit sphere and the preceding weak-convergence result shows that this sequence converges weakly
-- to `0`, which does not belong to the sphere.
/-- Helper for Example 2.32.2: every infinite-dimensional real Hilbert space contains an
orthonormal sequence indexed by `ℕ`. -/
lemma exists_orthonormal_sequence_of_not_finiteDimensional
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    (h_infinite : ¬ FiniteDimensional ℝ 𝓗) :
    ∃ e : ℕ → 𝓗, Orthonormal ℝ e := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℝ 𝓗
  -- A finite Hilbert-basis index set would force finite dimensionality, contradicting the hypothesis.
  have hw_infinite : w.Infinite := by
    by_contra hw_infinite
    have hw_finite : Set.Finite w := (Set.finite_or_infinite w).resolve_right hw_infinite
    haveI : Fintype w := hw_finite.fintype
    have hfd : FiniteDimensional ℝ 𝓗 :=
      Module.Basis.finiteDimensional_of_finite (b.toOrthonormalBasis.toBasis)
    exact h_infinite hfd
  -- Extract a countable orthonormal subfamily by embedding `ℕ` into the infinite basis index set.
  let f : ℕ ↪ w := Set.Infinite.natEmbedding w hw_infinite
  refine ⟨fun n ↦ b (f n), ?_⟩
  simpa [Function.comp] using b.orthonormal.comp f f.injective

/-- Helper for Example 2.32.2: orthonormal vectors lie on the weak unit sphere. -/
private lemma orthonormal_sequence_mem_weak_unitSphere
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    (e : ℕ → 𝓗) (he : Orthonormal ℝ e) :
    ∀ n, toWeakSpace ℝ 𝓗 (e n) ∈
      ((toWeakSpace ℝ 𝓗) '' Metric.sphere (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗)) := by
  intro n
  refine ⟨e n, ?_, rfl⟩
  -- Each term of an orthonormal family has norm `1`.
  simpa [Metric.mem_sphere, dist_eq_norm] using he.norm_eq_one n

/-- Helper for Example 2.32.2: the weak unit sphere excludes the origin. -/
private lemma zero_not_mem_weak_unitSphere
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗] :
    (0 : WeakSpace ℝ 𝓗) ∉
      ((toWeakSpace ℝ 𝓗) '' Metric.sphere (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗)) := by
  -- The origin has norm `0`, so it cannot lie on the norm-one sphere.
  rintro ⟨x, hx, hx0⟩
  have : x = 0 := (toWeakSpace ℝ 𝓗).injective hx0
  subst this
  simp at hx

/-- Example 2.32.2: in an infinite-dimensional real Hilbert space, the image of the unit sphere in
`WeakSpace ℝ 𝓗` is not sequentially closed. -/
theorem not_isSeqClosed_image_unitSphere_toWeakSpace
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    (h_infinite : ¬ FiniteDimensional ℝ 𝓗) :
    ¬ IsSeqClosed (((toWeakSpace ℝ 𝓗) '' Metric.sphere (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗))) := by
  -- Use an orthonormal sequence in the unit sphere converging weakly to `0`.
  intro h_seqClosed
  obtain ⟨e, he⟩ := exists_orthonormal_sequence_of_not_finiteDimensional h_infinite
  have hmem :
      ∀ n, toWeakSpace ℝ 𝓗 (e n) ∈
        ((toWeakSpace ℝ 𝓗) '' Metric.sphere (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗)) :=
    orthonormal_sequence_mem_weak_unitSphere e he
  have hweak :
      Tendsto (fun n ↦ toWeakSpace ℝ 𝓗 (e n)) atTop (𝓝 (0 : WeakSpace ℝ 𝓗)) :=
    orthonormal_sequence_tendsto_zero_weakly e he
  have hzero_mem :
      (0 : WeakSpace ℝ 𝓗) ∈
        ((toWeakSpace ℝ 𝓗) '' Metric.sphere (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗)) :=
    h_seqClosed hmem hweak
  -- Sequential closedness would force the weak limit `0` back into the sphere, contradiction.
  exact zero_not_mem_weak_unitSphere hzero_mem

/-- Example 2.32.2: in an infinite-dimensional real Hilbert space, the unit sphere is closed for
the strong topology, but its image in `WeakSpace ℝ 𝓗` is not sequentially closed. -/
theorem unitSphere_isClosed_in_strongTopology_and_not_seqClosed_in_weakTopology
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    (h_infinite : ¬ FiniteDimensional ℝ 𝓗) :
    IsClosed (Metric.sphere (0 : 𝓗) 1) ∧
      ¬ IsSeqClosed (((toWeakSpace ℝ 𝓗) '' Metric.sphere (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗))) := by
  refine ⟨?_, not_isSeqClosed_image_unitSphere_toWeakSpace h_infinite⟩
  simpa using (Metric.isClosed_sphere : IsClosed (Metric.sphere (0 : 𝓗) (1 : ℝ)))
