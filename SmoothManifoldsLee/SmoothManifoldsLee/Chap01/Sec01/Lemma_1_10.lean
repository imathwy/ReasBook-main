import SmoothManifoldsLee.Chap01.Sec01.Definition_1_extra_2
import SmoothManifoldsLee.Chap01.Sec01.Definition_1_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M]

/-- A precompact coordinate ball is a subset that is the source of a coordinate-ball chart and
has compact closure. -/
def IsPrecompactCoordinateBall (n : ℕ) (s : Set M) : Prop :=
  (∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
    e.source = s ∧ e.IsCoordinateBall) ∧
      IsCompact (closure s)

-- Proof sketch: if `s` is the source of a coordinate-ball chart `e`, then `s = e.source`, and the
-- source of an open partial homeomorphism is open.
/-- A precompact coordinate ball is open. -/
theorem IsPrecompactCoordinateBall.isOpen {s : Set M}
    (hs : IsPrecompactCoordinateBall n s) : IsOpen s := by
  rcases hs.1 with ⟨e, rfl, -⟩
  simpa using e.open_source

-- Proof sketch: this is the compact-closure component of the defining conjunction.
/-- A precompact coordinate ball has compact closure. -/
theorem IsPrecompactCoordinateBall.isCompact_closure {s : Set M}
    (hs : IsPrecompactCoordinateBall n s) : IsCompact (closure s) :=
  hs.2

/-- Helper for Lemma 1.10: restricting a chart to a Euclidean ball with compactly contained closed
ball produces a precompact coordinate ball in the manifold. -/
theorem isPrecompactCoordinateBall_chart_preimage_metric_ball [TopologicalManifold n M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) {c : EuclideanSpace ℝ (Fin n)}
    {r : ℝ} (hr : 0 < r) (hclosed : Metric.closedBall c r ⊆ e.target) :
    IsPrecompactCoordinateBall n (e.symm '' Metric.ball c r) := by
  let e' := e.trans (OpenPartialHomeomorph.ofSet (Metric.ball c r) Metric.isOpen_ball)
  have hball_target : Metric.ball c r ⊆ e.target := by
    exact (Metric.ball_subset_closedBall : Metric.ball c r ⊆ Metric.closedBall c r).trans hclosed
  have hsource : e'.source = e.symm '' Metric.ball c r := by
    -- The restricted chart is defined exactly on the inverse image of the chosen ball.
    dsimp [e']
    exact (e.symm_image_eq_source_inter_preimage hball_target).symm
  have htarget : e'.target = Metric.ball c r := by
    -- On the target side, the restriction keeps precisely the chosen Euclidean ball.
    dsimp [e']
    exact inter_eq_left.2 hball_target
  have hcompactCarrier : IsCompact (e.symm '' Metric.closedBall c r) := by
    -- The closed ball is compact in Euclidean space, and the inverse chart is continuous on it.
    exact (isCompact_closedBall (x := c) (r := r)).image_of_continuousOn
      (e.continuousOn_symm.mono hclosed)
  have hclosureCompact : IsCompact (closure (e.symm '' Metric.ball c r)) := by
    -- The closure stays inside the compact pullback of the closed Euclidean ball.
    exact hcompactCarrier.closure_of_subset
      (Set.image_mono (Metric.ball_subset_closedBall : Metric.ball c r ⊆ Metric.closedBall c r))
  refine ⟨?_, hclosureCompact⟩
  refine ⟨e', hsource, ?_⟩
  exact OpenPartialHomeomorph.isCoordinateBall_of_target_eq_ball e' c r hr htarget

/-- Helper for Lemma 1.10: every point of an open set lies in a precompact coordinate ball
contained in that open set. -/
theorem exists_isPrecompactCoordinateBall_subset_of_mem_open [TopologicalManifold n M] {x : M}
    {u : Set M} (hx : x ∈ u) (hu : IsOpen u) :
    ∃ s : Set M, IsPrecompactCoordinateBall n s ∧ x ∈ s ∧ s ⊆ u := by
  let e := chartAt (EuclideanSpace ℝ (Fin n)) x
  let y : EuclideanSpace ℝ (Fin n) := e x
  let w : Set (EuclideanSpace ℝ (Fin n)) := e '' (e.source ∩ u)
  have hxsource : x ∈ e.source := mem_chart_source _ x
  have hyw : y ∈ w := by
    refine ⟨x, ⟨hxsource, hx⟩, rfl⟩
  have hw_open : IsOpen w := by
    -- The image of the open neighborhood inside the chart source is open in Euclidean space.
    simpa [w] using e.isOpen_image_source_inter hu
  obtain ⟨r, hr, hclosed⟩ :
      ∃ r : ℝ, 0 < r ∧ Metric.closedBall y r ⊆ w := by
    -- Choose a small closed Euclidean ball around the charted point inside that open image.
    exact Metric.nhds_basis_closedBall.mem_iff.1 (hw_open.mem_nhds hyw)
  have hw_target : w ⊆ e.target := by
    -- The chart image of any subset of the source stays in the chart target.
    simpa [w] using (Set.image_mono (show e.source ∩ u ⊆ e.source from inter_subset_left)).trans
      e.image_source_eq_target.subset
  let s : Set M := e.symm '' Metric.ball y r
  have hs_precompact : IsPrecompactCoordinateBall n s := by
    -- Pull back the chosen Euclidean ball through the chart.
    simpa [s, y] using isPrecompactCoordinateBall_chart_preimage_metric_ball
      (n := n) e hr (hclosed.trans hw_target)
  have hxs : x ∈ s := by
    -- The charted point lies in every positive-radius ball centered at itself.
    refine ⟨y, Metric.mem_ball_self hr, ?_⟩
    simpa [y] using e.left_inv hxsource
  have hs_subset_source_u : s ⊆ e.source ∩ u := by
    -- The pulled-back ball lies inside the original open neighborhood because its image does.
    have hball_w : Metric.ball y r ⊆ w := by
      exact (Metric.ball_subset_closedBall : Metric.ball y r ⊆ Metric.closedBall y r).trans hclosed
    change e.symm '' Metric.ball y r ⊆ e.source ∩ u
    refine (Set.image_mono hball_w).trans ?_
    have himage : e.symm '' w = e.source ∩ u := by
      simpa [w] using e.symm_image_image_of_subset_source
        (s := e.source ∩ u) (show e.source ∩ u ⊆ e.source from inter_subset_left)
    exact himage.subset
  exact ⟨s, hs_precompact, hxs, fun z hz ↦ (hs_subset_source_u hz).2⟩

/-- Helper for Lemma 1.10: precompact coordinate balls form a topological basis on a topological
manifold. -/
theorem isTopologicalBasis_isPrecompactCoordinateBall [TopologicalManifold n M] :
    IsTopologicalBasis { s : Set M | IsPrecompactCoordinateBall n s } := by
  -- The local chart construction gives a basis element inside every open neighborhood.
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro s hs
    exact hs.isOpen
  · intro x u hx hu
    obtain ⟨s, hs, hxs, hsu⟩ := exists_isPrecompactCoordinateBall_subset_of_mem_open
      (n := n) hx hu
    exact ⟨s, hs, hxs, hsu⟩

/-- Lemma 1.10: every topological manifold has a countable topological basis consisting of
precompact coordinate balls. -/
-- Proof sketch: cover the manifold by countably many chart domains using second countability.
-- Inside each chart target, choose the countable family of rational Euclidean balls whose closures
-- stay inside the target. Pull these balls back along the chart maps and take the countable union
-- of the resulting families.
theorem exists_countable_precompact_coordinate_ball_basis [TopologicalManifold n M] :
    ∃ b : Set (Set M),
      b.Countable ∧ IsTopologicalBasis b ∧ ∀ s ∈ b, IsPrecompactCoordinateBall n s := by
  let B : Set (Set M) := { s : Set M | IsPrecompactCoordinateBall n s }
  have hB : IsTopologicalBasis B := isTopologicalBasis_isPrecompactCoordinateBall (n := n)
  -- Once the local basis is available, second countability lets us thin it to a countable subbasis.
  obtain ⟨b, hbB, hbCountable, hbBasis⟩ := hB.exists_countable
  exact ⟨b, hbCountable, hbBasis, fun s hs ↦ hbB hs⟩
