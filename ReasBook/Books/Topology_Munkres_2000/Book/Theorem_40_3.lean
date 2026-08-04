module

public import Topology_Munkres_2000.Book.Definition_20_9
public import Topology_Munkres_2000.Book.Lemma_39_2
public import Topology_Munkres_2000.Book.Lemma_40_1
public import Topology_Munkres_2000.Book.Lemma_40_2
public import Topology_Munkres_2000.Book.Theorem_34_2
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Metrizable.Uniformity

public section

open Filter Set TopologicalSpace Topology

universe u

/-- Helper for Theorem 40.3: the unit interval includes continuously into ℝ. -/
private def unitIntervalInclusion : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Helper for Theorem 40.3: the unit-interval inclusion evaluates to the
underlying real number. -/
@[simp] private lemma unitIntervalInclusion_apply (x : Set.Icc (0 : ℝ) 1) :
    unitIntervalInclusion x = (x : ℝ) := by
  -- Expose only the computation rule of the named inclusion.
  rfl

/-- Helper for Theorem 40.3: scaled zero-set functions associated to locally finite
basis layers separate points from closed sets and have a reciprocal layer bound. -/
private lemma existsScaledBasisCoordinates {X : Type u} [TopologicalSpace X] [T3Space X]
    {basis : Set (Set X)} {pieces : ℕ → Set (Set X)}
    (hbasis : IsTopologicalBasis basis) (hcover : basis = ⋃ n, pieces n)
    (hfinite : ∀ n, (pieces n).LocallyFinite) :
    ∃ f : (Σ n, pieces n) → C(X, ℝ),
      SeparatesPointsFromClosedSets f ∧
        (∀ j x, x ∉ (j.2 : Set X) → f j x = 0) ∧
          ∀ j x, f j x ∈ Set.Icc (0 : ℝ) (1 / ((j.1 : ℝ) + 1)) := by
  classical
  have hSigma : HasSigmaLocallyFiniteBasis X :=
    (hasSigmaLocallyFiniteBasis_iff X).mpr ⟨basis, pieces, hbasis, hcover, hfinite⟩
  letI : T4Space X := hSigma.t4Space
  have hpiecesSubset (n : ℕ) : pieces n ⊆ basis := by
    intro B hB
    rw [hcover]
    exact Set.mem_iUnion.mpr ⟨n, hB⟩
  have hclosed (j : Σ n, pieces n) : IsClosed ((j.2 : Set X)ᶜ) := by
    exact (hbasis.isOpen (hpiecesSubset j.1 j.2.property)).isClosed_compl
  have hgdelta (j : Σ n, pieces n) : IsGδ ((j.2 : Set X)ᶜ) := by
    exact hSigma.isGδ (hclosed j)
  choose g hzero hpositive using fun j ↦
    exists_continuousMap_Icc_zero_of_closed_isGδ (hclosed j) (hgdelta j)
  let f : (Σ n, pieces n) → C(X, ℝ) := fun j ↦
    (1 / ((j.1 : ℝ) + 1)) • unitIntervalInclusion.comp (g j)
  refine ⟨f, ?_, ?_, ?_⟩
  · -- A basis member inside the prescribed neighborhood supplies a positive coordinate.
    rw [SeparatesPointsFromClosedSets.iff_closedSet]
    intro x A hA hxA
    have hxComplement : x ∈ Aᶜ := hxA
    obtain ⟨B, hBbasis, hxB, hBsub⟩ :=
      hbasis.exists_subset_of_mem_open hxComplement hA.isOpen_compl
    rw [hcover] at hBbasis
    obtain ⟨n, hBpiece⟩ := Set.mem_iUnion.mp hBbasis
    let j : Σ n, pieces n := ⟨n, B, hBpiece⟩
    refine ⟨j, ?_, ?_⟩
    · have hxCompl : x ∉ (j.2 : Set X)ᶜ := by
        simpa only [Set.mem_compl_iff, not_not] using hxB
      have hscale : 0 < 1 / ((j.1 : ℝ) + 1) := by positivity
      simp only [f, ContinuousMap.smul_apply, ContinuousMap.comp_apply,
        unitIntervalInclusion_apply, smul_eq_mul]
      exact mul_pos hscale (hpositive j x hxCompl)
    · intro y hyA
      have hyB : y ∉ (j.2 : Set X) := by
        intro hy
        exact (hBsub hy) hyA
      have hyCompl : y ∈ (j.2 : Set X)ᶜ := hyB
      simp only [f, ContinuousMap.smul_apply, ContinuousMap.comp_apply,
        unitIntervalInclusion_apply, smul_eq_mul, hzero j y hyCompl, mul_zero]
  · -- The chosen zero-set function vanishes away from its basis member.
    intro j x hx
    have hxCompl : x ∈ (j.2 : Set X)ᶜ := hx
    simp only [f, ContinuousMap.smul_apply, ContinuousMap.comp_apply,
      unitIntervalInclusion_apply, smul_eq_mul, hzero j x hxCompl, mul_zero]
  · -- Scaling the unit-interval range gives the reciprocal amplitude bound.
    intro j x
    have hgRange := (g j x).property
    have hscale : 0 ≤ 1 / ((j.1 : ℝ) + 1) := by positivity
    simp only [f, ContinuousMap.smul_apply, ContinuousMap.comp_apply,
      unitIntervalInclusion_apply, smul_eq_mul]
    constructor
    · exact mul_nonneg hscale hgRange.1
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left hgRange.2 hscale

/-- Helper for Theorem 40.3: continuous functions supported on one locally finite
collection are eventually uniformly close at every point. -/
private lemma eventuallyUniformlyCloseOnLocallyFiniteLayer
    {X : Type u} [TopologicalSpace X] {family : Set (Set X)}
    (f : family → C(X, ℝ)) (hfinite : family.LocallyFinite)
    (hsupport : ∀ (B : family) x, x ∉ (B : Set X) → f B x = 0)
    (x : X) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in nhds x, ∀ B, dist (f B y) (f B x) < ε := by
  classical
  -- Work on a neighborhood that meets only finitely many supports.
  obtain ⟨U, hU, hactive⟩ := hfinite x
  have hclose : ∀ᶠ y in nhds x,
      ∀ B ∈ {B : family | ((B : Set X) ∩ U).Nonempty},
        dist (f B y) (f B x) < ε := by
    exact hactive.eventually_all.mpr fun B hB ↦
      Metric.continuousAt_iff'.mp (f B).continuous.continuousAt ε hε
  filter_upwards [hU, hclose] with y hyU hyclose
  intro B
  by_cases hBactive : B ∈ {B : family | ((B : Set X) ∩ U).Nonempty}
  · exact hyclose B hBactive
  · -- Outside the finite active family, both nearby evaluations vanish.
    have hxU : x ∈ U := mem_of_mem_nhds hU
    have hxB : x ∉ (B : Set X) := by
      intro hx
      exact hBactive ⟨x, hx, hxU⟩
    have hyB : y ∉ (B : Set X) := by
      intro hy
      exact hBactive ⟨y, hy, hyU⟩
    rw [hsupport B y hyB, hsupport B x hxB, dist_self]
    exact hε

/-- Helper for Theorem 40.3: sigma-locally finite support together with reciprocal
amplitude decay makes the combined evaluation map continuous in the uniform metric. -/
private lemma continuousUniformEvaluationOfSigmaLocallyFiniteSupport
    {X : Type u} [TopologicalSpace X] {pieces : ℕ → Set (Set X)}
    (f : (Σ n, pieces n) → C(X, ℝ))
    (hfinite : ∀ n, (pieces n).LocallyFinite)
    (hsupport : ∀ j x, x ∉ (j.2 : Set X) → f j x = 0)
    (hrange : ∀ j x, f j x ∈ Set.Icc (0 : ℝ) (1 / ((j.1 : ℝ) + 1))) :
    @Continuous X ((Σ n, pieces n) → ℝ) _
      (UniformMetric.topology (Σ n, pieces n)) (fun x j ↦ f j x) := by
  letI : MetricSpace ((Σ n, pieces n) → ℝ) :=
    UniformMetric.metricSpace (Σ n, pieces n)
  rw [Metric.continuous_iff']
  intro x ε hε
  -- Choose a cutoff after which every coordinate has amplitude below ε / 2.
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hε)
  have hlow : ∀ᶠ y in nhds x, ∀ n ∈ Finset.range (N + 1),
      ∀ B : pieces n, dist (f ⟨n, B⟩ y) (f ⟨n, B⟩ x) < ε / 2 := by
    exact (Finset.range (N + 1)).eventually_all.mpr fun n _hn ↦
      eventuallyUniformlyCloseOnLocallyFiniteLayer
        (fun B ↦ f ⟨n, B⟩) (hfinite n)
        (fun B y hy ↦ hsupport ⟨n, B⟩ y hy) x (half_pos hε)
  filter_upwards [hlow] with y hy
  -- Low layers are controlled by continuity; the reciprocal bound controls the tail.
  cases isEmpty_or_nonempty (Σ n, pieces n) with
  | inl hempty =>
      have heq : (fun j ↦ f j y) = fun j ↦ f j x := Subsingleton.elim _ _
      rw [heq, dist_self]
      exact hε
  | inr hnonempty =>
      rw [UniformMetric.dist_eq]
      refine (ciSup_le fun j ↦ ?_).trans_lt (half_lt_self hε)
      by_cases hj : j.1 < N + 1
      · exact (min_le_left _ _).trans (hy j.1 (Finset.mem_range.mpr hj) j.2).le
      · have hindex : N + 1 ≤ j.1 := Nat.le_of_not_gt hj
        have hcast : (N : ℝ) + 1 ≤ (j.1 : ℝ) + 1 := by
          have hcast' : (N : ℝ) + 1 ≤ (j.1 : ℝ) := by
            exact_mod_cast hindex
          exact hcast'.trans (le_add_of_nonneg_right zero_le_one)
        have hdenPositive : 0 < (N : ℝ) + 1 := by positivity
        have hamp : 1 / ((j.1 : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
          exact one_div_le_one_div_of_le hdenPositive hcast
        have hdist : dist (f j y) (f j x) ≤ 1 / ((j.1 : ℝ) + 1) := by
          rw [Real.dist_eq, abs_le]
          constructor
          · linarith [hrange j y |>.1, hrange j x |>.2]
          · linarith [hrange j y |>.2, hrange j x |>.1]
        exact (min_le_left _ _).trans (hdist.trans (hamp.trans hN.le))

/-- Helper for Theorem 40.3: the identity from the uniform topology on a real
function space to its product topology is continuous. -/
private lemma continuousUniformMetricToPi (J : Type u) :
    @Continuous (J → ℝ) (J → ℝ) (UniformMetric.topology J)
      (Pi.topologicalSpace : TopologicalSpace (J → ℝ)) id := by
  -- It suffices to control each coordinate projection by the uniform distance.
  refine @continuous_pi (X := J → ℝ) (ι := J) (A := fun _ ↦ ℝ)
    (UniformMetric.topology J) (fun _ ↦ inferInstance) (f := id) ?_
  intro j
  letI : MetricSpace (J → ℝ) := UniformMetric.metricSpace J
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro y hy
  rw [UniformMetric.dist_eq] at hy
  have hbounded : BddAbove (Set.range (fun i ↦ min (dist (y i) (x i)) 1)) := by
    refine ⟨1, ?_⟩
    rintro z ⟨i, rfl⟩
    exact min_le_right _ _
  have hcoord : min (dist (y j) (x j)) 1 < min ε 1 :=
    (le_ciSup hbounded j).trans_lt hy
  by_contra hdist
  exact (not_lt_of_ge (min_le_min (le_of_not_gt hdist) le_rfl)) hcoord

/-- Helper for Theorem 40.3: a continuous evaluation embedding into the uniform
function space pulls its metric back to the source. -/
private lemma metrizableSpaceOfUniformEvaluation {X : Type u} {J : Type u}
    [TopologicalSpace X] [T1Space X] (f : J → C(X, ℝ))
    (hseparates : SeparatesPointsFromClosedSets f)
    (hcontinuous : @Continuous X (J → ℝ) _ (UniformMetric.topology J)
      (fun x j ↦ f j x)) : MetrizableSpace X := by
  have hproduct : @Topology.IsEmbedding X (J → ℝ) _
      (Pi.topologicalSpace : TopologicalSpace (J → ℝ)) (fun x j ↦ f j x) :=
    isEmbedding_pi_of_neighborhood_functions f hseparates
  have hforget := continuousUniformMetricToPi J
  have hproductComp : @Topology.IsInducing X (J → ℝ) _
      (Pi.topologicalSpace : TopologicalSpace (J → ℝ))
      (id ∘ fun x j ↦ f j x) := by
    simpa only [Function.comp_def, id_eq] using hproduct.toIsInducing
  have hcontinuousLe :
      (inferInstance : TopologicalSpace X) ≤
        (UniformMetric.topology J).induced (fun x j ↦ f j x) :=
    (continuous_iff_le_induced (t₁ := inferInstance)
      (t₂ := UniformMetric.topology J)).mp hcontinuous
  have hforgetLe :
      UniformMetric.topology J ≤
        (Pi.topologicalSpace : TopologicalSpace (J → ℝ)).induced id :=
    (continuous_iff_le_induced (t₁ := UniformMetric.topology J)
      (t₂ := Pi.topologicalSpace)).mp hforget
  have hproductEq :
      (inferInstance : TopologicalSpace X) =
        (Pi.topologicalSpace : TopologicalSpace (J → ℝ)).induced
          (id ∘ fun x j ↦ f j x) :=
    hproductComp.eq_induced
  have htopologyEq :
      (inferInstance : TopologicalSpace X) =
        (UniformMetric.topology J).induced (fun x j ↦ f j x) := by
    -- Product inducing plus continuity of the forgetful identity pins down both inequalities.
    apply le_antisymm
    · exact hcontinuousLe
    · grw [hproductEq, ← induced_compose, ← hforgetLe]
  have hinducing : @Topology.IsInducing X (J → ℝ) _
      (UniformMetric.topology J) (fun x j ↦ f j x) :=
    @Topology.IsInducing.mk X (J → ℝ) _ (UniformMetric.topology J)
      (fun x j ↦ f j x) htopologyEq
  have huniform : @Topology.IsEmbedding X (J → ℝ) _
      (UniformMetric.topology J) (fun x j ↦ f j x) :=
    @Topology.IsEmbedding.mk X (J → ℝ) _ (UniformMetric.topology J)
      (fun x j ↦ f j x) hinducing hproduct.injective
  letI : TopologicalSpace (J → ℝ) := UniformMetric.topology J
  letI : MetricSpace (J → ℝ) := UniformMetric.metricSpace J
  exact huniform.metrizableSpace

/-- Helper for Theorem 40.3: every metrizable space has a sigma-locally finite
basis obtained from countably locally finite refinements of shrinking ball covers. -/
private theorem MetrizableSpace.hasSigmaLocallyFiniteBasis
    (X : Type u) [TopologicalSpace X] [MetrizableSpace X] :
    HasSigmaLocallyFiniteBasis X := by
  classical
  -- Use a compatible metric and refine the ball cover at each reciprocal scale.
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let radius : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  let ballCover : ℕ → Set (Set X) := fun n ↦ Set.range fun x ↦ Metric.ball x (radius n)
  have hcoverOpen (n : ℕ) : ∀ U ∈ ballCover n, IsOpen U := by
    rintro U ⟨x, rfl⟩
    exact Metric.isOpen_ball
  have hcoverUniv (n : ℕ) : ⋃₀ ballCover n = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hradiusPositive : 0 < radius n := by positivity
    have hxBall : x ∈ Metric.ball x (radius n) :=
      Metric.mem_ball_self hradiusPositive
    exact Set.mem_sUnion.mpr ⟨Metric.ball x (radius n), ⟨x, rfl⟩, hxBall⟩
  choose refinement hrefine hrefinementCover hrefinementCountable using fun n ↦
    TopologicalSpace.MetrizableSpace.exists_countablyLocallyFinite_openRefinement
      (ballCover n) (hcoverOpen n) (hcoverUniv n)
  choose pieces hpiecesUnion hpiecesFinite using fun n ↦
    Set.countablyLocallyFinite_iff.mp (hrefinementCountable n)
  let basisSets : Set (Set X) := ⋃ n, refinement n
  have hbasisOpen : ∀ U ∈ basisSets, IsOpen U := by
    intro U hU
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hU
    exact (hrefine n).isOpen_of_mem hn
  have hbasisNhds : ∀ x U, x ∈ U → IsOpen U →
      ∃ V ∈ basisSets, x ∈ V ∧ V ⊆ U := by
    intro x U hxU hUopen
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hUopen x hxU
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    have hxRefinement : x ∈ ⋃₀ refinement n := by
      rw [hrefinementCover n]
      exact Set.mem_univ x
    obtain ⟨V, hVrefinement, hxV⟩ := Set.mem_sUnion.mp hxRefinement
    refine ⟨V, Set.mem_iUnion.mpr ⟨n, hVrefinement⟩, hxV, ?_⟩
    obtain ⟨A, hAcover, hVA⟩ := (hrefine n).subset_of_mem hVrefinement
    obtain ⟨z, rfl⟩ := hAcover
    intro y hyV
    have hyBall := hVA hyV
    have hxBall := hVA hxV
    rw [Metric.mem_ball] at hyBall hxBall
    have hxBall' : dist z x < radius n := by
      simpa only [dist_comm] using hxBall
    apply hεsub
    calc
      dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
      _ < radius n + radius n := add_lt_add hyBall hxBall'
      _ = 2 * radius n := by ring
      _ < ε := by
        have htwoPositive : (0 : ℝ) < 2 := by norm_num
        have hscaled :=
          mul_lt_mul_of_pos_left hn htwoPositive
        dsimp [radius] at hscaled ⊢
        nlinarith
  have hbasis : IsTopologicalBasis basisSets :=
    isTopologicalBasis_of_isOpen_of_nhds hbasisOpen hbasisNhds
  rw [hasSigmaLocallyFiniteBasis_iff]
  refine ⟨basisSets, fun q ↦ pieces (Nat.unpair q).1 (Nat.unpair q).2,
    hbasis, ?_, ?_⟩
  · -- Pairing the refinement scale and its local-finiteness layer flattens the union.
    ext U
    constructor
    · intro hU
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hU
      rw [hpiecesUnion n] at hn
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hn
      have hpaired :
          U ∈ pieces (Nat.unpair (Nat.pair n m)).1
            (Nat.unpair (Nat.pair n m)).2 := by
        simpa only [Nat.unpair_pair] using hm
      exact Set.mem_iUnion.mpr ⟨Nat.pair n m, hpaired⟩
    · intro hU
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hU
      refine Set.mem_iUnion.mpr ⟨(Nat.unpair q).1, ?_⟩
      rw [hpiecesUnion (Nat.unpair q).1]
      exact Set.mem_iUnion.mpr ⟨(Nat.unpair q).2, hq⟩
  · intro q
    exact hpiecesFinite (Nat.unpair q).1 (Nat.unpair q).2

/-- Theorem 40.3 (Nagata-Smirnov metrization theorem): a topological space is
metrizable if and only if it is regular and has a countably locally finite basis. -/
theorem nagataSmirnovMetrization (X : Type u) [TopologicalSpace X] :
    MetrizableSpace X ↔ T3Space X ∧ HasSigmaLocallyFiniteBasis X := by
  constructor
  · intro hmetrizable
    letI : MetrizableSpace X := hmetrizable
    -- A compatible metric supplies regularity and the shrinking-refinement basis.
    exact ⟨inferInstance, MetrizableSpace.hasSigmaLocallyFiniteBasis X⟩
  · rintro ⟨hregular, hsigma⟩
    letI : T3Space X := hregular
    -- Scaled basis coordinates separate points and are continuous in the uniform metric.
    obtain ⟨basis, pieces, hbasis, hcover, hfinite⟩ :=
      (hasSigmaLocallyFiniteBasis_iff X).mp hsigma
    obtain ⟨f, hseparates, hsupport, hrange⟩ :=
      existsScaledBasisCoordinates hbasis hcover hfinite
    exact metrizableSpaceOfUniformEvaluation f hseparates
      (continuousUniformEvaluationOfSigmaLocallyFiniteSupport
        f hfinite hsupport hrange)
