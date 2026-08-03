module

public import Topology_Munkres_2000.Book.Theorem_50_4
public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Order.Filter.AtTopBot.Group
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import Mathlib.Topology.Metrizable.Urysohn

public section

open scoped BigOperators BoundedContinuousFunction

universe u

/-- Helper for Exercise 50.6: a locally compact second-countable Hausdorff space
admits a nonnegative continuous exhaustion tending to `atTop` at infinity. -/
private lemma exists_continuousMap_tendsto_cocompact_atTop
    {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] :
    ∃ q : C(X, ℝ), Filter.Tendsto q (Filter.cocompact X) Filter.atTop ∧
      ∀ x, 0 ≤ q x := by
  classical
  let K : CompactExhaustion X := CompactExhaustion.choice X
  have hclosed (n : ℕ) : IsClosed (K n) := (K.isCompact n).isClosed
  have hclosedCompl (n : ℕ) : IsClosed (interior (K (n + 1)))ᶜ :=
    isOpen_interior.isClosed_compl
  have hdisjoint (n : ℕ) : Disjoint (K n) (interior (K (n + 1)))ᶜ := by
    rw [Set.disjoint_left]
    intro x hx hxc
    exact hxc (K.subset_interior_succ n hx)
  choose φ hφzero hφone hφrange using fun n ↦
    exists_continuous_zero_one_of_isClosed (hclosed n) (hclosedCompl n) (hdisjoint n)
  let qfun : X → ℝ := fun x ↦ ∑ i ∈ Finset.range (K.find x), φ i x
  have qfun_nonneg (x : X) : 0 ≤ qfun x := by
    -- Every cutoff takes values in `[0, 1]`, hence so does every summand.
    apply Finset.sum_nonneg
    intro i hi
    exact (hφrange i x).1
  have qfun_eq_sum (s : ℕ) {x : X} (hx : x ∈ K s) :
      qfun x = ∑ i ∈ Finset.range s, φ i x := by
    have hfind : K.find x ≤ s := K.mem_iff_find_le.mp hx
    dsimp only [qfun]
    apply Finset.sum_subset (Finset.range_mono hfind)
    intro i his hifind
    have hfind_le_i : K.find x ≤ i := by
      simpa only [Finset.mem_range, not_lt] using hifind
    have hxi : x ∈ K i := K.subset hfind_le_i (K.mem_find x)
    exact hφzero i hxi
  have qfun_continuous : Continuous qfun := by
    -- Near any point the exhaustion is one fixed finite sum, since all later
    -- cutoffs vanish on a sufficiently large compact neighborhood.
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨s, hs⟩ := K.exists_mem_nhds x
    have heq : qfun =ᶠ[nhds x] fun y ↦ ∑ i ∈ Finset.range s, φ i y := by
      filter_upwards [hs] with y hy
      exact qfun_eq_sum s hy
    exact (continuous_finsetSum _ fun i _ ↦ (φ i).continuous).continuousAt.congr_of_eventuallyEq
      heq
  let q : C(X, ℝ) := ⟨qfun, qfun_continuous⟩
  refine ⟨q, ?_, ?_⟩
  · -- Outside the `n`th compact set, the first `n` cutoffs are all one.
    rw [Filter.hasBasis_cocompact.tendsto_iff Filter.atTop_basis_Ioi]
    intro r hr
    obtain ⟨n, hn⟩ := exists_nat_gt r
    refine ⟨K n, K.isCompact n, ?_⟩
    intro x hx
    have hfind : n < K.find x := by
      rw [← not_le]
      intro hle
      exact hx (K.mem_iff_find_le.mpr hle)
    have hone (i : ℕ) (hi : i ∈ Finset.range n) : φ i x = 1 := by
      have hi_succ : i + 1 ≤ n := by
        simp only [Finset.mem_range] at hi
        omega
      apply hφone i
      intro hxi
      exact hx (K.subset hi_succ (interior_subset hxi))
    have hsum_le :
        (∑ i ∈ Finset.range n, φ i x) ≤
          ∑ i ∈ Finset.range (K.find x), φ i x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hfind.le)
      intro i hi hnot
      exact (hφrange i x).1
    calc
      r < (n : ℝ) := hn
      _ = ∑ i ∈ Finset.range n, φ i x := by
        rw [Finset.sum_congr rfl hone]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      _ ≤ ∑ i ∈ Finset.range (K.find x), φ i x := hsum_le
  · intro x
    exact qfun_nonneg x

/-- Helper for Exercise 50.6: a nonnegative scalar exhaustion gives a
cocompact Euclidean-valued map by occupying one coordinate. -/
private lemma exists_cocompact_euclideanMap {m : ℕ}
    {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] :
    ∃ p : C(X, EuclideanSpace ℝ (Fin (2 * m + 1))),
      Filter.Tendsto p (Filter.cocompact X)
        (Filter.cocompact (EuclideanSpace ℝ (Fin (2 * m + 1)))) := by
  obtain ⟨q, hq, hq_nonneg⟩ := exists_continuousMap_tendsto_cocompact_atTop (X := X)
  have hdim : 0 < 2 * m + 1 := by omega
  let i : Fin (2 * m + 1) := ⟨0, hdim⟩
  have pcontinuous : Continuous (fun x ↦ EuclideanSpace.single i (q x)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (2 * m + 1) ↦ ℝ)).comp
    apply continuous_pi
    intro j
    by_cases hji : j = i
    · simpa [Pi.single_apply, hji] using q.continuous
    · have hij : i ≠ j := Ne.symm hji
      simpa [Pi.single_apply, hji, hij] using
        (continuous_const : Continuous fun _ : X ↦ (0 : ℝ))
  let p : C(X, EuclideanSpace ℝ (Fin (2 * m + 1))) :=
    ⟨fun x ↦ EuclideanSpace.single i (q x), pcontinuous⟩
  refine ⟨p, ?_⟩
  -- Properness of Euclidean space reduces cocompact convergence to divergence
  -- of the norm, which is exactly the scalar exhaustion in the chosen coordinate.
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
  have hnorm : (fun x ↦ ‖p x‖) = q := by
    funext x
    have hp_apply : p x = EuclideanSpace.single i (q x) := rfl
    rw [hp_apply, PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg (hq_nonneg x)]
  rw [hnorm]
  exact hq

/-- Helper for Exercise 50.6: adding a bounded continuous map preserves
cocompact convergence into a proper normed additive group. -/
private lemma ContinuousMap.tendsto_cocompact_add_bounded
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [ProperSpace E]
    (p : C(X, E))
    (hp : Filter.Tendsto p (Filter.cocompact X) (Filter.cocompact E))
    (h : X →ᵇ E) :
    Filter.Tendsto (p + h.toContinuousMap) (Filter.cocompact X)
      (Filter.cocompact E) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded] at hp ⊢
  have hbound (x : X) :
      ‖p x‖ - ‖h‖ ≤ ‖(p + h.toContinuousMap) x‖ := by
    calc
      ‖p x‖ - ‖h‖ ≤ ‖p x‖ - ‖h x‖ :=
        sub_le_sub_left (h.norm_coe_le_norm x) _
      _ ≤ ‖p x + h x‖ := by
        simpa only [norm_neg, sub_neg_eq_add] using norm_sub_norm_le (p x) (-h x)
      _ = ‖(p + h.toContinuousMap) x‖ := rfl
  -- The lower comparison tends to infinity because it differs from `‖p x‖`
  -- by the fixed global bound `‖h‖`.
  apply Filter.tendsto_atTop_mono hbound
  simpa only [sub_eq_add_neg] using
    Filter.tendsto_atTop_add_const_right _ (-‖h‖) hp

/-- Helper for Exercise 50.6: restrict an affine bounded perturbation of `p`
to a prescribed subset. -/
private def ContinuousMap.restrictBoundedPerturbation
    {X E : Type*} [TopologicalSpace X]
    [PseudoMetricSpace E] [Add E] [ContinuousAdd E] (p : C(X, E)) (K : Set X)
    (h : X →ᵇ E) : C(K, E) :=
  (p + h.toContinuousMap).restrict K

/-- Helper for Exercise 50.6: evaluation of a restricted affine bounded
perturbation is pointwise addition. -/
private lemma ContinuousMap.restrictBoundedPerturbation_apply
    {X E : Type*} [TopologicalSpace X]
    [PseudoMetricSpace E] [Add E] [ContinuousAdd E] (p : C(X, E)) (K : Set X)
    (h : X →ᵇ E) (x : K) :
    p.restrictBoundedPerturbation K h x = p x + h x := by
  rfl

/-- Helper for Exercise 50.6: restriction of an affine perturbation does not
increase the uniform distance between its bounded perturbation terms. -/
private lemma ContinuousMap.dist_restrictBoundedPerturbation_le
    {X E : Type*} [TopologicalSpace X] [PseudoMetricSpace X]
    [NormedAddCommGroup E] {K : Set X} [CompactSpace K]
    (p : C(X, E)) (g h : X →ᵇ E) :
    dist (p.restrictBoundedPerturbation K g)
      (p.restrictBoundedPerturbation K h) ≤ dist g h := by
  apply (ContinuousMap.dist_le dist_nonneg).2
  intro x
  simp only [ContinuousMap.restrictBoundedPerturbation_apply, dist_add_left]
  exact BoundedContinuousFunction.dist_coe_le_dist (f := g) (g := h) x

/-- Helper for Exercise 50.6: bounded perturbations that separate a compact
set at a reciprocal scale form an open dense set. -/
private lemma isOpen_dense_boundedPerturbations_separatesOnCompact
    {X : Type u} [MetricSpace X] {m : ℕ} (K : Set X) (hK : IsCompact K)
    (h_dim : HasCoveringDimensionLE K m)
    (p : C(X, EuclideanSpace ℝ (Fin (2 * m + 1)))) (n : ℕ) :
    IsOpen {h : X →ᵇ EuclideanSpace ℝ (Fin (2 * m + 1)) |
      (p.restrictBoundedPerturbation K h).SeparatesAtScale
        (1 / (n + 1 : ℝ))} ∧
    Dense {h : X →ᵇ EuclideanSpace ℝ (Fin (2 * m + 1)) |
      (p.restrictBoundedPerturbation K h).SeparatesAtScale
        (1 / (n + 1 : ℝ))} := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  constructor
  · -- Pull the compact-domain open ball back along the nonexpanding
    -- restriction-of-perturbations map.
    rw [Metric.isOpen_iff]
    intro h hh
    have hopen := isOpen_setOf_separatesAtScale
      (X := K) (E := EuclideanSpace ℝ (Fin (2 * m + 1)))
      (δ := 1 / (n + 1 : ℝ))
    rw [Metric.isOpen_iff] at hopen
    obtain ⟨ε, hε, hball⟩ := hopen (p.restrictBoundedPerturbation K h) hh
    refine ⟨ε, hε, ?_⟩
    intro g hg
    apply hball
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (p.dist_restrictBoundedPerturbation_le g h)
      (Metric.mem_ball.mp hg)
  · -- Approximate on `K`, extend the compact correction without increasing
    -- its norm, and add that bounded extension to the original perturbation.
    rw [Metric.dense_iff]
    intro h ε hε
    let fK : C(K, EuclideanSpace ℝ (Fin (2 * m + 1))) :=
      p.restrictBoundedPerturbation K h
    have hdense := (isOpen_dense_setOf_separatesAtScale h_dim n).2
    rw [Metric.dense_iff] at hdense
    obtain ⟨gK, hgKball, hgKsep⟩ :=
      hdense fK ε hε
    let dK : K →ᵇ EuclideanSpace ℝ (Fin (2 * m + 1)) :=
      BoundedContinuousFunction.mkOfCompact (gK - fK)
    obtain ⟨d, hdnorm, hdrestrict⟩ :=
      BoundedContinuousFunction.exists_norm_eq_restrict_eq hK.isClosed ℝ dK
    refine ⟨h + d, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      simpa only [add_sub_cancel_left, hdnorm, dK,
        BoundedContinuousFunction.norm_mkOfCompact, dist_eq_norm]
        using Metric.mem_ball.mp hgKball
    · have hd_apply (x : K) : d x = dK x := by
        have h := DFunLike.congr_fun hdrestrict x
        exact h
      have hrestrict : p.restrictBoundedPerturbation K (h + d) = gK := by
        apply ContinuousMap.ext
        intro x
        rw [p.restrictBoundedPerturbation_apply K (h + d) x]
        have hadd_apply : (h + d) x = h x + d x := rfl
        rw [hadd_apply, hd_apply x]
        simp only [dK,
          BoundedContinuousFunction.mkOfCompact_apply, fK,
          ContinuousMap.sub_apply, p.restrictBoundedPerturbation_apply]
        abel
      simp only [Set.mem_setOf_eq]
      rw [hrestrict]
      exact hgKsep

/-- Helper for Exercise 50.6: a map whose restriction to every member of a
compact exhaustion is injective is itself injective. -/
private lemma Function.Injective.of_injectiveOnCompactExhaustion
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    (K : CompactExhaustion X) (f : C(X, E))
    (hf : ∀ n : ℕ, Function.Injective (f.restrict (K n))) :
    Function.Injective f := by
  intro x y hxy
  obtain ⟨a, hxa⟩ := K.exists_mem x
  obtain ⟨b, hyb⟩ := K.exists_mem y
  let n := max a b
  have ha_le : a ≤ n := le_max_left _ _
  have hb_le : b ≤ n := le_max_right _ _
  have hxK : x ∈ K n := K.subset ha_le hxa
  have hyK : y ∈ K n := K.subset hb_le hyb
  -- Put both points in one exhaustion member and use injectivity there.
  have hsub : (⟨x, hxK⟩ : K n) = ⟨y, hyK⟩ := hf n hxy
  exact congrArg Subtype.val hsub

/-- Exercise 50.6. A locally compact Hausdorff space with a countable basis whose
compact subspaces have covering dimension at most `m` admits a closed embedding
into `EuclideanSpace ℝ (Fin (2 * m + 1))`. -/
theorem exists_isClosedEmbedding_euclidean_of_compactDimension_le {m : ℕ}
    {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X]
    (h_dim : ∀ K : Set X, IsCompact K → HasCoveringDimensionLE K m) :
    ∃ f : X → EuclideanSpace ℝ (Fin (2 * m + 1)),
      Topology.IsClosedEmbedding f := by
  -- Fix one compatible metric and one compact exhaustion. The hypotheses
  -- provide both metrizability and sigma-compactness canonically.
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let K : CompactExhaustion X := CompactExhaustion.choice X
  obtain ⟨p, hp⟩ := exists_cocompact_euclideanMap (m := m) (X := X)
  let good : ℕ → Set (X →ᵇ EuclideanSpace ℝ (Fin (2 * m + 1))) := fun r ↦
    {h | (p.restrictBoundedPerturbation (K (Nat.unpair r).1) h).SeparatesAtScale
      (1 / ((Nat.unpair r).2 + 1 : ℝ))}
  have hopen : ∀ r, IsOpen (good r) := by
    intro r
    exact (isOpen_dense_boundedPerturbations_separatesOnCompact
      (K (Nat.unpair r).1) (K.isCompact (Nat.unpair r).1)
      (h_dim (K (Nat.unpair r).1) (K.isCompact (Nat.unpair r).1))
      p (Nat.unpair r).2).1
  have hdense : ∀ r, Dense (good r) := by
    intro r
    exact (isOpen_dense_boundedPerturbations_separatesOnCompact
      (K (Nat.unpair r).1) (K.isCompact (Nat.unpair r).1)
      (h_dim (K (Nat.unpair r).1) (K.isCompact (Nat.unpair r).1))
      p (Nat.unpair r).2).2
  -- Baire category chooses one globally bounded perturbation satisfying every
  -- reciprocal separation scale on every compact exhaustion member.
  obtain ⟨h, hh⟩ := (BaireSpace.baire_property good hopen hdense).nonempty
  let f : C(X, EuclideanSpace ℝ (Fin (2 * m + 1))) := p + h.toContinuousMap
  have hrestrict_injective : ∀ a : ℕ, Function.Injective (f.restrict (K a)) := by
    intro a
    apply Function.Injective.of_separatesAtAllReciprocalScales (f.restrict (K a))
    intro j
    have hgood := Set.mem_iInter.mp hh (Nat.pair a j)
    simp only [good] at hgood
    have hunpair := Nat.unpair_pair a j
    rw [hunpair] at hgood
    have hsep := Set.mem_setOf_eq.mp hgood
    simpa only [f, ContinuousMap.restrictBoundedPerturbation] using hsep
  have hinjective : Function.Injective f :=
    Function.Injective.of_injectiveOnCompactExhaustion K f hrestrict_injective
  have hf_cocompact : Filter.Tendsto f (Filter.cocompact X)
      (Filter.cocompact (EuclideanSpace ℝ (Fin (2 * m + 1)))) := by
    exact p.tendsto_cocompact_add_bounded hp h
  have hf_proper : IsProperMap f := by
    exact isProperMap_iff_tendsto_cocompact.mpr ⟨f.continuous, hf_cocompact⟩
  -- A continuous proper injection is a closed embedding.
  refine ⟨f, ?_⟩
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    f.continuous hinjective hf_proper.isClosedMap

open scoped CoveringDimension

/-- The numerical covering-dimension form of Exercise 50.6. -/
theorem exists_isClosedEmbedding_euclidean_of_compact_coveringDimension_le {m : ℕ}
    {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X]
    (h_dim : ∀ K : Set X, IsCompact K → dim K ≤ (m : WithBot ℕ∞)) :
    ∃ f : X → EuclideanSpace ℝ (Fin (2 * m + 1)),
      Topology.IsClosedEmbedding f :=
  exists_isClosedEmbedding_euclidean_of_compactDimension_le fun K hK ↦
    (coveringDimension_le_iff K m).1 (h_dim K hK)
