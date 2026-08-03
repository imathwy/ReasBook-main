module

public import Topology_Munkres_2000.Book.Definition_40_4.SigmaLocallyDiscreteFamily
public import Topology_Munkres_2000.Book.Theorem_40_3
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Metrizable.Uniformity

public section

open ENNReal Set TopologicalSpace Topology

universe u v

variable {ι : Type u} {Y : Type v}

/-- Helper for Theorem 40.1: an open cover of a pseudo-emetric space has an open precise
refinement that is locally discrete at each natural-number level. -/
private lemma exists_sigmaLocallyDiscrete_openRefinement [PseudoEMetricSpace Y]
    (cover : ι → Set Y) (hopen : ∀ i, IsOpen (cover i))
    (hcover : ⋃ i, cover i = Set.univ) :
    ∃ refinement : ℕ → ι → Set Y,
      (∀ n i, IsOpen (refinement n i)) ∧
        ((⋃ n, ⋃ i, refinement n i) = Set.univ) ∧
          (∀ n i, refinement n i ⊆ cover i) ∧
            ∀ n, LocallyDiscreteFamily (Subtype.val : Set.range (refinement n) → Set Y) := by
  classical
  -- The construction follows the level decomposition in the metric paracompactness proof.
  have pow_pos : ∀ k : ℕ, (0 : ℝ≥0∞) < 2⁻¹ ^ k := fun k ↦
    ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _
  have hpow_le : ∀ {m n : ℕ}, m ≤ n → (2⁻¹ : ℝ≥0∞) ^ n ≤ 2⁻¹ ^ m :=
    fun h ↦ pow_le_pow_right_of_le_one'
      (ENNReal.inv_le_one.2 ENNReal.one_lt_two.le) h
  have h2pow : ∀ n : ℕ, 2 * (2⁻¹ : ℝ≥0∞) ^ (n + 1) = 2⁻¹ ^ n := fun n ↦ by
    simp [pow_succ', ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ofNat_ne_top]
  have hcoverPoint : ∀ y : Y, ∃ i, y ∈ cover i := by
    intro y
    have hy : y ∈ ⋃ i, cover i := by
      rw [hcover]
      exact Set.mem_univ y
    exact Set.mem_iUnion.mp hy
  obtain ⟨_, wellFounded⟩ := exists_wellFoundedLT ι
  let index (y : Y) : ι :=
    wellFounded_lt.min {i : ι | y ∈ cover i} (hcoverPoint y)
  have mem_index (y : Y) : y ∈ cover (index y) :=
    wellFounded_lt.min_mem _ (hcoverPoint y)
  have notMem_of_lt_index {y : Y} {i : ι} (hlt : i < index y)
      (hyi : y ∈ cover i) : False :=
    wellFounded_lt.not_lt_min {i : ι | y ∈ cover i} hyi hlt
  set refinement : ℕ → ι → Set Y :=
    Nat.strongRec fun n previous i ↦
      ⋃ (y : Y) (_ : index y = i) (_ : Metric.eball y (3 * 2⁻¹ ^ n) ⊆ cover i)
        (_ : ∀ (m : ℕ) (hm : m < n) (j : ι), y ∉ previous m hm j),
          Metric.eball y (2⁻¹ ^ n) with hrefinement
  have refinement_eq (n : ℕ) (i : ι) :
      refinement n i =
        ⋃ (y : Y) (_ : index y = i) (_ : Metric.eball y (3 * 2⁻¹ ^ n) ⊆ cover i)
          (_ : ∀ (m : ℕ), m < n → ∀ j : ι, y ∉ refinement m j),
            Metric.eball y (2⁻¹ ^ n) := by
    simp only [hrefinement]
    rw [Nat.strongRec_eq]
  have mem_refinement {n : ℕ} {i : ι} {z : Y} :
      z ∈ refinement n i ↔
        ∃ y : Y, index y = i ∧ Metric.eball y (3 * 2⁻¹ ^ n) ⊆ cover i ∧
          (∀ (m : ℕ), m < n → ∀ j : ι, y ∉ refinement m j) ∧
            edist z y < 2⁻¹ ^ n := by
    rw [refinement_eq]
    simp only [Set.mem_iUnion, Metric.mem_eball, exists_prop]
  have refinement_cover (y : Y) : ∃ n i, y ∈ refinement n i := by
    obtain ⟨n, hn⟩ :
        ∃ n : ℕ, Metric.eball y (3 * 2⁻¹ ^ n) ⊆ cover (index y) := by
      obtain ⟨ε, hε, hεsub⟩ := EMetric.isOpen_iff.mp (hopen (index y)) y (mem_index y)
      have hεthird : 0 < ε / 3 := ENNReal.div_pos_iff.mpr ⟨hε.ne', ENNReal.coe_ne_top⟩
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt hεthird.ne'
      refine ⟨n, (Metric.eball_subset_eball ?_).trans hεsub⟩
      simpa only [div_eq_mul_inv, mul_comm] using (ENNReal.mul_lt_of_lt_div hn).le
    by_contra! hmissing
    apply hmissing n (index y)
    exact mem_refinement.mpr
      ⟨y, rfl, hn, fun m _ i ↦ hmissing m i, Metric.mem_eball_self (pow_pos n)⟩
  have refinement_open (n : ℕ) (i : ι) : IsOpen (refinement n i) := by
    rw [refinement_eq]
    iterate 4 refine isOpen_iUnion fun _ ↦ ?_
    exact Metric.isOpen_eball
  have refinement_subset (n : ℕ) (i : ι) : refinement n i ⊆ cover i := by
    intro z hz
    obtain ⟨y, rfl, hsubset, -, hzy⟩ := mem_refinement.mp hz
    exact hsubset (hzy.trans_le (le_mul_of_one_le_left' (by norm_num1)))
  have refinement_local (n : ℕ) :
      LocallyDiscreteFamily (Subtype.val : Set.range (refinement n) → Set Y) := by
    rw [locallyDiscreteFamily_subtype_iff]
    intro y
    obtain ⟨m, i, hy⟩ := refinement_cover y
    have hnhds : refinement m i ∈ 𝓝 y :=
      IsOpen.mem_nhds (refinement_open m i) hy
    obtain ⟨k, -, hk : Metric.eball y (2⁻¹ ^ k) ⊆ refinement m i⟩ :=
      (nhds_basis_uniformity uniformity_basis_edist_inv_two_pow).mem_iff.mp hnhds
    let neighborhood := Metric.eball y (2⁻¹ ^ (m + k + 1))
    have high_disjoint (level : ℕ) (hlevel : m + k + 1 ≤ level) (j : ι) :
        Disjoint (refinement level j) neighborhood := by
      rw [disjoint_iff_inf_le]
      rintro z ⟨hzD, hzB⟩
      obtain ⟨center, -, -, hprior, hzCenter⟩ := mem_refinement.mp hzD
      have hcenterOutside : center ∉ Metric.eball y (2⁻¹ ^ k) := by
        intro hcenter
        exact hprior m (by omega) i (hk hcenter)
      apply hcenterOutside
      rw [Metric.mem_eball]
      calc
        edist center y ≤ edist z center + edist z y := edist_triangle_left _ _ _
        _ < 2⁻¹ ^ level + 2⁻¹ ^ (m + k + 1) :=
          ENNReal.add_lt_add hzCenter hzB
        _ ≤ 2⁻¹ ^ (k + 1) + 2⁻¹ ^ (k + 1) :=
          add_le_add (hpow_le (by omega)) (hpow_le (by omega))
        _ = 2⁻¹ ^ k := by rw [← two_mul, h2pow]
    refine ⟨neighborhood, Metric.eball_mem_nhds _ (pow_pos _), ?_⟩
    rintro A ⟨z₁, hz₁D, hz₁B⟩ B ⟨z₂, hz₂D, hz₂B⟩
    by_cases hlevel : n ≤ m + k
    · obtain ⟨i₁, hi₁⟩ := A.property
      obtain ⟨i₂, hi₂⟩ := B.property
      apply Subtype.ext
      rw [← hi₁, ← hi₂]
      by_contra hsets
      have hiNe : i₁ ≠ i₂ := fun hindices ↦
        hsets (congrArg (refinement n) hindices)
      have impossible {j₁ j₂ : ι} {w₁ w₂ : Y}
          (hlt : j₁ < j₂) (hw₁D : w₁ ∈ refinement n j₁)
          (hw₁B : w₁ ∈ neighborhood) (hw₂D : w₂ ∈ refinement n j₂)
          (hw₂B : w₂ ∈ neighborhood) : False := by
        obtain ⟨center₁, rfl, hsubset, -, hdist₁⟩ := mem_refinement.mp hw₁D
        obtain ⟨center₂, rfl, -, -, hdist₂⟩ := mem_refinement.mp hw₂D
        apply notMem_of_lt_index hlt
        apply hsubset
        have hdist₂' : edist center₂ w₂ < 2⁻¹ ^ n := by
          simpa only [edist_comm] using hdist₂
        have hw₁B' : edist y w₁ < 2⁻¹ ^ (m + k + 1) := by
          simpa only [neighborhood, Metric.mem_eball, edist_comm] using hw₁B
        calc
          edist center₂ center₁ ≤ edist center₂ y + edist y center₁ :=
            edist_triangle _ _ _
          _ ≤ (edist center₂ w₂ + edist w₂ y) +
              (edist y w₁ + edist w₁ center₁) :=
            add_le_add (edist_triangle _ _ _) (edist_triangle _ _ _)
          _ < (2⁻¹ ^ n + 2⁻¹ ^ (m + k + 1)) +
              (2⁻¹ ^ (m + k + 1) + 2⁻¹ ^ n) := by
            exact ENNReal.add_lt_add
              (ENNReal.add_lt_add hdist₂' hw₂B)
              (ENNReal.add_lt_add hw₁B' hdist₁)
          _ = 2 * (2⁻¹ ^ n + 2⁻¹ ^ (m + k + 1)) := by
            simp only [two_mul, add_comm, add_left_comm, add_assoc]
          _ ≤ 2 * (2⁻¹ ^ n + 2⁻¹ ^ (n + 1)) := by
            gcongr 2 * (_ + ?_)
            exact hpow_le (by omega)
          _ = 3 * 2⁻¹ ^ n := by
            rw [mul_add, h2pow, ← two_add_one_eq_three, add_mul, one_mul]
      exact (hiNe.lt_or_gt.elim
        (fun hlt ↦ (impossible hlt (hi₁ ▸ hz₁D) hz₁B (hi₂ ▸ hz₂D) hz₂B).elim)
        (fun hgt ↦ (impossible hgt (hi₂ ▸ hz₂D) hz₂B (hi₁ ▸ hz₁D) hz₁B).elim))
    · obtain ⟨i₁, hi₁⟩ := A.property
      have hz₁D' : z₁ ∈ refinement n i₁ := hi₁ ▸ hz₁D
      exact ((high_disjoint n (by omega) i₁).le_bot ⟨hz₁D', hz₁B⟩).elim
  refine ⟨refinement, refinement_open, ?_, refinement_subset, refinement_local⟩
  -- Coverage is the pointwise coverage proved above, rewritten as an indexed union.
  refine Set.iUnion_eq_univ_iff.mpr fun y ↦ ?_
  obtain ⟨n, i, hy⟩ := refinement_cover y
  exact ⟨n, Set.mem_iUnion.mpr ⟨i, hy⟩⟩

/-- Helper for Theorem 40.1: every metrizable space has a sigma-locally-discrete basis. -/
private theorem MetrizableSpace.hasSigmaLocallyDiscreteBasis
    (X : Type u) [TopologicalSpace X] [MetrizableSpace X] :
    HasSigmaLocallyDiscreteBasis X := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let radius (n : ℕ) : ℝ := 1 / (n + 1)
  have radius_pos (n : ℕ) : 0 < radius n := by
    exact one_div_pos.mpr (by positivity)
  let cover (n : ℕ) (x : X) := Metric.ball x (radius n / 4)
  have cover_open (n : ℕ) (x : X) : IsOpen (cover n x) := Metric.isOpen_ball
  have cover_univ (n : ℕ) : ⋃ x, cover n x = Set.univ := by
    refine Set.iUnion_eq_univ_iff.mpr fun x ↦ ?_
    exact ⟨x, Metric.mem_ball_self (div_pos (radius_pos n) (by norm_num))⟩
  choose refinement refinement_open refinement_cover refinement_subset refinement_local using
    fun n ↦ exists_sigmaLocallyDiscrete_openRefinement (cover n) (cover_open n) (cover_univ n)
  let basisSets : Set (Set X) := Set.range fun p : ℕ × ℕ × X ↦ refinement p.1 p.2.1 p.2.2
  have basis_open : ∀ U ∈ basisSets, IsOpen U := by
    rintro U ⟨p, rfl⟩
    exact refinement_open p.1 p.2.1 p.2.2
  have basis_nhds : ∀ x U, x ∈ U → IsOpen U →
      ∃ V ∈ basisSets, x ∈ V ∧ V ⊆ U := by
    intro x U hx hU
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hU x hx
    obtain ⟨n, hn : 1 / (n + 1 : ℝ) < 2 * ε⟩ :=
      exists_nat_one_div_lt (show 0 < (2 : ℝ) * ε by positivity)
    have hnRadius : radius n / 2 < ε := by
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
      simpa only [radius, mul_comm] using hn
    have hxcover : x ∈ (⋃ m, ⋃ i, refinement n m i) := by
      rw [refinement_cover n]
      exact Set.mem_univ x
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hxcover
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hm
    refine ⟨refinement n m i, ⟨(n, m, i), rfl⟩, hxi, ?_⟩
    intro y hy
    have hyball := refinement_subset n m i hy
    have hxball := refinement_subset n m i hxi
    rw [Metric.mem_ball] at hyball hxball
    apply hεsub
    calc
      dist y x ≤ dist y i + dist i x := dist_triangle _ _ _
      _ < radius n / 4 + radius n / 4 :=
        add_lt_add hyball (by simpa only [dist_comm] using hxball)
      _ = radius n / 2 := by ring
      _ < ε := hnRadius
  have basis_topological : TopologicalSpace.IsTopologicalBasis basisSets :=
    TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds basis_open basis_nhds
  rw [hasSigmaLocallyDiscreteBasis_iff]
  refine ⟨basisSets, fun q ↦ Set.range fun x ↦
    refinement (Nat.unpair q).1 (Nat.unpair q).2 x, basis_topological, ?_, ?_⟩
  · ext U
    constructor
    · rintro ⟨p, rfl⟩
      refine Set.mem_iUnion.mpr ⟨Nat.pair p.1 p.2.1, ?_⟩
      exact ⟨p.2.2, by rw [Nat.unpair_pair]⟩
    · intro hU
      obtain ⟨q, x, rfl⟩ := Set.mem_iUnion.mp hU
      exact ⟨((Nat.unpair q).1, (Nat.unpair q).2, x), rfl⟩
  · intro q
    exact refinement_local (Nat.unpair q).1 (Nat.unpair q).2

/-- Helper for Theorem 40.1: a sigma-locally-discrete basis is sigma-locally finite. -/
private theorem HasSigmaLocallyDiscreteBasis.hasSigmaLocallyFiniteBasis
    {X : Type u} [TopologicalSpace X] (hX : HasSigmaLocallyDiscreteBasis X) :
    HasSigmaLocallyFiniteBasis X := by
  rw [hasSigmaLocallyDiscreteBasis_iff] at hX
  rw [hasSigmaLocallyFiniteBasis_iff]
  obtain ⟨basis, pieces, hbasis, hunion, hlocal⟩ := hX
  refine ⟨basis, pieces, hbasis, hunion, ?_⟩
  intro n
  exact (hlocal n).locallyFinite

/-- Theorem 40.1 (Bing metrization theorem): a topological space is metrizable if and
only if it is regular and has a countably locally discrete basis. -/
theorem bingMetrization (X : Type u) [TopologicalSpace X] :
    MetrizableSpace X ↔ T3Space X ∧ HasSigmaLocallyDiscreteBasis X := by
  constructor
  · intro hX
    letI : MetrizableSpace X := hX
    -- Metric spaces are regular, and the preceding helper supplies the required basis.
    exact ⟨inferInstance, MetrizableSpace.hasSigmaLocallyDiscreteBasis X⟩
  · rintro ⟨hregular, hbasis⟩
    -- Forget local discreteness levelwise, then apply Nagata--Smirnov.
    exact (nagataSmirnovMetrization X).mpr
      ⟨hregular, hbasis.hasSigmaLocallyFiniteBasis⟩
