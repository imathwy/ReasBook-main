module

public import Topology_Munkres_2000.Book.Definition_20_9.UniformMetric
public import Topology_Munkres_2000.Book.Definition_19_1.BoxTopology

public section

open scoped Topology

universe u

namespace UniformMetric

/-- Helper for Theorem 20.4: each truncated coordinate distance is bounded by the uniform
distance. -/
private lemma coordinateDist_le_uniformDist {J : Type u} (x y : J → ℝ) (j : J) :
    min (dist (x j) (y j)) 1 ≤ (metricSpace J).dist x y := by
  -- Select the `j`th term from the supremum defining the uniform distance.
  rw [dist_eq]
  apply le_ciSup (α := ℝ) (f := fun k : J ↦ min (dist (x k) (y k)) 1)
  · exact ⟨1, Set.forall_mem_range.mpr fun i ↦ min_le_right _ _⟩

/-- Helper for Theorem 20.4: a uniform coordinatewise bound controls the uniform distance. -/
private lemma uniformDist_le_of_coordinateDist_le {J : Type u}
    (x y : J → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ j, min (dist (x j) (y j)) 1 ≤ r) :
    (metricSpace J).dist x y ≤ r := by
  -- Bound the defining supremum, treating the empty product separately.
  rw [dist_eq]
  cases isEmpty_or_nonempty J with
  | inl _ => simpa using hr
  | inr _ => exact ciSup_le h

/-- Helper for Theorem 20.4: the coordinate box of radius `ε / 2` lies in the uniform
`ε`-ball. -/
private lemma boxInterval_subset_uniformBall {J : Type u}
    (x : J → ℝ) {ε : ℝ} (hε : 0 < ε) :
    Set.pi Set.univ (fun j ↦ Set.Ioo (x j - ε / 2) (x j + ε / 2)) ⊆
      @Metric.ball (J → ℝ) (metricSpace J).toPseudoMetricSpace x ε := by
  -- Convert coordinate interval membership into a uniform supremum estimate.
  intro y hy
  have hdist : (metricSpace J).dist y x ≤ ε / 2 := by
    apply uniformDist_le_of_coordinateDist_le
    · linarith
    · intro j
      have hj := (Set.mem_pi.mp hy) j (Set.mem_univ j)
      have habs : |y j - x j| < ε / 2 := by
        rw [abs_lt]
        constructor
        · linarith [hj.1]
        · linarith [hj.2]
      have hd : dist (y j) (x j) ≤ ε / 2 := by
        rw [Real.dist_eq]
        exact habs.le
      exact (min_le_left _ _).trans hd
  have hhalf : ε / 2 < ε := by
    linarith
  exact lt_of_le_of_lt hdist hhalf

/-- Helper for Theorem 20.4: on an infinite product, the uniform half-ball at zero is not
product-open. -/
private lemma uniformBall_zero_not_productOpen (J : Type u) [Infinite J] :
    ¬ IsOpen[Pi.topologicalSpace]
      (@Metric.ball (J → ℝ) (metricSpace J).toPseudoMetricSpace 0 (1 / 2)) := by
  -- A product neighborhood controls finitely many coordinates, so alter an uncontrolled one.
  classical
  intro hopen
  have hzero : (0 : J → ℝ) ∈
      @Metric.ball (J → ℝ) (metricSpace J).toPseudoMetricSpace 0 (1 / 2) := by
    simp
  obtain ⟨I, U, hU, hsub⟩ := isOpen_pi_iff.mp hopen 0 hzero
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset I
  let y : J → ℝ := Function.update 0 j 1
  have hybasis : y ∈ (I : Set J).pi U := by
    rw [Set.mem_pi]
    intro i hi
    have hij : i ≠ j := by
      intro h
      apply hj
      simpa [h] using hi
    dsimp [y]
    rw [Function.update_of_ne hij]
    exact (hU i hi).2
  have hyball : (metricSpace J).dist y 0 < 1 / 2 := hsub hybasis
  have hcoord := coordinateDist_le_uniformDist y 0 j
  have hjvalue : y j = 1 := by
    simp [y]
  rw [hjvalue, Pi.zero_apply, Real.dist_eq] at hcoord
  norm_num at hcoord hyball
  linarith

/-- Helper for Theorem 20.4: an infinite product has a box-open neighborhood of zero that is
not uniform-open. -/
private lemma exists_boxOpen_not_uniformOpen (J : Type u) [Infinite J] :
    ∃ U : Set (J → ℝ), IsOpen[Pi.boxTopologicalSpace (fun _ : J ↦ ℝ)] U ∧
      (0 : J → ℝ) ∈ U ∧ ¬ IsOpen[topology J] U := by
  -- Use radii tending to zero along a countable embedded subset of `J`.
  classical
  let e : ℕ ↪ J := Infinite.natEmbedding J
  let r : J → ℝ := fun j ↦ 1 / (((Function.invFun e j : ℕ) : ℝ) + 1)
  let U : Set (J → ℝ) := Set.pi Set.univ fun j ↦ Set.Ioo (-r j) (r j)
  refine ⟨U, ?_, ?_, ?_⟩
  · exact @Pi.isOpen_box J (fun _ ↦ ℝ) (fun _ ↦ inferInstance)
      (fun j ↦ Set.Ioo (-r j) (r j)) (fun j ↦ isOpen_Ioo)
  · rw [Set.mem_pi]
    intro j hj
    have hrpos : 0 < r j := by
      dsimp [r]
      positivity
    constructor
    · simpa using hrpos
    · simpa using hrpos
  · intro hopen
    have hzero : (0 : J → ℝ) ∈ U := by
      rw [Set.mem_pi]
      intro j hj
      have hrpos : 0 < r j := by
        dsimp [r]
        positivity
      constructor
      · simpa using hrpos
      · simpa using hrpos
    have hopen' : @IsOpen (J → ℝ) (topology J) U := hopen
    rw [@Metric.isOpen_iff _ (metricSpace J).toPseudoMetricSpace] at hopen'
    obtain ⟨ε, hε, hball⟩ := hopen' 0 hzero
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    let j := e n
    let a : ℝ := 1 / ((n : ℝ) + 1)
    let y : J → ℝ := Function.update 0 j a
    have hrj : r j = a := by
      dsimp [r, j, a, e]
      rw [Function.leftInverse_invFun (Infinite.natEmbedding J).injective]
    have ha0 : 0 ≤ a := by
      dsimp [a]
      positivity
    have ha1 : a ≤ 1 := by
      dsimp [a]
      rw [div_le_one (by positivity)]
      norm_num
    have hydist : (metricSpace J).dist y 0 < ε := by
      refine lt_of_le_of_lt (uniformDist_le_of_coordinateDist_le y 0 a ha0 ?_) hn
      intro i
      by_cases hij : i = j
      · subst i
        have hyj : y j = a := by
          simp [y]
        rw [hyj, Pi.zero_apply, Real.dist_eq, sub_zero, abs_of_nonneg ha0, min_eq_left ha1]
      · dsimp [y]
        rw [Function.update_of_ne hij]
        simpa using ha0
    have hyU := hball hydist
    have hyj : y j = a := by
      simp [y]
    have hycoord := (Set.mem_pi.mp hyU) j (Set.mem_univ j)
    rw [hyj, hrj] at hycoord
    exact (lt_irrefl a hycoord.2).elim

/-- Companion for Theorem 20.4 (1): The uniform topology on `J → ℝ` is finer than
the product topology.
This is `≤` in Lean's reverse-inclusion order on topologies. -/
theorem topology_le_product (J : Type u) :
    topology J ≤ (Pi.topologicalSpace : TopologicalSpace (J → ℝ)) := by
  -- Each coordinate evaluation is continuous because its truncated distance is uniformly bounded.
  rw [← continuous_id_iff_le]
  refine @continuous_pi (J → ℝ) J (fun _ ↦ ℝ) (topology J) (fun _ ↦ inferInstance)
    id ?_
  intro j
  letI : MetricSpace (J → ℝ) := metricSpace J
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro y hy
  have hmin : min (dist (y j) (x j)) 1 < min ε 1 :=
    lt_of_le_of_lt (coordinateDist_le_uniformDist y x j) hy
  by_cases hd : dist (y j) (x j) ≤ 1
  · exact lt_of_lt_of_le (by simpa [min_eq_left hd] using hmin) (min_le_left ε 1)
  · have hminOne : (1 : ℝ) < min ε 1 := by
      rw [min_eq_right (le_of_not_ge hd)] at hmin
      exact hmin
    have hcontra : (1 : ℝ) < 1 := lt_of_lt_of_le hminOne (min_le_right ε 1)
    exact hcontra.false.elim

/-- Companion for Theorem 20.4 (2): The uniform topology on `J → ℝ` is coarser than
the box topology.
Equivalently, the box topology is `≤` the uniform topology in Lean's order. -/
theorem box_le_topology (J : Type u) :
    Pi.boxTopologicalSpace (fun _ : J ↦ ℝ) ≤ topology J := by
  -- Every uniform-open neighborhood contains a coordinatewise open box.
  intro s hs
  have hs' : @IsOpen (J → ℝ) (topology J) s := hs
  rw [@Metric.isOpen_iff _ (metricSpace J).toPseudoMetricSpace] at hs'
  rw [@isOpen_iff_mem_nhds _ (Pi.boxTopologicalSpace (fun _ : J ↦ ℝ))]
  intro x hx
  obtain ⟨ε, hε, hball⟩ := hs' x hx
  let U : J → Set ℝ := fun j ↦ Set.Ioo (x j - ε / 2) (x j + ε / 2)
  have hUopen : ∀ j, IsOpen (U j) := fun j ↦ isOpen_Ioo
  have hxU : x ∈ Set.pi Set.univ U := by
    rw [Set.mem_pi]
    intro j hj
    dsimp [U]
    constructor
    · linarith
    · linarith
  have hUsub : Set.pi Set.univ U ⊆ s :=
    (boxInterval_subset_uniformBall x hε).trans hball
  have hUbox : IsOpen[Pi.boxTopologicalSpace (fun _ : J ↦ ℝ)] (Set.pi Set.univ U) := by
    exact @Pi.isOpen_box J (fun _ ↦ ℝ) (fun _ ↦ inferInstance) U hUopen
  exact Filter.mem_of_superset
    (@IsOpen.mem_nhds _ (Pi.boxTopologicalSpace (fun _ : J ↦ ℝ)) x _ hUbox hxU) hUsub

/-- Companion for Theorem 20.4 (3): If `J` is infinite, the uniform topology on `J → ℝ`
is strictly finer
than the product topology, expressed by `<` in Lean's order. -/
theorem topology_lt_product (J : Type u) [Infinite J] :
    topology J < (Pi.topologicalSpace : TopologicalSpace (J → ℝ)) := by
  -- The uniform half-ball is open uniformly but not in the product topology.
  refine lt_of_le_of_ne (topology_le_product J) ?_
  intro heq
  apply uniformBall_zero_not_productOpen J
  rw [← heq]
  exact @Metric.isOpen_ball _ (metricSpace J).toPseudoMetricSpace _ _

/-- Theorem 20.4 (4): If `J` is infinite, the uniform topology on `J → ℝ` is strictly coarser
than the box topology, so the box topology is `<` the uniform topology in Lean's order. -/
theorem box_lt_topology (J : Type u) [Infinite J] :
    Pi.boxTopologicalSpace (fun _ : J ↦ ℝ) < topology J := by
  -- A shrinking box is box-open but fails to contain any uniform ball about zero.
  refine lt_of_le_of_ne (box_le_topology J) ?_
  intro heq
  obtain ⟨U, hUbox, hzero, hUnot⟩ := exists_boxOpen_not_uniformOpen J
  apply hUnot
  rw [← heq]
  exact hUbox

end UniformMetric
