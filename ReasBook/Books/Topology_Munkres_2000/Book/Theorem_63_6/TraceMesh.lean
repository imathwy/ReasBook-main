module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Topology.UniformSpace.HeineCantor

public section

open Set

namespace Schoenflies

universe u v

variable {E : Type u} [MetricSpace E]
variable {I : Type v}

/-- Helper for Theorem 63.6: finite cyclic data covering the circle by compact
connected arcs, with only neighboring arcs allowed to meet. -/
structure CircleCyclicMesh (n : ℕ) where
  vertex : Fin (n + 4) → Circle
  arc : Fin (n + 4) → Set Circle
  vertex_mem_arc : ∀ i, vertex i ∈ arc i
  nextVertex_mem_arc : ∀ i, vertex (i + 1) ∈ arc i
  iUnion_arc : ⋃ i, arc i = Set.univ
  isCompact_arc : ∀ i, IsCompact (arc i)
  isConnected_arc : ∀ i, IsConnected (arc i)
  disjoint_arc_of_not_adjacent : ∀ i j, i ≠ j →
    ¬(SimpleGraph.cycleGraph (n + 4)).Adj i j → Disjoint (arc i) (arc j)

/-- Helper for Theorem 63.6: the unit-period additive quotient followed by the
canonical homeomorphism parameterizes the complex unit circle. -/
noncomputable def unitCircleIntervalParam : ℝ → Circle :=
  fun t ↦ AddCircle.homeomorphCircle one_ne_zero (t : UnitAddCircle)

/-- Helper for Theorem 63.6: the unit-interval circle parameterization is continuous. -/
lemma continuous_unitCircleIntervalParam : Continuous unitCircleIntervalParam := by
  -- Compose continuity of the quotient map with the canonical circle homeomorphism.
  exact (AddCircle.homeomorphCircle one_ne_zero).continuous.comp
    (AddCircle.continuous_mk' 1)

/-- Helper for Theorem 63.6: the `i`th equal-interval arc in a cyclic partition
of the circle into `n + 4` pieces. -/
noncomputable def equalIntervalCircleArc (n : ℕ) (i : Fin (n + 4)) : Set Circle :=
  unitCircleIntervalParam ''
    Icc ((i.val : ℝ) / (n + 4 : ℝ)) ((i.val + 1 : ℕ) / (n + 4 : ℝ))

/-- Helper for Theorem 63.6: every point of the real unit interval belongs to
one of its `n + 4` equal closed subintervals. -/
private lemma exists_mem_equalInterval (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ i : Fin (n + 4),
      t ∈ Icc ((i.val : ℝ) / (n + 4 : ℝ))
        ((i.val + 1 : ℕ) / (n + 4 : ℝ)) := by
  -- The endpoint one belongs to the last interval; otherwise take the floor
  -- of `(n + 4) * t`.
  by_cases ht_one : t = 1
  · refine ⟨⟨n + 3, by omega⟩, ?_⟩
    rw [ht_one]
    constructor
    · apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 4)).2
      norm_num
    · apply (le_div_iff₀ (by positivity : (0 : ℝ) < n + 4)).2
      norm_num [Nat.cast_add]
      linarith
  · have ht_lt_one : t < 1 := lt_of_le_of_ne ht.2 ht_one
    have ht_nonneg : 0 ≤ (n + 4 : ℝ) * t := mul_nonneg (by positivity) ht.1
    let k : ℕ := ⌊(n + 4 : ℝ) * t⌋₊
    have hk_lt : k < n + 4 := by
      rw [Nat.floor_lt ht_nonneg]
      have hden_pos : (0 : ℝ) < (n + 4 : ℕ) := by positivity
      simpa only [Nat.cast_add, Nat.cast_ofNat] using
        mul_lt_of_lt_one_right hden_pos ht_lt_one
    refine ⟨⟨k, hk_lt⟩, ?_⟩
    constructor
    · apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 4)).2
      simpa only [k, mul_comm] using Nat.floor_le ht_nonneg
    · apply (le_div_iff₀ (by positivity : (0 : ℝ) < n + 4)).2
      simpa only [Fin.val_mk, Nat.cast_add, Nat.cast_one, k, mul_comm] using
        (Nat.lt_floor_add_one ((n + 4 : ℝ) * t)).le

/-- Helper for Theorem 63.6: the equal-interval arcs cover the circle. -/
lemma iUnion_equalIntervalCircleArc (n : ℕ) :
    ⋃ i : Fin (n + 4), equalIntervalCircleArc n i = Set.univ := by
  -- Lift an arbitrary circle point to `[0,1]`, then choose its equal subinterval.
  apply Set.eq_univ_of_forall
  intro z
  let e : UnitAddCircle ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  have hz : e.symm z ∈ ((↑) : ℝ → UnitAddCircle) '' Icc (0 : ℝ) 1 := by
    have hcover : ((↑) : ℝ → UnitAddCircle) '' Icc (0 : ℝ) 1 = Set.univ := by
      simpa only [zero_add] using AddCircle.coe_image_Icc_eq (1 : ℝ) 0
    rw [hcover]
    exact Set.mem_univ _
  obtain ⟨t, ht, htq⟩ := hz
  obtain ⟨i, hi⟩ := exists_mem_equalInterval n ht
  rw [Set.mem_iUnion]
  refine ⟨i, t, hi, ?_⟩
  -- The chosen lift represents `z` because `e` is injective.
  simpa [e, unitCircleIntervalParam] using congrArg e htq

/-- Helper for Theorem 63.6: each equal-interval circle arc is compact. -/
lemma isCompact_equalIntervalCircleArc (n : ℕ) (i : Fin (n + 4)) :
    IsCompact (equalIntervalCircleArc n i) := by
  -- Continuous images preserve compactness of the closed parameter interval.
  exact isCompact_Icc.image continuous_unitCircleIntervalParam

/-- Helper for Theorem 63.6: each equal-interval circle arc is connected. -/
lemma isConnected_equalIntervalCircleArc (n : ℕ) (i : Fin (n + 4)) :
    IsConnected (equalIntervalCircleArc n i) := by
  -- Continuous images preserve connectedness of the closed parameter interval.
  have hle : (i.val : ℝ) / (n + 4 : ℝ) ≤
      (i.val + 1 : ℕ) / (n + 4 : ℝ) := by
    apply (div_le_div_iff_of_pos_right (by positivity)).2
    norm_num
  exact (isConnected_Icc hle).image _ continuous_unitCircleIntervalParam.continuousOn

/-- Helper for Theorem 63.6: equality of unit-period quotient representatives
in `[0,1]` is ordinary equality, apart from the two endpoint identifications. -/
private lemma unitAddCircle_coe_eq_coe_iff_of_mem_Icc {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (s : UnitAddCircle) = (t : UnitAddCircle) ↔
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  -- Away from the right endpoint the quotient map is injective on `[0,1)`.
  constructor
  · intro hst
    by_cases hs_one : s = 1
    · by_cases ht_one : t = 1
      · exact Or.inl (hs_one.trans ht_one.symm)
      · right
        right
        refine ⟨hs_one, ?_⟩
        have ht_Ico : t ∈ Ico (0 : ℝ) (0 + 1) := by
          simpa only [zero_add] using ⟨ht.1, lt_of_le_of_ne ht.2 ht_one⟩
        apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
          ht_Ico (by norm_num)).mp
        calc
          (t : UnitAddCircle) = (s : UnitAddCircle) := hst.symm
          _ = (1 : ℝ) := congrArg (↑· : ℝ → UnitAddCircle) hs_one
          _ = 0 := AddCircle.coe_period 1
    · by_cases ht_one : t = 1
      · right
        left
        refine ⟨?_, ht_one⟩
        have hs_Ico : s ∈ Ico (0 : ℝ) (0 + 1) := by
          simpa only [zero_add] using ⟨hs.1, lt_of_le_of_ne hs.2 hs_one⟩
        apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
          hs_Ico (by norm_num)).mp
        calc
          (s : UnitAddCircle) = (t : UnitAddCircle) := hst
          _ = (1 : ℝ) := congrArg (↑· : ℝ → UnitAddCircle) ht_one
          _ = 0 := AddCircle.coe_period 1
      · left
        have hs_Ico : s ∈ Ico (0 : ℝ) (0 + 1) := by
          simpa only [zero_add] using ⟨hs.1, lt_of_le_of_ne hs.2 hs_one⟩
        have ht_Ico : t ∈ Ico (0 : ℝ) (0 + 1) := by
          simpa only [zero_add] using ⟨ht.1, lt_of_le_of_ne ht.2 ht_one⟩
        exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
          hs_Ico ht_Ico).mp hst
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact (AddCircle.coe_period 1).symm
    · exact AddCircle.coe_period 1

/-- Helper for Theorem 63.6: two distinct mesh indices whose ordinary values
differ by at most one are adjacent in the cycle graph. -/
private lemma cycleGraph_adj_of_index_le {n : ℕ} {i j : Fin (n + 4)}
    (hne : i ≠ j) (hij : i.val ≤ j.val + 1) (hji : j.val ≤ i.val + 1) :
    (SimpleGraph.cycleGraph (n + 4)).Adj i j := by
  -- The two inequalities and distinctness leave exactly the two successor cases.
  rw [SimpleGraph.cycleGraph_adj']
  by_cases hij_lt : i < j
  · right
    rw [Fin.sub_val_of_le hij_lt.le]
    omega
  · left
    have hji_lt : j < i := lt_of_le_of_ne (le_of_not_gt hij_lt) (Ne.symm hne)
    rw [Fin.sub_val_of_le hji_lt.le]
    omega

/-- Helper for Theorem 63.6: the first and last equal-interval indices are
neighbors in the cyclic indexing graph. -/
private lemma cycleGraph_adj_zero_last (n : ℕ) :
    (SimpleGraph.cycleGraph (n + 4)).Adj
      (0 : Fin (n + 4)) ⟨n + 3, by omega⟩ := by
  -- In modular arithmetic the first index minus the last index is one.
  have hlast : (⟨n + 3, by omega⟩ : Fin (n + 4)) = -1 := by
    apply Fin.ext
    simp only [Fin.coe_neg_one]
  rw [SimpleGraph.cycleGraph_adj']
  left
  rw [hlast]
  simp

/-- Helper for Theorem 63.6: every parameter in an equal mesh interval lies
in the real unit interval. -/
private lemma mem_unitInterval_of_mem_equalInterval {n : ℕ} {i : Fin (n + 4)}
    {t : ℝ} (ht : t ∈ Icc ((i.val : ℝ) / (n + 4 : ℝ))
      ((i.val + 1 : ℕ) / (n + 4 : ℝ))) : t ∈ Icc (0 : ℝ) 1 := by
  -- Both endpoints lie in `[0,1]`, so the same holds for every intermediate point.
  constructor
  · exact (div_nonneg (Nat.cast_nonneg _) (by positivity)).trans ht.1
  · apply ht.2.trans
    apply (div_le_one (by positivity)).2
    exact_mod_cast Nat.succ_le_of_lt i.isLt

/-- Helper for Theorem 63.6: only the first mesh interval contains parameter zero. -/
private lemma index_eq_zero_of_zero_mem_equalInterval {n : ℕ} {i : Fin (n + 4)}
    (hzero : (0 : ℝ) ∈ Icc ((i.val : ℝ) / (n + 4 : ℝ))
      ((i.val + 1 : ℕ) / (n + 4 : ℝ))) : i = 0 := by
  -- Multiplying the lower-endpoint inequality by the positive denominator
  -- forces the nonnegative index value to vanish.
  have hval : (i.val : ℝ) ≤ 0 := by
    simpa only [zero_mul] using
      (div_le_iff₀ (by positivity : (0 : ℝ) < n + 4)).mp hzero.1
  apply Fin.ext
  exact_mod_cast (Nat.eq_zero_of_le_zero (by exact_mod_cast hval))

/-- Helper for Theorem 63.6: only the last mesh interval contains parameter one. -/
private lemma index_eq_last_of_one_mem_equalInterval {n : ℕ} {i : Fin (n + 4)}
    (hone : (1 : ℝ) ∈ Icc ((i.val : ℝ) / (n + 4 : ℝ))
      ((i.val + 1 : ℕ) / (n + 4 : ℝ))) : i = ⟨n + 3, by omega⟩ := by
  -- Multiplying the upper-endpoint inequality shows that the successor of the
  -- index reaches the full mesh cardinality.
  have hval : (n + 4 : ℝ) ≤ (i.val + 1 : ℕ) := by
    simpa only [one_mul] using
      (le_div_iff₀ (by positivity : (0 : ℝ) < n + 4)).mp hone.2
  apply Fin.ext
  have hnat : n + 4 ≤ i.val + 1 := by exact_mod_cast hval
  change i.val = n + 3
  omega

/-- Helper for Theorem 63.6: distinct nonneighboring equal-interval circle
arcs are disjoint. -/
lemma disjoint_equalIntervalCircleArc_of_not_adjacent (n : ℕ)
    {i j : Fin (n + 4)} (hne : i ≠ j)
    (hnotAdj : ¬(SimpleGraph.cycleGraph (n + 4)).Adj i j) :
    Disjoint (equalIntervalCircleArc n i) (equalIntervalCircleArc n j) := by
  -- Pull a hypothetical intersection back to two unit-interval parameters.
  rw [Set.disjoint_left]
  intro z hzi hzj
  obtain ⟨s, hsi, hsz⟩ := hzi
  obtain ⟨t, htj, htz⟩ := hzj
  have hs_unit := mem_unitInterval_of_mem_equalInterval hsi
  have ht_unit := mem_unitInterval_of_mem_equalInterval htj
  let e : UnitAddCircle ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  have hquot : (s : UnitAddCircle) = (t : UnitAddCircle) := by
    apply e.injective
    simpa [e, unitCircleIntervalParam] using hsz.trans htz.symm
  apply hnotAdj
  -- Quotient injectivity gives either a common real parameter or the endpoint wrap.
  rcases (unitAddCircle_coe_eq_coe_iff_of_mem_Icc hs_unit ht_unit).mp hquot with
    hst | hwrap | hwrap
  · have hijReal : (i.val : ℝ) ≤ (j.val + 1 : ℕ) := by
      calc
        (i.val : ℝ) ≤ s * (n + 4 : ℝ) :=
          (div_le_iff₀ (by positivity : (0 : ℝ) < n + 4)).mp hsi.1
        _ = t * (n + 4 : ℝ) := by rw [hst]
        _ ≤ (j.val + 1 : ℕ) :=
          (le_div_iff₀ (by positivity : (0 : ℝ) < n + 4)).mp htj.2
    have hjiReal : (j.val : ℝ) ≤ (i.val + 1 : ℕ) := by
      calc
        (j.val : ℝ) ≤ t * (n + 4 : ℝ) :=
          (div_le_iff₀ (by positivity : (0 : ℝ) < n + 4)).mp htj.1
        _ = s * (n + 4 : ℝ) := by rw [hst]
        _ ≤ (i.val + 1 : ℕ) :=
          (le_div_iff₀ (by positivity : (0 : ℝ) < n + 4)).mp hsi.2
    exact cycleGraph_adj_of_index_le hne (by exact_mod_cast hijReal)
      (by exact_mod_cast hjiReal)
  · obtain ⟨rfl, rfl⟩ := hwrap
    rw [index_eq_zero_of_zero_mem_equalInterval hsi,
      index_eq_last_of_one_mem_equalInterval htj]
    exact cycleGraph_adj_zero_last n
  · obtain ⟨rfl, rfl⟩ := hwrap
    rw [index_eq_last_of_one_mem_equalInterval hsi,
      index_eq_zero_of_zero_mem_equalInterval htj]
    exact (cycleGraph_adj_zero_last n).symm

/-- Helper for Theorem 63.6: the endpoints of every equal real mesh interval
are ordered. -/
private lemma equalInterval_left_le_right (n : ℕ) (i : Fin (n + 4)) :
    (i.val : ℝ) / (n + 4 : ℝ) ≤
      (i.val + 1 : ℕ) / (n + 4 : ℝ) := by
  -- Division by the positive mesh cardinality preserves the successor inequality.
  apply (div_le_div_iff_of_pos_right (by positivity)).2
  norm_num

/-- Helper for Theorem 63.6: the canonical vertex at a cyclic mesh index. -/
noncomputable def equalIntervalCircleVertex (n : ℕ) (i : Fin (n + 4)) : Circle :=
  unitCircleIntervalParam ((i.val : ℝ) / (n + 4 : ℝ))

/-- Helper for Theorem 63.6: consecutive vertices of the canonical cyclic
mesh are distinct. -/
lemma equalIntervalCircleVertex_ne_next (n : ℕ) (i : Fin (n + 4)) :
    equalIntervalCircleVertex n i ≠ equalIntervalCircleVertex n (i + 1) := by
  -- Equality on the circle would identify the two equal-interval parameters
  -- in the unit-period additive quotient.
  intro hvertices
  have hquot :
      (((i.val : ℝ) / (n + 4 : ℝ) : ℝ) : UnitAddCircle) =
        ((((i + 1).val : ℝ) / (n + 4 : ℝ) : ℝ) : UnitAddCircle) := by
    apply (AddCircle.homeomorphCircle one_ne_zero).injective
    simpa only [equalIntervalCircleVertex, unitCircleIntervalParam] using hvertices
  have hiMem : (i.val : ℝ) / (n + 4 : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).2
      exact_mod_cast Nat.le_of_lt i.isLt
  have hnextMem : ((i + 1).val : ℝ) / (n + 4 : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).2
      exact_mod_cast Nat.le_of_lt (i + 1).isLt
  have hiLt : (i.val : ℝ) / (n + 4 : ℝ) < 1 := by
    apply (div_lt_one (by positivity)).2
    exact_mod_cast i.isLt
  have hnextLt : ((i + 1).val : ℝ) / (n + 4 : ℝ) < 1 := by
    apply (div_lt_one (by positivity)).2
    exact_mod_cast (i + 1).isLt
  -- Neither parameter is the right endpoint, so quotient equality is ordinary
  -- real equality; clearing the common denominator contradicts cyclic successor.
  have hparameters :
      (i.val : ℝ) / (n + 4 : ℝ) = ((i + 1).val : ℝ) / (n + 4 : ℝ) := by
    rcases (unitAddCircle_coe_eq_coe_iff_of_mem_Icc hiMem hnextMem).mp hquot with
      h | ⟨_, hnextOne⟩ | ⟨hiOne, _⟩
    · exact h
    · exact False.elim ((ne_of_lt hnextLt) hnextOne)
    · exact False.elim ((ne_of_lt hiLt) hiOne)
  have hvalues : i.val = (i + 1).val := by
    exact_mod_cast (div_left_inj' (by positivity : (n + 4 : ℝ) ≠ 0)).mp hparameters
  by_cases hlast : i.val + 1 = n + 4
  · have hnext : (i + 1).val = 0 := by
      rw [Fin.val_add]
      norm_num
      rw [hlast, Nat.mod_self]
    rw [hnext] at hvalues
    omega
  · have hnextLt : i.val + 1 < n + 4 := by omega
    rw [Fin.val_add_one_of_lt' hnextLt] at hvalues
    omega

/-- Helper for Theorem 63.6: parameters zero and one give the same circle point. -/
private lemma unitCircleIntervalParam_one_eq_zero :
    unitCircleIntervalParam 1 = unitCircleIntervalParam 0 := by
  -- The endpoints differ by the period of `UnitAddCircle`.
  unfold unitCircleIntervalParam
  exact congrArg (AddCircle.homeomorphCircle one_ne_zero) (AddCircle.coe_period 1)

/-- Helper for Theorem 63.6: each mesh vertex is the initial endpoint of its arc. -/
lemma equalIntervalCircleVertex_mem_arc (n : ℕ) (i : Fin (n + 4)) :
    equalIntervalCircleVertex n i ∈ equalIntervalCircleArc n i := by
  -- Use the left endpoint as its own parameter witness.
  refine ⟨(i.val : ℝ) / (n + 4 : ℝ),
    left_mem_Icc.mpr (equalInterval_left_le_right n i), ?_⟩
  rfl

/-- Helper for Theorem 63.6: the next cyclic vertex is the terminal endpoint
of the current equal-interval arc. -/
lemma equalIntervalCircleNextVertex_mem_arc (n : ℕ) (i : Fin (n + 4)) :
    equalIntervalCircleVertex n (i + 1) ∈ equalIntervalCircleArc n i := by
  -- Ordinary successors use the right endpoint directly; the last successor
  -- wraps from parameter one back to parameter zero.
  by_cases hlast : i.val + 1 = n + 4
  · have hnext : (i + 1).val = 0 := by
      rw [Fin.val_add]
      norm_num
      rw [hlast, Nat.mod_self]
    refine ⟨(i.val + 1 : ℕ) / (n + 4 : ℝ),
      right_mem_Icc.mpr (equalInterval_left_le_right n i), ?_⟩
    unfold equalIntervalCircleVertex
    rw [hnext]
    have hright : ((i.val + 1 : ℕ) : ℝ) / (n + 4 : ℝ) = 1 := by
      apply (div_eq_one_iff_eq (by positivity : (n + 4 : ℝ) ≠ 0)).2
      exact_mod_cast hlast
    rw [hright, unitCircleIntervalParam_one_eq_zero]
    congr 1
    norm_num
  · have hnext_lt : i.val + 1 < n + 4 := by omega
    have hnext : (i + 1).val = i.val + 1 := by
      exact Fin.val_add_one_of_lt' hnext_lt
    refine ⟨(i.val + 1 : ℕ) / (n + 4 : ℝ),
      right_mem_Icc.mpr (equalInterval_left_le_right n i), ?_⟩
    unfold equalIntervalCircleVertex
    rw [hnext]

/-- Helper for Theorem 63.6: the canonical cyclic mesh made from equal
subintervals of the unit-period circle parameterization. -/
noncomputable def equalIntervalCircleMesh (n : ℕ) : CircleCyclicMesh n :=
  {
    vertex := equalIntervalCircleVertex n
    arc := equalIntervalCircleArc n
    vertex_mem_arc := equalIntervalCircleVertex_mem_arc n
    nextVertex_mem_arc := equalIntervalCircleNextVertex_mem_arc n
    iUnion_arc := iUnion_equalIntervalCircleArc n
    isCompact_arc := isCompact_equalIntervalCircleArc n
    isConnected_arc := isConnected_equalIntervalCircleArc n
    disjoint_arc_of_not_adjacent := fun i j ↦
      disjoint_equalIntervalCircleArc_of_not_adjacent n (i := i) (j := j)
  }

/-- Helper for Theorem 63.6: the canonical mesh's vertex projection has the
expected equal-interval formula. -/
lemma equalIntervalCircleMesh_vertex (n : ℕ) (i : Fin (n + 4)) :
    (equalIntervalCircleMesh n).vertex i = equalIntervalCircleVertex n i := by
  -- The projection is definitionally the named vertex map.
  rfl

/-- Helper for Theorem 63.6: the canonical mesh's arc projection has the
expected equal-interval formula. -/
lemma equalIntervalCircleMesh_arc (n : ℕ) (i : Fin (n + 4)) :
    (equalIntervalCircleMesh n).arc i = equalIntervalCircleArc n i := by
  -- The projection is definitionally the named arc map.
  rfl

/-- Helper for Theorem 63.6: a continuous circle trace has arbitrarily fine
canonical cyclic meshes, measured by the diameters of the trace arcs. -/
theorem existsFineEqualIntervalCircleMesh (g : Circle → E) (hg : Continuous g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ i : Fin (n + 4),
      Metric.diam (g '' (equalIntervalCircleMesh n).arc i) < ε := by
  -- Apply Heine--Cantor to the lifted trace on the compact real unit interval.
  have hlift : Continuous (fun t : ℝ ↦ g (unitCircleIntervalParam t)) :=
    hg.comp continuous_unitCircleIntervalParam
  have huniform : UniformContinuousOn (fun t : ℝ ↦ g (unitCircleIntervalParam t))
      (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hlift.continuousOn
  obtain ⟨δ, hδ, hclose⟩ :=
    Metric.uniformContinuousOn_iff.mp huniform (ε / 2) (half_pos hε)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n, ?_⟩
  intro i
  rw [equalIntervalCircleMesh_arc]
  -- The selected mesh width is smaller than the uniform-continuity radius.
  have hwidth_lt : 1 / (n + 4 : ℝ) < δ := by
    have hwidth_le : 1 / (n + 4 : ℝ) ≤ 1 / (n + 1 : ℝ) := by
      apply one_div_le_one_div_of_le
      · positivity
      · norm_num
    exact hwidth_le.trans_lt hn
  apply (Metric.diam_le_of_forall_dist_le (half_pos hε).le ?_).trans_lt
  · linarith
  · intro x hx y hy
    obtain ⟨zx, hzx, rfl⟩ := hx
    obtain ⟨sx, hsx, rfl⟩ := hzx
    obtain ⟨zy, hzy, rfl⟩ := hy
    obtain ⟨sy, hsy, rfl⟩ := hzy
    have hsx_unit := mem_unitInterval_of_mem_equalInterval hsx
    have hsy_unit := mem_unitInterval_of_mem_equalInterval hsy
    have hmeshWidth :
        ((i.val + 1 : ℕ) : ℝ) / (n + 4 : ℝ) -
            (i.val : ℝ) / (n + 4 : ℝ) = 1 / (n + 4 : ℝ) := by
      field_simp
      norm_num [Nat.cast_add]
    have hdist_le : dist sx sy ≤ 1 / (n + 4 : ℝ) := by
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hsx.1, hsx.2, hsy.1, hsy.2, hmeshWidth]
    exact (hclose sx hsx_unit sy hsy_unit (hdist_le.trans_lt hwidth_lt)).le

/-- Helper for Theorem 63.6: choose a separating thickening radius for one
indexed pair, using radius one when the pair carries no separation requirement. -/
private noncomputable def pairSeparationRadius
    (K : I → Set E) (R : I → I → Prop)
    (hcompact : ∀ i, IsCompact (K i))
    (hdisjoint : ∀ i j, R i j → Disjoint (K i) (K j)) : I × I → ℝ :=
  fun p ↦ @dite ℝ (R p.1 p.2) (Classical.propDecidable _)
    (fun hp ↦ Classical.choose
      ((hdisjoint p.1 p.2 hp).exists_thickenings
        (hcompact p.1) (hcompact p.2).isClosed))
    (fun _ ↦ 1)

/-- Helper for Theorem 63.6: every selected pairwise separation radius is positive. -/
private lemma pairSeparationRadius_pos
    (K : I → Set E) (R : I → I → Prop)
    (hcompact : ∀ i, IsCompact (K i))
    (hdisjoint : ∀ i j, R i j → Disjoint (K i) (K j))
    (p : I × I) : 0 < pairSeparationRadius K R hcompact hdisjoint p := by
  -- Required pairs use the positive radius supplied by compact separation;
  -- unrestricted pairs use the positive fallback radius one.
  classical
  unfold pairSeparationRadius
  split_ifs with hp
  · exact (Classical.choose_spec
      ((hdisjoint p.1 p.2 hp).exists_thickenings
        (hcompact p.1) (hcompact p.2).isClosed)).1
  · exact zero_lt_one

/-- Helper for Theorem 63.6: a required pair is separated at its selected radius. -/
private lemma pairSeparationRadius_disjoint
    (K : I → Set E) (R : I → I → Prop)
    (hcompact : ∀ i, IsCompact (K i))
    (hdisjoint : ∀ i j, R i j → Disjoint (K i) (K j))
    {i j : I} (hR : R i j) :
    Disjoint
      (Metric.thickening (pairSeparationRadius K R hcompact hdisjoint (i, j)) (K i))
      (Metric.thickening (pairSeparationRadius K R hcompact hdisjoint (i, j)) (K j)) := by
  -- Unfold the required-pair branch and read the separation specification.
  classical
  unfold pairSeparationRadius
  rw [dif_pos hR]
  exact (Classical.choose_spec
    ((hdisjoint i j hR).exists_thickenings (hcompact i) (hcompact j).isClosed)).2

/-- Helper for Theorem 63.6: finitely many pairwise compact-set separation
requirements admit one positive thickening radius satisfying all of them. -/
theorem existsUniformThickeningRadius
    [Finite I] (K : I → Set E) (R : I → I → Prop)
    (hcompact : ∀ i, IsCompact (K i))
    (hdisjoint : ∀ i j, R i j → Disjoint (K i) (K j)) :
    ∃ r > 0, ∀ i j, R i j →
      Disjoint (Metric.thickening r (K i)) (Metric.thickening r (K j)) := by
  -- Include radius one so the finite set of candidate radii is nonempty even
  -- when the index type itself is empty.
  classical
  letI : Fintype I := Fintype.ofFinite I
  let candidates : Finset ℝ :=
    insert 1 (Finset.univ.image (pairSeparationRadius K R hcompact hdisjoint))
  have hcandidates : candidates.Nonempty := by
    exact ⟨1, Finset.mem_insert_self 1 _⟩
  let r : ℝ := candidates.min' hcandidates
  have hr_mem : r ∈ candidates := Finset.min'_mem candidates hcandidates
  have hr_pos : 0 < r := by
    rcases Finset.mem_insert.mp hr_mem with hr_one | hr_image
    · simpa only [hr_one] using zero_lt_one
    · obtain ⟨p, _, hrp⟩ := Finset.mem_image.mp hr_image
      rw [← hrp]
      exact pairSeparationRadius_pos K R hcompact hdisjoint p
  refine ⟨r, hr_pos, ?_⟩
  intro i j hR
  -- Shrink both selected thickenings to the common finite minimum.
  have hr_le : r ≤ pairSeparationRadius K R hcompact hdisjoint (i, j) := by
    apply Finset.min'_le candidates
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
  exact (pairSeparationRadius_disjoint K R hcompact hdisjoint hR).mono
    (Metric.thickening_mono hr_le (K i)) (Metric.thickening_mono hr_le (K j))

/-- Helper for Theorem 63.6: the common separation radius can additionally be
chosen below any prescribed positive bound. -/
theorem existsUniformThickeningRadius_lt
    [Finite I] (K : I → Set E) (R : I → I → Prop)
    (hcompact : ∀ i, IsCompact (K i))
    (hdisjoint : ∀ i j, R i j → Disjoint (K i) (K j))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r > 0, r < ρ ∧ ∀ i j, R i j →
      Disjoint (Metric.thickening r (K i)) (Metric.thickening r (K j)) := by
  -- Halve the smaller of the finite separation radius and the prescribed bound.
  obtain ⟨r₀, hr₀, hseparate⟩ :=
    existsUniformThickeningRadius K R hcompact hdisjoint
  let r : ℝ := min r₀ ρ / 2
  have hr : 0 < r := by
    exact div_pos (lt_min hr₀ hρ) zero_lt_two
  have hr_le : r ≤ r₀ := by
    dsimp only [r]
    linarith [min_le_left r₀ ρ]
  have hr_lt : r < ρ := by
    dsimp only [r]
    linarith [min_le_right r₀ ρ, lt_min hr₀ hρ]
  refine ⟨r, hr, hr_lt, ?_⟩
  intro i j hR
  exact (hseparate i j hR).mono
    (Metric.thickening_mono hr_le (K i)) (Metric.thickening_mono hr_le (K j))

/-- Helper for Theorem 63.6: a finite compact family of small sets has small
thickenings that remain disjoint for every prescribed separated pair. -/
theorem existsSeparatedSmallThickenings
    [Finite I] (K : I → Set E) (R : I → I → Prop)
    (hcompact : ∀ i, IsCompact (K i))
    (hdisjoint : ∀ i j, R i j → Disjoint (K i) (K j))
    {ε : ℝ} (hε : 0 < ε) (hdiam : ∀ i, Metric.diam (K i) < ε / 3) :
    ∃ r > 0,
      (∀ i, Metric.diam (Metric.thickening r (K i)) < ε) ∧
      ∀ i j, R i j →
        Disjoint (Metric.thickening r (K i)) (Metric.thickening r (K j)) := by
  -- Bound the common radius by `ε / 3`, leaving two thirds for thickening.
  obtain ⟨r, hr, hrε, hseparate⟩ :=
    existsUniformThickeningRadius_lt K R hcompact hdisjoint (div_pos hε zero_lt_three)
  refine ⟨r, hr, ?_, hseparate⟩
  intro i
  -- The standard diameter estimate adds at most twice the chosen radius.
  calc
    Metric.diam (Metric.thickening r (K i)) ≤ Metric.diam (K i) + 2 * r :=
      Metric.diam_thickening_le (K i) hr.le
    _ < ε := by linarith [hdiam i]

end Schoenflies
