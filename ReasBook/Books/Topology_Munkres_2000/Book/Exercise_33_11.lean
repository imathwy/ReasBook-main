module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Real
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Separation.GDelta

public section

open Filter Set Topology

namespace RegularCounterexample

/-- A valid index for one of the even vertical segments. -/
structure LineIndex where
  m : ℤ
  even : Even m

/-- A valid index for one of the odd semicircular bridges. -/
structure BridgeIndex where
  n : ℤ
  k : ℕ
  odd : Odd n
  two_le : 2 ≤ k

/-- The plane locus made from the even vertical segments and odd semicircular bridges. -/
def GeometricPoint (x y : ℝ) : Prop :=
  (∃ i : LineIndex, x = i.m ∧ y ∈ Icc (-1) 0) ∨
    ∃ i : BridgeIndex,
      ((x = i.n + 1 - (1 : ℝ) / i.k ∧ y ∈ Icc (-1) 0) ∨
        (x = i.n - 1 + (1 : ℝ) / i.k ∧ y ∈ Icc (-1) 0) ∨
        ((x - i.n) ^ 2 + y ^ 2 = (1 - (1 : ℝ) / i.k) ^ 2 ∧ 0 ≤ y))

/-- A point of the geometric plane locus, bundled with its coordinates. -/
structure PlanePoint where
  x : ℝ
  y : ℝ
  mem_geometric : GeometricPoint x y

/-- Plane points are determined by their two coordinates. -/
@[ext]
theorem PlanePoint.ext {p q : PlanePoint} (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  cases p
  cases q
  simp_all

/-- The counterexample carrier: its plane locus together with two added end points. -/
inductive Space where
  | plane : PlanePoint → Space
  | leftEnd : Space
  | rightEnd : Space

/-- The horizontal coordinate of a plane point, undefined at the two added ends. -/
def xCoord : Space → Option ℝ
  | Space.plane p => some p.x
  | Space.leftEnd => none
  | Space.rightEnd => none

/-- The vertical coordinate of a plane point, undefined at the two added ends. -/
def yCoord : Space → Option ℝ
  | Space.plane p => some p.y
  | Space.leftEnd => none
  | Space.rightEnd => none

/-- The two added end points are distinct. -/
theorem leftEnd_ne_rightEnd : Space.leftEnd ≠ Space.rightEnd := by
  intro h
  cases h

/-- The vertical segment `Lₘ` for an even integer `m`. -/
def line (i : LineIndex) : Set Space :=
  {p | ∃ q : PlanePoint, p = Space.plane q ∧ q.x = i.m ∧ q.y ∈ Icc (-1) 0}

/-- The bridge `Cₙ,ₖ`, including its two legs and upper semicircle. -/
def curve (i : BridgeIndex) : Set Space :=
  {p | ∃ q : PlanePoint, p = Space.plane q ∧
    ((q.x = i.n + 1 - (1 : ℝ) / i.k ∧ q.y ∈ Icc (-1) 0) ∨
      (q.x = i.n - 1 + (1 : ℝ) / i.k ∧ q.y ∈ Icc (-1) 0) ∨
      ((q.x - i.n) ^ 2 + q.y ^ 2 = (1 - (1 : ℝ) / i.k) ^ 2 ∧ 0 ≤ q.y))}

/-- The prescribed coordinates of the top point lie in the geometric locus. -/
theorem topPoint_mem_geometric (i : BridgeIndex) :
    GeometricPoint i.n (1 - (1 : ℝ) / i.k) := by
  -- Place the prescribed point on the semicircular part of its indexed bridge.
  refine Or.inr ⟨i, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
  · ring
  · -- The index bound makes the reciprocal at most one.
    have hk : (1 : ℝ) ≤ i.k := by
      exact_mod_cast i.two_le.trans' (by omega : 1 ≤ 2)
    simpa using sub_nonneg.mpr (one_div_le_one_div_of_le zero_lt_one hk)

/-- The topmost point `pₙ,ₖ` of an odd-indexed bridge. -/
noncomputable def topPoint (i : BridgeIndex) : Space :=
  Space.plane ⟨i.n, 1 - (1 : ℝ) / i.k, topPoint_mem_geometric i⟩

/-- The top point has horizontal coordinate `n`. -/
@[simp]
theorem xCoord_topPoint (i : BridgeIndex) : xCoord (topPoint i) = some i.n := by
  simp [topPoint, xCoord]

/-- The top point has vertical coordinate `1 - 1 / k`. -/
@[simp]
theorem yCoord_topPoint (i : BridgeIndex) :
    yCoord (topPoint i) = some (1 - (1 : ℝ) / i.k) := by
  simp [topPoint, yCoord]

/-- An even vertical-line coordinate belongs to the geometric locus. -/
theorem linePoint_mem_geometric (i : LineIndex) (d : ℝ) (hd : d ∈ Icc (-1) 0) :
    GeometricPoint i.m d := by
  exact Or.inl ⟨i, rfl, hd⟩

/-- The point `(m,d)` on an even vertical segment. -/
def linePoint (i : LineIndex) (d : ℝ) (hd : d ∈ Icc (-1) 0) : Space :=
  Space.plane ⟨i.m, d, linePoint_mem_geometric i d hd⟩

/-- The line point has horizontal coordinate `m`. -/
@[simp]
theorem xCoord_linePoint (i : LineIndex) (d : ℝ) (hd : d ∈ Icc (-1) 0) :
    xCoord (linePoint i d hd) = some i.m := by
  simp [linePoint, xCoord]

/-- The line point has vertical coordinate `d`. -/
@[simp]
theorem yCoord_linePoint (i : LineIndex) (d : ℝ) (hd : d ∈ Icc (-1) 0) :
    yCoord (linePoint i d hd) = some d := by
  simp [linePoint, yCoord]

/-- A horizontal open segment in the plane part of the space. -/
def horizontalSlice (l r d : ℝ) : Set Space :=
  {p | ∃ q : PlanePoint, p = Space.plane q ∧ l < q.x ∧ q.x < r ∧ q.y = d}

/-- The basic neighborhood of the left added end point indexed by `m`. -/
def leftRay (i : LineIndex) : Set Space :=
  {Space.leftEnd} ∪ {p | ∃ q : PlanePoint, p = Space.plane q ∧ q.x < i.m}

/-- The basic neighborhood of the right added end point indexed by `m`. -/
def rightRay (i : LineIndex) : Set Space :=
  {Space.rightEnd} ∪ {p | ∃ q : PlanePoint, p = Space.plane q ∧ i.m < q.x}

/-- The four displayed families of basis elements for the counterexample space. -/
def basicSets : Set (Set Space) :=
  {s | (∃ l r d : ℝ, l < r ∧
      (∀ i : BridgeIndex, topPoint i ∉ horizontalSlice l r d) ∧
      s = horizontalSlice l r d) ∨
    (∃ i : BridgeIndex, ∃ t : Set Space, t.Finite ∧ s = curve i \ t) ∨
    (∃ i : LineIndex, s = leftRay i) ∨
    ∃ i : LineIndex, s = rightRay i}

/-- The topology generated by the four designated families of basic sets. -/
instance instTopologicalSpace : TopologicalSpace Space :=
  TopologicalSpace.generateFrom basicSets

/-- The installed topology is generated by `basicSets`. -/
theorem topology_eq_generateFrom :
    (inferInstance : TopologicalSpace Space) = TopologicalSpace.generateFrom basicSets := rfl

/-- Helper for Exercise 33.11: every left-end ray is one of the designated basic sets. -/
lemma leftRay_mem_basicSets (i : LineIndex) : leftRay i ∈ basicSets := by
  -- Select the third family in the definition of `basicSets`.
  exact Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))

/-- Helper for Exercise 33.11: every right-end ray is one of the designated basic sets. -/
lemma rightRay_mem_basicSets (i : LineIndex) : rightRay i ∈ basicSets := by
  -- Select the fourth family in the definition of `basicSets`.
  exact Or.inr (Or.inr (Or.inr ⟨i, rfl⟩))

/-- Helper for Exercise 33.11: deleting finitely many points from a bridge gives a basic set. -/
lemma curve_diff_mem_basicSets (i : BridgeIndex) {t : Set Space} (ht : t.Finite) :
    curve i \ t ∈ basicSets := by
  -- Select the second family in the definition of `basicSets`.
  exact Or.inr (Or.inl ⟨i, t, ht, rfl⟩)

/-- Helper for Exercise 33.11: a top-free horizontal slice is a designated basic set. -/
lemma horizontalSlice_mem_basicSets {l r d : ℝ} (hlr : l < r)
    (htop : ∀ i : BridgeIndex, topPoint i ∉ horizontalSlice l r d) :
    horizontalSlice l r d ∈ basicSets := by
  -- Select the first family in the definition of `basicSets`.
  exact Or.inl ⟨l, r, d, hlr, htop, rfl⟩

/-- Helper for Exercise 33.11: the left end belongs to every left-end ray. -/
lemma leftEnd_mem_leftRay (i : LineIndex) : Space.leftEnd ∈ leftRay i := by
  -- Membership is supplied by the distinguished singleton in the ray.
  exact Or.inl rfl

/-- Helper for Exercise 33.11: the right end belongs to every right-end ray. -/
lemma rightEnd_mem_rightRay (i : LineIndex) : Space.rightEnd ∈ rightRay i := by
  -- Membership is supplied by the distinguished singleton in the ray.
  exact Or.inl rfl

/-- Helper for Exercise 33.11: smaller cutoffs give smaller left-end rays. -/
lemma leftRay_mono {i j : LineIndex} (hij : i.m ≤ j.m) : leftRay i ⊆ leftRay j := by
  -- Preserve the left end and enlarge the strict horizontal bound for plane points.
  intro p hp
  rcases hp with hp | ⟨q, rfl, hq⟩
  · exact Or.inl hp
  · have hijReal : (i.m : ℝ) ≤ j.m := by
      exact_mod_cast hij
    exact Or.inr ⟨q, rfl, hq.trans_le hijReal⟩

/-- Helper for Exercise 33.11: larger cutoffs give smaller right-end rays. -/
lemma rightRay_anti {i j : LineIndex} (hij : j.m ≤ i.m) : rightRay i ⊆ rightRay j := by
  -- Preserve the right end and weaken the strict lower bound for plane points.
  intro p hp
  rcases hp with hp | ⟨q, rfl, hq⟩
  · exact Or.inl hp
  · have hijReal : (j.m : ℝ) ≤ i.m := by
      exact_mod_cast hij
    exact Or.inr ⟨q, rfl, hijReal.trans_lt hq⟩

/-- Helper for Exercise 33.11: a basic set containing the left end is a left-end ray. -/
lemma eq_leftRay_of_mem_basicSets_of_leftEnd_mem {s : Set Space}
    (hs : s ∈ basicSets) (hp : Space.leftEnd ∈ s) : ∃ i : LineIndex, s = leftRay i := by
  -- The other three generator families contain only plane points or the right end.
  rcases hs with ⟨l, r, d, hlr, htop, rfl⟩ |
      ⟨i, t, ht, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [horizontalSlice] at hp
  · simp [curve] at hp
  · exact ⟨i, rfl⟩
  · simp [rightRay] at hp

/-- Helper for Exercise 33.11: a basic set containing the right end is a right-end ray. -/
lemma eq_rightRay_of_mem_basicSets_of_rightEnd_mem {s : Set Space}
    (hs : s ∈ basicSets) (hp : Space.rightEnd ∈ s) : ∃ i : LineIndex, s = rightRay i := by
  -- The other three generator families contain only plane points or the left end.
  rcases hs with ⟨l, r, d, hlr, htop, rfl⟩ |
      ⟨i, t, ht, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [horizontalSlice] at hp
  · simp [curve] at hp
  · simp [leftRay] at hp
  · exact ⟨i, rfl⟩

/-- Helper for Exercise 33.11: the designated basic sets cover the whole counterexample space. -/
lemma basicSets_sUnion_eq_univ : ⋃₀ basicSets = (Set.univ : Set Space) := by
  -- A sufficiently far right even coordinate gives a left ray containing any plane point.
  apply sUnion_eq_univ_iff.mpr
  intro p
  cases p with
  | leftEnd =>
      have hzero : Even (0 : ℤ) := by
        exact ⟨0, by omega⟩
      let i : LineIndex := ⟨0, hzero⟩
      exact ⟨leftRay i, leftRay_mem_basicSets i, by simp [leftRay]⟩
  | rightEnd =>
      have hzero : Even (0 : ℤ) := by
        exact ⟨0, by omega⟩
      let i : LineIndex := ⟨0, hzero⟩
      exact ⟨rightRay i, rightRay_mem_basicSets i, by simp [rightRay]⟩
  | plane q =>
      obtain ⟨n : ℕ, hn⟩ := exists_nat_gt q.x
      have heven : Even (2 * (n : ℤ)) := by
        exact ⟨n, by ring⟩
      let i : LineIndex := ⟨2 * n, heven⟩
      refine ⟨leftRay i, leftRay_mem_basicSets i, ?_⟩
      -- The chosen even integer is at least the natural number already above `q.x`.
      have hnNat : n ≤ 2 * n := by omega
      have hnle : (n : ℝ) ≤ (2 * n : ℕ) := by
        exact_mod_cast hnNat
      have hq : q.x < (i.m : ℝ) := by
        dsimp [i]
        exact hn.trans_le hnle
      exact Or.inr ⟨q, rfl, hq⟩

/-- Helper for Exercise 33.11: every bridge radius is strictly positive. -/
lemma bridgeRadius_pos (i : BridgeIndex) : 0 < 1 - (1 : ℝ) / i.k := by
  -- The index bound makes the denominator strictly larger than one.
  have hk : (1 : ℝ) < i.k := by
    exact_mod_cast i.two_le
  have hdiv : (1 : ℝ) / i.k < 1 := by
    rw [div_lt_one]
    · exact hk
    · exact zero_lt_one.trans hk
  linarith

/-- Helper for Exercise 33.11: every bridge radius is strictly less than one. -/
lemma bridgeRadius_lt_one (i : BridgeIndex) : 1 - (1 : ℝ) / i.k < 1 := by
  -- Positivity of the reciprocal gives the strict upper bound.
  have hk : (0 : ℝ) < i.k := by
    exact_mod_cast (show 0 < i.k from lt_of_lt_of_le (by omega) i.two_le)
  have hdiv : 0 < (1 : ℝ) / i.k := div_pos zero_lt_one hk
  linarith

/-- Helper for Exercise 33.11: bridge radii strictly increase with their natural index. -/
lemma bridgeRadius_lt_of_k_lt {i j : BridgeIndex} (hij : i.k < j.k) :
    1 - (1 : ℝ) / i.k < 1 - (1 : ℝ) / j.k := by
  -- Reciprocal reverses the strict order on positive natural-number casts.
  have hi : (0 : ℝ) < i.k := by
    exact_mod_cast (show 0 < i.k from lt_of_lt_of_le (by omega) i.two_le)
  have hijReal : (i.k : ℝ) < j.k := by
    exact_mod_cast hij
  have hrecip : (1 : ℝ) / j.k < 1 / i.k := one_div_lt_one_div_of_lt hi hijReal
  linarith

/-- Helper for Exercise 33.11: a bridge is determined by its center and positive radius. -/
lemma BridgeIndex.ext_of_n_eq_of_radius_eq {i j : BridgeIndex} (hn : i.n = j.n)
    (hradius : 1 - (1 : ℝ) / i.k = 1 - (1 : ℝ) / j.k) : i = j := by
  -- Equality of radii gives equality of positive reciprocal denominators.
  have hrecip : (1 : ℝ) / i.k = 1 / j.k := by
    linarith
  have hinv : ((i.k : ℝ)⁻¹) = (j.k : ℝ)⁻¹ := by
    simpa [one_div] using hrecip
  have hkReal : (i.k : ℝ) = j.k := inv_injective hinv
  have hk : i.k = j.k := by
    exact_mod_cast hkReal
  cases i
  cases j
  simp_all

/-- Helper for Exercise 33.11: two arc equations with one center determine the same bridge. -/
lemma bridgeIndex_eq_of_center_eq_of_arc_mem {i j : BridgeIndex} {q : PlanePoint}
    (hn : j.n = i.n)
    (hiArc : (q.x - i.n) ^ 2 + q.y ^ 2 = (1 - (1 : ℝ) / i.k) ^ 2)
    (hjArc : (q.x - j.n) ^ 2 + q.y ^ 2 = (1 - (1 : ℝ) / j.k) ^ 2) :
    j = i := by
  -- After identifying centers, positivity turns equality of squared radii into equality of radii.
  have hradiusSq : (1 - (1 : ℝ) / j.k) ^ 2 = (1 - (1 : ℝ) / i.k) ^ 2 := by
    rw [hn] at hjArc
    linarith
  have hradius : 1 - (1 : ℝ) / j.k = 1 - (1 : ℝ) / i.k := by
    nlinarith [bridgeRadius_pos i, bridgeRadius_pos j]
  exact BridgeIndex.ext_of_n_eq_of_radius_eq hn hradius

/-- Helper for Exercise 33.11: a distinguished top point lies on exactly its indexed bridge. -/
lemma topPoint_mem_curve_iff {i j : BridgeIndex} : topPoint i ∈ curve j ↔ i = j := by
  constructor
  · intro h
    -- Normalize membership into the two legs or the semicircular branch.
    rcases h with ⟨q, hq, hcurve⟩
    injection hq with hqi
    subst q
    rcases hcurve with hleg | hleg | harc
    · exact (not_le_of_gt (bridgeRadius_pos i) hleg.2.2).elim
    · exact (not_le_of_gt (bridgeRadius_pos i) hleg.2.2).elim
    · -- The radius bound forces the two odd integer centers to agree.
      have harcEq : (((i.n : ℝ) - j.n) ^ 2) + (1 - (1 : ℝ) / i.k) ^ 2 =
          (1 - (1 : ℝ) / j.k) ^ 2 := by
        simpa [topPoint] using harc.1
      have hdiffSq : (((i.n : ℝ) - j.n) ^ 2) < 1 := by
        nlinarith [bridgeRadius_pos i, bridgeRadius_lt_one i,
          bridgeRadius_pos j, bridgeRadius_lt_one j, harcEq]
      have hdiffLower : (-1 : ℝ) < (i.n : ℝ) - j.n := by
        nlinarith [sq_nonneg ((i.n : ℝ) - j.n)]
      have hdiffUpper : (i.n : ℝ) - j.n < 1 := by
        nlinarith [sq_nonneg ((i.n : ℝ) - j.n)]
      have hn : i.n = j.n := by
        have hzLower : (-1 : ℤ) < i.n - j.n := by
          exact_mod_cast hdiffLower
        have hzUpper : i.n - j.n < (1 : ℤ) := by
          exact_mod_cast hdiffUpper
        omega
      -- With the center fixed, equality of the positive radii fixes the natural index.
      have hkReal : (i.k : ℝ) = j.k := by
        have hnReal : (i.n : ℝ) = j.n := by
          exact_mod_cast hn
        have heq : (1 : ℝ) / i.k = 1 / j.k := by
          nlinarith [bridgeRadius_pos i, bridgeRadius_pos j, harcEq]
        have hinv : ((i.k : ℝ)⁻¹) = (j.k : ℝ)⁻¹ := by
          simpa [one_div] using heq
        exact inv_injective hinv
      have hk : i.k = j.k := by
        exact_mod_cast hkReal
      cases i
      cases j
      simp_all
  · rintro rfl
    -- The defining top coordinates satisfy the semicircle equation.
    refine ⟨_, rfl, Or.inr (Or.inr ⟨?_, (bridgeRadius_pos i).le⟩)⟩
    ring

/-- Helper for Exercise 33.11: every bridge point lies strictly between its neighboring
lines. -/
lemma curve_x_bounds {i : BridgeIndex} {q : PlanePoint} (hq : Space.plane q ∈ curve i) :
    (i.n : ℝ) - 1 < q.x ∧ q.x < (i.n : ℝ) + 1 := by
  -- Each leg is in the open unit cell because the reciprocal is strictly between zero and one.
  rcases hq with ⟨q', hq', hcurve⟩
  injection hq' with hqq
  subst q'
  have hk : (0 : ℝ) < (1 : ℝ) / i.k := by
    have hik : (0 : ℝ) < i.k := by
      exact_mod_cast (show 0 < i.k from lt_of_lt_of_le (by omega) i.two_le)
    exact div_pos zero_lt_one hik
  have hklt : (1 : ℝ) / i.k < 1 := by
    linarith [bridgeRadius_pos i]
  rcases hcurve with hleg | hleg | harc
  · constructor <;> rw [hleg.1] <;> linarith
  · constructor <;> rw [hleg.1] <;> linarith
  · -- On the semicircle, the horizontal offset has magnitude below the radius, hence below one.
    have hsq : (q.x - (i.n : ℝ)) ^ 2 < 1 := by
      nlinarith [sq_nonneg q.y, bridgeRadius_pos i, bridgeRadius_lt_one i, harc.1]
    constructor <;> nlinarith [sq_nonneg (q.x - (i.n : ℝ))]

/-- Helper for Exercise 33.11: two odd bridge cells containing one horizontal coordinate
have the same center. -/
lemma curveCenter_eq_of_mem_of_mem_cell {i j : BridgeIndex} {q : PlanePoint}
    (hq : Space.plane q ∈ curve j)
    (hcell : (i.n : ℝ) - 1 < q.x ∧ q.x < (i.n : ℝ) + 1) :
    j.n = i.n := by
  -- Combine the two open-cell bounds to place the integer center difference in `(-2, 2)`.
  have hjcell := curve_x_bounds (i := j) (q := q) hq
  have hlowerReal : (-2 : ℝ) < (j.n : ℝ) - i.n := by
    linarith
  have hupperReal : (j.n : ℝ) - i.n < 2 := by
    linarith
  have hlower : (-2 : ℤ) < j.n - i.n := by
    exact_mod_cast hlowerReal
  have hupper : j.n - i.n < (2 : ℤ) := by
    exact_mod_cast hupperReal
  -- The difference of two odd integers is even, so the only possibility is zero.
  rcases j.odd with ⟨a, ha⟩
  rcases i.odd with ⟨b, hb⟩
  omega

/-- Helper for Exercise 33.11: an even line coordinate cannot lie inside an odd bridge cell. -/
lemma not_mem_bridgeCell_of_lineIndex (i : BridgeIndex) (j : LineIndex) :
    ¬ ((i.n : ℝ) - 1 < j.m ∧ (j.m : ℝ) < i.n + 1) := by
  -- Cast the strict cell inequalities to integers and use opposite parity.
  rintro ⟨hlowerReal, hupperReal⟩
  have hlower : i.n - 1 < j.m := by
    exact_mod_cast hlowerReal
  have hupper : j.m < i.n + 1 := by
    exact_mod_cast hupperReal
  rcases i.odd with ⟨a, ha⟩
  rcases j.even with ⟨b, hb⟩
  omega

/-- Helper for Exercise 33.11: the squared radius of one bridge is isolated among all
admissible squared bridge radii. -/
lemma exists_isolatingInterval_bridgeRadiusSq (i : BridgeIndex) :
    ∃ a b : ℝ,
      (1 - (1 : ℝ) / i.k) ^ 2 ∈ Ioo a b ∧
        ∀ j : BridgeIndex, (1 - (1 : ℝ) / j.k) ^ 2 ∈ Ioo a b → j.k = i.k := by
  -- Use the next squared radius as the upper endpoint and either zero or the predecessor
  -- squared radius as the lower endpoint.
  have hnextTwo : 2 ≤ i.k + 1 := by
    have hiTwo := i.two_le
    omega
  let next : BridgeIndex := ⟨i.n, i.k + 1, i.odd, hnextTwo⟩
  by_cases htwo : i.k = 2
  · refine ⟨0, (1 - (1 : ℝ) / next.k) ^ 2, ?_, ?_⟩
    · constructor
      · nlinarith [bridgeRadius_pos i]
      · exact (sq_lt_sq₀ (bridgeRadius_pos i).le (bridgeRadius_pos next).le).mpr
          (bridgeRadius_lt_of_k_lt (by dsimp [next]; omega))
    · intro j hj
      have hnotlt : ¬ i.k < j.k := by
        intro hij
        have hnextLe : next.k ≤ j.k := by
          dsimp [next]
          omega
        have hradiusLe : 1 - (1 : ℝ) / next.k ≤ 1 - (1 : ℝ) / j.k := by
          rcases hnextLe.eq_or_lt with h | h
          · rw [h]
          · exact (bridgeRadius_lt_of_k_lt h).le
        have hsquareLe : (1 - (1 : ℝ) / next.k) ^ 2 ≤
            (1 - (1 : ℝ) / j.k) ^ 2 := by
          nlinarith [bridgeRadius_pos next, bridgeRadius_pos j]
        exact (not_lt_of_ge hsquareLe) hj.2
      have hjTwo := j.two_le
      omega
  · have hprevTwo : 2 ≤ i.k - 1 := by
      have hiTwo := i.two_le
      omega
    let prev : BridgeIndex := ⟨i.n, i.k - 1, i.odd, hprevTwo⟩
    refine ⟨(1 - (1 : ℝ) / prev.k) ^ 2,
      (1 - (1 : ℝ) / next.k) ^ 2, ?_, ?_⟩
    · constructor
      · exact (sq_lt_sq₀ (bridgeRadius_pos prev).le (bridgeRadius_pos i).le).mpr
          (bridgeRadius_lt_of_k_lt (by dsimp [prev]; omega))
      · exact (sq_lt_sq₀ (bridgeRadius_pos i).le (bridgeRadius_pos next).le).mpr
          (bridgeRadius_lt_of_k_lt (by dsimp [next]; omega))
    · intro j hj
      have hnotlt : ¬ j.k < i.k := by
        intro hji
        have hjLe : j.k ≤ prev.k := by
          dsimp [prev]
          omega
        have hradiusLe : 1 - (1 : ℝ) / j.k ≤ 1 - (1 : ℝ) / prev.k := by
          rcases hjLe.eq_or_lt with h | h
          · rw [h]
          · exact (bridgeRadius_lt_of_k_lt h).le
        have hsquareLe : (1 - (1 : ℝ) / j.k) ^ 2 ≤
            (1 - (1 : ℝ) / prev.k) ^ 2 := by
          nlinarith [bridgeRadius_pos j, bridgeRadius_pos prev]
        exact (not_lt_of_ge hsquareLe) hj.1
      have hnotgt : ¬ i.k < j.k := by
        intro hij
        have hnextLe : next.k ≤ j.k := by
          dsimp [next]
          omega
        have hradiusLe : 1 - (1 : ℝ) / next.k ≤ 1 - (1 : ℝ) / j.k := by
          rcases hnextLe.eq_or_lt with h | h
          · rw [h]
          · exact (bridgeRadius_lt_of_k_lt h).le
        have hsquareLe : (1 - (1 : ℝ) / next.k) ^ 2 ≤
            (1 - (1 : ℝ) / j.k) ^ 2 := by
          nlinarith [bridgeRadius_pos next, bridgeRadius_pos j]
        exact (not_lt_of_ge hsquareLe) hj.2
      omega

/-- Helper for Exercise 33.11: a continuous real map pulls an open interval back to an
open interval around the chosen point. -/
lemma exists_Ioo_mapsTo_Ioo_of_continuousAt {f : ℝ → ℝ} {x a b : ℝ}
    (hf : ContinuousAt f x) (hx : f x ∈ Ioo a b) :
    ∃ l r : ℝ, l < x ∧ x < r ∧ MapsTo f (Ioo l r) (Ioo a b) := by
  -- Continuity makes the target interval a neighborhood preimage, which contains a real interval.
  have hpreimage : f ⁻¹' Ioo a b ∈ 𝓝 x := hf (Ioo_mem_nhds hx.1 hx.2)
  obtain ⟨l, r, ⟨hl, hr⟩, hlr⟩ := mem_nhds_iff_exists_Ioo_subset.mp hpreimage
  exact ⟨l, r, hl, hr, fun _ hz ↦ hlr hz⟩

/-- Helper for Exercise 33.11: a point on the right leg of a bridge has a singleton
horizontal slice in the geometric locus. -/
lemma exists_horizontalSlice_eq_singleton_of_rightLeg_mem {i : BridgeIndex} {q : PlanePoint}
    (hx : q.x = i.n + 1 - (1 : ℝ) / i.k) (hy : q.y ∈ Icc (-1) 0) :
    ∃ l r : ℝ, l < q.x ∧ q.x < r ∧ horizontalSlice l r q.y = {Space.plane q} := by
  -- Pull an interval isolating the indexed squared radius back through the squared offset map.
  obtain ⟨a, b, hiRadius, hisolate⟩ := exists_isolatingInterval_bridgeRadiusSq i
  have hqRadius : (q.x - (i.n : ℝ)) ^ 2 = (1 - (1 : ℝ) / i.k) ^ 2 := by
    rw [hx]
    ring
  have hcontinuous : ContinuousAt (fun x : ℝ ↦ (x - (i.n : ℝ)) ^ 2) q.x := by
    fun_prop
  obtain ⟨l₀, r₀, hl₀, hr₀, hmaps⟩ :=
    exists_Ioo_mapsTo_Ioo_of_continuousAt hcontinuous (hqRadius ▸ hiRadius)
  let l := max l₀ (i.n : ℝ)
  let r := min r₀ ((i.n : ℝ) + 1)
  have hcenter : (i.n : ℝ) < q.x := by
    rw [hx]
    linarith [bridgeRadius_pos i]
  have hright : q.x < (i.n : ℝ) + 1 := by
    rw [hx]
    have hk : (0 : ℝ) < (1 : ℝ) / i.k := by
      have hik : (0 : ℝ) < i.k := by
        exact_mod_cast (show 0 < i.k from lt_of_lt_of_le (by omega) i.two_le)
      exact div_pos zero_lt_one hik
    linarith
  have hlq : l < q.x := by
    simp only [l, max_lt_iff]
    exact ⟨hl₀, hcenter⟩
  have hqr : q.x < r := by
    simp only [r, lt_min_iff]
    exact ⟨hr₀, hright⟩
  refine ⟨l, r, hlq, hqr, Set.Subset.antisymm ?_ ?_⟩
  · intro p hp
    rcases hp with ⟨q', rfl, hql, hqr', hy'⟩
    have hcell : (i.n : ℝ) - 1 < q'.x ∧ q'.x < (i.n : ℝ) + 1 := by
      constructor
      · have hcenter' : (i.n : ℝ) < q'.x := (le_max_right l₀ i.n).trans_lt hql
        linarith
      · exact hqr'.trans_le (min_le_right r₀ ((i.n : ℝ) + 1))
    have hside : (i.n : ℝ) < q'.x := (le_max_right l₀ i.n).trans_lt hql
    have hmap : (q'.x - (i.n : ℝ)) ^ 2 ∈ Ioo a b := by
      apply hmaps
      constructor
      · exact (le_max_left l₀ i.n).trans_lt hql
      · exact hqr'.trans_le (min_le_left r₀ ((i.n : ℝ) + 1))
    rcases q'.mem_geometric with ⟨j, hxLine, hyLine⟩ | ⟨j, hleg | hleg | harc⟩
    · exact (not_mem_bridgeCell_of_lineIndex i j ⟨hxLine ▸ hcell.1, hxLine ▸ hcell.2⟩).elim
    · have hn : j.n = i.n := curveCenter_eq_of_mem_of_mem_cell
          ⟨q', rfl, Or.inl hleg⟩ hcell
      have hjRadius : (1 - (1 : ℝ) / j.k) ^ 2 ∈ Ioo a b := by
        have heq : (q'.x - (i.n : ℝ)) ^ 2 = (1 - (1 : ℝ) / j.k) ^ 2 := by
          rw [hleg.1, hn]
          ring
        rwa [← heq]
      have hk : j.k = i.k := hisolate j hjRadius
      apply Set.mem_singleton_iff.mpr
      apply congrArg Space.plane
      apply PlanePoint.ext
      · rw [hleg.1, hn, hk, hx]
      · exact hy'
    · have hn : j.n = i.n := curveCenter_eq_of_mem_of_mem_cell
          ⟨q', rfl, Or.inr (Or.inl hleg)⟩ hcell
      rw [hleg.1, hn] at hside
      nlinarith [bridgeRadius_pos j]
    · have hyZero : q'.y = 0 := by
        rw [hy']
        exact le_antisymm hy.2 (hy' ▸ harc.2)
      have hn : j.n = i.n := curveCenter_eq_of_mem_of_mem_cell
          ⟨q', rfl, Or.inr (Or.inr harc)⟩ hcell
      have hjRadius : (1 - (1 : ℝ) / j.k) ^ 2 ∈ Ioo a b := by
        norm_num [hyZero, hn] at harc
        simpa [one_div] using harc ▸ hmap
      have hk : j.k = i.k := hisolate j hjRadius
      apply Set.mem_singleton_iff.mpr
      apply congrArg Space.plane
      apply PlanePoint.ext
      · rw [hn, hk] at harc
        rw [hx]
        nlinarith [bridgeRadius_pos i]
      · exact hy'
  · intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst p
    exact ⟨q, rfl, hlq, hqr, rfl⟩

/-- Helper for Exercise 33.11: a point on the left leg of a bridge has a singleton
horizontal slice in the geometric locus. -/
lemma exists_horizontalSlice_eq_singleton_of_leftLeg_mem {i : BridgeIndex} {q : PlanePoint}
    (hx : q.x = i.n - 1 + (1 : ℝ) / i.k) (hy : q.y ∈ Icc (-1) 0) :
    ∃ l r : ℝ, l < q.x ∧ q.x < r ∧ horizontalSlice l r q.y = {Space.plane q} := by
  -- Pull the same isolated squared-radius interval back on the left side of the center.
  obtain ⟨a, b, hiRadius, hisolate⟩ := exists_isolatingInterval_bridgeRadiusSq i
  have hqRadius : (q.x - (i.n : ℝ)) ^ 2 = (1 - (1 : ℝ) / i.k) ^ 2 := by
    rw [hx]
    ring
  have hcontinuous : ContinuousAt (fun x : ℝ ↦ (x - (i.n : ℝ)) ^ 2) q.x := by
    fun_prop
  obtain ⟨l₀, r₀, hl₀, hr₀, hmaps⟩ :=
    exists_Ioo_mapsTo_Ioo_of_continuousAt hcontinuous (hqRadius ▸ hiRadius)
  let l := max l₀ ((i.n : ℝ) - 1)
  let r := min r₀ (i.n : ℝ)
  have hleft : (i.n : ℝ) - 1 < q.x := by
    rw [hx]
    have hk : (0 : ℝ) < (1 : ℝ) / i.k := by
      have hik : (0 : ℝ) < i.k := by
        exact_mod_cast (show 0 < i.k from lt_of_lt_of_le (by omega) i.two_le)
      exact div_pos zero_lt_one hik
    linarith
  have hcenter : q.x < (i.n : ℝ) := by
    rw [hx]
    linarith [bridgeRadius_pos i]
  have hlq : l < q.x := by
    simp only [l, max_lt_iff]
    exact ⟨hl₀, hleft⟩
  have hqr : q.x < r := by
    simp only [r, lt_min_iff]
    exact ⟨hr₀, hcenter⟩
  refine ⟨l, r, hlq, hqr, Set.Subset.antisymm ?_ ?_⟩
  · intro p hp
    rcases hp with ⟨q', rfl, hql, hqr', hy'⟩
    have hcell : (i.n : ℝ) - 1 < q'.x ∧ q'.x < (i.n : ℝ) + 1 := by
      constructor
      · exact (le_max_right l₀ ((i.n : ℝ) - 1)).trans_lt hql
      · have hcenter' : q'.x < (i.n : ℝ) := hqr'.trans_le (min_le_right r₀ i.n)
        linarith
    have hside : q'.x < (i.n : ℝ) := hqr'.trans_le (min_le_right r₀ i.n)
    have hmap : (q'.x - (i.n : ℝ)) ^ 2 ∈ Ioo a b := by
      apply hmaps
      constructor
      · exact (le_max_left l₀ ((i.n : ℝ) - 1)).trans_lt hql
      · exact hqr'.trans_le (min_le_left r₀ i.n)
    rcases q'.mem_geometric with ⟨j, hxLine, hyLine⟩ | ⟨j, hleg | hleg | harc⟩
    · exact (not_mem_bridgeCell_of_lineIndex i j ⟨hxLine ▸ hcell.1, hxLine ▸ hcell.2⟩).elim
    · have hn : j.n = i.n := curveCenter_eq_of_mem_of_mem_cell
          ⟨q', rfl, Or.inl hleg⟩ hcell
      rw [hleg.1, hn] at hside
      nlinarith [bridgeRadius_pos j]
    · have hn : j.n = i.n := curveCenter_eq_of_mem_of_mem_cell
          ⟨q', rfl, Or.inr (Or.inl hleg)⟩ hcell
      have hjRadius : (1 - (1 : ℝ) / j.k) ^ 2 ∈ Ioo a b := by
        have heq : (q'.x - (i.n : ℝ)) ^ 2 = (1 - (1 : ℝ) / j.k) ^ 2 := by
          rw [hleg.1, hn]
          ring
        rwa [← heq]
      have hk : j.k = i.k := hisolate j hjRadius
      apply Set.mem_singleton_iff.mpr
      apply congrArg Space.plane
      apply PlanePoint.ext
      · rw [hleg.1, hn, hk, hx]
      · exact hy'
    · have hyZero : q'.y = 0 := by
        rw [hy']
        exact le_antisymm hy.2 (hy' ▸ harc.2)
      have hn : j.n = i.n := curveCenter_eq_of_mem_of_mem_cell
          ⟨q', rfl, Or.inr (Or.inr harc)⟩ hcell
      have hjRadius : (1 - (1 : ℝ) / j.k) ^ 2 ∈ Ioo a b := by
        norm_num [hyZero, hn] at harc
        simpa [one_div] using harc ▸ hmap
      have hk : j.k = i.k := hisolate j hjRadius
      apply Set.mem_singleton_iff.mpr
      apply congrArg Space.plane
      apply PlanePoint.ext
      · rw [hn, hk] at harc
        rw [hx]
        nlinarith [bridgeRadius_pos i]
      · exact hy'
  · intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst p
    exact ⟨q, rfl, hlq, hqr, rfl⟩

/-- Helper for Exercise 33.11: a positive-height point on the left half of a bridge arc
has a singleton horizontal slice in the geometric locus. -/
lemma exists_horizontalSlice_eq_singleton_of_posArc_lt_center {i : BridgeIndex}
    {q : PlanePoint}
    (harc : (q.x - i.n) ^ 2 + q.y ^ 2 = (1 - (1 : ℝ) / i.k) ^ 2)
    (hy : 0 < q.y) (hx : q.x < (i.n : ℝ)) :
    ∃ l r : ℝ, l < q.x ∧ q.x < r ∧ horizontalSlice l r q.y = {Space.plane q} := by
  -- Isolate the bridge radius after pulling it back along the fixed-height circle equation.
  obtain ⟨a, b, hiRadius, hisolate⟩ := exists_isolatingInterval_bridgeRadiusSq i
  have hcontinuous :
      ContinuousAt (fun x : ℝ ↦ (x - (i.n : ℝ)) ^ 2 + q.y ^ 2) q.x := by
    fun_prop
  obtain ⟨l₀, r₀, hl₀, hr₀, hmaps⟩ :=
    exists_Ioo_mapsTo_Ioo_of_continuousAt hcontinuous (harc ▸ hiRadius)
  let l := max l₀ ((i.n : ℝ) - 1)
  let r := min r₀ (i.n : ℝ)
  have hleft : (i.n : ℝ) - 1 < q.x := by
    have hsq : (q.x - (i.n : ℝ)) ^ 2 < 1 := by
      nlinarith [sq_nonneg q.y, bridgeRadius_pos i, bridgeRadius_lt_one i, harc]
    nlinarith [sq_nonneg (q.x - (i.n : ℝ))]
  have hlq : l < q.x := by
    simp only [l, max_lt_iff]
    exact ⟨hl₀, hleft⟩
  have hqr : q.x < r := by
    simp only [r, lt_min_iff]
    exact ⟨hr₀, hx⟩
  refine ⟨l, r, hlq, hqr, Set.Subset.antisymm ?_ ?_⟩
  · intro p hp
    rcases hp with ⟨q', rfl, hql, hqr', hy'⟩
    have hcell : (i.n : ℝ) - 1 < q'.x ∧ q'.x < (i.n : ℝ) + 1 := by
      constructor
      · exact (le_max_right l₀ ((i.n : ℝ) - 1)).trans_lt hql
      · have hcenter' : q'.x < (i.n : ℝ) := hqr'.trans_le (min_le_right r₀ i.n)
        linarith
    have hside : q'.x < (i.n : ℝ) := hqr'.trans_le (min_le_right r₀ i.n)
    have hmap : (q'.x - (i.n : ℝ)) ^ 2 + q.y ^ 2 ∈ Ioo a b := by
      apply hmaps
      exact ⟨(le_max_left l₀ ((i.n : ℝ) - 1)).trans_lt hql,
        hqr'.trans_le (min_le_left r₀ i.n)⟩
    rcases q'.mem_geometric with ⟨j, hxLine, hyLine⟩ | ⟨j, hleg | hleg | harc'⟩
    · exact (not_mem_bridgeCell_of_lineIndex i j ⟨hxLine ▸ hcell.1, hxLine ▸ hcell.2⟩).elim
    · have : q'.y ≤ 0 := hleg.2.2
      rw [hy'] at this
      linarith
    · have : q'.y ≤ 0 := hleg.2.2
      rw [hy'] at this
      linarith
    · have hn : j.n = i.n := curveCenter_eq_of_mem_of_mem_cell
          ⟨q', rfl, Or.inr (Or.inr harc')⟩ hcell
      have hjRadius : (1 - (1 : ℝ) / j.k) ^ 2 ∈ Ioo a b := by
        have heq : (q'.x - (i.n : ℝ)) ^ 2 + q.y ^ 2 =
            (1 - (1 : ℝ) / j.k) ^ 2 := by
          simpa [hn, hy'] using harc'.1
        rwa [heq] at hmap
      have hk : j.k = i.k := hisolate j hjRadius
      apply Set.mem_singleton_iff.mpr
      apply congrArg Space.plane
      apply PlanePoint.ext
      · rw [hn, hk, hy'] at harc'
        nlinarith [harc]
      · exact hy'
  · intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst p
    exact ⟨q, rfl, hlq, hqr, rfl⟩

/-- Helper for Exercise 33.11: a positive-height point on the right half of a bridge arc
has a singleton horizontal slice in the geometric locus. -/
lemma exists_horizontalSlice_eq_singleton_of_posArc_gt_center {i : BridgeIndex}
    {q : PlanePoint}
    (harc : (q.x - i.n) ^ 2 + q.y ^ 2 = (1 - (1 : ℝ) / i.k) ^ 2)
    (hy : 0 < q.y) (hx : (i.n : ℝ) < q.x) :
    ∃ l r : ℝ, l < q.x ∧ q.x < r ∧ horizontalSlice l r q.y = {Space.plane q} := by
  -- Repeat the fixed-height radius isolation while keeping every competitor right of the center.
  obtain ⟨a, b, hiRadius, hisolate⟩ := exists_isolatingInterval_bridgeRadiusSq i
  have hcontinuous :
      ContinuousAt (fun x : ℝ ↦ (x - (i.n : ℝ)) ^ 2 + q.y ^ 2) q.x := by
    fun_prop
  obtain ⟨l₀, r₀, hl₀, hr₀, hmaps⟩ :=
    exists_Ioo_mapsTo_Ioo_of_continuousAt hcontinuous (harc ▸ hiRadius)
  let l := max l₀ (i.n : ℝ)
  let r := min r₀ ((i.n : ℝ) + 1)
  have hright : q.x < (i.n : ℝ) + 1 := by
    have hsq : (q.x - (i.n : ℝ)) ^ 2 < 1 := by
      nlinarith [sq_nonneg q.y, bridgeRadius_pos i, bridgeRadius_lt_one i, harc]
    nlinarith [sq_nonneg (q.x - (i.n : ℝ))]
  have hlq : l < q.x := by
    simp only [l, max_lt_iff]
    exact ⟨hl₀, hx⟩
  have hqr : q.x < r := by
    simp only [r, lt_min_iff]
    exact ⟨hr₀, hright⟩
  refine ⟨l, r, hlq, hqr, Set.Subset.antisymm ?_ ?_⟩
  · intro p hp
    rcases hp with ⟨q', rfl, hql, hqr', hy'⟩
    have hcell : (i.n : ℝ) - 1 < q'.x ∧ q'.x < (i.n : ℝ) + 1 := by
      constructor
      · have hcenter' : (i.n : ℝ) < q'.x := (le_max_right l₀ i.n).trans_lt hql
        linarith
      · exact hqr'.trans_le (min_le_right r₀ ((i.n : ℝ) + 1))
    have hside : (i.n : ℝ) < q'.x := (le_max_right l₀ i.n).trans_lt hql
    have hmap : (q'.x - (i.n : ℝ)) ^ 2 + q.y ^ 2 ∈ Ioo a b := by
      apply hmaps
      exact ⟨(le_max_left l₀ i.n).trans_lt hql,
        hqr'.trans_le (min_le_left r₀ ((i.n : ℝ) + 1))⟩
    rcases q'.mem_geometric with ⟨j, hxLine, hyLine⟩ | ⟨j, hleg | hleg | harc'⟩
    · exact (not_mem_bridgeCell_of_lineIndex i j ⟨hxLine ▸ hcell.1, hxLine ▸ hcell.2⟩).elim
    · have : q'.y ≤ 0 := hleg.2.2
      rw [hy'] at this
      linarith
    · have : q'.y ≤ 0 := hleg.2.2
      rw [hy'] at this
      linarith
    · have hn : j.n = i.n := curveCenter_eq_of_mem_of_mem_cell
          ⟨q', rfl, Or.inr (Or.inr harc')⟩ hcell
      have hjRadius : (1 - (1 : ℝ) / j.k) ^ 2 ∈ Ioo a b := by
        have heq : (q'.x - (i.n : ℝ)) ^ 2 + q.y ^ 2 =
            (1 - (1 : ℝ) / j.k) ^ 2 := by
          simpa [hn, hy'] using harc'.1
        rwa [heq] at hmap
      have hk : j.k = i.k := hisolate j hjRadius
      apply Set.mem_singleton_iff.mpr
      apply congrArg Space.plane
      apply PlanePoint.ext
      · rw [hn, hk, hy'] at harc'
        nlinarith [harc]
      · exact hy'
  · intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst p
    exact ⟨q, rfl, hlq, hqr, rfl⟩

/-- Helper for Exercise 33.11: every non-top point of one bridge has a singleton horizontal
slice in the geometric locus. -/
lemma exists_horizontalSlice_eq_singleton_of_curve_mem {i : BridgeIndex} {q : PlanePoint}
    (hq : Space.plane q ∈ curve i) (hnotTop : Space.plane q ≠ topPoint i) :
    ∃ l r : ℝ, l < q.x ∧ q.x < r ∧ horizontalSlice l r q.y = {Space.plane q} := by
  -- Normalize bridge membership into the two legs and the semicircle.
  rcases hq with ⟨q', hq', hcurve⟩
  injection hq' with hqq
  subst q'
  rcases hcurve with hright | hleft | harc
  · exact exists_horizontalSlice_eq_singleton_of_rightLeg_mem hright.1 hright.2
  · exact exists_horizontalSlice_eq_singleton_of_leftLeg_mem hleft.1 hleft.2
  · by_cases hyZero : q.y = 0
    · -- A zero-height arc point is one of the two leg endpoints.
      have hoffsetSq : (q.x - (i.n : ℝ)) ^ 2 =
          (1 - (1 : ℝ) / i.k) ^ 2 := by
        simpa [hyZero] using harc.1
      rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hoffsetSq with hoffset | hoffset
      · apply exists_horizontalSlice_eq_singleton_of_rightLeg_mem
        · calc
            q.x = (q.x - (i.n : ℝ)) + i.n := by ring
            _ = (1 - (1 : ℝ) / i.k) + i.n := by rw [hoffset]
            _ = (i.n : ℝ) + 1 - (1 : ℝ) / i.k := by ring
        · simp [hyZero]
      · apply exists_horizontalSlice_eq_singleton_of_leftLeg_mem
        · calc
            q.x = (q.x - (i.n : ℝ)) + i.n := by ring
            _ = -(1 - (1 : ℝ) / i.k) + i.n := by rw [hoffset]
            _ = (i.n : ℝ) - 1 + (1 : ℝ) / i.k := by ring
        · simp [hyZero]
    · have hyPos : 0 < q.y := lt_of_le_of_ne harc.2 (Ne.symm hyZero)
      have hxCenter : q.x ≠ (i.n : ℝ) := by
        intro hx
        apply hnotTop
        unfold topPoint
        apply congrArg Space.plane
        apply PlanePoint.ext
        · exact hx
        · dsimp
          rw [hx] at harc
          norm_num at harc
          rcases (sq_eq_sq_iff_eq_or_eq_neg).mp harc.1 with hyEq | hyEq
          · simpa [one_div] using hyEq
          · exfalso
            rw [hyEq] at hyPos
            have hnonpos : -(1 - ((i.k : ℝ)⁻¹)) ≤ 0 := by
              simpa [one_div] using neg_nonpos.mpr (bridgeRadius_pos i).le
            exact (not_lt_of_ge hnonpos) hyPos
      -- The non-top positive arc point lies on exactly one strict side of the center.
      rcases lt_or_gt_of_ne hxCenter with hxLeft | hxRight
      · exact exists_horizontalSlice_eq_singleton_of_posArc_lt_center harc.1 hyPos hxLeft
      · exact exists_horizontalSlice_eq_singleton_of_posArc_gt_center harc.1 hyPos hxRight

/-- Helper for Exercise 33.11: a basic set containing a top point contains a cofinite
part of its bridge. -/
lemma exists_curveDiff_subset_basic_of_topPoint_mem {i : BridgeIndex} {s : Set Space}
    (hs : s ∈ basicSets) (hp : topPoint i ∈ s) :
    ∃ t : Set Space, t.Finite ∧ topPoint i ∈ curve i \ t ∧ curve i \ t ⊆ s := by
  -- Classify the containing generator and retain the canonical indexed bridge.
  rcases hs with ⟨l, r, d, hlr, htop, rfl⟩ |
      ⟨j, t, ht, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact (htop i hp).elim
  · have hij : i = j := topPoint_mem_curve_iff.mp hp.1
    subst j
    exact ⟨t, ht, hp, fun _ hq ↦ hq⟩
  · -- Odd/even spacing upgrades containment of the top point to containment of the whole bridge.
    rcases hp with hp | ⟨q, hq, hqi⟩
    · cases hp
    · have hx : (i.n : ℝ) = q.x := by
        have hxCoord := congrArg xCoord hq
        simpa [topPoint, xCoord] using hxCoord
      have hin : i.n < j.m := by
        exact_mod_cast hx.trans_lt hqi
      have hnext : i.n + 1 ≤ j.m := by omega
      refine ⟨∅, Set.finite_empty, ⟨topPoint_mem_curve_iff.mpr rfl, by simp⟩, ?_⟩
      intro p hp
      rcases hp.1 with ⟨q', rfl, hcurve⟩
      have hbound := (curve_x_bounds (i := i) (q := q') ⟨q', rfl, hcurve⟩).2
      have hnextReal : (i.n : ℝ) + 1 ≤ j.m := by
        exact_mod_cast hnext
      exact Or.inr ⟨q', rfl, hbound.trans_le hnextReal⟩
  · rcases hp with hp | ⟨q, hq, hji⟩
    · cases hp
    · have hx : (i.n : ℝ) = q.x := by
        have hxCoord := congrArg xCoord hq
        simpa [topPoint, xCoord] using hxCoord
      have hin : j.m < i.n := by
        exact_mod_cast hji.trans_eq hx.symm
      have hprev : j.m ≤ i.n - 1 := by omega
      refine ⟨∅, Set.finite_empty, ⟨topPoint_mem_curve_iff.mpr rfl, by simp⟩, ?_⟩
      intro p hp
      rcases hp.1 with ⟨q', rfl, hcurve⟩
      have hbound := (curve_x_bounds (i := i) (q := q') ⟨q', rfl, hcurve⟩).1
      have hprevReal : (j.m : ℝ) ≤ (i.n : ℝ) - 1 := by
        exact_mod_cast hprev
      exact Or.inr ⟨q', rfl, hprevReal.trans_lt hbound⟩

/-- Helper for Exercise 33.11: a non-top plane point in a basic generator has a top-free
horizontal basic neighborhood contained in that generator. -/
lemma exists_horizontalBasic_subset_of_nonTop_mem {q : PlanePoint} {s : Set Space}
    (hnotTop : ∀ i : BridgeIndex, Space.plane q ≠ topPoint i)
    (hs : s ∈ basicSets) (hq : Space.plane q ∈ s) :
    ∃ l r : ℝ, l < q.x ∧ q.x < r ∧ horizontalSlice l r q.y ∈ basicSets ∧
      (∀ i : BridgeIndex, topPoint i ∉ horizontalSlice l r q.y) ∧
      horizontalSlice l r q.y ⊆ s := by
  -- Normalize each generator separately; bridge points use the singleton isolation interface.
  rcases hs with ⟨l, r, d, hlr, htop, rfl⟩ |
      ⟨i, t, ht, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rcases hq with ⟨q', hq', hql, hqr, hy⟩
    injection hq' with hqq
    subst q'
    subst d
    exact ⟨l, r, hql, hqr, horizontalSlice_mem_basicSets hlr htop, htop,
      fun _ hp ↦ hp⟩
  · obtain ⟨l, r, hlq, hqr, hsingleton⟩ :=
      exists_horizontalSlice_eq_singleton_of_curve_mem hq.1 (hnotTop i)
    have htopFree : ∀ j : BridgeIndex, topPoint j ∉ horizontalSlice l r q.y := by
      intro j hj
      rw [hsingleton, Set.mem_singleton_iff] at hj
      exact hnotTop j hj.symm
    refine ⟨l, r, hlq, hqr, horizontalSlice_mem_basicSets (hlq.trans hqr) htopFree,
      htopFree, ?_⟩
    intro p hp
    rw [hsingleton, Set.mem_singleton_iff] at hp
    subst p
    exact hq
  · rcases hq with hq | ⟨q', hq', hqi⟩
    · cases hq
    · injection hq' with hqq
      subst q'
      rcases q.mem_geometric with ⟨j, hx, hy⟩ | ⟨j, hcurve⟩
      · let l := q.x - 1
        let r := min (q.x + 1) i.m
        have hlq : l < q.x := by simp [l]
        have hqr : q.x < r := by
          simp only [r, lt_min_iff]
          exact ⟨by linarith, hqi⟩
        have htopFree : ∀ j : BridgeIndex, topPoint j ∉ horizontalSlice l r q.y := by
          intro j hj
          rcases hj with ⟨q', hq', _, _, hy'⟩
          injection hq' with hqTop
          subst q'
          exact (not_lt_of_ge hy.2) ((bridgeRadius_pos j).trans_eq hy')
        refine ⟨l, r, hlq, hqr,
          horizontalSlice_mem_basicSets (hlq.trans hqr) htopFree, htopFree, ?_⟩
        intro p hp
        rcases hp with ⟨q', rfl, _, hqr', _⟩
        exact Or.inr ⟨q', rfl, hqr'.trans_le (min_le_right (q.x + 1) i.m)⟩
      · obtain ⟨l, r, hlq, hqr, hsingleton⟩ :=
          exists_horizontalSlice_eq_singleton_of_curve_mem ⟨q, rfl, hcurve⟩ (hnotTop j)
        have htopFree : ∀ k : BridgeIndex, topPoint k ∉ horizontalSlice l r q.y := by
          intro k hk
          rw [hsingleton, Set.mem_singleton_iff] at hk
          exact hnotTop k hk.symm
        refine ⟨l, r, hlq, hqr,
          horizontalSlice_mem_basicSets (hlq.trans hqr) htopFree, htopFree, ?_⟩
        intro p hp
        rw [hsingleton, Set.mem_singleton_iff] at hp
        subst p
        exact Or.inr ⟨q, rfl, hqi⟩
  · rcases hq with hq | ⟨q', hq', hiq⟩
    · cases hq
    · injection hq' with hqq
      subst q'
      rcases q.mem_geometric with ⟨j, hx, hy⟩ | ⟨j, hcurve⟩
      · let l := max (q.x - 1) i.m
        let r := q.x + 1
        have hlq : l < q.x := by
          simp only [l, max_lt_iff]
          exact ⟨by linarith, hiq⟩
        have hqr : q.x < r := by simp [r]
        have htopFree : ∀ j : BridgeIndex, topPoint j ∉ horizontalSlice l r q.y := by
          intro j hj
          rcases hj with ⟨q', hq', _, _, hy'⟩
          injection hq' with hqTop
          subst q'
          exact (not_lt_of_ge hy.2) ((bridgeRadius_pos j).trans_eq hy')
        refine ⟨l, r, hlq, hqr,
          horizontalSlice_mem_basicSets (hlq.trans hqr) htopFree, htopFree, ?_⟩
        intro p hp
        rcases hp with ⟨q', rfl, hql', _, _⟩
        exact Or.inr ⟨q', rfl, (le_max_right (q.x - 1) i.m).trans_lt hql'⟩
      · obtain ⟨l, r, hlq, hqr, hsingleton⟩ :=
          exists_horizontalSlice_eq_singleton_of_curve_mem ⟨q, rfl, hcurve⟩ (hnotTop j)
        have htopFree : ∀ k : BridgeIndex, topPoint k ∉ horizontalSlice l r q.y := by
          intro k hk
          rw [hsingleton, Set.mem_singleton_iff] at hk
          exact hnotTop k hk.symm
        refine ⟨l, r, hlq, hqr,
          horizontalSlice_mem_basicSets (hlq.trans hqr) htopFree, htopFree, ?_⟩
        intro p hp
        rw [hsingleton, Set.mem_singleton_iff] at hp
        subst p
        exact Or.inr ⟨q, rfl, hiq⟩

/-- Helper for Exercise 33.11: basic sets refine locally at a common plane point. -/
lemma basicSets_exists_subset_inter_plane (q : PlanePoint) :
    ∀ s ∈ basicSets, ∀ t ∈ basicSets, Space.plane q ∈ s ∩ t →
      ∃ u ∈ basicSets, Space.plane q ∈ u ∧ u ⊆ s ∩ t := by
  intro s hs t ht hp
  by_cases htop : ∃ i : BridgeIndex, Space.plane q = topPoint i
  · -- At a bridge top, intersect two cofinite bridge neighborhoods by uniting deletions.
    obtain ⟨i, hi⟩ := htop
    have hps : topPoint i ∈ s := by
      rw [← hi]
      exact hp.1
    have hpt : topPoint i ∈ t := by
      rw [← hi]
      exact hp.2
    obtain ⟨a, haFinite, haTop, haSub⟩ :=
      exists_curveDiff_subset_basic_of_topPoint_mem hs hps
    obtain ⟨b, hbFinite, hbTop, hbSub⟩ :=
      exists_curveDiff_subset_basic_of_topPoint_mem ht hpt
    refine ⟨curve i \ (a ∪ b), curve_diff_mem_basicSets i (haFinite.union hbFinite), ?_, ?_⟩
    · rw [hi]
      exact ⟨haTop.1, fun hab ↦ hab.elim haTop.2 hbTop.2⟩
    · intro p hp'
      exact ⟨haSub ⟨hp'.1, fun ha ↦ hp'.2 (Or.inl ha)⟩,
        hbSub ⟨hp'.1, fun hb ↦ hp'.2 (Or.inr hb)⟩⟩
  · -- Route correction: normalize each generator to a horizontal neighborhood first, then
    -- intersect only the two endpoint intervals.
    have hnotTop : ∀ i : BridgeIndex, Space.plane q ≠ topPoint i := by
      intro i hi
      exact htop ⟨i, hi⟩
    obtain ⟨ls, rs, hls, hrs, hsbasic, hsTopFree, hssub⟩ :=
      exists_horizontalBasic_subset_of_nonTop_mem hnotTop hs hp.1
    obtain ⟨lt, rt, hlt, hrt, htbasic, htTopFree, htsub⟩ :=
      exists_horizontalBasic_subset_of_nonTop_mem hnotTop ht hp.2
    let l := max ls lt
    let r := min rs rt
    have hlq : l < q.x := by
      simp only [l, max_lt_iff]
      exact ⟨hls, hlt⟩
    have hqr : q.x < r := by
      simp only [r, lt_min_iff]
      exact ⟨hrs, hrt⟩
    have hlr : l < r := hlq.trans hqr
    have htopFree : ∀ i : BridgeIndex, topPoint i ∉ horizontalSlice l r q.y := by
      intro i hi
      apply hsTopFree i
      rcases hi with ⟨q', hq', hql, hqr', hy⟩
      refine ⟨q', hq', ?_, ?_, hy⟩
      · exact (le_max_left ls lt).trans_lt hql
      · exact hqr'.trans_le (min_le_left rs rt)
    refine ⟨horizontalSlice l r q.y,
      horizontalSlice_mem_basicSets hlr htopFree, ?_, ?_⟩
    · exact ⟨q, rfl, hlq, hqr, rfl⟩
    · intro p hp'
      have hps : p ∈ horizontalSlice ls rs q.y := by
        rcases hp' with ⟨q', rfl, hql, hqr', hy⟩
        refine ⟨q', rfl, ?_, ?_, hy⟩
        · exact (le_max_left ls lt).trans_lt hql
        · exact hqr'.trans_le (min_le_left _ _)
      have hpt : p ∈ horizontalSlice lt rt q.y := by
        rcases hp' with ⟨q', rfl, hql, hqr', hy⟩
        refine ⟨q', rfl, ?_, ?_, hy⟩
        · exact (le_max_right ls lt).trans_lt hql
        · exact hqr'.trans_le (min_le_right _ _)
      exact ⟨hssub hps, htsub hpt⟩

/-- Helper for Exercise 33.11: two designated basic sets refine locally at each common point. -/
lemma basicSets_exists_subset_inter :
    ∀ s ∈ basicSets, ∀ t ∈ basicSets, ∀ p ∈ s ∩ t,
      ∃ u ∈ basicSets, p ∈ u ∧ u ⊆ s ∩ t := by
  -- Route correction: pairwise curve intersections are unnecessary; classify the common point.
  intro s hs t ht p hp
  cases p with
  | leftEnd =>
      obtain ⟨i, rfl⟩ := eq_leftRay_of_mem_basicSets_of_leftEnd_mem hs hp.1
      obtain ⟨j, rfl⟩ := eq_leftRay_of_mem_basicSets_of_leftEnd_mem ht hp.2
      rcases le_total i.m j.m with hij | hji
      · refine ⟨leftRay i, leftRay_mem_basicSets i, leftEnd_mem_leftRay i, ?_⟩
        exact fun p hp ↦ ⟨hp, leftRay_mono hij hp⟩
      · refine ⟨leftRay j, leftRay_mem_basicSets j, leftEnd_mem_leftRay j, ?_⟩
        exact fun p hp ↦ ⟨leftRay_mono hji hp, hp⟩
  | rightEnd =>
      obtain ⟨i, rfl⟩ := eq_rightRay_of_mem_basicSets_of_rightEnd_mem hs hp.1
      obtain ⟨j, rfl⟩ := eq_rightRay_of_mem_basicSets_of_rightEnd_mem ht hp.2
      rcases le_total i.m j.m with hij | hji
      · refine ⟨rightRay j, rightRay_mem_basicSets j, rightEnd_mem_rightRay j, ?_⟩
        exact fun p hp ↦ ⟨rightRay_anti hij hp, hp⟩
      · refine ⟨rightRay i, rightRay_mem_basicSets i, rightEnd_mem_rightRay i, ?_⟩
        exact fun p hp ↦ ⟨hp, rightRay_anti hji hp⟩
  | plane q =>
      exact basicSets_exists_subset_inter_plane q s hs t ht hp

/-- Helper for Exercise 33.11: the four designated families form a basis for the topology on
`Space`. -/
theorem basicSets_isTopologicalBasis : TopologicalSpace.IsTopologicalBasis basicSets := by
  -- Assemble the basis from local intersection refinement, coverage, and the defining topology.
  exact ⟨basicSets_exists_subset_inter, basicSets_sUnion_eq_univ, topology_eq_generateFrom⟩

/-- Helper for Exercise 33.11: a fiber of a continuous real-valued function is a `Gδ` set. -/
theorem continuous_fiber_isGδ {α : Type u} [TopologicalSpace α] {f : α → ℝ}
    (hf : Continuous f) (c : ℝ) : IsGδ (f ⁻¹' {c}) :=
  (IsGδ.singleton c).preimage hf

/-- Points of `Cₙ,ₖ` where `f` differs from its value at the top point. -/
def exceptionalSet (f : Space → ℝ) (i : BridgeIndex) : Set Space :=
  {p | p ∈ curve i ∧ f p ≠ f (topPoint i)}

/-- Membership in an exceptional set records both curve membership and value inequality. -/
theorem mem_exceptionalSet_iff {f : Space → ℝ} {i : BridgeIndex} {p : Space} :
    p ∈ exceptionalSet f i ↔ p ∈ curve i ∧ f p ≠ f (topPoint i) := Iff.rfl

/-- Helper for Exercise 33.11: each exceptional subset of a bridge is countable. -/
theorem exceptionalSet_countable {f : Space → ℝ} (hf : Continuous f) (i : BridgeIndex) :
    (exceptionalSet f i).Countable := by
  classical
  -- Present the fiber through the bridge top as a countable intersection of open sets.
  obtain ⟨U, hUOpen, hFiber⟩ := (continuous_fiber_isGδ hf (f (topPoint i))).eq_iInter_nat
  have hcofinite (m : ℕ) :
      ∃ t : Set Space, t.Finite ∧ topPoint i ∈ curve i \ t ∧ curve i \ t ⊆ U m := by
    have htopU : topPoint i ∈ U m := by
      have htopFiber : topPoint i ∈ f ⁻¹' {f (topPoint i)} := by
        simp only [mem_preimage, mem_singleton_iff]
      rw [hFiber] at htopFiber
      exact mem_iInter.mp htopFiber m
    obtain ⟨s, hsBasic, htopS, hsU⟩ :=
      basicSets_isTopologicalBasis.isOpen_iff.mp (hUOpen m) (topPoint i) htopU
    obtain ⟨t, htFinite, htop, htS⟩ :=
      exists_curveDiff_subset_basic_of_topPoint_mem hsBasic htopS
    exact ⟨t, htFinite, htop, htS.trans hsU⟩
  choose t htFinite htop htU using hcofinite
  -- Outside the fiber, a bridge point must occur in one of the finite complements.
  refine (Set.countable_iUnion fun m ↦ (htFinite m).countable).mono ?_
  intro p hp
  by_contra hpUnion
  have hpU : ∀ m : ℕ, p ∈ U m := by
    intro m
    apply htU m
    refine ⟨hp.1, ?_⟩
    intro hpt
    exact hpUnion (mem_iUnion.mpr ⟨m, hpt⟩)
  have hpFiber : p ∈ f ⁻¹' {f (topPoint i)} := by
    rw [hFiber]
    exact mem_iInter.mpr hpU
  have hpValue : f p = f (topPoint i) := by
    simpa only [mem_preimage, mem_singleton_iff] using hpFiber
  exact hp.2 hpValue

/-- A point of the plane locus lies on the horizontal line of height `d`. -/
def LiesOnHorizontal (d : ℝ) : Space → Prop
  | Space.plane p => p.y = d
  | Space.leftEnd => False
  | Space.rightEnd => False

/-- A horizontal level avoids all exceptional sets for a fixed function. -/
def AvoidsExceptionalSets (f : Space → ℝ) (d : ℝ) : Prop :=
  ∀ i : BridgeIndex, ∀ p ∈ exceptionalSet f i, ¬ LiesOnHorizontal d p

/-- Helper for Exercise 33.11: one horizontal level avoids every exceptional set. -/
theorem exists_avoidingLevel {f : Space → ℝ} (hf : Continuous f) :
    ∃ d ∈ Icc (-1) 0, AvoidsExceptionalSets f d := by
  classical
  -- Encode bridge indices by their integer and natural coordinates.
  let encode : BridgeIndex → ℤ × ℕ := fun i ↦ (i.n, i.k)
  have hencode : Function.Injective encode := by
    intro i j hij
    cases i with
    | mk n k hn hk =>
      cases j with
      | mk n' k' hn' hk' =>
        simp only [encode, Prod.mk.injEq] at hij
        cases hij.1
        cases hij.2
        rfl
  letI : Countable BridgeIndex := hencode.countable
  let forbidden : Set ℝ :=
    ⋃ i : BridgeIndex, Option.some ⁻¹' (yCoord '' exceptionalSet f i)
  have hforbidden : forbidden.Countable := by
    exact Set.countable_iUnion fun i ↦
      ((exceptionalSet_countable hf i).image yCoord).preimage (Option.some_injective ℝ)
  have hnotSubset : ¬ Icc (-1 : ℝ) 0 ⊆ forbidden := by
    intro hsubset
    have hinterval : (Icc (-1 : ℝ) 0).Countable := hforbidden.mono hsubset
    have : (0 : ℝ) ≤ -1 := Cardinal.Real.Icc_countable_iff.mp hinterval
    norm_num at this
  obtain ⟨d, hd, hdForbidden⟩ := Set.not_subset.mp hnotSubset
  refine ⟨d, hd, ?_⟩
  -- Membership at height `d` would put `d` in the forbidden coordinate set.
  intro i p hp hhorizontal
  apply hdForbidden
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  cases p with
  | plane q =>
      refine ⟨Space.plane q, hp, ?_⟩
      simpa [LiesOnHorizontal, yCoord] using congrArg Option.some hhorizontal
  | leftEnd => simp [LiesOnHorizontal] at hhorizontal
  | rightEnd => simp [LiesOnHorizontal] at hhorizontal

/-- Subtracting one from an odd integer gives an even integer. -/
theorem even_sub_one_of_odd {n : ℤ} (hn : Odd n) : Even (n - 1) :=
  hn.sub_odd odd_one

/-- Adding one to an odd integer gives an even integer. -/
theorem even_add_one_of_odd {n : ℤ} (hn : Odd n) : Even (n + 1) :=
  hn.add_odd odd_one

/-- The valid bridge index with fixed odd center `n` and variable height index `k`. -/
def bridgeIndex (n : ℤ) (hn : Odd n) (k : {k : ℕ // 2 ≤ k}) : BridgeIndex :=
  ⟨n, k, hn, k.property⟩

/-- The even line immediately to the left of an odd bridge center. -/
def leftLineIndex (n : ℤ) (hn : Odd n) : LineIndex :=
  ⟨n - 1, even_sub_one_of_odd hn⟩

/-- The even line immediately to the right of an odd bridge center. -/
def rightLineIndex (n : ℤ) (hn : Odd n) : LineIndex :=
  ⟨n + 1, even_add_one_of_odd hn⟩

/-- Helper for Exercise 33.11: the left-leg coordinates belong to their indexed bridge. -/
lemma leftLegPoint_mem_geometric (n : ℤ) (hn : Odd n) (k : {k : ℕ // 2 ≤ k})
    (d : ℝ) (hd : d ∈ Icc (-1) 0) :
    GeometricPoint (n - 1 + (1 : ℝ) / k) d := by
  -- Use the second vertical leg in the defining geometric disjunction.
  exact Or.inr ⟨bridgeIndex n hn k, Or.inr (Or.inl ⟨rfl, hd⟩)⟩

/-- Helper for Exercise 33.11: the point at height `d` on the left leg of a bridge. -/
noncomputable def leftLegPoint (n : ℤ) (hn : Odd n) (k : {k : ℕ // 2 ≤ k})
    (d : ℝ) (hd : d ∈ Icc (-1) 0) : Space :=
  Space.plane ⟨n - 1 + (1 : ℝ) / k, d, leftLegPoint_mem_geometric n hn k d hd⟩

/-- Helper for Exercise 33.11: the right-leg coordinates belong to their indexed bridge. -/
lemma rightLegPoint_mem_geometric (n : ℤ) (hn : Odd n) (k : {k : ℕ // 2 ≤ k})
    (d : ℝ) (hd : d ∈ Icc (-1) 0) :
    GeometricPoint (n + 1 - (1 : ℝ) / k) d := by
  -- Use the first vertical leg in the defining geometric disjunction.
  exact Or.inr ⟨bridgeIndex n hn k, Or.inl ⟨rfl, hd⟩⟩

/-- Helper for Exercise 33.11: the point at height `d` on the right leg of a bridge. -/
noncomputable def rightLegPoint (n : ℤ) (hn : Odd n) (k : {k : ℕ // 2 ≤ k})
    (d : ℝ) (hd : d ∈ Icc (-1) 0) : Space :=
  Space.plane ⟨n + 1 - (1 : ℝ) / k, d, rightLegPoint_mem_geometric n hn k d hd⟩

/-- Helper for Exercise 33.11: an even-line point is never a bridge top. -/
lemma linePoint_ne_topPoint (i : LineIndex) (d : ℝ) (hd : d ∈ Icc (-1) 0)
    (j : BridgeIndex) : linePoint i d hd ≠ topPoint j := by
  -- Equality of the points would identify an even integer with an odd integer.
  intro h
  have hx := congrArg xCoord h
  simp only [xCoord_linePoint, xCoord_topPoint] at hx
  have hxReal : (i.m : ℝ) = j.n := Option.some.inj hx
  have hxInt : i.m = j.n := by
    exact_mod_cast hxReal
  rcases i.even with ⟨a, ha⟩
  rcases j.odd with ⟨b, hb⟩
  omega

/-- Helper for Exercise 33.11: reciprocal indices tend to zero after restricting to
`k ≥ 2`. -/
lemma restricted_one_div_tendsto_zero :
    Tendsto (fun k : {k : ℕ // 2 ≤ k} ↦ (1 : ℝ) / k) atTop (𝓝 0) := by
  -- Restriction to a final interval does not change an at-top limit.
  exact tendsto_comp_val_Ici_atTop.mpr tendsto_one_div_atTop_nhds_zero_nat

/-- Helper for Exercise 33.11: left-leg points converge to the adjacent left vertical line. -/
lemma leftLegPoints_tendsto_leftLine (n : ℤ) (hn : Odd n) (d : ℝ)
    (hd : d ∈ Icc (-1) 0) :
    Tendsto (fun k : {k : ℕ // 2 ≤ k} ↦ leftLegPoint n hn k d hd) atTop
      (𝓝 (linePoint (leftLineIndex n hn) d hd)) := by
  -- It suffices to enter each designated basic neighborhood of the line point.
  refine basicSets_isTopologicalBasis.nhds_hasBasis.tendsto_right_iff.mpr ?_
  intro s hs
  obtain ⟨l, r, hl, hr, hsliceBasic, htopFree, hsubset⟩ :=
    exists_horizontalBasic_subset_of_nonTop_mem
      (q := ⟨(leftLineIndex n hn).m, d,
        linePoint_mem_geometric (leftLineIndex n hn) d hd⟩)
      (linePoint_ne_topPoint (leftLineIndex n hn) d hd) hs.1 hs.2
  have hx : Tendsto (fun k : {k : ℕ // 2 ≤ k} ↦
      (n : ℝ) - 1 + (1 : ℝ) / k) atTop (𝓝 ((n : ℝ) - 1)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add restricted_one_div_tendsto_zero :
        Tendsto (fun k : {k : ℕ // 2 ≤ k} ↦
          ((n : ℝ) - 1) + (1 : ℝ) / k) atTop (𝓝 (((n : ℝ) - 1) + 0)))
  have hl' : l < (n : ℝ) - 1 := by
    simpa only [leftLineIndex, Int.cast_sub, Int.cast_one] using hl
  have hr' : (n : ℝ) - 1 < r := by
    simpa only [leftLineIndex, Int.cast_sub, Int.cast_one] using hr
  have hevent : ∀ᶠ k : {k : ℕ // 2 ≤ k} in atTop,
      (n : ℝ) - 1 + (1 : ℝ) / k ∈ Ioo l r := hx (Ioo_mem_nhds hl' hr')
  filter_upwards [hevent] with k hk
  apply hsubset
  exact ⟨_, rfl, hk.1, hk.2, rfl⟩

/-- Helper for Exercise 33.11: right-leg points converge to the adjacent right vertical line. -/
lemma rightLegPoints_tendsto_rightLine (n : ℤ) (hn : Odd n) (d : ℝ)
    (hd : d ∈ Icc (-1) 0) :
    Tendsto (fun k : {k : ℕ // 2 ≤ k} ↦ rightLegPoint n hn k d hd) atTop
      (𝓝 (linePoint (rightLineIndex n hn) d hd)) := by
  -- Refine a basic neighborhood to a horizontal slice and use coordinate convergence.
  refine basicSets_isTopologicalBasis.nhds_hasBasis.tendsto_right_iff.mpr ?_
  intro s hs
  obtain ⟨l, r, hl, hr, hsliceBasic, htopFree, hsubset⟩ :=
    exists_horizontalBasic_subset_of_nonTop_mem
      (q := ⟨(rightLineIndex n hn).m, d,
        linePoint_mem_geometric (rightLineIndex n hn) d hd⟩)
      (linePoint_ne_topPoint (rightLineIndex n hn) d hd) hs.1 hs.2
  have hx : Tendsto (fun k : {k : ℕ // 2 ≤ k} ↦
      (n : ℝ) + 1 - (1 : ℝ) / k) atTop (𝓝 ((n : ℝ) + 1)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub restricted_one_div_tendsto_zero :
        Tendsto (fun k : {k : ℕ // 2 ≤ k} ↦
          ((n : ℝ) + 1) - (1 : ℝ) / k) atTop (𝓝 (((n : ℝ) + 1) - 0)))
  have hl' : l < (n : ℝ) + 1 := by
    simpa only [rightLineIndex, Int.cast_add, Int.cast_one] using hl
  have hr' : (n : ℝ) + 1 < r := by
    simpa only [rightLineIndex, Int.cast_add, Int.cast_one] using hr
  have hevent : ∀ᶠ k : {k : ℕ // 2 ≤ k} in atTop,
      (n : ℝ) + 1 - (1 : ℝ) / k ∈ Ioo l r := hx (Ioo_mem_nhds hl' hr')
  filter_upwards [hevent] with k hk
  apply hsubset
  exact ⟨_, rfl, hk.1, hk.2, rfl⟩

/-- Helper for Exercise 33.11: avoidance identifies a left-leg value with its bridge-top value. -/
lemma leftLegValue_eq_topValue {f : Space → ℝ} {n : ℤ} {hn : Odd n}
    {k : {k : ℕ // 2 ≤ k}} {d : ℝ} {hd : d ∈ Icc (-1) 0}
    (havoid : AvoidsExceptionalSets f d) :
    f (leftLegPoint n hn k d hd) = f (topPoint (bridgeIndex n hn k)) := by
  -- A differing value would put this height-`d` leg point in the exceptional set.
  by_contra hne
  have hExceptional :
      leftLegPoint n hn k d hd ∈ exceptionalSet f (bridgeIndex n hn k) :=
    ⟨⟨_, rfl, Or.inr (Or.inl ⟨rfl, hd⟩)⟩, hne⟩
  exact (havoid (bridgeIndex n hn k) (leftLegPoint n hn k d hd) hExceptional) rfl

/-- Helper for Exercise 33.11: avoidance identifies a right-leg value with its bridge-top value. -/
lemma rightLegValue_eq_topValue {f : Space → ℝ} {n : ℤ} {hn : Odd n}
    {k : {k : ℕ // 2 ≤ k}} {d : ℝ} {hd : d ∈ Icc (-1) 0}
    (havoid : AvoidsExceptionalSets f d) :
    f (rightLegPoint n hn k d hd) = f (topPoint (bridgeIndex n hn k)) := by
  -- The same exceptional-set contradiction applies on the right leg.
  by_contra hne
  have hExceptional :
      rightLegPoint n hn k d hd ∈ exceptionalSet f (bridgeIndex n hn k) :=
    ⟨⟨_, rfl, Or.inl ⟨rfl, hd⟩⟩, hne⟩
  exact (havoid (bridgeIndex n hn k) (rightLegPoint n hn k d hd) hExceptional) rfl

/-- Helper for Exercise 33.11: values at bridge tops converge to the value on the left adjacent
line. -/
theorem topValues_tendsto_left {f : Space → ℝ} (hf : Continuous f) (n : ℤ) (hn : Odd n)
    (d : ℝ) (hd : d ∈ Icc (-1) 0) (havoid : AvoidsExceptionalSets f d) :
    Tendsto
      (fun k : {k : ℕ // 2 ≤ k} ↦ f (topPoint (bridgeIndex n hn k))) atTop
      (𝓝 (f (linePoint (leftLineIndex n hn) d hd))) := by
  -- Map left-leg convergence through `f`, then replace every leg value by its top value.
  refine Tendsto.congr' ?_
    (hf.continuousAt.tendsto.comp (leftLegPoints_tendsto_leftLine n hn d hd))
  exact Eventually.of_forall fun k ↦
    leftLegValue_eq_topValue (n := n) (hn := hn) (k := k) (hd := hd) havoid

/-- Helper for Exercise 33.11: values at bridge tops converge to the value on the right adjacent
line. -/
theorem topValues_tendsto_right {f : Space → ℝ} (hf : Continuous f) (n : ℤ) (hn : Odd n)
    (d : ℝ) (hd : d ∈ Icc (-1) 0) (havoid : AvoidsExceptionalSets f d) :
    Tendsto
      (fun k : {k : ℕ // 2 ≤ k} ↦ f (topPoint (bridgeIndex n hn k))) atTop
      (𝓝 (f (linePoint (rightLineIndex n hn) d hd))) := by
  -- Map right-leg convergence through `f`, then use the avoidance equality pointwise.
  refine Tendsto.congr' ?_
    (hf.continuousAt.tendsto.comp (rightLegPoints_tendsto_rightLine n hn d hd))
  exact Eventually.of_forall fun k ↦
    rightLegValue_eq_topValue (n := n) (hn := hn) (k := k) (hd := hd) havoid

/-- Helper for Exercise 33.11: the values on the two adjacent vertical lines agree. -/
theorem linePoint_eq {f : Space → ℝ} (hf : Continuous f) (n : ℤ) (hn : Odd n)
    (d : ℝ) (hd : d ∈ Icc (-1) 0) (havoid : AvoidsExceptionalSets f d) :
    f (linePoint (leftLineIndex n hn) d hd) =
      f (linePoint (rightLineIndex n hn) d hd) := by
  -- The common sequence of bridge-top values has both adjacent line values as limits.
  exact tendsto_nhds_unique
    (topValues_tendsto_left hf n hn d hd havoid)
    (topValues_tendsto_right hf n hn d hd havoid)

/-- Helper for Exercise 33.11: twice an integer is even. -/
lemma even_two_mul (z : ℤ) : Even (2 * z) := by
  -- The multiplier itself witnesses evenness.
  refine ⟨z, ?_⟩
  ring

/-- Helper for Exercise 33.11: the canonical even line at coordinate `2z`. -/
def evenLineIndex (z : ℤ) : LineIndex :=
  ⟨2 * z, even_two_mul z⟩

/-- Helper for Exercise 33.11: line indices are determined by their integer coordinate. -/
lemma LineIndex.ext {i j : LineIndex} (h : i.m = j.m) : i = j := by
  cases i
  cases j
  simp_all

/-- Helper for Exercise 33.11: an odd center between two canonical even lines. -/
lemma odd_two_mul_add_one (z : ℤ) : Odd (2 * z + 1) := by
  -- The integer `z` witnesses the standard odd normal form.
  refine ⟨z, ?_⟩
  ring

/-- Helper for Exercise 33.11: the left neighbor of `2z+1` is the canonical line `2z`. -/
lemma leftLineIndex_two_mul_add_one (z : ℤ) :
    leftLineIndex (2 * z + 1) (odd_two_mul_add_one z) = evenLineIndex z := by
  -- Both bundled indices have the same integer coordinate; proof fields are irrelevant.
  apply LineIndex.ext
  dsimp only [leftLineIndex, evenLineIndex]
  ring

/-- Helper for Exercise 33.11: the right neighbor of `2z+1` is the canonical line `2(z+1)`. -/
lemma rightLineIndex_two_mul_add_one (z : ℤ) :
    rightLineIndex (2 * z + 1) (odd_two_mul_add_one z) = evenLineIndex (z + 1) := by
  -- Normalize the two integer coordinates and use proof irrelevance for evenness.
  apply LineIndex.ext
  dsimp only [rightLineIndex, evenLineIndex]
  ring

/-- Helper for Exercise 33.11: consecutive canonical even-line points have equal values. -/
lemma evenLinePoint_succ_eq {f : Space → ℝ} (hf : Continuous f) (z : ℤ)
    (d : ℝ) (hd : d ∈ Icc (-1) 0) (havoid : AvoidsExceptionalSets f d) :
    f (linePoint (evenLineIndex z) d hd) =
      f (linePoint (evenLineIndex (z + 1)) d hd) := by
  -- Apply adjacent-line equality at the intervening odd center `2z+1`.
  simpa only [leftLineIndex_two_mul_add_one, rightLineIndex_two_mul_add_one] using
    linePoint_eq hf (2 * z + 1) (odd_two_mul_add_one z) d hd havoid

/-- Helper for Exercise 33.11: the negative even-line sequence converges to the left end. -/
lemma evenLinePoints_tendsto_leftEnd (d : ℝ) (hd : d ∈ Icc (-1) 0) :
    Tendsto (fun k : ℕ ↦ linePoint (evenLineIndex (-(k : ℤ))) d hd) atTop
      (𝓝 Space.leftEnd) := by
  -- Every basic neighborhood of the left end is a left ray with a fixed cutoff.
  refine basicSets_isTopologicalBasis.nhds_hasBasis.tendsto_right_iff.mpr ?_
  intro s hs
  obtain ⟨i, rfl⟩ := eq_leftRay_of_mem_basicSets_of_leftEnd_mem hs.1 hs.2
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (-(i.m : ℝ))
  filter_upwards [eventually_ge_atTop N] with k hk
  apply Or.inr
  refine ⟨_, rfl, ?_⟩
  have hkReal : (N : ℝ) ≤ k := by
    exact_mod_cast hk
  dsimp only [linePoint, evenLineIndex]
  push_cast
  linarith

/-- Helper for Exercise 33.11: the positive even-line sequence converges to the right end. -/
lemma evenLinePoints_tendsto_rightEnd (d : ℝ) (hd : d ∈ Icc (-1) 0) :
    Tendsto (fun k : ℕ ↦ linePoint (evenLineIndex (k : ℤ)) d hd) atTop
      (𝓝 Space.rightEnd) := by
  -- Every basic neighborhood of the right end is a right ray with a fixed cutoff.
  refine basicSets_isTopologicalBasis.nhds_hasBasis.tendsto_right_iff.mpr ?_
  intro s hs
  obtain ⟨i, rfl⟩ := eq_rightRay_of_mem_basicSets_of_rightEnd_mem hs.1 hs.2
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (i.m : ℝ)
  filter_upwards [eventually_ge_atTop N] with k hk
  apply Or.inr
  refine ⟨_, rfl, ?_⟩
  have hkReal : (N : ℝ) ≤ k := by
    exact_mod_cast hk
  dsimp only [linePoint, evenLineIndex]
  push_cast
  linarith

/-- Helper for Exercise 33.11: all nonnegative canonical even lines have the central value. -/
lemma nonnegativeEvenLineValue_eq_zero {f : Space → ℝ} (hf : Continuous f)
    (k : ℕ) (d : ℝ) (hd : d ∈ Icc (-1) 0) (havoid : AvoidsExceptionalSets f d) :
    f (linePoint (evenLineIndex (k : ℤ)) d hd) =
      f (linePoint (evenLineIndex 0) d hd) := by
  -- Induct along consecutive even lines, using the bridge between each pair.
  induction k with
  | zero => rfl
  | succ k ih =>
      calc
        f (linePoint (evenLineIndex ((k + 1 : ℕ) : ℤ)) d hd) =
            f (linePoint (evenLineIndex (k : ℤ)) d hd) := by
              simpa only [Nat.cast_add, Nat.cast_one] using
                (evenLinePoint_succ_eq hf (k : ℤ) d hd havoid).symm
        _ = f (linePoint (evenLineIndex 0) d hd) := ih

/-- Helper for Exercise 33.11: all nonpositive canonical even lines have the central value. -/
lemma nonpositiveEvenLineValue_eq_zero {f : Space → ℝ} (hf : Continuous f)
    (k : ℕ) (d : ℝ) (hd : d ∈ Icc (-1) 0) (havoid : AvoidsExceptionalSets f d) :
    f (linePoint (evenLineIndex (-(k : ℤ))) d hd) =
      f (linePoint (evenLineIndex 0) d hd) := by
  -- Induct leftwards; the successor bridge joins `-k-1` to `-k`.
  induction k with
  | zero => rfl
  | succ k ih =>
      calc
        f (linePoint (evenLineIndex (-((k + 1 : ℕ) : ℤ))) d hd) =
            f (linePoint (evenLineIndex (-(k : ℤ))) d hd) := by
              have hleft : -((k + 1 : ℕ) : ℤ) = -((k : ℤ) + 1) := by
                push_cast
                ring
              have hright : -(k : ℤ) = -((k : ℤ) + 1) + 1 := by
                ring
              rw [hleft, hright]
              exact evenLinePoint_succ_eq hf (-((k : ℤ) + 1)) d hd havoid
        _ = f (linePoint (evenLineIndex 0) d hd) := ih

/-- Helper for Exercise 33.11: every continuous real-valued function identifies the two added
ends. -/
theorem continuous_leftEnd_eq_rightEnd {f : Space → ℝ} (hf : Continuous f) :
    f Space.leftEnd = f Space.rightEnd := by
  -- Choose one exceptional-set-free level and compare both endpoint limits to its central line.
  obtain ⟨d, hd, hAvoid⟩ := exists_avoidingLevel hf
  have hleft := hf.continuousAt.tendsto.comp (evenLinePoints_tendsto_leftEnd d hd)
  have hright := hf.continuousAt.tendsto.comp (evenLinePoints_tendsto_rightEnd d hd)
  have hleftConst :
      Tendsto (fun k : ℕ ↦ f (linePoint (evenLineIndex (-(k : ℤ))) d hd)) atTop
        (𝓝 (f (linePoint (evenLineIndex 0) d hd))) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    exact Eventually.of_forall fun k ↦ (nonpositiveEvenLineValue_eq_zero hf k d hd hAvoid).symm
  have hrightConst :
      Tendsto (fun k : ℕ ↦ f (linePoint (evenLineIndex (k : ℤ)) d hd)) atTop
        (𝓝 (f (linePoint (evenLineIndex 0) d hd))) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    exact Eventually.of_forall fun k ↦ (nonnegativeEvenLineValue_eq_zero hf k d hd hAvoid).symm
  calc
    f Space.leftEnd = f (linePoint (evenLineIndex 0) d hd) :=
      tendsto_nhds_unique hleft hleftConst
    _ = f Space.rightEnd := (tendsto_nhds_unique hright hrightConst).symm

/-- Helper for Exercise 33.11: distinct points admit a designated basic neighborhood
of the first that omits the second. -/
lemma exists_basicSet_separating {x y : Space} (hxy : x ≠ y) :
    ∃ s ∈ basicSets, x ∈ s ∧ y ∉ s := by
  classical
  -- Endpoints are separated by rays whose even cutoff is chosen beyond a plane coordinate.
  cases x with
  | leftEnd =>
      cases y with
      | leftEnd => exact (hxy rfl).elim
      | rightEnd =>
          refine ⟨leftRay (evenLineIndex 0), leftRay_mem_basicSets _, leftEnd_mem_leftRay _, ?_⟩
          intro hy
          rcases hy with hy | ⟨q, hq, hqx⟩
          · exact leftEnd_ne_rightEnd hy.symm
          · cases hq
      | plane q =>
          obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (-q.x)
          refine ⟨leftRay (evenLineIndex (-(N : ℤ))), leftRay_mem_basicSets _,
            leftEnd_mem_leftRay _, ?_⟩
          intro hq
          rcases hq with hq | ⟨q', hq', hlt⟩
          · cases hq
          · injection hq' with hqq
            subst q'
            dsimp only [evenLineIndex] at hlt
            push_cast at hlt
            have hNNonneg : (0 : ℝ) ≤ N := by positivity
            linarith
  | rightEnd =>
      cases y with
      | rightEnd => exact (hxy rfl).elim
      | leftEnd =>
          refine ⟨rightRay (evenLineIndex 0), rightRay_mem_basicSets _, rightEnd_mem_rightRay _, ?_⟩
          intro hy
          rcases hy with hy | ⟨q, hq, hqx⟩
          · exact leftEnd_ne_rightEnd hy
          · cases hq
      | plane q =>
          obtain ⟨N : ℕ, hN⟩ := exists_nat_gt q.x
          refine ⟨rightRay (evenLineIndex (N : ℤ)), rightRay_mem_basicSets _,
            rightEnd_mem_rightRay _, ?_⟩
          intro hq
          rcases hq with hq | ⟨q', hq', hlt⟩
          · cases hq
          · injection hq' with hqq
            subst q'
            dsimp only [evenLineIndex] at hlt
            push_cast at hlt
            have hNNonneg : (0 : ℝ) ≤ N := by positivity
            linarith
  | plane q =>
      by_cases htop : ∃ i : BridgeIndex, Space.plane q = topPoint i
      · obtain ⟨i, hi⟩ := htop
        let t : Set Space := {y}
        refine ⟨curve i \ t, curve_diff_mem_basicSets i (Set.finite_singleton y), ?_, ?_⟩
        · constructor
          · rw [hi]
            exact topPoint_mem_curve_iff.mpr rfl
          · simpa only [t, mem_singleton_iff, ne_eq] using hxy
        · intro hy
          exact hy.2 (Set.mem_singleton y)
      · have hnotTop : ∀ i : BridgeIndex, Space.plane q ≠ topPoint i := by
          intro i hi
          exact htop ⟨i, hi⟩
        obtain ⟨s, hsBasic, hqs, hsUniv⟩ :=
          basicSets_isTopologicalBasis.isOpen_iff.mp isOpen_univ (Space.plane q) (mem_univ _)
        obtain ⟨l, r, hl, hr, hsliceBasic, htopFree, hsubset⟩ :=
          exists_horizontalBasic_subset_of_nonTop_mem hnotTop hsBasic hqs
        cases y with
        | leftEnd =>
            refine ⟨horizontalSlice l r q.y, hsliceBasic, ⟨q, rfl, hl, hr, rfl⟩, ?_⟩
            simp [horizontalSlice]
        | rightEnd =>
            refine ⟨horizontalSlice l r q.y, hsliceBasic, ⟨q, rfl, hl, hr, rfl⟩, ?_⟩
            simp [horizontalSlice]
        | plane q' =>
            by_cases hy : q'.y = q.y
            · have hx : q'.x ≠ q.x := by
                intro hx
                apply hxy
                apply congrArg Space.plane
                exact PlanePoint.ext hx.symm hy.symm
              rcases lt_or_gt_of_ne hx with hxlt | hxgt
              · let l' := max l ((q'.x + q.x) / 2)
                have hl' : l' < q.x := by
                  simp only [l', max_lt_iff]
                  constructor
                  · exact hl
                  · linarith
                have htopFree' : ∀ i : BridgeIndex,
                    topPoint i ∉ horizontalSlice l' r q.y := by
                  intro i hi
                  apply htopFree i
                  rcases hi with ⟨u, hu, hul, hur, huy⟩
                  exact ⟨u, hu, (le_max_left _ _).trans_lt hul, hur, huy⟩
                refine ⟨horizontalSlice l' r q.y,
                  horizontalSlice_mem_basicSets (hl'.trans hr) htopFree',
                  ⟨q, rfl, hl', hr, rfl⟩, ?_⟩
                rintro ⟨u, hu, hul, hur, huy⟩
                injection hu with huu
                subst u
                dsimp only [l'] at hul
                have hmid : (q'.x + q.x) / 2 < q'.x :=
                  (le_max_right l ((q'.x + q.x) / 2)).trans_lt hul
                linarith
              · let r' := min r ((q.x + q'.x) / 2)
                have hr' : q.x < r' := by
                  simp only [r', lt_min_iff]
                  constructor
                  · exact hr
                  · linarith
                have htopFree' : ∀ i : BridgeIndex,
                    topPoint i ∉ horizontalSlice l r' q.y := by
                  intro i hi
                  apply htopFree i
                  rcases hi with ⟨u, hu, hul, hur, huy⟩
                  exact ⟨u, hu, hul, hur.trans_le (min_le_left _ _), huy⟩
                refine ⟨horizontalSlice l r' q.y,
                  horizontalSlice_mem_basicSets (hl.trans hr') htopFree',
                  ⟨q, rfl, hl, hr', rfl⟩, ?_⟩
                rintro ⟨u, hu, hul, hur, huy⟩
                injection hu with huu
                subst u
                dsimp only [r'] at hur
                have hmid : q'.x < (q.x + q'.x) / 2 :=
                  hur.trans_le (min_le_right r ((q.x + q'.x) / 2))
                linarith
            · refine ⟨horizontalSlice l r q.y, hsliceBasic,
                ⟨q, rfl, hl, hr, rfl⟩, ?_⟩
              rintro ⟨u, hu, hul, hur, huy⟩
              injection hu with huu
              subst u
              exact hy huy

/-- Helper for Exercise 33.11: the concrete space satisfies the `T₁` axiom. -/
lemma space_t1 : T1Space Space := by
  -- The preceding basic separator is open because every designated basic set is open.
  rw [t1Space_iff_exists_open]
  intro x y hxy
  obtain ⟨s, hsBasic, hxs, hys⟩ := exists_basicSet_separating hxy
  exact ⟨s, basicSets_isTopologicalBasis.isOpen hsBasic, hxs, hys⟩

/-- The counterexample space satisfies the `T₁` separation axiom. -/
instance instT1Space : T1Space Space := by
  -- Install the named separation theorem as the canonical instance.
  exact space_t1

/-- Helper for Exercise 33.11: every singleton in the concrete space is closed. -/
lemma space_singleton_isClosed (p : Space) : IsClosed ({p} : Set Space) := by
  -- This is the singleton formulation of the installed `T₁` instance.
  exact isClosed_singleton

/-- Helper for Exercise 33.11: the closed horizontal band between two coordinates. -/
def horizontalBand (l r d : ℝ) : Set Space :=
  {p | ∃ q : PlanePoint, p = Space.plane q ∧ q.x ∈ Icc l r ∧ q.y = d}

/-- Helper for Exercise 33.11: a fixed bridge meets a bounded horizontal band in
finitely many points. -/
lemma curve_inter_horizontalBand_finite (i : BridgeIndex) (l r d : ℝ) :
    (curve i ∩ horizontalBand l r d).Finite := by
  classical
  -- Project to the horizontal coordinate; at a fixed height there are at most four candidates.
  let coord : Space → ℝ := fun p ↦ match p with
    | Space.plane q => q.x
    | Space.leftEnd => 0
    | Space.rightEnd => 0
  let delta : ℝ := (1 - (1 : ℝ) / i.k) ^ 2 - d ^ 2
  let candidates : Set ℝ :=
    {i.n + 1 - (1 : ℝ) / i.k,
      i.n - 1 + (1 : ℝ) / i.k,
      i.n + Real.sqrt delta,
      i.n - Real.sqrt delta}
  have hcandidates : candidates.Finite := by
    simp only [candidates]
    exact Set.toFinite _
  apply Set.Finite.of_finite_image (f := coord)
  · apply hcandidates.subset
    rintro x ⟨p, hp, rfl⟩
    rcases hp.1 with ⟨q, rfl, hcurve⟩
    rcases hp.2 with ⟨q', hq', hxBand, hyBand⟩
    injection hq' with hqq
    subst q'
    simp only [coord, candidates, mem_insert_iff, mem_singleton_iff]
    rcases hcurve with hright | hleft | harc
    · exact Or.inl hright.1
    · exact Or.inr (Or.inl hleft.1)
    · have hsq : (q.x - (i.n : ℝ)) ^ 2 = delta := by
        dsimp only [delta]
        rw [hyBand] at harc
        linarith [harc.1]
      have hdelta : 0 ≤ delta := by
        rw [← hsq]
        positivity
      have hsqrt : (q.x - (i.n : ℝ)) ^ 2 = Real.sqrt delta ^ 2 := by
        rw [Real.sq_sqrt hdelta]
        exact hsq
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsqrt with hpos | hneg
      · have hx : q.x = (i.n : ℝ) + Real.sqrt delta := by
          linarith
        exact Or.inr (Or.inr (Or.inl hx))
      · have hx : q.x = (i.n : ℝ) - Real.sqrt delta := by
          linarith
        exact Or.inr (Or.inr (Or.inr hx))
  · intro p hp q hq heq
    rcases hp.2 with ⟨p', rfl, hpIcc, hpY⟩
    rcases hq.2 with ⟨q', rfl, hqIcc, hqY⟩
    apply congrArg Space.plane
    apply PlanePoint.ext
    · simpa only [coord] using heq
    · exact hpY.trans hqY.symm

/-- Helper for Exercise 33.11: every bounded horizontal band is closed. -/
lemma horizontalBand_isClosed (l r d : ℝ) : IsClosed (horizontalBand l r d) := by
  classical
  -- Prove openness of the complement by refining separately at ends, tops, and ordinary points.
  rw [← isOpen_compl_iff]
  apply basicSets_isTopologicalBasis.isOpen_iff.mpr
  intro p hp
  simp only [mem_compl_iff] at hp
  cases p with
  | leftEnd =>
      obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (-l)
      let i := evenLineIndex (-(N : ℤ))
      refine ⟨leftRay i, leftRay_mem_basicSets i, leftEnd_mem_leftRay i, ?_⟩
      intro p hpRay
      simp only [mem_compl_iff]
      intro hpBand
      rcases hpRay with hpEnd | ⟨q, rfl, hq⟩
      · rcases hpBand with ⟨q, hq, hqIcc, hy⟩
        have hpEq : p = Space.leftEnd := by
          simpa only [mem_singleton_iff] using hpEnd
        cases hpEq.symm.trans hq
      · rcases hpBand with ⟨q', hq', hqIcc, hy⟩
        injection hq' with hqq
        subst q'
        dsimp only [i, evenLineIndex] at hq
        push_cast at hq
        have hNNonneg : (0 : ℝ) ≤ N := by positivity
        linarith [hqIcc.1]
  | rightEnd =>
      obtain ⟨N : ℕ, hN⟩ := exists_nat_gt r
      let i := evenLineIndex (N : ℤ)
      refine ⟨rightRay i, rightRay_mem_basicSets i, rightEnd_mem_rightRay i, ?_⟩
      intro p hpRay
      simp only [mem_compl_iff]
      intro hpBand
      rcases hpRay with hpEnd | ⟨q, rfl, hq⟩
      · rcases hpBand with ⟨q, hq, hqIcc, hy⟩
        have hpEq : p = Space.rightEnd := by
          simpa only [mem_singleton_iff] using hpEnd
        cases hpEq.symm.trans hq
      · rcases hpBand with ⟨q', hq', hqIcc, hy⟩
        injection hq' with hqq
        subst q'
        dsimp only [i, evenLineIndex] at hq
        push_cast at hq
        have hNNonneg : (0 : ℝ) ≤ N := by positivity
        linarith [hqIcc.2]
  | plane q =>
      by_cases htop : ∃ i : BridgeIndex, Space.plane q = topPoint i
      · obtain ⟨i, hi⟩ := htop
        let t := curve i ∩ horizontalBand l r d
        have htFinite : t.Finite := curve_inter_horizontalBand_finite i l r d
        refine ⟨curve i \ t, curve_diff_mem_basicSets i htFinite, ?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · rw [hi]
            exact topPoint_mem_curve_iff.mpr rfl
          · intro hqt
            exact hp hqt.2
        · intro z hz
          simp only [mem_compl_iff]
          intro hzBand
          exact hz.2 ⟨hz.1, hzBand⟩
      · have hnotTop : ∀ i : BridgeIndex, Space.plane q ≠ topPoint i := by
          intro i hi
          exact htop ⟨i, hi⟩
        obtain ⟨s, hsBasic, hqs, hsUniv⟩ :=
          basicSets_isTopologicalBasis.isOpen_iff.mp isOpen_univ (Space.plane q) (mem_univ _)
        obtain ⟨a, b, ha, hb, hsliceBasic, htopFree, hsubset⟩ :=
          exists_horizontalBasic_subset_of_nonTop_mem hnotTop hsBasic hqs
        by_cases hy : q.y = d
        · have hxOutside : q.x < l ∨ r < q.x := by
            by_contra hx
            simp only [not_or, not_lt] at hx
            exact hp ⟨q, rfl, hx, hy⟩
          rcases hxOutside with hxLeft | hxRight
          · let b' := min b ((q.x + l) / 2)
            have hqb' : q.x < b' := by
              simp only [b', lt_min_iff]
              have hmid : q.x < (q.x + l) / 2 := by
                linarith
              exact ⟨hb, hmid⟩
            have htopFree' : ∀ i : BridgeIndex,
                topPoint i ∉ horizontalSlice a b' q.y := by
              intro i hi
              apply htopFree i
              rcases hi with ⟨u, hu, hua, hub, huy⟩
              exact ⟨u, hu, hua, hub.trans_le (min_le_left _ _), huy⟩
            refine ⟨horizontalSlice a b' q.y,
              horizontalSlice_mem_basicSets (ha.trans hqb') htopFree',
              ⟨q, rfl, ha, hqb', rfl⟩, ?_⟩
            intro z hz
            simp only [mem_compl_iff]
            intro hzBand
            rcases hz with ⟨u, rfl, hua, hub, huy⟩
            rcases hzBand with ⟨u', hu', huIcc, huY⟩
            injection hu' with huu
            subst u'
            dsimp only [b'] at hub
            have huMid : u.x < (q.x + l) / 2 := hub.trans_le (min_le_right _ _)
            linarith [huIcc.1]
          · let a' := max a ((r + q.x) / 2)
            have ha'q : a' < q.x := by
              simp only [a', max_lt_iff]
              have hmid : (r + q.x) / 2 < q.x := by
                linarith
              exact ⟨ha, hmid⟩
            have htopFree' : ∀ i : BridgeIndex,
                topPoint i ∉ horizontalSlice a' b q.y := by
              intro i hi
              apply htopFree i
              rcases hi with ⟨u, hu, hua, hub, huy⟩
              exact ⟨u, hu, (le_max_left _ _).trans_lt hua, hub, huy⟩
            refine ⟨horizontalSlice a' b q.y,
              horizontalSlice_mem_basicSets (ha'q.trans hb) htopFree',
              ⟨q, rfl, ha'q, hb, rfl⟩, ?_⟩
            intro z hz
            simp only [mem_compl_iff]
            intro hzBand
            rcases hz with ⟨u, rfl, hua, hub, huy⟩
            rcases hzBand with ⟨u', hu', huIcc, huY⟩
            injection hu' with huu
            subst u'
            dsimp only [a'] at hua
            have huMid : (r + q.x) / 2 < u.x :=
              (le_max_right a ((r + q.x) / 2)).trans_lt hua
            linarith [huIcc.2]
        · refine ⟨horizontalSlice a b q.y, hsliceBasic,
            ⟨q, rfl, ha, hb, rfl⟩, ?_⟩
          intro z hz
          simp only [mem_compl_iff]
          intro hzBand
          rcases hz with ⟨u, rfl, hua, hub, huy⟩
          rcases hzBand with ⟨u', hu', huIcc, huY⟩
          injection hu' with huu
          subst u'
          exact hy (huy.symm.trans huY)

/-- Helper for Exercise 33.11: bridge points lie between the two radius endpoints. -/
lemma curve_x_radius_bounds {i : BridgeIndex} {q : PlanePoint}
    (hq : Space.plane q ∈ curve i) :
    (i.n : ℝ) - (1 - (1 : ℝ) / i.k) ≤ q.x ∧
      q.x ≤ (i.n : ℝ) + (1 - (1 : ℝ) / i.k) := by
  -- Legs give equality at an endpoint; the arc equation bounds the squared offset.
  rcases hq with ⟨q', hq', hcurve⟩
  injection hq' with hqq
  subst q'
  rcases hcurve with hright | hleft | harc
  · rw [hright.1]
    constructor <;> linarith [bridgeRadius_pos i]
  · rw [hleft.1]
    constructor <;> linarith [bridgeRadius_pos i]
  · have hsquare : (q.x - (i.n : ℝ)) ^ 2 ≤ (1 - (1 : ℝ) / i.k) ^ 2 := by
      nlinarith [sq_nonneg q.y, harc.1]
    constructor <;> nlinarith [bridgeRadius_pos i, sq_nonneg (q.x - (i.n : ℝ))]

/-- Helper for Exercise 33.11: a point common to two bridges determines the same bridge index. -/
lemma curveIndex_eq_of_mem_of_mem {i j : BridgeIndex} {p : Space}
    (hi : p ∈ curve i) (hj : p ∈ curve j) : i = j := by
  -- Put both memberships on one plane point and first identify the odd cell centers.
  rcases hi with ⟨q, rfl, hiCurve⟩
  rcases hj with ⟨q', hq', hjCurve⟩
  injection hq' with hqq
  subst q'
  have hiMem : Space.plane q ∈ curve i := ⟨q, rfl, hiCurve⟩
  have hjMem : Space.plane q ∈ curve j := ⟨q, rfl, hjCurve⟩
  have hnji : j.n = i.n :=
    curveCenter_eq_of_mem_of_mem_cell hjMem (curve_x_bounds hiMem)
  have hnij : i.n = j.n := hnji.symm
  have hnijReal : (i.n : ℝ) = j.n := congrArg (fun z : ℤ ↦ (z : ℝ)) hnij
  by_cases hyNeg : q.y < 0
  · -- Below the axis only the vertical legs occur, and their side fixes the radius.
    rcases hiCurve with hiRight | hiLeft | hiArc
    · rcases hjCurve with hjRight | hjLeft | hjArc
      · have hradius : 1 - (1 : ℝ) / i.k = 1 - (1 : ℝ) / j.k := by
          have hcoord := hiRight.1.symm.trans hjRight.1
          rw [hnijReal] at hcoord
          linarith
        exact BridgeIndex.ext_of_n_eq_of_radius_eq hnij hradius
      · have hcoord := hiRight.1.symm.trans hjLeft.1
        rw [hnijReal] at hcoord
        nlinarith [bridgeRadius_pos i, bridgeRadius_pos j]
      · exact (not_lt_of_ge hjArc.2) hyNeg |>.elim
    · rcases hjCurve with hjRight | hjLeft | hjArc
      · have hcoord := hiLeft.1.symm.trans hjRight.1
        rw [hnijReal] at hcoord
        nlinarith [bridgeRadius_pos i, bridgeRadius_pos j]
      · have hradius : 1 - (1 : ℝ) / i.k = 1 - (1 : ℝ) / j.k := by
          have hcoord := hiLeft.1.symm.trans hjLeft.1
          rw [hnijReal] at hcoord
          linarith
        exact BridgeIndex.ext_of_n_eq_of_radius_eq hnij hradius
      · exact (not_lt_of_ge hjArc.2) hyNeg |>.elim
    · exact (not_lt_of_ge hiArc.2) hyNeg |>.elim
  · by_cases hyPos : 0 < q.y
    · -- Above the axis both memberships are on concentric semicircles.
      rcases hiCurve with hiRight | hiLeft | hiArc
      · exact (not_lt_of_ge hiRight.2.2) hyPos |>.elim
      · exact (not_lt_of_ge hiLeft.2.2) hyPos |>.elim
      · rcases hjCurve with hjRight | hjLeft | hjArc
        · exact (not_lt_of_ge hjRight.2.2) hyPos |>.elim
        · exact (not_lt_of_ge hjLeft.2.2) hyPos |>.elim
        · exact (bridgeIndex_eq_of_center_eq_of_arc_mem hnji hiArc.1 hjArc.1).symm
    · -- On the axis, every branch satisfies the corresponding circle equation.
      have hyZero : q.y = 0 := by linarith
      have hiArcEq :
          (q.x - (i.n : ℝ)) ^ 2 + q.y ^ 2 = (1 - (1 : ℝ) / i.k) ^ 2 := by
        rcases hiCurve with hiRight | hiLeft | hiArc
        · rw [hiRight.1, hyZero]
          ring
        · rw [hiLeft.1, hyZero]
          ring
        · exact hiArc.1
      have hjArcEq :
          (q.x - (j.n : ℝ)) ^ 2 + q.y ^ 2 = (1 - (1 : ℝ) / j.k) ^ 2 := by
        rcases hjCurve with hjRight | hjLeft | hjArc
        · rw [hjRight.1, hyZero]
          ring
        · rw [hjLeft.1, hyZero]
          ring
        · exact hjArc.1
      exact (bridgeIndex_eq_of_center_eq_of_arc_mem hnji hiArcEq hjArcEq).symm

/-- Helper for Exercise 33.11: distinct indexed bridges are disjoint. -/
lemma curve_disjoint_of_ne {i j : BridgeIndex} (hij : i ≠ j) :
    Disjoint (curve i) (curve j) := by
  -- Any common point would identify the two indices by the preceding geometric lemma.
  rw [Set.disjoint_left]
  intro p hi hj
  exact hij (curveIndex_eq_of_mem_of_mem hi hj)

/-- Helper for Exercise 33.11: every indexed bridge is closed. -/
lemma curve_isClosed (i : BridgeIndex) : IsClosed (curve i) := by
  classical
  -- Refine the complement at endpoints, other bridge tops, isolated bridge points, and line points.
  rw [← isOpen_compl_iff]
  apply basicSets_isTopologicalBasis.isOpen_iff.mpr
  intro p hp
  simp only [mem_compl_iff] at hp
  cases p with
  | leftEnd =>
      let j := leftLineIndex i.n i.odd
      refine ⟨leftRay j, leftRay_mem_basicSets j, leftEnd_mem_leftRay j, ?_⟩
      intro p hpRay
      simp only [mem_compl_iff]
      intro hpCurve
      rcases hpRay with hpEnd | ⟨q, rfl, hq⟩
      · rcases hpCurve with ⟨q, hq, hcurve⟩
        have hpEq : p = Space.leftEnd := by
          simpa only [mem_singleton_iff] using hpEnd
        cases hpEq.symm.trans hq
      · have hbound := (curve_x_bounds hpCurve).1
        dsimp only [j, leftLineIndex] at hq
        have hq' : q.x < (i.n : ℝ) - 1 := by
          exact_mod_cast hq
        exact (not_lt_of_ge hbound.le) hq'
  | rightEnd =>
      let j := rightLineIndex i.n i.odd
      refine ⟨rightRay j, rightRay_mem_basicSets j, rightEnd_mem_rightRay j, ?_⟩
      intro p hpRay
      simp only [mem_compl_iff]
      intro hpCurve
      rcases hpRay with hpEnd | ⟨q, rfl, hq⟩
      · rcases hpCurve with ⟨q, hq, hcurve⟩
        have hpEq : p = Space.rightEnd := by
          simpa only [mem_singleton_iff] using hpEnd
        cases hpEq.symm.trans hq
      · have hbound := (curve_x_bounds hpCurve).2
        dsimp only [j, rightLineIndex] at hq
        have hq' : (i.n : ℝ) + 1 < q.x := by
          exact_mod_cast hq
        exact (not_lt_of_ge hbound.le) hq'
  | plane q =>
      by_cases htop : ∃ j : BridgeIndex, Space.plane q = topPoint j
      · obtain ⟨j, hj⟩ := htop
        have hji : j ≠ i := by
          intro hji
          subst j
          apply hp
          rw [hj]
          exact topPoint_mem_curve_iff.mpr rfl
        refine ⟨curve j \ ∅, curve_diff_mem_basicSets j Set.finite_empty, ?_, ?_⟩
        · constructor
          · rw [hj]
            exact topPoint_mem_curve_iff.mpr rfl
          · simp
        · intro z hz
          simp only [mem_compl_iff]
          exact fun hzi ↦ Set.disjoint_left.mp (curve_disjoint_of_ne hji) hz.1 hzi
      · have hnotTop : ∀ j : BridgeIndex, Space.plane q ≠ topPoint j := by
          intro j hj
          exact htop ⟨j, hj⟩
        rcases q.mem_geometric with ⟨j, hxLine, hyLine⟩ | ⟨j, hqCurve⟩
        · have hcell : ¬ ((i.n : ℝ) - 1 < q.x ∧ q.x < (i.n : ℝ) + 1) := by
            intro hcell
            exact not_mem_bridgeCell_of_lineIndex i j ⟨hxLine ▸ hcell.1, hxLine ▸ hcell.2⟩
          have hside : q.x ≤ (i.n : ℝ) - 1 ∨ (i.n : ℝ) + 1 ≤ q.x := by
            rw [not_and_or] at hcell
            exact hcell.imp le_of_not_gt le_of_not_gt
          have htopFreeAtLine : ∀ a b : ℝ, ∀ k : BridgeIndex,
              topPoint k ∉ horizontalSlice a b q.y := by
            intro a b k hk
            rcases hk with ⟨u, hu, hua, hub, huy⟩
            injection hu with huu
            subst u
            exact (not_lt_of_ge hyLine.2) ((bridgeRadius_pos k).trans_eq huy)
          rcases hside with hleft | hright
          · let edge := (i.n : ℝ) - (1 - (1 : ℝ) / i.k)
            let a := q.x - 1
            let b := (q.x + edge) / 2
            have hqEdge : q.x < edge := by
              dsimp only [edge]
              have hk : 0 < (1 : ℝ) / i.k := by
                linarith [bridgeRadius_lt_one i]
              linarith
            have haq : a < q.x := by dsimp only [a]; linarith
            have hqb : q.x < b := by dsimp only [b]; linarith
            refine ⟨horizontalSlice a b q.y,
              horizontalSlice_mem_basicSets (haq.trans hqb) (htopFreeAtLine a b),
              ⟨q, rfl, haq, hqb, rfl⟩, ?_⟩
            intro z hz
            simp only [mem_compl_iff]
            intro hzCurve
            rcases hz with ⟨u, rfl, hua, hub, huy⟩
            have huEdge := (curve_x_radius_bounds hzCurve).1
            dsimp only [b] at hub
            linarith
          · let edge := (i.n : ℝ) + (1 - (1 : ℝ) / i.k)
            let a := (edge + q.x) / 2
            let b := q.x + 1
            have hEdgeq : edge < q.x := by
              dsimp only [edge]
              have hk : 0 < (1 : ℝ) / i.k := by
                linarith [bridgeRadius_lt_one i]
              linarith
            have haq : a < q.x := by dsimp only [a]; linarith
            have hqb : q.x < b := by dsimp only [b]; linarith
            refine ⟨horizontalSlice a b q.y,
              horizontalSlice_mem_basicSets (haq.trans hqb) (htopFreeAtLine a b),
              ⟨q, rfl, haq, hqb, rfl⟩, ?_⟩
            intro z hz
            simp only [mem_compl_iff]
            intro hzCurve
            rcases hz with ⟨u, rfl, hua, hub, huy⟩
            have huEdge := (curve_x_radius_bounds hzCurve).2
            dsimp only [a] at hua
            linarith
        · obtain ⟨a, b, ha, hb, hsingleton⟩ :=
            exists_horizontalSlice_eq_singleton_of_curve_mem
              ⟨q, rfl, hqCurve⟩ (hnotTop j)
          have htopFree : ∀ k : BridgeIndex, topPoint k ∉ horizontalSlice a b q.y := by
            intro k hk
            rw [hsingleton, mem_singleton_iff] at hk
            exact hnotTop k hk.symm
          refine ⟨horizontalSlice a b q.y,
            horizontalSlice_mem_basicSets (ha.trans hb) htopFree,
            ⟨q, rfl, ha, hb, rfl⟩, ?_⟩
          intro z hz
          simp only [mem_compl_iff]
          rw [hsingleton, mem_singleton_iff] at hz
          subst z
          exact hp

/-- Helper for Exercise 33.11: a non-top point on a bridge is an open singleton. -/
lemma isOpen_singleton_of_curve_mem_of_ne_top {i : BridgeIndex} {q : PlanePoint}
    (hq : Space.plane q ∈ curve i) (hnotTop : Space.plane q ≠ topPoint i) :
    IsOpen ({Space.plane q} : Set Space) := by
  -- The established singleton horizontal slice is top-free and hence basic.
  obtain ⟨l, r, hl, hr, hsingleton⟩ :=
    exists_horizontalSlice_eq_singleton_of_curve_mem hq hnotTop
  have htopFree : ∀ j : BridgeIndex, topPoint j ∉ horizontalSlice l r q.y := by
    intro j hj
    rw [hsingleton, mem_singleton_iff] at hj
    have hji : j = i := topPoint_mem_curve_iff.mp (hj ▸ hq)
    subst j
    exact hnotTop hj.symm
  rw [← hsingleton]
  exact basicSets_isTopologicalBasis.isOpen
    (horizontalSlice_mem_basicSets (hl.trans hr) htopFree)

/-- Helper for Exercise 33.11: deleting non-top points from a bridge leaves a closed set. -/
lemma isClosed_curveDiff_of_topPoint_not_mem {i : BridgeIndex} {t : Set Space}
    (htop : topPoint i ∉ t) : IsClosed (curve i \ t) := by
  classical
  -- The removed part of the bridge is a union of open singleton bridge points.
  have hopen : IsOpen (t ∩ curve i) := by
    have heq : t ∩ curve i = ⋃ p ∈ t ∩ curve i, {p} := by
      ext p
      simp
    rw [heq]
    apply isOpen_biUnion
    intro p hp
    rcases hp.2 with ⟨q, rfl, hqCurve⟩
    apply isOpen_singleton_of_curve_mem_of_ne_top
    · exact ⟨q, rfl, hqCurve⟩
    · intro hqTop
      apply htop
      rw [← hqTop]
      exact hp.1
  have heq : curve i \ t = curve i \ (t ∩ curve i) := by
    ext p
    simp only [Set.mem_sdiff, mem_inter_iff]
    tauto
  rw [heq]
  exact (curve_isClosed i).sdiff hopen

/-- Helper for Exercise 33.11: the closed weak ray extending left from an even cutoff. -/
def closedLeftRay (i : LineIndex) : Set Space :=
  (rightRay i)ᶜ

/-- Helper for Exercise 33.11: the closed weak ray extending right from an even cutoff. -/
def closedRightRay (i : LineIndex) : Set Space :=
  (leftRay i)ᶜ

/-- Helper for Exercise 33.11: a closed left ray is a closed neighborhood of the left end. -/
lemma closedLeftRay_mem_nhds (i : LineIndex) : closedLeftRay i ∈ 𝓝 Space.leftEnd := by
  -- The open left ray at the same cutoff lies inside the closed weak ray.
  have hopen : IsOpen (leftRay i) :=
    basicSets_isTopologicalBasis.isOpen (leftRay_mem_basicSets i)
  apply mem_of_superset (hopen.mem_nhds (leftEnd_mem_leftRay i))
  intro p hp
  simp only [closedLeftRay, mem_compl_iff]
  intro hpRight
  rcases hp with hpLeftEnd | ⟨q, hq, hqLeft⟩
  · subst p
    rcases hpRight with hpRightEnd | ⟨q, hq, hqRight⟩
    · cases hpRightEnd
    · cases hq
  · rcases hpRight with hpRightEnd | ⟨q', hq', hqRight⟩
    · subst p
      cases hpRightEnd
    · have hqq := congrArg xCoord (hq.symm.trans hq')
      have hxx : q.x = q'.x := Option.some.inj hqq
      linarith

/-- Helper for Exercise 33.11: a closed right ray is a closed neighborhood of the right end. -/
lemma closedRightRay_mem_nhds (i : LineIndex) : closedRightRay i ∈ 𝓝 Space.rightEnd := by
  -- The open right ray at the same cutoff lies inside the closed weak ray.
  have hopen : IsOpen (rightRay i) :=
    basicSets_isTopologicalBasis.isOpen (rightRay_mem_basicSets i)
  apply mem_of_superset (hopen.mem_nhds (rightEnd_mem_rightRay i))
  intro p hp
  simp only [closedRightRay, mem_compl_iff]
  intro hpLeft
  rcases hp with hpRightEnd | ⟨q, hq, hqRight⟩
  · subst p
    rcases hpLeft with hpLeftEnd | ⟨q, hq, hqLeft⟩
    · cases hpLeftEnd
    · cases hq
  · rcases hpLeft with hpLeftEnd | ⟨q', hq', hqLeft⟩
    · subst p
      cases hpLeftEnd
    · have hqq := congrArg xCoord (hq.symm.trans hq')
      have hxx : q.x = q'.x := Option.some.inj hqq
      linarith

/-- Helper for Exercise 33.11: closed weak rays on the left are closed. -/
lemma closedLeftRay_isClosed (i : LineIndex) : IsClosed (closedLeftRay i) := by
  -- Its complement is the designated open right ray.
  exact (basicSets_isTopologicalBasis.isOpen (rightRay_mem_basicSets i)).isClosed_compl

/-- Helper for Exercise 33.11: closed weak rays on the right are closed. -/
lemma closedRightRay_isClosed (i : LineIndex) : IsClosed (closedRightRay i) := by
  -- Its complement is the designated open left ray.
  exact (basicSets_isTopologicalBasis.isOpen (leftRay_mem_basicSets i)).isClosed_compl

/-- Helper for Exercise 33.11: every basic neighborhood contains a closed neighborhood. -/
lemma exists_closedNeighborhood_subset_basic {p : Space} {s : Set Space}
    (hs : s ∈ basicSets) (hp : p ∈ s) :
    ∃ t : Set Space, t ∈ 𝓝 p ∧ IsClosed t ∧ t ⊆ s := by
  classical
  -- Treat the two ends by smaller weak rays, a top by a cofinite bridge, and other points by bands.
  cases p with
  | leftEnd =>
      obtain ⟨j, rfl⟩ := eq_leftRay_of_mem_basicSets_of_leftEnd_mem hs hp
      rcases j.even with ⟨z, hz⟩
      let i := evenLineIndex (z - 1)
      refine ⟨closedLeftRay i, closedLeftRay_mem_nhds i, closedLeftRay_isClosed i, ?_⟩
      intro p hpClosed
      simp only [closedLeftRay, mem_compl_iff] at hpClosed
      cases p with
      | leftEnd => exact leftEnd_mem_leftRay j
      | rightEnd =>
          exact (hpClosed (rightEnd_mem_rightRay i)).elim
      | plane q =>
          apply Or.inr
          refine ⟨q, rfl, ?_⟩
          have hnotRight : ¬ (i.m : ℝ) < q.x := by
            intro hiq
            exact hpClosed (Or.inr ⟨q, rfl, hiq⟩)
          have hle : q.x ≤ (i.m : ℝ) := le_of_not_gt hnotRight
          have hij : (i.m : ℝ) < j.m := by
            dsimp only [i, evenLineIndex]
            rw [hz]
            push_cast
            linarith
          exact hle.trans_lt hij
  | rightEnd =>
      obtain ⟨j, rfl⟩ := eq_rightRay_of_mem_basicSets_of_rightEnd_mem hs hp
      rcases j.even with ⟨z, hz⟩
      let i := evenLineIndex (z + 1)
      refine ⟨closedRightRay i, closedRightRay_mem_nhds i, closedRightRay_isClosed i, ?_⟩
      intro p hpClosed
      simp only [closedRightRay, mem_compl_iff] at hpClosed
      cases p with
      | rightEnd => exact rightEnd_mem_rightRay j
      | leftEnd =>
          exact (hpClosed (leftEnd_mem_leftRay i)).elim
      | plane q =>
          apply Or.inr
          refine ⟨q, rfl, ?_⟩
          have hnotLeft : ¬ q.x < (i.m : ℝ) := by
            intro hqi
            exact hpClosed (Or.inr ⟨q, rfl, hqi⟩)
          have hle : (i.m : ℝ) ≤ q.x := le_of_not_gt hnotLeft
          have hji : (j.m : ℝ) < i.m := by
            dsimp only [i, evenLineIndex]
            rw [hz]
            push_cast
            linarith
          exact hji.trans_le hle
  | plane q =>
      by_cases htop : ∃ i : BridgeIndex, Space.plane q = topPoint i
      · obtain ⟨i, hi⟩ := htop
        have htopS : topPoint i ∈ s := by
          rw [← hi]
          exact hp
        obtain ⟨t, htFinite, htopCurveDiff, htS⟩ :=
          exists_curveDiff_subset_basic_of_topPoint_mem hs htopS
        have hopen : IsOpen (curve i \ t) :=
          basicSets_isTopologicalBasis.isOpen (curve_diff_mem_basicSets i htFinite)
        have hqCurveDiff : Space.plane q ∈ curve i \ t := by
          rw [hi]
          exact htopCurveDiff
        refine ⟨curve i \ t, hopen.mem_nhds hqCurveDiff, ?_, htS⟩
        exact isClosed_curveDiff_of_topPoint_not_mem htopCurveDiff.2
      · have hnotTop : ∀ i : BridgeIndex, Space.plane q ≠ topPoint i := by
          intro i hi
          exact htop ⟨i, hi⟩
        obtain ⟨l, r, hl, hr, hsliceBasic, htopFree, hsliceS⟩ :=
          exists_horizontalBasic_subset_of_nonTop_mem hnotTop hs hp
        let a := (l + q.x) / 2
        let b := (q.x + r) / 2
        have hla : l < a := by dsimp only [a]; linarith
        have haq : a < q.x := by dsimp only [a]; linarith
        have hqb : q.x < b := by dsimp only [b]; linarith
        have hbr : b < r := by dsimp only [b]; linarith
        have htopFree' : ∀ i : BridgeIndex,
            topPoint i ∉ horizontalSlice a b q.y := by
          intro i hi
          apply htopFree i
          rcases hi with ⟨u, hu, hua, hub, huy⟩
          exact ⟨u, hu, hla.trans hua, hub.trans hbr, huy⟩
        have hopen : IsOpen (horizontalSlice a b q.y) :=
          basicSets_isTopologicalBasis.isOpen
            (horizontalSlice_mem_basicSets (haq.trans hqb) htopFree')
        have hsliceBand : horizontalSlice a b q.y ⊆ horizontalBand a b q.y := by
          intro p hpSlice
          rcases hpSlice with ⟨u, rfl, hua, hub, huy⟩
          exact ⟨u, rfl, ⟨hua.le, hub.le⟩, huy⟩
        refine ⟨horizontalBand a b q.y,
          mem_of_superset (hopen.mem_nhds ⟨q, rfl, haq, hqb, rfl⟩) hsliceBand,
          horizontalBand_isClosed a b q.y, ?_⟩
        intro p hpBand
        apply hsliceS
        rcases hpBand with ⟨u, rfl, huab, huy⟩
        exact ⟨u, rfl, hla.trans_le huab.1, huab.2.trans_lt hbr, huy⟩

/-- Helper for Exercise 33.11: the concrete topology is regular. -/
lemma space_regular : RegularSpace Space := by
  -- Refine an arbitrary neighborhood first to a basic set, then use its closed refinement.
  apply Iff.mpr ((regularSpace_TFAE Space).out 0 3)
  intro p u hu
  obtain ⟨s, hs, hsu⟩ := basicSets_isTopologicalBasis.nhds_hasBasis.mem_iff.mp hu
  obtain ⟨t, htp, htClosed, hts⟩ :=
    exists_closedNeighborhood_subset_basic hs.1 hs.2
  exact ⟨t, htp, htClosed, hts.trans hsu⟩

/-- Helper for Exercise 33.11: the counterexample space is regular. -/
instance instRegularSpace : RegularSpace Space := by
  -- Install the named closed-neighborhood theorem as the canonical regularity instance.
  exact space_regular

/-- Exercise 33.11: The counterexample space is regular but not completely regular. -/
theorem not_completelyRegularSpace : ¬ CompletelyRegularSpace Space := by
  -- A complete-regularity separator would distinguish the two added ends.
  intro hcomplete
  letI : CompletelyRegularSpace Space := hcomplete
  obtain ⟨g, hg, hgleft, hgright⟩ :=
    CompletelyRegularSpace.completely_regular Space.leftEnd {Space.rightEnd}
      isClosed_singleton (by simp [leftEnd_ne_rightEnd])
  -- Coercing the separator to ℝ contradicts the universal endpoint equality.
  have hend := continuous_leftEnd_eq_rightEnd (continuous_subtype_val.comp hg)
  have hgrightEnd : g Space.rightEnd = 1 := hgright (by simp)
  simp only [Function.comp_apply, hgleft, hgrightEnd] at hend
  exact zero_ne_one hend

end RegularCounterexample
