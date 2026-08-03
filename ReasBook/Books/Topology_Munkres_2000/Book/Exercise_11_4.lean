module

public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Real.Basic

public section

namespace IncreasingPlaneOrder

/-- The relation used in Exercise 11.4: the strict relation on `ℝ × ℝ` whose first coordinate is
strictly increasing and whose second coordinate is nondecreasing. -/
def lt (p q : ℝ × ℝ) : Prop :=
  p.1 < q.1 ∧ p.2 ≤ q.2

scoped[IncreasingPlaneOrder] infix:50 " ≺ " => IncreasingPlaneOrder.lt

open scoped IncreasingPlaneOrder

/-- Coordinate characterization of the strict increasing-plane order. -/
@[simp] theorem lt_iff (p q : ℝ × ℝ) :
    p ≺ q ↔ p.1 < q.1 ∧ p.2 ≤ q.2 := Iff.rfl

/-- The strict increasing-plane relation is a strict partial order. -/
instance instIsStrictOrder : IsStrictOrder (ℝ × ℝ) (· ≺ ·) where
  irrefl p := by
    -- Irreflexivity is already forced by the strict first-coordinate inequality.
    simp [lt]
  trans p q r hpq hqr := by
    -- Transitivity combines strict increase in the first coordinate
    -- with weak increase in the second.
    exact ⟨lt_trans hpq.1 hqr.1, le_trans hpq.2 hqr.2⟩

/-- The graph of a real-valued function on a subset of `ℝ`. -/
def graph (D : Set ℝ) (f : D → ℝ) : Set (ℝ × ℝ) :=
  Set.range fun d ↦ (d.1, f d)

/-- Membership in the graph of a function on a subset of `ℝ`. -/
@[simp] theorem mem_graph {D : Set ℝ} {f : D → ℝ} {x y : ℝ} :
    (x, y) ∈ graph D f ↔ ∃ d : D, d.1 = x ∧ f d = y := by
  simp [graph, Prod.ext_iff]

/-- Helper for Exercise 11.4: a graph is a chain exactly when its function is monotone. -/
lemma isChain_graph_iff_monotone {D : Set ℝ} {f : D → ℝ} :
    IsChain (· ≺ ·) (graph D f) ↔ Monotone f := by
  constructor
  · intro hchain d e hde
    -- Distinct domain coordinates are oriented by the chain relation on their graph points.
    rcases hde.eq_or_lt with rfl | hlt
    · exact le_rfl
    · have hne : (d.1, f d) ≠ (e.1, f e) := by
        intro heq
        exact hlt.ne (Subtype.ext (congrArg Prod.fst heq))
      rcases hchain ⟨d, rfl⟩ ⟨e, rfl⟩ hne with hforward | hbackward
      · exact hforward.2
      · exact False.elim (hlt.not_gt hbackward.1)
  · intro hmon p hp q hq hpq
    rcases hp with ⟨d, rfl⟩
    rcases hq with ⟨e, rfl⟩
    -- Unequal graph points have unequal first coordinates, so linearity chooses an orientation.
    have hde : d.1 ≠ e.1 := by
      intro hfirst
      apply hpq
      have hsubtype : d = e := Subtype.ext hfirst
      exact congrArg (fun z : D ↦ (z.1, f z)) hsubtype
    rcases lt_or_gt_of_ne hde with hlt | hgt
    · exact Or.inl ⟨hlt, hmon (le_of_lt hlt)⟩
    · exact Or.inr ⟨hgt, hmon (le_of_lt hgt)⟩

/-- Helper for Exercise 11.4: maximality of a monotone graph is characterized by
order-connectedness of its domain and divergence at every finite endpoint. -/
lemma isMaxChain_graph_iff {D : Set ℝ} {f : D → ℝ} :
    IsMaxChain (· ≺ ·) (graph D f) ↔
      D.OrdConnected ∧ Monotone f ∧
        (BddBelow D → ¬BddBelow (Set.range f)) ∧
        (BddAbove D → ¬BddAbove (Set.range f)) := by
  constructor
  · intro hmax
    have hmon : Monotone f := isChain_graph_iff_monotone.mp hmax.isChain
    have hconnected : D.OrdConnected := by
      constructor
      intro a ha b hb x hx
      by_contra hxD
      have hax : a < x := lt_of_le_of_ne hx.1 (fun h ↦ hxD (h ▸ ha))
      have hxb : x < b := lt_of_le_of_ne hx.2 (fun h ↦ hxD (h.symm ▸ hb))
      let leftValues : Set ℝ := {y | ∃ d : D, d.1 < x ∧ f d = y}
      have hleftNonempty : leftValues.Nonempty := by
        refine ⟨f ⟨a, ha⟩, ?_⟩
        exact ⟨⟨a, ha⟩, hax, rfl⟩
      have hleftBdd : BddAbove leftValues := by
        refine ⟨f ⟨b, hb⟩, ?_⟩
        intro y hy
        rcases hy with ⟨d, hd, rfl⟩
        have hdb : d.1 < b := lt_trans hd hxb
        exact hmon (show d ≤ ⟨b, hb⟩ from hdb.le)
      let inserted : ℝ × ℝ := (x, sSup leftValues)
      have hinsertComparable : ∀ q ∈ graph D f, inserted ≠ q → inserted ≺ q ∨ q ≺ inserted := by
        intro q hq _
        rcases hq with ⟨d, rfl⟩
        have hne : x ≠ d.1 := fun h ↦ hxD (h ▸ d.property)
        rcases lt_or_gt_of_ne hne with hxd | hdx
        · left
          refine ⟨hxd, ?_⟩
          apply csSup_le hleftNonempty
          intro y hy
          rcases hy with ⟨e, he, rfl⟩
          have hed : e.1 < d.1 := lt_trans he hxd
          exact hmon hed.le
        · right
          refine ⟨hdx, ?_⟩
          exact le_csSup hleftBdd ⟨d, hdx, rfl⟩
      have hinsertChain : IsChain (· ≺ ·) (insert inserted (graph D f)) :=
        hmax.isChain.insert hinsertComparable
      have heq := hmax.2 hinsertChain (Set.subset_insert inserted (graph D f))
      have hinsertMem : inserted ∈ graph D f := by
        rw [heq]
        exact Set.mem_insert inserted (graph D f)
      rcases hinsertMem with ⟨d, hd⟩
      have hcoord : d.1 = x := congrArg Prod.fst hd
      exact hxD (hcoord ▸ d.property)
    refine ⟨hconnected, hmon, ?_, ?_⟩
    · intro hDbdd hfbdd
      rcases hDbdd with ⟨a, ha⟩
      rcases hfbdd with ⟨y, hy⟩
      let inserted : ℝ × ℝ := (a - 1, y)
      have hinsertComparable : ∀ q ∈ graph D f, inserted ≠ q → inserted ≺ q ∨ q ≺ inserted := by
        intro q hq _
        rcases hq with ⟨d, rfl⟩
        left
        refine ⟨lt_of_lt_of_le (sub_lt_self a zero_lt_one) (ha d.property), ?_⟩
        exact hy ⟨d, rfl⟩
      have hinsertChain : IsChain (· ≺ ·) (insert inserted (graph D f)) :=
        hmax.isChain.insert hinsertComparable
      have heq := hmax.2 hinsertChain (Set.subset_insert inserted (graph D f))
      have hinsertMem : inserted ∈ graph D f := by
        rw [heq]
        exact Set.mem_insert inserted (graph D f)
      rcases hinsertMem with ⟨d, hd⟩
      have hcoord : d.1 = a - 1 := congrArg Prod.fst hd
      exact (not_lt_of_ge (ha d.property)) (hcoord ▸ sub_lt_self a zero_lt_one)
    · intro hDbdd hfbdd
      rcases hDbdd with ⟨a, ha⟩
      rcases hfbdd with ⟨y, hy⟩
      let inserted : ℝ × ℝ := (a + 1, y)
      have hinsertComparable : ∀ q ∈ graph D f, inserted ≠ q → inserted ≺ q ∨ q ≺ inserted := by
        intro q hq _
        rcases hq with ⟨d, rfl⟩
        right
        refine ⟨lt_of_le_of_lt (ha d.property) (lt_add_one a), ?_⟩
        exact hy ⟨d, rfl⟩
      have hinsertChain : IsChain (· ≺ ·) (insert inserted (graph D f)) :=
        hmax.isChain.insert hinsertComparable
      have heq := hmax.2 hinsertChain (Set.subset_insert inserted (graph D f))
      have hinsertMem : inserted ∈ graph D f := by
        rw [heq]
        exact Set.mem_insert inserted (graph D f)
      rcases hinsertMem with ⟨d, hd⟩
      have hcoord : d.1 = a + 1 := congrArg Prod.fst hd
      exact (not_lt_of_ge (ha d.property)) (hcoord.symm ▸ lt_add_one a)
  · rintro ⟨hconnected, hmon, hlower, hupper⟩
    constructor
    · exact isChain_graph_iff_monotone.mpr hmon
    · intro t ht hsubset
      apply Set.Subset.antisymm hsubset
      intro p hp
      by_cases hxD : p.1 ∈ D
      · let d : D := ⟨p.1, hxD⟩
        have hgraph : (d.1, f d) ∈ t := hsubset ⟨d, rfl⟩
        by_cases heq : p = (d.1, f d)
        · exact heq ▸ ⟨d, rfl⟩
        · rcases ht hp hgraph heq with hforward | hbackward
          · exact (lt_irrefl p.1 hforward.1).elim
          · exact (lt_irrefl p.1 hbackward.1).elim
      · have hDnonempty : D.Nonempty := by
          by_contra hDempty
          have hD : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hDempty
          have hDbdd : BddBelow D := by
            rw [hD]
            exact bddBelow_empty
          have hfbdd : BddBelow (Set.range f) := by
            refine ⟨0, ?_⟩
            intro y hy
            rcases hy with ⟨d, rfl⟩
            exact False.elim (by simpa [hD] using d.property)
          exact hlower hDbdd hfbdd
        rcases hDnonempty with ⟨x₀, hx₀⟩
        let d₀ : D := ⟨x₀, hx₀⟩
        have hne : p.1 ≠ d₀.1 := by
          intro h
          exact hxD (by simp [h, d₀.property])
        rcases lt_or_gt_of_ne hne with hxd₀ | hd₀x
        · have hallRight : ∀ d : D, p.1 < d.1 := by
            intro d
            rcases lt_trichotomy d.1 p.1 with hdx | hdx | hxd
            · have hbetween : p.1 ∈ Set.Icc d.1 d₀.1 := ⟨le_of_lt hdx, le_of_lt hxd₀⟩
              exact False.elim (hxD (hconnected.out' d.property d₀.property hbetween))
            · exact False.elim (hxD (hdx ▸ d.property))
            · exact hxd
          have hDbdd : BddBelow D := ⟨p.1, fun d hd ↦ le_of_lt (hallRight ⟨d, hd⟩)⟩
          have hfbdd : BddBelow (Set.range f) := by
            refine ⟨p.2, ?_⟩
            intro y hy
            rcases hy with ⟨d, rfl⟩
            have hgraph : (d.1, f d) ∈ t := hsubset ⟨d, rfl⟩
            have hne : p ≠ (d.1, f d) := by
              intro heq
              exact (hallRight d).ne (congrArg Prod.fst heq)
            rcases ht hp hgraph hne with hforward | hbackward
            · exact hforward.2
            · exact False.elim ((hallRight d).not_gt hbackward.1)
          exact False.elim (hlower hDbdd hfbdd)
        · have hallLeft : ∀ d : D, d.1 < p.1 := by
            intro d
            rcases lt_trichotomy d.1 p.1 with hdx | hdx | hxd
            · exact hdx
            · exact False.elim (hxD (hdx ▸ d.property))
            · have hbetween : p.1 ∈ Set.Icc d₀.1 d.1 := ⟨le_of_lt hd₀x, le_of_lt hxd⟩
              exact False.elim (hxD (hconnected.out' d₀.property d.property hbetween))
          have hDbdd : BddAbove D := ⟨p.1, fun d hd ↦ le_of_lt (hallLeft ⟨d, hd⟩)⟩
          have hfbdd : BddAbove (Set.range f) := by
            refine ⟨p.2, ?_⟩
            intro y hy
            rcases hy with ⟨d, rfl⟩
            have hgraph : (d.1, f d) ∈ t := hsubset ⟨d, rfl⟩
            have hne : p ≠ (d.1, f d) := by
              intro heq
              exact (hallLeft d).ne' (congrArg Prod.fst heq)
            rcases ht hp hgraph hne with hforward | hbackward
            · exact False.elim ((hallLeft d).not_gt hforward.1)
            · exact hbackward.2
          exact False.elim (hupper hDbdd hfbdd)

/-- Helper for Exercise 11.4: every chain is the graph of a monotone function on its
set of first coordinates. -/
lemma isChain_exists_monotoneGraph {s : Set (ℝ × ℝ)} (hchain : IsChain (· ≺ ·) s) :
    ∃ D : Set ℝ, ∃ f : D → ℝ, Monotone f ∧ s = graph D f := by
  classical
  let D : Set ℝ := Prod.fst '' s
  have hrepresentative : ∀ d : D, ∃ p ∈ s, p.1 = d.1 := by
    intro d
    rcases d.property with ⟨p, hp, hpd⟩
    exact ⟨p, hp, hpd⟩
  let chosen : D → ℝ × ℝ := fun d ↦ Classical.choose (hrepresentative d)
  let f : D → ℝ := fun d ↦ (chosen d).2
  have hchosenMem (d : D) : chosen d ∈ s := (Classical.choose_spec (hrepresentative d)).1
  have hchosenFst (d : D) : (chosen d).1 = d.1 := (Classical.choose_spec (hrepresentative d)).2
  have hsgraph : s = graph D f := by
    ext p
    constructor
    · intro hp
      let d : D := ⟨p.1, ⟨p, hp, rfl⟩⟩
      have heq : p = chosen d := by
        by_contra hne
        rcases hchain hp (hchosenMem d) hne with hforward | hbackward
        · have hbad : p.1 < p.1 := lt_of_lt_of_eq hforward.1 (hchosenFst d)
          exact (lt_irrefl p.1 hbad).elim
        · have hbad : p.1 < p.1 := lt_of_eq_of_lt (hchosenFst d).symm hbackward.1
          exact (lt_irrefl p.1 hbad).elim
      have hpair : (d.1, f d) = chosen d := by
        ext
        · exact (hchosenFst d).symm
        · rfl
      exact ⟨d, hpair.trans heq.symm⟩
    · intro hp
      rcases hp with ⟨d, rfl⟩
      have hpair : (d.1, f d) = chosen d := by
        ext
        · exact (hchosenFst d).symm
        · rfl
      simpa only [hpair] using hchosenMem d
  refine ⟨D, f, ?_, hsgraph⟩
  rw [hsgraph] at hchain
  exact isChain_graph_iff_monotone.mp hchain

/-- Helper for Exercise 11.4: every monotone graph with domain `ℝ` is a maximal chain. -/
lemma univGraph_isMaxChain {f : ℝ → ℝ} (hmon : Monotone f) :
    IsMaxChain (· ≺ ·) (Set.range fun x : ℝ ↦ (x, f x)) := by
  constructor
  · -- Monotonicity makes every pair of distinct graph points comparable.
    intro p hp q hq hpq
    rcases hp with ⟨x, rfl⟩
    rcases hq with ⟨y, rfl⟩
    have hxy : x ≠ y := by
      intro h
      exact hpq (congrArg (fun z ↦ (z, f z)) h)
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · exact Or.inl ⟨hlt, hmon hlt.le⟩
    · exact Or.inr ⟨hgt, hmon hgt.le⟩
  · intro t ht hsubset
    apply Set.Subset.antisymm hsubset
    intro p hp
    -- Comparing with the graph point at the same first coordinate forces equality.
    have hgraph : (p.1, f p.1) ∈ t := hsubset ⟨p.1, rfl⟩
    by_contra hnot
    have hne : p ≠ (p.1, f p.1) := by
      intro heq
      exact hnot ⟨p.1, heq.symm⟩
    rcases ht hp hgraph hne with hforward | hbackward
    · exact (lt_irrefl p.1 hforward.1).elim
    · exact (lt_irrefl p.1 hbackward.1).elim

/-- The first example in Exercise 11.4: the curve `y = x ^ 3` is a maximal simply ordered subset
of `ℝ × ℝ` under the strict increasing-plane order. -/
theorem cubeGraph_isMaxChain :
    IsMaxChain (· ≺ ·) (Set.range fun x : ℝ ↦ (x, x ^ 3)) := by
  -- An odd power is strictly monotone, hence monotone.
  exact univGraph_isMaxChain (show Odd 3 by decide).strictMono_pow.monotone

/-- The second example in Exercise 11.4: the curve `y = 2` is a maximal simply ordered subset of
`ℝ × ℝ` under the strict increasing-plane order. -/
theorem horizontalLineTwo_isMaxChain :
    IsMaxChain (· ≺ ·) (Set.range fun x : ℝ ↦ (x, 2)) := by
  -- A constant function is monotone, so its full graph is maximal.
  exact univGraph_isMaxChain monotone_const

/-- The counterexample in Exercise 11.4: the curve `y = x ^ 2` is not a maximal simply ordered
subset of `ℝ × ℝ` under the strict increasing-plane order. -/
theorem squareGraph_not_isMaxChain :
    ¬IsMaxChain (· ≺ ·) (Set.range fun x : ℝ ↦ (x, x ^ 2)) := by
  intro hmax
  -- The graph points above `-1` and `0` are incomparable.
  have hpair := hmax.isChain (show ((-1 : ℝ), (-1 : ℝ) ^ 2) ∈ Set.range
      (fun x : ℝ ↦ (x, x ^ 2)) by exact ⟨-1, rfl⟩)
    (show ((0 : ℝ), (0 : ℝ) ^ 2) ∈ Set.range (fun x : ℝ ↦ (x, x ^ 2)) by
      exact ⟨0, rfl⟩)
    (by norm_num)
  rcases hpair with hforward | hbackward
  · have hbad : (1 : ℝ) ≤ 0 := by
      simpa [lt] using hforward.2
    exact (not_le_of_gt zero_lt_one) hbad
  · have hbad : (1 : ℝ) < 0 := by
      simpa [lt] using hbackward.1
    exact (not_lt_of_ge zero_le_one) hbad

/-- Exercise 11.4: The maximal simply ordered subsets are exactly graphs of
monotone real-valued functions on intervals, with values unbounded below or above
whenever the domain has a strict lower or upper bound, respectively. -/
theorem isMaxChain_iff (s : Set (ℝ × ℝ)) :
    IsMaxChain (· ≺ ·) s ↔ ∃ D : Set ℝ, ∃ f : D → ℝ,
      D.OrdConnected ∧ Monotone f ∧ s = graph D f ∧
        (BddBelow D → ¬BddBelow (Set.range f)) ∧
        (BddAbove D → ¬BddAbove (Set.range f)) := by
  constructor
  · intro hmax
    -- Represent the maximal chain as a monotone graph, then read off the graph criteria.
    rcases isChain_exists_monotoneGraph hmax.isChain with ⟨D, f, hmon, hs⟩
    have hgraphMax : IsMaxChain (· ≺ ·) (graph D f) := hs ▸ hmax
    rcases isMaxChain_graph_iff.mp hgraphMax with ⟨hconnected, _, hlower, hupper⟩
    exact ⟨D, f, hconnected, hmon, hs, hlower, hupper⟩
  · rintro ⟨D, f, hconnected, hmon, hs, hlower, hupper⟩
    -- The endpoint and interval conditions make the graph maximal, and `s` is that graph.
    rw [hs]
    exact isMaxChain_graph_iff.mpr ⟨hconnected, hmon, hlower, hupper⟩

end IncreasingPlaneOrder
