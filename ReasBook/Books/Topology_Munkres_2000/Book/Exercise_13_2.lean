module

public import Mathlib.Order.Comparable
public import Topology_Munkres_2000.Book.Example_12_1.ThreePointTopology

public section

namespace ThreePointTopology

/-- `i.IsFinerThan j` is the refinement relation read from Figure 12.1. -/
def Displayed.IsFinerThan : Displayed → Displayed → Prop
  | .discrete, _ => True
  | _, .indiscrete => True
  | .aAndAB, .abOnly => True
  | .bAndABAndBC, .bOnly => True
  | .bAndABAndBC, .abOnly => True
  | .bAndCAndAB, .bOnly => True
  | .bAndCAndAB, .bAndABAndBC => True
  | .bAndCAndAB, .abOnly => True
  | .aAndB, .aAndAB => True
  | .aAndB, .bOnly => True
  | .aAndB, .abOnly => True
  | i, j => i = j

/-- Helper for Exercise 13.2: a proposition holds at every point of `ThreePoint`
exactly when it holds at `a`, `b`, and `c`. -/
lemma forallThreePoint_iff (p : ThreePoint → Prop) :
    (∀ x, p x) ↔ p .a ∧ p .b ∧ p .c := by
  -- Evaluate a universal proposition at the three constructors, and conversely eliminate them.
  constructor
  · intro h
    exact ⟨h .a, h .b, h .c⟩
  · rintro ⟨ha, hb, hc⟩ x
    cases x
    · exact ha
    · exact hb
    · exact hc

/-- Helper for Exercise 13.2: every subset of `ThreePoint` is one of its eight
canonical subsets. -/
lemma set_eq_oneOfEight (s : Set ThreePoint) :
    s = ∅ ∨ s = {.a} ∨ s = {.b} ∨ s = {.c} ∨ s = {.a, .b} ∨
      s = {.a, .c} ∨ s = {.b, .c} ∨ s = Set.univ := by
  -- Split on membership of the three points, then identify the resulting subset extensionally.
  classical
  by_cases ha : .a ∈ s
  · by_cases hb : .b ∈ s
    · by_cases hc : .c ∈ s
      · right
        right
        right
        right
        right
        right
        right
        ext x
        cases x <;> simp_all
      · right
        right
        right
        right
        left
        ext x
        cases x <;> simp_all
    · by_cases hc : .c ∈ s
      · right
        right
        right
        right
        right
        left
        ext x
        cases x <;> simp_all
      · right
        left
        ext x
        cases x <;> simp_all
  · by_cases hb : .b ∈ s
    · by_cases hc : .c ∈ s
      · right
        right
        right
        right
        right
        right
        left
        ext x
        cases x <;> simp_all
      · right
        right
        left
        ext x
        cases x <;> simp_all
    · by_cases hc : .c ∈ s
      · right
        right
        right
        left
        ext x
        cases x <;> simp_all
      · left
        ext x
        cases x <;> simp_all

/-- Helper for Exercise 13.2: inclusion between displayed open-set families is
determined by the eight canonical subsets of `ThreePoint`. -/
lemma openSets_subset_iff_canonical (i j : Displayed) :
    openSets j ⊆ openSets i ↔
      (∅ ∈ openSets j → ∅ ∈ openSets i) ∧
      ({.a} ∈ openSets j → {.a} ∈ openSets i) ∧
      ({.b} ∈ openSets j → {.b} ∈ openSets i) ∧
      ({.c} ∈ openSets j → {.c} ∈ openSets i) ∧
      ({.a, .b} ∈ openSets j → {.a, .b} ∈ openSets i) ∧
      ({.a, .c} ∈ openSets j → {.a, .c} ∈ openSets i) ∧
      ({.b, .c} ∈ openSets j → {.b, .c} ∈ openSets i) ∧
      (Set.univ ∈ openSets j → Set.univ ∈ openSets i) := by
  -- Specialize family inclusion to the eight representatives, or classify an arbitrary set.
  constructor
  · intro h
    exact ⟨h (a := ∅), h (a := {.a}), h (a := {.b}), h (a := {.c}),
      h (a := {.a, .b}), h (a := {.a, .c}), h (a := {.b, .c}), h (a := Set.univ)⟩
  · rintro ⟨hempty, ha, hb, hc, hab, hac, hbc, huniv⟩ s hs
    rcases set_eq_oneOfEight s with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hempty hs
    · exact ha hs
    · exact hb hs
    · exact hc hs
    · exact hab hs
    · exact hac hs
    · exact hbc hs
    · exact huniv hs

/-- Helper for Exercise 13.2: inclusion of displayed open-set families is exactly
the refinement relation encoded by Figure 12.1. -/
lemma openSets_subset_iff_isFinerThan (i j : Displayed) :
    openSets j ⊆ openSets i ↔ i.IsFinerThan j := by
  -- Reduce arbitrary family inclusion to the eight possible subsets of `ThreePoint`.
  rw [openSets_subset_iff_canonical]
  -- Compute the resulting finite truth table after exposing every displayed branch.
  cases i <;> cases j <;>
    simp [mem_openSets_iff, Displayed.IsFinerThan, Set.ext_iff, forallThreePoint_iff]

/-- Exercise 13.2: the complete comparison of the nine topologies in Figure 12.1.
In Lean's reversed order on topologies, `topology i ≤ topology j` says that the
topology represented by `i` is finer than the topology represented by `j`. -/
theorem topology_le_iff (i j : Displayed) :
    topology i ≤ topology j ↔ i.IsFinerThan j := by
  -- Translate reversed topology order into inclusion of the explicit open-set families.
  rw [TopologicalSpace.le_def]
  change (∀ s, (topology j).IsOpen s → (topology i).IsOpen s) ↔ _
  simp_rw [isOpen_iff]
  change openSets j ⊆ openSets i ↔ _
  -- Apply the separately verified finite comparison table.
  exact openSets_subset_iff_isFinerThan i j

/-- Two displayed topologies are comparable exactly when either one is finer than the other. -/
theorem comparable_iff (i j : Displayed) :
    Relation.SymmGen (· ≤ ·) (topology i) (topology j) ↔
      i.IsFinerThan j ∨ j.IsFinerThan i := by
  change topology i ≤ topology j ∨ topology j ≤ topology i ↔ _
  rw [topology_le_iff, topology_le_iff]

end ThreePointTopology
