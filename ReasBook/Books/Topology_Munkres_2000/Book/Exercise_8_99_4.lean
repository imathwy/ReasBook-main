module

public import Topology_Munkres_2000.Book.Exercise_20_2
public import Topology_Munkres_2000.Book.Exercise_8_99_4.Charts
public import Mathlib.Analysis.Real.Cardinality

public section

/- Exercise 8.99.4 (1). The real plane with the dictionary order topology is locally
1-euclidean. -/
#check (inferInstance : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (ℝ ×ₗ ℝ))

/- Exercise 8.99.4 (2). The real plane with the dictionary order topology is metrizable. -/
#check realProdLexMetrizableSpace

open Prod.Lex

/-- Helper for Exercise 8.99.4: every same-fiber lexicographic interval is open. -/
private lemma isOpen_realProdLexVerticalIoo (x a b : ℝ) :
    IsOpen (Set.Ioo (toLex (x, a)) (toLex (x, b)) : Set (ℝ ×ₗ ℝ)) := by
  -- Regard the declared dictionary-order topology through its order-topology interface.
  letI : OrderTopology (ℝ ×ₗ ℝ) := ⟨rfl⟩
  exact isOpen_Ioo

/-- Helper for Exercise 8.99.4: a same-fiber interval with ordered endpoints is nonempty. -/
private lemma realProdLexVerticalIoo_nonempty (x a b : ℝ) (hab : a < b) :
    (Set.Ioo (toLex (x, a)) (toLex (x, b)) : Set (ℝ ×ₗ ℝ)).Nonempty := by
  -- Insert an intermediate second coordinate and lift its inequalities to lexicographic ones.
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  refine ⟨toLex (x, c), ?_⟩
  exact ⟨toLex_lt_toLex.mpr (Or.inr ⟨rfl, hac⟩),
    toLex_lt_toLex.mpr (Or.inr ⟨rfl, hcb⟩)⟩

/-- Helper for Exercise 8.99.4: fixed-endpoint intervals in distinct vertical fibers are
pairwise disjoint. -/
private lemma realProdLexVerticalIoo_pairwiseDisjoint (a b : ℝ) :
    Pairwise (Function.onFun Disjoint fun x : ℝ ↦
      (Set.Ioo (toLex (x, a)) (toLex (x, b)) : Set (ℝ ×ₗ ℝ))) := by
  -- Membership in either interval recovers its indexing first coordinate.
  intro x y hxy
  dsimp only [Function.onFun]
  rw [Set.disjoint_left]
  intro z hzx hzy
  rw [realProdLex_Ioo_same_fst] at hzx hzy
  exact hxy (hzx.1.symm.trans hzy.1)

/-- Exercise 8.99.4 (3). The real plane with the dictionary order topology has no countable
basis, so it fails condition (ii) for being a 1-manifold. -/
theorem realProdLexNotSecondCountable : ¬ SecondCountableTopology (ℝ ×ₗ ℝ) := by
  -- A countable basis would make the space separable.
  intro secondCountable
  letI : SecondCountableTopology (ℝ ×ₗ ℝ) := secondCountable
  have hnegOne_lt_one : (-1 : ℝ) < 1 := by
    norm_num
  have hopen : ∀ x : ℝ,
      IsOpen (Set.Ioo (toLex (x, -1)) (toLex (x, 1)) : Set (ℝ ×ₗ ℝ)) :=
    fun x ↦ isOpen_realProdLexVerticalIoo x (-1) 1
  have hnonempty : ∀ x : ℝ,
      (Set.Ioo (toLex (x, -1)) (toLex (x, 1)) : Set (ℝ ×ₗ ℝ)).Nonempty :=
    fun x ↦ realProdLexVerticalIoo_nonempty x (-1) 1 hnegOne_lt_one
  -- The uncountably indexed disjoint open family would have to be countable in a separable space.
  have hdisjoint := realProdLexVerticalIoo_pairwiseDisjoint (-1) 1
  exact not_countable (hdisjoint.countable_of_isOpen_disjoint hopen hnonempty)
