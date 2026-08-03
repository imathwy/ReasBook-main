module

public import Topology_Munkres_2000.Book.Definition_4_5.LinearContinuum
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.CompleteLatticeIntervals
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Tactic.Linarith

public section

open Prod.Lex

universe u

/-- Helper for Example 24.2: every point of `Set.Ico (0 : ℝ) 1` has a
strictly larger point in the same interval. -/
lemma halfOpenUnitInterval_exists_gt (y : Set.Ico (0 : ℝ) 1) :
    ∃ z : Set.Ico (0 : ℝ) 1, y < z := by
  -- The midpoint with the omitted endpoint stays inside the interval.
  have hmem : (y.1 + 1) / 2 ∈ Set.Ico (0 : ℝ) 1 := by
    constructor
    · linarith [y.property.1]
    · linarith [y.property.2]
  let z : Set.Ico (0 : ℝ) 1 := ⟨(y.1 + 1) / 2, hmem⟩
  refine ⟨z, ?_⟩
  -- The omitted endpoint is strictly above `y`, so the midpoint is too.
  have hyLt : y.1 < (y.1 + 1) / 2 := by
    linarith [y.property.2]
  exact Subtype.mk_lt_mk.mpr hyLt

/-- Helper for Example 24.2: the half-open unit interval has no greatest element. -/
instance instNoMaxOrderIcoZeroOne : NoMaxOrder (Set.Ico (0 : ℝ) 1) where
  exists_gt := halfOpenUnitInterval_exists_gt

/-- Helper for Example 24.2: first coordinates at which an upper bound of `s`
occurs in the lexicographic product. -/
def lexUpperBoundFirsts {X : Type u} [LinearOrder X]
    (s : Set (X ×ₗ Set.Ico (0 : ℝ) 1)) : Set X :=
  {x | ∃ b, toLex (x, b) ∈ upperBounds s}

/-- Helper for Example 24.2: second coordinates giving an upper bound of `s`
at the fixed first coordinate `x`. -/
def lexUpperBoundSeconds {X : Type u} [LinearOrder X]
    (s : Set (X ×ₗ Set.Ico (0 : ℝ) 1)) (x : X) : Set (Set.Ico (0 : ℝ) 1) :=
  {b | toLex (x, b) ∈ upperBounds s}

/-- Helper for Example 24.2: every nonempty bounded-above subset of the
lexicographic product has a least upper bound. -/
lemma exists_isLUB_lexIco {X : Type u} [LinearOrder X] [WellFoundedLT X]
    (s : Set (X ×ₗ Set.Ico (0 : ℝ) 1)) (_hs : s.Nonempty) (hb : BddAbove s) :
    ∃ a, IsLUB s a := by
  classical
  -- Minimize the first coordinate among all upper bounds of `s`.
  obtain ⟨upper, hUpper⟩ := hb
  have hFirstNonempty : (lexUpperBoundFirsts s).Nonempty := by
    exact ⟨(ofLex upper).1, (ofLex upper).2, hUpper⟩
  let x₀ : X := wellFounded_lt.min (lexUpperBoundFirsts s) hFirstNonempty
  have hx₀Mem : x₀ ∈ lexUpperBoundFirsts s := by
    exact wellFounded_lt.min_mem (lexUpperBoundFirsts s) hFirstNonempty
  obtain ⟨witnessSecond, hWitnessSecond⟩ := hx₀Mem
  have hSecondNonempty : (lexUpperBoundSeconds s x₀).Nonempty := by
    exact ⟨witnessSecond, hWitnessSecond⟩
  -- The interval's left endpoint bounds all admissible second coordinates below.
  have hzeroMem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
    constructor
    · exact le_rfl
    · norm_num
  let zero : Set.Ico (0 : ℝ) 1 := ⟨0, hzeroMem⟩
  letI : Inhabited (Set.Ico (0 : ℝ) 1) := ⟨zero⟩
  have hSecondBoundedBelow : BddBelow (lexUpperBoundSeconds s x₀) := by
    refine ⟨zero, ?_⟩
    intro b hb
    exact b.property.1
  have hSecondGLB : IsGLB (lexUpperBoundSeconds s x₀)
      (sInf (lexUpperBoundSeconds s x₀)) :=
    isGLB_csInf (s := lexUpperBoundSeconds s x₀) hSecondNonempty
      (hb := hSecondBoundedBelow)
  let b₀ : Set.Ico (0 : ℝ) 1 := sInf (lexUpperBoundSeconds s x₀)
  refine ⟨toLex (x₀, b₀), ?_⟩
  constructor
  · -- Each point of `s` lies below the chosen first slice and its infimal bound.
    intro p hp
    have hpWitness : p ≤ toLex (x₀, witnessSecond) := hWitnessSecond hp
    have hpFirst : (ofLex p).1 ≤ x₀ := monotone_fst p (toLex (x₀, witnessSecond)) hpWitness
    rcases hpFirst.eq_or_lt with hpFirstEq | hpFirstLt
    · apply Prod.Lex.le_iff.mpr
      right
      refine ⟨hpFirstEq, ?_⟩
      apply hSecondGLB.2
      intro b hb
      have hpUpper : p ≤ toLex (x₀, b) := hb hp
      have hpNotFirstLt : ¬ (ofLex p).1 < x₀ := by
        rw [hpFirstEq]
        exact lt_irrefl x₀
      exact (Prod.Lex.le_iff.mp hpUpper).resolve_left hpNotFirstLt |>.2
    · exact Prod.Lex.le_iff.mpr (Or.inl hpFirstLt)
  · -- Minimality of the first slice, then the GLB property, gives leastness.
    intro c hc
    have hcFirstMem : (ofLex c).1 ∈ lexUpperBoundFirsts s := by
      exact ⟨(ofLex c).2, hc⟩
    have hx₀Le : x₀ ≤ (ofLex c).1 := by
      exact le_of_not_gt (wellFounded_lt.not_lt_min (lexUpperBoundFirsts s) hcFirstMem)
    rcases hx₀Le.eq_or_lt with hFirstEq | hFirstLt
    · apply Prod.Lex.le_iff.mpr
      right
      refine ⟨hFirstEq, ?_⟩
      apply hSecondGLB.1
      simpa [lexUpperBoundSeconds, hFirstEq] using hc
    · exact Prod.Lex.le_iff.mpr (Or.inl hFirstLt)
