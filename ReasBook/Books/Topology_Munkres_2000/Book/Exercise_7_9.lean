module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

public section

/-- A real sequence on the positive integers satisfies the initial values and
squared-successor-minus-squared-predecessor recurrence from Exercise 7.9(a). -/
def IsSqSuccSubSqPredSequence (h : ℕ+ → ℝ) : Prop :=
  h 1 = 1 ∧ h 2 = 2 ∧ ∀ n : ℕ+, 2 ≤ n →
    h n = h (n + 1) ^ 2 - h (n - 1) ^ 2

/-- Helper for Exercise 7.9: the state recursion whose entries are consecutive
values of a solution tail. -/
noncomputable def sqSuccState (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, b)
  | k + 1 =>
      let state := sqSuccState a b k
      (state.2, Real.sqrt (state.2 + state.1 ^ 2))

/-- Helper for Exercise 7.9: a positive second initial entry remains positive
throughout the consecutive-value state recursion. -/
lemma sqSuccState_second_pos (a b : ℝ) (hb : 0 < b) (k : ℕ) :
    0 < (sqSuccState a b k).2 := by
  -- Positivity propagates because every new radicand contains the preceding
  -- positive second component and a nonnegative square.
  induction k with
  | zero =>
      exact hb
  | succ k ih =>
      rw [sqSuccState]
      exact Real.sqrt_pos.2 (add_pos_of_pos_of_nonneg ih (sq_nonneg _))

/-- Helper for Exercise 7.9: one state step squares to the preceding second
entry plus the square of the preceding first entry. -/
lemma sqSuccState_step_sq (a b : ℝ) (hb : 0 < b) (k : ℕ) :
    (sqSuccState a b (k + 1)).2 ^ 2 =
      (sqSuccState a b k).2 + (sqSuccState a b k).1 ^ 2 := by
  -- The positivity invariant supplies the square-root side condition.
  rw [sqSuccState]
  exact Real.sq_sqrt (add_nonneg (le_of_lt (sqSuccState_second_pos a b hb k)) (sq_nonneg _))

/-- Helper for Exercise 7.9: the first entry after one state step is the
preceding second entry. -/
lemma sqSuccState_succ_fst (a b : ℝ) (k : ℕ) :
    (sqSuccState a b (k + 1)).1 = (sqSuccState a b k).2 := by
  -- This is the first projection of the defining state transition.
  rw [sqSuccState]

/-- Helper for Exercise 7.9: the candidate solution with prescribed third
value `c`, followed by its recursively generated positive tail. -/
noncomputable def sqSuccSubSqPredSequenceFromThird (c : ℝ) : ℕ+ → ℝ := fun n ↦
  match n.natPred with
  | 0 => 1
  | 1 => 2
  | k + 2 => (sqSuccState c (Real.sqrt (4 + c)) k).1

/-- Helper for Exercise 7.9: an admissible prescribed third value produces a
solution, and the resulting solution has that third value. -/
lemma sqSuccSubSqPredSequenceFromThird_spec (c : ℝ) (hc : c ^ 2 = 3)
    (hcpos : 0 < 4 + c) :
    IsSqSuccSubSqPredSequence (sqSuccSubSqPredSequenceFromThird c) ∧
      sqSuccSubSqPredSequenceFromThird c 3 = c := by
  -- The first two values and the prescribed third value are computation rules.
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · rfl
    · rfl
    · intro n hn
      -- Splitting the carrier isolates the initial recurrence and the recursive tail.
      obtain ⟨m, hm⟩ := n
      rcases m with _ | _ | _ | k
      · omega
      · norm_num at hn
      · norm_num [sqSuccSubSqPredSequenceFromThird, PNat.natPred, PNat.sub_coe,
          Nat.toPNat', sqSuccState, hc]
      · rcases k with _ | k
        · have hsqrt : Real.sqrt (4 + c) ^ 2 = 4 + c :=
            Real.sq_sqrt (le_of_lt hcpos)
          norm_num [sqSuccSubSqPredSequenceFromThird, PNat.natPred, PNat.sub_coe,
            Nat.toPNat', sqSuccState, hsqrt]
        · have hsqrtpos : 0 < Real.sqrt (4 + c) := Real.sqrt_pos.2 hcpos
          have hstep := sqSuccState_step_sq c (Real.sqrt (4 + c)) hsqrtpos k
          have hfst := sqSuccState_succ_fst c (Real.sqrt (4 + c)) k
          have hfstNext := sqSuccState_succ_fst c (Real.sqrt (4 + c)) (k + 1)
          have honeLtTwo : (1 : ℕ+) < 2 := by
            norm_num
          have honeLt : (1 : ℕ+) < ⟨k + 1 + 1 + 1 + 1, hm⟩ := by
            exact lt_of_lt_of_le honeLtTwo hn
          norm_num [sqSuccSubSqPredSequenceFromThird, PNat.natPred, PNat.sub_coe,
            Nat.toPNat', honeLt, hfst, hfstNext, hstep]
  · rfl

/-- Exercise 7.9 (1): there exists a real-valued function on the positive integers
with the given initial values and squared-successor-minus-squared-predecessor formula. -/
theorem existsRealSequenceOfSqSuccSubSqPred :
    ∃ h : ℕ+ → ℝ, IsSqSuccSubSqPredSequence h := by
  -- Choose the positive square root of `3` as the third value.
  have hthreeNonneg : (0 : ℝ) ≤ 3 := by
    norm_num
  have hfourPos : (0 : ℝ) < 4 := by
    norm_num
  have hsqrt : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt hthreeNonneg
  have hpos : 0 < 4 + Real.sqrt 3 :=
    add_pos_of_pos_of_nonneg hfourPos (Real.sqrt_nonneg 3)
  exact ⟨sqSuccSubSqPredSequenceFromThird (Real.sqrt 3),
    (sqSuccSubSqPredSequenceFromThird_spec (Real.sqrt 3) hsqrt hpos).1⟩

/-- Exercise 7.9 (2): the initial values and
squared-successor-minus-squared-predecessor formula do not determine the function uniquely. -/
theorem realSequenceSqSuccSubSqPred_not_unique :
    ¬ ∃! h : ℕ+ → ℝ, IsSqSuccSubSqPredSequence h := by
  -- The two signs of `√3` give different admissible third values and hence
  -- different recursively generated solution tails.
  have hthreeNonneg : (0 : ℝ) ≤ 3 := by
    norm_num
  have hthreePos : (0 : ℝ) < 3 := by
    norm_num
  have hfourPos : (0 : ℝ) < 4 := by
    norm_num
  have hsqrt : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt hthreeNonneg
  have hsqrtpos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 hthreePos
  have hplus : 0 < 4 + Real.sqrt 3 :=
    add_pos_of_pos_of_nonneg hfourPos (Real.sqrt_nonneg 3)
  have hminus : 0 < 4 + -Real.sqrt 3 := by
    nlinarith
  have hnegSq : (-Real.sqrt 3) ^ 2 = (3 : ℝ) := by
    nlinarith
  intro hunique
  obtain ⟨h, hh, hunique⟩ := hunique
  have hplusEq := hunique (sqSuccSubSqPredSequenceFromThird (Real.sqrt 3))
    (sqSuccSubSqPredSequenceFromThird_spec (Real.sqrt 3) hsqrt hplus).1
  have hminusEq := hunique (sqSuccSubSqPredSequenceFromThird (-Real.sqrt 3))
    (sqSuccSubSqPredSequenceFromThird_spec (-Real.sqrt 3) hnegSq hminus).1
  have hthirdPlus := (sqSuccSubSqPredSequenceFromThird_spec
    (Real.sqrt 3) hsqrt hplus).2
  have hthirdMinus := (sqSuccSubSqPredSequenceFromThird_spec
    (-Real.sqrt 3) hnegSq hminus).2
  have heq : Real.sqrt 3 = -Real.sqrt 3 := by
    calc
      Real.sqrt 3 = sqSuccSubSqPredSequenceFromThird (Real.sqrt 3) 3 := hthirdPlus.symm
      _ = h 3 := congrFun hplusEq 3
      _ = sqSuccSubSqPredSequenceFromThird (-Real.sqrt 3) 3 := (congrFun hminusEq 3).symm
      _ = -Real.sqrt 3 := hthirdMinus
  nlinarith

/-- Exercise 7.9 (3): no real-valued function on the positive integers has the
given initial values and squared-successor-plus-squared-predecessor formula. -/
theorem not_existsRealSequenceOfSqSuccAddSqPred :
    ¬ ∃ h : ℕ+ → ℝ,
      h 1 = 1 ∧ h 2 = 2 ∧ ∀ n : ℕ+, 2 ≤ n →
        h n = h (n + 1) ^ 2 + h (n - 1) ^ 2 := by
  -- The equations at indices `2` and `3` force a square to be negative.
  rintro ⟨h, h1, h2, hrec⟩
  have htwoLeTwo : (2 : ℕ+) ≤ 2 := le_rfl
  have htwoLeThree : (2 : ℕ+) ≤ 3 := by
    norm_num
  have hrec2 := hrec 2 htwoLeTwo
  have hrec3 := hrec 3 htwoLeThree
  have htwoSucc : (2 : ℕ+) + 1 = 3 := rfl
  have htwoPred : (2 : ℕ+) - 1 = 1 := rfl
  have hthreeSucc : (3 : ℕ+) + 1 = 4 := rfl
  have hthreePred : (3 : ℕ+) - 1 = 2 := rfl
  rw [htwoSucc, htwoPred, h1, h2] at hrec2
  rw [hthreeSucc, hthreePred, h2] at hrec3
  nlinarith [sq_nonneg (h 3), sq_nonneg (h 4)]
