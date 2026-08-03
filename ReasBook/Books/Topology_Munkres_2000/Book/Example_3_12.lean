module

public import Topology_Munkres_2000.Book.Example_3_11
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Order.Cover
public import Mathlib.Tactic.PNatToNat
@[expose] public section

/-- The real-valued formula `(n, t) ↦ n + t - 1` from Example 3.12. -/
def pnatUnitLexValue (x : ℕ+ ×ₗ Set.Ico (0 : ℝ) 1) : ℝ :=
  let p := ofLex x
  (p.1 : ℝ) + (p.2 : ℝ) - 1

/-- The formula `pnatUnitLexValue` is nonnegative. -/
theorem pnatUnitLexValue_nonneg (x : ℕ+ ×ₗ Set.Ico (0 : ℝ) 1) :
    0 ≤ pnatUnitLexValue x := by
  rcases x with ⟨n, t⟩
  change 0 ≤ (n : ℝ) + (t : ℝ) - 1
  apply sub_nonneg.mpr
  exact le_trans (Nat.one_le_cast.mpr n.prop) (le_add_of_nonneg_right t.prop.1)

/-- The staircase correspondence from the dictionary-ordered product
`ℕ+ ×ₗ Set.Ico (0 : ℝ) 1` to the nonnegative real numbers. -/
def pnatUnitLexToNonnegative (x : ℕ+ ×ₗ Set.Ico (0 : ℝ) 1) : Set.Ici (0 : ℝ) :=
  ⟨pnatUnitLexValue x, pnatUnitLexValue_nonneg x⟩

/-- Helper for Example 3.12: the scalar staircase formula is strictly increasing. -/
lemma pnatUnitLexValue_strictMono : StrictMono pnatUnitLexValue := by
  -- Split lexicographic comparison into the integer-step and within-step cases.
  rintro ⟨n₁, t₁⟩ ⟨n₂, t₂⟩ h
  rcases Prod.Lex.lt_iff.mp h with hn | ⟨hn, ht⟩
  · have hgap : (n₁ : ℝ) + 1 ≤ (n₂ : ℝ) := by
      change n₁ < n₂ at hn
      exact_mod_cast PNat.add_one_le_iff.mpr hn
    have hbeforeStep : (n₁ : ℝ) + (t₁ : ℝ) < (n₁ : ℝ) + 1 := by
      linarith [t₁.property.2]
    have hafterStep : (n₁ : ℝ) + 1 ≤ (n₂ : ℝ) + (t₂ : ℝ) :=
      hgap.trans (le_add_of_nonneg_right t₂.property.1)
    -- A full integer step dominates the remaining fractional part.
    change (n₁ : ℝ) + (t₁ : ℝ) - 1 < (n₂ : ℝ) + (t₂ : ℝ) - 1
    exact sub_lt_sub_right (hbeforeStep.trans_le hafterStep) 1
  · change n₁ = n₂ at hn
    subst n₂
    -- With the integer coordinate fixed, strictness is exactly strictness of the fraction.
    change (t₁ : ℝ) < (t₂ : ℝ) at ht
    change (n₁ : ℝ) + (t₁ : ℝ) - 1 < (n₁ : ℝ) + (t₂ : ℝ) - 1
    linarith

/-- Example 3.12 (1): The staircase correspondence is strictly order-preserving. -/
theorem pnatUnitLexToNonnegative_strictMono :
    StrictMono pnatUnitLexToNonnegative := by
  -- Compare the underlying real values using the scalar strict-monotonicity lemma.
  intro x y hxy
  exact pnatUnitLexValue_strictMono hxy

/-- Helper for Example 3.12: the fractional part of a real lies in `[0, 1)`. -/
lemma realFract_mem_Ico (y : ℝ) : Int.fract y ∈ Set.Ico (0 : ℝ) 1 := by
  -- The standard floor-ring bounds give both endpoints of the half-open interval.
  exact ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩

/-- Helper for Example 3.12: the canonical floor-and-fraction preimage of a nonnegative real. -/
noncomputable def pnatUnitLexPreimage (y : Set.Ici (0 : ℝ)) : ℕ+ ×ₗ Set.Ico (0 : ℝ) 1 :=
  toLex (Nat.succPNat (⌊(y : ℝ)⌋₊), ⟨Int.fract y, realFract_mem_Ico y⟩)

/-- Helper for Example 3.12: the staircase value of the canonical preimage is the original real. -/
lemma pnatUnitLexPreimage_value (y : Set.Ici (0 : ℝ)) :
    pnatUnitLexValue (pnatUnitLexPreimage y) = (y : ℝ) := by
  -- Normalize the positive-natural successor and then use floor plus fractional part.
  simp only [pnatUnitLexValue, pnatUnitLexPreimage, ofLex_toLex, Nat.succPNat_coe,
    Nat.cast_succ]
  rw [natCast_floor_eq_intCast_floor y.property]
  rw [add_assoc, add_comm 1 (Int.fract (y : ℝ)), ← add_assoc, add_sub_cancel_right,
    Int.floor_add_fract]

/-- Example 3.12 (2): The staircase correspondence is onto the
nonnegative real numbers. -/
theorem pnatUnitLexToNonnegative_surjective :
    Function.Surjective pnatUnitLexToNonnegative := by
  -- The named canonical preimage provides a witness with the required scalar value.
  intro y
  refine ⟨pnatUnitLexPreimage y, ?_⟩
  ext
  exact pnatUnitLexPreimage_value y

/-- The staircase correspondence is bijective. -/
theorem pnatUnitLexToNonnegative_bijective :
    Function.Bijective pnatUnitLexToNonnegative :=
  ⟨pnatUnitLexToNonnegative_strictMono.injective,
    pnatUnitLexToNonnegative_surjective⟩

/-- The staircase correspondence has the stated formula. -/
@[simp]
theorem pnatUnitLexToNonnegative_apply (x : ℕ+ ×ₗ Set.Ico (0 : ℝ) 1) :
    (pnatUnitLexToNonnegative x : ℝ) = pnatUnitLexValue x := rfl

/-- Example 3.12 (3): In the dictionary order on
`Set.Ico (0 : ℝ) 1 ×ₗ ℕ+`, incrementing the positive-integer coordinate gives
the immediate successor. -/
theorem unitPnatLex_covBy_addOne (t : Set.Ico (0 : ℝ) 1) (n : ℕ+) :
    toLex (t, n) ⋖ toLex (t, n + 1) := by
  -- In a lexicographic fiber, the cover is the usual successor cover on `ℕ+`.
  apply Prod.Lex.toLex_covBy_toLex_iff.mpr
  apply Or.inl
  refine ⟨rfl, ?_⟩
  constructor
  · exact PNat.lt_add_one_iff.mpr le_rfl
  · intro m hnm hmn
    pnat_to_nat
    omega
