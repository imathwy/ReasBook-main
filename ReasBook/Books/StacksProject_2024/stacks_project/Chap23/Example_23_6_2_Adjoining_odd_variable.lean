import StacksProject_2024.stacks_project.Chap23.Definition_23_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace ParitySplitGradedAlgebra

variable {R : Type u} [CommRing R] (A : ParitySplitGradedAlgebra R)

/-- Example 23.6.2 (Adjoining odd variable) (1): the degree-`m` graded piece of the odd-variable
extension `A⟨T⟩`, namely `A_m ⊕ A_{m - d}T`. -/
@[stacks 09PH]
abbrev adjoinOddVariableGrading (d : ℕ) : ℕ → Type v :=
  fun m ↦ A.piece m × A.piece (m - d)

/-- Evaluating `adjoinOddVariableGrading` recovers the explicit textbook grading
`A_m ⊕ A_{m - d}T`. -/
theorem adjoinOddVariableGrading_apply (d m : ℕ) :
    A.adjoinOddVariableGrading d m = (A.piece m × A.piece (m - d)) :=
  rfl

/-- The underlying even part of the odd-variable extension `A⟨T⟩`, written as pairs
`x + yT` with `x ∈ Aₑᵥₑₙ` and `y ∈ Aₒdd`. -/
abbrev adjoinOddVariable : Type v :=
  A ₑᵥₑₙ × A ₒdd

/-- The positive even part of `A⟨T⟩`, written as pairs `x + yT` with
`x ∈ Aₑᵥₑₙ₊` and `y ∈ Aₒdd`. -/
abbrev adjoinOddPositive : Type v :=
  A ₑᵥₑₙ₊ × A ₒdd

/-- The embedded copy of `Aₑᵥₑₙ` inside the odd-variable extension `A⟨T⟩`. -/
def ofEven (x : A ₑᵥₑₙ) : A.adjoinOddVariable :=
  (x, 0)

@[simp] theorem ofEven_fst (x : A ₑᵥₑₙ) :
    (A.ofEven x).1 = x :=
  rfl

@[simp] theorem ofEven_snd (x : A ₑᵥₑₙ) :
    (A.ofEven x).2 = 0 :=
  rfl

/-- The embedded copy of `Aₑᵥₑₙ₊` inside the positive even part of `A⟨T⟩`. -/
def ofPositive (x : A ₑᵥₑₙ₊) : A.adjoinOddPositive :=
  (x, 0)

@[simp] theorem ofPositive_fst (x : A ₑᵥₑₙ₊) :
    (A.ofPositive x).1 = x :=
  rfl

@[simp] theorem ofPositive_snd (x : A ₑᵥₑₙ₊) :
    (A.ofPositive x).2 = 0 :=
  rfl

end ParitySplitGradedAlgebra

namespace DividedPowerStructure

variable {R : Type u} [CommRing R] {A : ParitySplitGradedAlgebra R}

/-- The explicit divided-power family on the positive even part of the odd-variable extension
`A⟨T⟩`. -/
def adjoinOddVariableGamma (Γ : DividedPowerStructure R A) :
    ℕ → A.adjoinOddPositive → A.adjoinOddVariable
  | 0, _ => A.ofEven A.oneEven
  | n + 1, (x, y) => (Γ (n + 1) x, A.evenMulOdd (Γ n x) y)

/-- At index `0`, the odd-variable divided power is the unit. -/
theorem adjoinOddVariableGamma_zero (Γ : DividedPowerStructure R A)
    (z : A.adjoinOddPositive) :
    adjoinOddVariableGamma Γ 0 z = A.ofEven A.oneEven :=
  rfl

/-- At index `n + 1`, the odd-variable divided power is
`γ_{n + 1}(x) + γ_n(x) y T`. -/
theorem adjoinOddVariableGamma_succ (Γ : DividedPowerStructure R A)
    (n : ℕ) (x : A ₑᵥₑₙ₊) (y : A ₒdd) :
    adjoinOddVariableGamma Γ (n + 1) (x, y) =
      (Γ (n + 1) x, A.evenMulOdd (Γ n x) y) :=
  rfl

/-- The explicit odd-variable divided powers restrict to the original divided powers on the
embedded copy of `A`. -/
theorem adjoinOddVariableGamma_compatible (Γ : DividedPowerStructure R A)
    (n : ℕ) (x : A ₑᵥₑₙ₊) :
    adjoinOddVariableGamma Γ (n + 1) (A.ofPositive x) =
      A.ofEven (Γ (n + 1) x) := by
  simp [adjoinOddVariableGamma, ParitySplitGradedAlgebra.ofPositive,
    ParitySplitGradedAlgebra.ofEven]

/-- The defining identities for a divided-power family on the odd-variable extension `A⟨T⟩`. -/
class IsAdjoinOddVariableDividedPower (Γ : DividedPowerStructure R A)
    (Δ : ℕ → A.adjoinOddPositive → A.adjoinOddVariable) : Prop where
  /-- The zeroth divided power on `A⟨T⟩` is the unit. -/
  zero (z : A.adjoinOddPositive) : Δ 0 z = A.ofEven A.oneEven
  /-- The successor divided powers satisfy the explicit odd-variable recursion. -/
  succ (n : ℕ) (x : A ₑᵥₑₙ₊) (y : A ₒdd) :
      Δ (n + 1) (x, y) = (Γ (n + 1) x, A.evenMulOdd (Γ n x) y)

/-- An odd-variable divided-power family restricts to the original divided powers on the embedded
copy of `A`. -/
theorem IsAdjoinOddVariableDividedPower.compatible
    {Γ : DividedPowerStructure R A}
    {Δ : ℕ → A.adjoinOddPositive → A.adjoinOddVariable}
    (hΔ : Γ.IsAdjoinOddVariableDividedPower Δ)
    (n : ℕ) (x : A ₑᵥₑₙ₊) :
    Δ (n + 1) (A.ofPositive x) = A.ofEven (Γ (n + 1) x) := by
  simp [hΔ.succ, ParitySplitGradedAlgebra.ofPositive, ParitySplitGradedAlgebra.ofEven,
    ParitySplitGradedAlgebra.evenMulOdd]

/-- The explicit recursion `adjoinOddVariableGamma` satisfies the source characterization of the
divided powers on `A⟨T⟩`. -/
theorem adjoinOddVariableGamma_isAdjoinOddVariableDividedPower
    (Γ : DividedPowerStructure R A) :
    Γ.IsAdjoinOddVariableDividedPower (adjoinOddVariableGamma Γ) where
  zero := adjoinOddVariableGamma_zero Γ
  succ := adjoinOddVariableGamma_succ Γ

/-- Any odd-variable divided-power family is equal to the explicit recursion from
Example 23.6.2. -/
theorem IsAdjoinOddVariableDividedPower.eq_adjoinOddVariableGamma
    {Γ : DividedPowerStructure R A}
    {Δ : ℕ → A.adjoinOddPositive → A.adjoinOddVariable}
    (hΔ : Γ.IsAdjoinOddVariableDividedPower Δ) :
    Δ = adjoinOddVariableGamma Γ := by
  funext n z
  cases n with
  | zero =>
      exact hΔ.zero z
  | succ n =>
      rcases z with ⟨x, y⟩
      exact hΔ.succ n x y

/-- The source characterization of an odd-variable divided-power family is equivalent to equality
with the explicit recursion `adjoinOddVariableGamma`. -/
theorem isAdjoinOddVariableDividedPower_iff_eq_adjoinOddVariableGamma
    (Γ : DividedPowerStructure R A)
    (Δ : ℕ → A.adjoinOddPositive → A.adjoinOddVariable) :
    Γ.IsAdjoinOddVariableDividedPower Δ ↔
      Δ = adjoinOddVariableGamma Γ := by
  constructor
  · intro hΔ
    exact hΔ.eq_adjoinOddVariableGamma
  · intro hΔ
    rw [hΔ]
    exact adjoinOddVariableGamma_isAdjoinOddVariableDividedPower Γ

/-- Example 23.6.2 (Adjoining odd variable): after the grading from
`A.adjoinOddVariableGrading d` is fixed, the odd-variable divided-power family on `A⟨T⟩` is
uniquely determined by the source recursion
`γ_0(x + yT) = 1` and
`γ_{n + 1}(x + yT) = γ_{n + 1}(x) + γ_n(x) y T`. Compatibility with the embedded copy of `A`
is recovered separately from `IsAdjoinOddVariableDividedPower.compatible`. -/
@[stacks 09PH]
theorem existsUniqueAdjoinOddVariableDividedPower (Γ : DividedPowerStructure R A) :
    ∃! Δ : ℕ → A.adjoinOddPositive → A.adjoinOddVariable,
      Γ.IsAdjoinOddVariableDividedPower Δ := by
  refine ⟨adjoinOddVariableGamma Γ,
    adjoinOddVariableGamma_isAdjoinOddVariableDividedPower Γ, ?_⟩
  intro Δ hΔ
  exact hΔ.eq_adjoinOddVariableGamma

end DividedPowerStructure
