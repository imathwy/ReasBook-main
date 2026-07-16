import StacksProject_2024.stacks_project.Chap23.Definition_23_6_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace ParitySplitGradedAlgebra

variable {R : Type u} [CommRing R] (A : ParitySplitGradedAlgebra R)

/-- Example 23.6.3 (Adjoining even variable) (1): the degree-`m` graded piece of the even-variable
extension `A⟨T⟩`, for `T` of degree `d`, is the direct sum
`A_m ⊕ A_{m - d}T ⊕ A_{m - 2d}T^(2) ⊕ ···`. -/
@[stacks 09PI]
abbrev adjoinEvenVariableGrading (d : ℕ) : ℕ → Type v :=
  fun m ↦ Π₀ i : ℕ, A.piece (m - i * d)

/-- Evaluating `adjoinEvenVariableGrading` recovers the explicit direct-sum grading
`A_m ⊕ A_{m - d}T ⊕ A_{m - 2d}T^(2) ⊕ ···`. -/
theorem adjoinEvenVariableGrading_apply (d m : ℕ) :
    A.adjoinEvenVariableGrading d m = (Π₀ i : ℕ, A.piece (m - i * d)) :=
  rfl

/-- The underlying even part of `A⟨T⟩`, written as finitely supported coefficients in `A ₑᵥₑₙ` of
the divided powers `T^(i)`. -/
abbrev adjoinEvenVariable : Type v :=
  ℕ →₀ A ₑᵥₑₙ

/-- The positive even part of `A⟨T⟩`, viewed canonically as the submodule of finitely supported
coefficients whose constant term lies in the canonical image of `A ₑᵥₑₙ₊` inside `A ₑᵥₑₙ`. -/
abbrev adjoinEvenPositive : Submodule R A.adjoinEvenVariable :=
  A.evenPositiveSubmodule.comap (Finsupp.lapply 0)

/-- Membership in the positive even part is exactly the condition that the constant coefficient
lies in the canonical image of `A ₑᵥₑₙ₊` inside `A ₑᵥₑₙ`. -/
@[simp]
theorem mem_adjoinEvenPositive_iff (x : A.adjoinEvenVariable) :
    x ∈ A.adjoinEvenPositive ↔ x 0 ∈ A.evenPositiveSubmodule :=
  Iff.rfl

/-- The embedded copy of `A ₑᵥₑₙ` inside `A⟨T⟩`, supported in degree `0`. -/
def ofEven (x : A ₑᵥₑₙ) : A.adjoinEvenVariable :=
  Finsupp.single 0 x

@[simp] theorem ofEven_apply (x : A ₑᵥₑₙ) (i : ℕ) :
    A.ofEven x i = if i = 0 then x else 0 := by
  by_cases hi : i = 0
  · subst hi
    simp [ofEven]
  · simp [ofEven, hi]

@[simp] theorem ofEven_zero (x : A ₑᵥₑₙ) :
    A.ofEven x 0 = x := by
  simp [ofEven]

@[simp] theorem ofEven_succ (x : A ₑᵥₑₙ) (i : ℕ) :
    A.ofEven x (i + 1) = 0 := by
  simp [ofEven]

/-- The embedded copy of `A ₑᵥₑₙ₊` inside the positive even part of `A⟨T⟩`. -/
def ofPositive (x : A ₑᵥₑₙ₊) : A.adjoinEvenPositive :=
  ⟨A.ofEven (A.evenPositiveToEven x), by
    rw [mem_adjoinEvenPositive_iff, ofEven_zero]
    exact ⟨x, rfl⟩⟩

@[simp] theorem ofPositive_coe (x : A ₑᵥₑₙ₊) :
    (A.ofPositive x : A.adjoinEvenVariable) = A.ofEven (A.evenPositiveToEven x) :=
  rfl

@[simp] theorem ofPositive_apply (x : A ₑᵥₑₙ₊) (i : ℕ) :
    (A.ofPositive x : A.adjoinEvenVariable) i =
      if i = 0 then A.evenPositiveToEven x else 0 := by
  simpa using (A.ofEven_apply (A.evenPositiveToEven x) i)

@[simp] theorem ofPositive_zero (x : A ₑᵥₑₙ₊) :
    (A.ofPositive x : A.adjoinEvenVariable) 0 = A.evenPositiveToEven x := by
  simpa using (A.ofEven_zero (A.evenPositiveToEven x))

@[simp] theorem ofPositive_succ (x : A ₑᵥₑₙ₊) (i : ℕ) :
    (A.ofPositive x : A.adjoinEvenVariable) (i + 1) = 0 := by
  simpa using (A.ofEven_succ (A.evenPositiveToEven x) i)

/-- The divided-power monomial `T^(i)` in the underlying even part of `A⟨T⟩`. -/
def tDividedPower (i : ℕ) : A.adjoinEvenVariable :=
  Finsupp.single i A.oneEven

@[simp] theorem tDividedPower_apply (i j : ℕ) :
    A.tDividedPower i j = if j = i then A.oneEven else 0 := by
  by_cases hij : j = i
  · subst hij
    simp [tDividedPower]
  · simp [tDividedPower, hij]

@[simp] theorem tDividedPower_self (i : ℕ) :
    A.tDividedPower i i = A.oneEven := by
  simp [tDividedPower]

@[simp] theorem tDividedPower_apply_ne {i j : ℕ} (hij : j ≠ i) :
    A.tDividedPower i j = 0 := by
  simp [tDividedPower, hij]

/-- The zeroth divided-power monomial is the embedded unit of `A_even`. -/
@[simp] theorem tDividedPower_zero :
    A.tDividedPower 0 = A.ofEven A.oneEven := by
  exact Finsupp.ext fun i ↦ by
    by_cases hi : i = 0
    · subst hi
      simp [tDividedPower, ofEven]
    · simp [tDividedPower, ofEven, hi]

/-- The positive divided-power monomial `T^(i)` for `i > 0`, viewed in the positive even part of
`A⟨T⟩`. -/
def tPositiveDividedPower (i : ℕ+) : A.adjoinEvenPositive :=
  ⟨A.tDividedPower i, by
    have hi : (0 : ℕ) ≠ i := Nat.ne_of_lt i.pos
    rw [mem_adjoinEvenPositive_iff]
    simp [tDividedPower, hi]⟩

@[simp] theorem tPositiveDividedPower_coe (i : ℕ+) :
    (A.tPositiveDividedPower i : A.adjoinEvenVariable) = A.tDividedPower i :=
  rfl

@[simp] theorem tPositiveDividedPower_apply (i : ℕ+) (j : ℕ) :
    (A.tPositiveDividedPower i : A.adjoinEvenVariable) j =
      if j = i then A.oneEven else 0 := by
  simpa using (A.tDividedPower_apply (i : ℕ) j)

@[simp] theorem tPositiveDividedPower_zero (i : ℕ+) :
    (A.tPositiveDividedPower i : A.adjoinEvenVariable) 0 = 0 := by
  change A.tDividedPower i 0 = 0
  exact A.tDividedPower_apply_ne (Nat.ne_of_lt i.pos)

@[simp] theorem tPositiveDividedPower_self (i : ℕ+) :
    (A.tPositiveDividedPower i : A.adjoinEvenVariable) i = A.oneEven := by
  simpa using (A.tDividedPower_self (i : ℕ))

instance instMulAdjoinEvenVariable : Mul A.adjoinEvenVariable where
  mul x y :=
    x.sum fun i xi ↦
      y.sum fun j yj ↦
        Finsupp.single (i + j)
          (((i + j).factorial / (i.factorial * j.factorial) : ℕ) • A.evenMul xi yj)

/-- Multiplication on the explicit `T^(i)`-basis of `A⟨T⟩`, determined by the rule
`T^(n) * T^(m) = ((n + m)!)/(n!m!) T^(n + m)`. -/
@[simp] theorem adjoinEvenVariable_mul_def (x y : A.adjoinEvenVariable) :
    x * y =
      x.sum fun i xi ↦
        y.sum fun j yj ↦
          Finsupp.single (i + j)
            (((i + j).factorial / (i.factorial * j.factorial) : ℕ) • A.evenMul xi yj) :=
  rfl

/-- On the distinguished divided-power basis, multiplication in `A⟨T⟩` recovers the textbook
formula `T^(n) T^(m) = ((n + m)!)/(n!m!) T^(n + m)`. -/
theorem tDividedPower_mul_tDividedPower (n m : ℕ) :
    A.tDividedPower n * A.tDividedPower m =
      (((n + m).factorial / (n.factorial * m.factorial) : ℕ) • A.tDividedPower (n + m)) := by
  sorry

/-- A divided-power structure on the positive even part of the even-variable extension `A⟨T⟩`. -/
structure AdjoinEvenVariableDividedPowerStructure (A : ParitySplitGradedAlgebra R) where
  /-- The total family `Δ_n : A⟨T⟩_{even,+} → A⟨T⟩_even`. -/
  gamma : ℕ → A.adjoinEvenPositive → A.adjoinEvenVariable
  /-- For positive indices, the divided power lands again in `A⟨T⟩_{even,+}`. -/
  gamma_mem_adjoinEvenPositive (n : ℕ+) (x : A.adjoinEvenPositive) :
      gamma n x ∈ A.adjoinEvenPositive
  /-- The first divided power is the inclusion of `A⟨T⟩_{even,+}` into `A⟨T⟩_even`. -/
  gamma_one (x : A.adjoinEvenPositive) :
      gamma 1 x = x
  /-- The zeroth divided power is the unit of `A⟨T⟩_even`. -/
  gamma_zero (x : A.adjoinEvenPositive) :
      gamma 0 x = A.ofEven A.oneEven
  /-- The product formula `Δ_n(x)Δ_m(x) = ((n + m)!)/(n!m!) Δ_{n + m}(x)`. -/
  gamma_mul (n m : ℕ) (x : A.adjoinEvenPositive) :
      gamma n x * gamma m x =
        (((n + m).factorial / (n.factorial * m.factorial) : ℕ) • gamma (n + m) x)
  /-- On the positive even part, divided powers turn sums into the usual convolution formula. -/
  gamma_add (n : ℕ) (x y : A.adjoinEvenPositive) :
      gamma n (x + y) =
        (Finset.antidiagonal n).sum fun ij ↦ gamma ij.1 x * gamma ij.2 y
  /-- Iterated divided powers satisfy `Δ_n(Δ_m(x)) = ((nm)!)/(n!(m!)^n) Δ_{nm}(x)` for
  positive `m`. -/
  gamma_comp (n : ℕ) (m : ℕ+) (x : A.adjoinEvenPositive) :
      gamma n ⟨gamma m x, gamma_mem_adjoinEvenPositive m x⟩ =
        (((n * (m : ℕ)).factorial / (n.factorial * (m : ℕ).factorial ^ n) : ℕ) •
          gamma (n * (m : ℕ)) x)

namespace AdjoinEvenVariableDividedPowerStructure

variable {R : Type u} [CommRing R] {A : ParitySplitGradedAlgebra R}

attribute [simp] AdjoinEvenVariableDividedPowerStructure.gamma_zero
attribute [simp] AdjoinEvenVariableDividedPowerStructure.gamma_one

/-- An adjoined even-variable divided-power structure evaluates to its family of maps `Δ_n`. -/
instance : CoeFun A.AdjoinEvenVariableDividedPowerStructure
    (fun _ ↦ ℕ → A.adjoinEvenPositive → A.adjoinEvenVariable) where
  coe Δ := Δ.gamma

@[simp] theorem coe_apply (Δ : A.AdjoinEvenVariableDividedPowerStructure)
    (n : ℕ) (x : A.adjoinEvenPositive) :
    Δ n x = Δ.gamma n x :=
  rfl

/-- For a positive index, `Δ_n` canonically refines to a map
`A⟨T⟩_{even,+} → A⟨T⟩_{even,+}`. -/
abbrev gammaPos (Δ : A.AdjoinEvenVariableDividedPowerStructure)
    (n : ℕ+) (x : A.adjoinEvenPositive) : A.adjoinEvenPositive :=
  ⟨Δ n x, Δ.gamma_mem_adjoinEvenPositive n x⟩

/-- An adjoined even-variable divided-power structure is determined by its family of maps
`Δ_n`. -/
theorem ext (Δ₁ Δ₂ : A.AdjoinEvenVariableDividedPowerStructure)
    (hgamma : ∀ n x, Δ₁ n x = Δ₂ n x) : Δ₁ = Δ₂ := by
  cases Δ₁ with
  | mk gamma gamma_mem_adjoinEvenPositive gamma_one gamma_zero gamma_mul gamma_add gamma_comp =>
      cases Δ₂ with
      | mk gamma' gamma_mem_adjoinEvenPositive' gamma_one' gamma_zero' gamma_mul' gamma_add'
          gamma_comp' =>
          dsimp at hgamma
          have hgamma' : gamma = gamma' := funext fun n ↦ funext fun x ↦ hgamma n x
          cases hgamma'
          simp

/-- Evaluating `gammaPos` recovers the positive-index refinement `Δ_n :
 A⟨T⟩_{even,+} → A⟨T⟩_{even,+}`. -/
@[simp] theorem coe_gammaPos (Δ : A.AdjoinEvenVariableDividedPowerStructure)
    (n : ℕ+) (x : A.adjoinEvenPositive) :
    Δ.gammaPos n x = Δ n x := by
  rfl

/-- For a natural-number index equipped with a positivity proof, the divided power factors
through the positive even part. -/
theorem gamma_eq_gammaPos_nat (Δ : A.AdjoinEvenVariableDividedPowerStructure)
    (n : ℕ) (hn : 0 < n) (x : A.adjoinEvenPositive) :
    Δ n x = Δ.gammaPos ⟨n, hn⟩ x :=
  rfl

/-- Iterated divided powers can be evaluated with an explicit natural-number outer index and a
positive inner index. -/
theorem gamma_comp_nat (Δ : A.AdjoinEvenVariableDividedPowerStructure)
    (n m : ℕ) (hm : 0 < m) (x : A.adjoinEvenPositive) :
    Δ n (Δ.gammaPos ⟨m, hm⟩ x) =
      (((n * m).factorial / (n.factorial * m.factorial ^ n) : ℕ) • Δ (n * m) x) :=
  Δ.gamma_comp n ⟨m, hm⟩ x

/-- Iterated divided powers with positive indices use the positive-index refinement on the inner
term. -/
theorem gamma_comp_pos (Δ : A.AdjoinEvenVariableDividedPowerStructure)
    (n m : ℕ+) (x : A.adjoinEvenPositive) :
    Δ.gammaPos n (Δ.gammaPos m x) =
      (((((n : ℕ) * (m : ℕ)).factorial
            / ((n : ℕ).factorial * (m : ℕ).factorial ^ (n : ℕ)) : ℕ)) •
        Δ ((n : ℕ) * (m : ℕ)) x) := by
  calc
    Δ.gammaPos n (Δ.gammaPos m x) = Δ n (Δ.gammaPos m x) :=
      rfl
    _ = (((((n : ℕ) * (m : ℕ)).factorial
          / ((n : ℕ).factorial * (m : ℕ).factorial ^ (n : ℕ)) : ℕ)) •
        Δ ((n : ℕ) * (m : ℕ)) x) := Δ.gamma_comp n m x

end AdjoinEvenVariableDividedPowerStructure

end ParitySplitGradedAlgebra

namespace DividedPowerStructure

variable {R : Type u} [CommRing R] {A : ParitySplitGradedAlgebra R}
variable {Γ : DividedPowerStructure R A}
variable {Δ Δ₀ Δ₁ Δ₂ : A.AdjoinEvenVariableDividedPowerStructure}

/-- The source characterization of a divided-power structure on the positive even part of the
even-variable extension `A⟨T⟩`: it extends the given divided powers on `A` and sends `T^(i)` to
`T^(ni)`. -/
class IsAdjoinEvenVariableDividedPower (Γ : DividedPowerStructure R A)
    (Δ : A.AdjoinEvenVariableDividedPowerStructure) : Prop where
  /-- On the embedded copy of `A ₑᵥₑₙ₊`, the adjoined divided powers agree with the original
  divided powers. -/
  ofPositive (n : ℕ) (x : A ₑᵥₑₙ₊) :
      Δ n (A.ofPositive x) = A.ofEven (Γ n x)
  /-- On positive divided-power monomials, the adjoined divided powers satisfy
  `Δ_n(T^(i)) = T^(ni)`. -/
  tPositiveDividedPower (n : ℕ) (i : ℕ+) :
      Δ n (A.tPositiveDividedPower i) = A.tDividedPower (n * (i : ℕ))

/-- A source-faithful even-variable divided-power family restricts to the original divided powers
on the embedded copy of `A ₑᵥₑₙ₊`. -/
@[simp] theorem IsAdjoinEvenVariableDividedPower.ofPositive_apply
    (hΔ : Γ.IsAdjoinEvenVariableDividedPower Δ)
    (n : ℕ) (x : A ₑᵥₑₙ₊) :
    Δ n (A.ofPositive x) = A.ofEven (Γ n x) :=
  hΔ.ofPositive n x

/-- A source-faithful even-variable divided-power family sends `T^(i)` to `T^(ni)`. -/
@[simp] theorem IsAdjoinEvenVariableDividedPower.tPositiveDividedPower_apply
    (hΔ : Γ.IsAdjoinEvenVariableDividedPower Δ)
    (n : ℕ) (i : ℕ+) :
    Δ n (A.tPositiveDividedPower i) = A.tDividedPower (n * (i : ℕ)) :=
  hΔ.tPositiveDividedPower n i

/-- Example 23.6.3 (Adjoining even variable) (2): once the even-variable grading from
`A.adjoinEvenVariableGrading d` has been fixed for a positive even degree `d`, the divided-power
structure on the positive even part of `A⟨T⟩` is uniquely characterized by extending the given
divided powers on `A` and by the rule `Δ_n(T^(i)) = T^(ni)`. The dependence on `d` is carried by
the grading, while this characterization of `Δ` itself is independent of the numeric value of
that even positive degree. -/
@[stacks 09PI]
theorem existsUniqueAdjoinEvenVariableDividedPower (Γ : DividedPowerStructure R A) :
    ∃! Δ : A.AdjoinEvenVariableDividedPowerStructure,
      Γ.IsAdjoinEvenVariableDividedPower Δ := sorry

/-- Any two even-variable divided-power families satisfying the source characterization agree. -/
theorem IsAdjoinEvenVariableDividedPower.eq
    (hΔ₁ : Γ.IsAdjoinEvenVariableDividedPower Δ₁)
    (hΔ₂ : Γ.IsAdjoinEvenVariableDividedPower Δ₂) :
    Δ₁ = Δ₂ := by
  exact ExistsUnique.unique (existsUniqueAdjoinEvenVariableDividedPower Γ) hΔ₁ hΔ₂

/-- Once one source-faithful even-variable divided-power family is known, every other candidate is
equal to it. -/
theorem isAdjoinEvenVariableDividedPower_iff_eq
    (Γ : DividedPowerStructure R A)
    (hΔ₀ : Γ.IsAdjoinEvenVariableDividedPower Δ₀)
    (Δ : A.AdjoinEvenVariableDividedPowerStructure) :
    Γ.IsAdjoinEvenVariableDividedPower Δ ↔ Δ = Δ₀ := by
  constructor
  · intro hΔ
    exact hΔ.eq hΔ₀
  · rintro rfl
    exact hΔ₀

end DividedPowerStructure

end
