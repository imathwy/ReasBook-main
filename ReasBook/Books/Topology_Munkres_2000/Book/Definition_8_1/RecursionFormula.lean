module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Set.Restrict

public section

universe u

namespace Function

/-- A positive-integer recursion formula with initial value `a₀` and history rule `ρ`. -/
def IsPositiveRecursionFormula {A : Type u} (h : ℕ+ → A) (a₀ : A)
    (ρ : ∀ {i : ℕ+}, 1 < i → (Set.Iio i → A) → A) : Prop :=
  h 1 = a₀ ∧ ∀ (i : ℕ+) (hi : 1 < i), h i = ρ hi ((Set.Iio i).restrict h)

/-- The initial value prescribed by a positive-integer recursion formula. -/
theorem IsPositiveRecursionFormula.eq_one {A : Type u} {a₀ : A}
    {ρ : ∀ {i : ℕ+}, 1 < i → (Set.Iio i → A) → A} {h : ℕ+ → A}
    (hh : h.IsPositiveRecursionFormula a₀ ρ) :
    h 1 = a₀ :=
  hh.1

/-- The later values prescribed by a positive-integer recursion formula. -/
theorem IsPositiveRecursionFormula.eq_of_one_lt {A : Type u} {a₀ : A}
    {ρ : ∀ {i : ℕ+}, 1 < i → (Set.Iio i → A) → A} {h : ℕ+ → A}
    (hh : h.IsPositiveRecursionFormula a₀ ρ) (i : ℕ+) (hi : 1 < i) :
    h i = ρ hi ((Set.Iio i).restrict h) :=
  hh.2 i hi

/-- Build a positive-integer recursion formula from its initial and recursive equations. -/
theorem IsPositiveRecursionFormula.mk {A : Type u} {a₀ : A}
    {ρ : ∀ {i : ℕ+}, 1 < i → (Set.Iio i → A) → A} {h : ℕ+ → A}
    (h_one : h 1 = a₀)
    (h_later : ∀ (i : ℕ+) (hi : 1 < i), h i = ρ hi ((Set.Iio i).restrict h)) :
    h.IsPositiveRecursionFormula a₀ ρ :=
  ⟨h_one, h_later⟩

end Function

end
