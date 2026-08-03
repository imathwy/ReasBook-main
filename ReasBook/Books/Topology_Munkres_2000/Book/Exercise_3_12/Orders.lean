module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.Hom.Basic

@[expose] public section

namespace PositivePairOrder

/-- Positive-integer pairs with the dictionary order. -/
abbrev Dictionary := Lex (ℕ+ × ℕ+)

/-- Positive-integer pairs ordered first by coordinate difference and then by the second
coordinate. -/
structure Difference where
  x : ℕ+
  y : ℕ+

/-- Positive-integer pairs ordered first by coordinate sum and then by the second coordinate. -/
structure Sum where
  x : ℕ+
  y : ℕ+

namespace Difference

/-- The underlying positive-integer pair. -/
def equivProd : Difference ≃ ℕ+ × ℕ+ where
  toFun p := (p.x, p.y)
  invFun p := ⟨p.1, p.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- The product view of a difference-ordered pair. -/
@[simp]
theorem equivProd_apply (p : Difference) : equivProd p = (p.x, p.y) := rfl

/-- The difference-ordered pair associated to a product. -/
@[simp]
theorem equivProd_symm_apply (p : ℕ+ × ℕ+) : equivProd.symm p = ⟨p.1, p.2⟩ := rfl

/-- The lexicographic coordinates defining the difference-first order. -/
def coordinates (p : Difference) : Lex (ℤ × ℕ+) :=
  toLex ((p.x : ℤ) - (p.y : ℤ), p.y)

/-- The formula for the difference-first coordinate map. -/
@[simp]
theorem coordinates_apply (p : Difference) :
    coordinates p = toLex ((p.x : ℤ) - (p.y : ℤ), p.y) := rfl

/-- The difference-first coordinate map is injective. -/
theorem coordinates_injective : Function.Injective coordinates := by
  -- Equality of the second coordinate and of the difference recovers the first coordinate.
  intro p q h
  have hy : p.y = q.y := congrArg (fun r : Lex (ℤ × ℕ+) ↦ (ofLex r).2) h
  have hdifference : (p.x : ℤ) - (p.y : ℤ) = (q.x : ℤ) - (q.y : ℤ) :=
    congrArg (fun r : Lex (ℤ × ℕ+) ↦ (ofLex r).1) h
  have hyInteger : (p.y : ℤ) = (q.y : ℤ) := congrArg (fun n : ℕ+ ↦ (n : ℤ)) hy
  have hxInteger : (p.x : ℤ) = (q.x : ℤ) := by omega
  have hx : p.x = q.x := by exact_mod_cast hxInteger
  cases p
  cases q
  simp only at hx hy ⊢
  subst hx
  subst hy
  rfl

/-- The linear order transported from the difference-first lexicographic coordinates. -/
instance instLinearOrder : LinearOrder Difference :=
  LinearOrder.lift' coordinates coordinates_injective

/-- Comparison in the difference-first order, in the textbook coordinates. -/
theorem lt_iff (p q : Difference) :
    p < q ↔
      (p.x : ℤ) - (p.y : ℤ) < (q.x : ℤ) - (q.y : ℤ) ∨
        (p.x : ℤ) - (p.y : ℤ) = (q.x : ℤ) - (q.y : ℤ) ∧ p.y < q.y := by
  -- The transported order is exactly lexicographic comparison of `coordinates`.
  exact Prod.Lex.toLex_lt_toLex

end Difference

namespace Sum

/-- The underlying positive-integer pair. -/
def equivProd : Sum ≃ ℕ+ × ℕ+ where
  toFun p := (p.x, p.y)
  invFun p := ⟨p.1, p.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- The product view of a sum-ordered pair. -/
@[simp]
theorem equivProd_apply (p : Sum) : equivProd p = (p.x, p.y) := rfl

/-- The sum-ordered pair associated to a product. -/
@[simp]
theorem equivProd_symm_apply (p : ℕ+ × ℕ+) : equivProd.symm p = ⟨p.1, p.2⟩ := rfl

/-- The lexicographic coordinates defining the sum-first order. -/
def coordinates (p : Sum) : Lex (ℕ+ × ℕ+) :=
  toLex (p.x + p.y, p.y)

/-- The formula for the sum-first coordinate map. -/
@[simp]
theorem coordinates_apply (p : Sum) : coordinates p = toLex (p.x + p.y, p.y) := rfl

/-- The sum-first coordinate map is injective. -/
theorem coordinates_injective : Function.Injective coordinates := by
  -- Equality of the second coordinate and of the sum recovers the first coordinate.
  intro p q h
  have hy : p.y = q.y := congrArg (fun r : Lex (ℕ+ × ℕ+) ↦ (ofLex r).2) h
  have hsum : p.x + p.y = q.x + q.y :=
    congrArg (fun r : Lex (ℕ+ × ℕ+) ↦ (ofLex r).1) h
  cases p
  cases q
  simp only at hy hsum ⊢
  subst hy
  congr 1
  exact add_right_cancel hsum

/-- The linear order transported from the sum-first lexicographic coordinates. -/
instance instLinearOrder : LinearOrder Sum :=
  LinearOrder.lift' coordinates coordinates_injective

/-- The least sum-ordered positive pair is `(1, 1)`. -/
instance instOrderBot : OrderBot Sum where
  bot := ⟨1, 1⟩
  bot_le p := by
    -- Positivity of both coordinates makes `(1, 1)` lexicographically least by sum.
    change coordinates ⟨1, 1⟩ ≤ coordinates p
    simp only [coordinates_apply]
    rw [Prod.Lex.toLex_le_toLex]
    have hsum : (1 : ℕ+) + 1 ≤ p.x + p.y := add_le_add p.x.property p.y.property
    rcases hsum.lt_or_eq with hsum | hsum
    · exact Or.inl hsum
    · exact Or.inr ⟨hsum, p.y.property⟩

/-- The bottom element of the sum-first order is `(1, 1)`. -/
@[simp]
theorem bot_eq : (⊥ : Sum) = ⟨1, 1⟩ := rfl

/-- Comparison in the sum-first order, in the textbook coordinates. -/
theorem lt_iff (p q : Sum) :
    p < q ↔ p.x + p.y < q.x + q.y ∨ p.x + p.y = q.x + q.y ∧ p.y < q.y := by
  -- The transported order is exactly lexicographic comparison of `coordinates`.
  exact Prod.Lex.toLex_lt_toLex

end Sum

end PositivePairOrder
