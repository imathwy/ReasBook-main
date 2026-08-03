module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Prod.Lex
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.SetTheory.Ordinal.Arithmetic

public section

open Prod.Lex
open scoped Cardinal
open scoped Ordinal

/- Example 10.5 (1): The positive natural numbers are countably infinite. -/
#check Cardinal.mk_pnat

/-- For Example 10.5 (2), if `0 < n`, the dictionary order on `Fin n ×ₗ ℕ+` is
countably infinite. -/
theorem finPnatLexCardinal (n : ℕ) (h_n : 0 < n) :
    Cardinal.mk (Fin n ×ₗ ℕ+) = ℵ₀ := by
  change Cardinal.mk (Fin n × ℕ+) = ℵ₀
  rw [Cardinal.mk_prod, Cardinal.mk_fintype, Cardinal.mk_pnat]
  simp [h_n.ne']

/-- For Example 10.5 (3), the dictionary order on `ℕ+ ×ₗ ℕ+` is countably infinite. -/
theorem pnatLexCardinal : Cardinal.mk (ℕ+ ×ₗ ℕ+) = ℵ₀ := by
  change Cardinal.mk (ℕ+ × ℕ+) = ℵ₀
  exact Cardinal.mk_eq_aleph0 (ℕ+ × ℕ+)

/-- For Example 10.5 (4), the nested dictionary order on `ℕ+ ×ₗ (ℕ+ ×ₗ ℕ+)` is
countably infinite. -/
theorem pnatTripleLexCardinal : Cardinal.mk (ℕ+ ×ₗ (ℕ+ ×ₗ ℕ+)) = ℵ₀ := by
  change Cardinal.mk (ℕ+ × (ℕ+ × ℕ+)) = ℵ₀
  exact Cardinal.mk_eq_aleph0 (ℕ+ × (ℕ+ × ℕ+))

/-- The order type of the positive natural numbers is `ω`. -/
theorem pnatOrderType : typeLT ℕ+ = ω := by
  simpa using OrderIso.pnatIsoNat.ordinalType_congr

/-- The dictionary order on `Fin n ×ₗ ℕ+` has order type `ω * n`. -/
theorem finPnatLexOrderType (n : ℕ) : typeLT (Fin n ×ₗ ℕ+) = ω * n := by
  rw [show typeLT (Fin n ×ₗ ℕ+) =
    Ordinal.type (Prod.Lex ((· < ·) : Fin n → Fin n → Prop)
      ((· < ·) : ℕ+ → ℕ+ → Prop)) from rfl]
  rw [Ordinal.type_prod_lex, pnatOrderType, Ordinal.type_fin]

/-- The dictionary order on `ℕ+ ×ₗ ℕ+` has order type `ω * ω`. -/
theorem pnatLexOrderType : typeLT (ℕ+ ×ₗ ℕ+) = ω * ω := by
  change Ordinal.type (Prod.Lex ((· < ·) : ℕ+ → ℕ+ → Prop)
    ((· < ·) : ℕ+ → ℕ+ → Prop)) = ω * ω
  rw [Ordinal.type_prod_lex, pnatOrderType]

/-- The nested dictionary order on `ℕ+ ×ₗ (ℕ+ ×ₗ ℕ+)` has order type
`(ω * ω) * ω`. -/
theorem pnatTripleLexOrderType : typeLT (ℕ+ ×ₗ (ℕ+ ×ₗ ℕ+)) = (ω * ω) * ω := by
  rw [show typeLT (ℕ+ ×ₗ (ℕ+ ×ₗ ℕ+)) =
    Ordinal.type (Prod.Lex ((· < ·) : ℕ+ → ℕ+ → Prop)
      ((· < ·) : (ℕ+ ×ₗ ℕ+) → (ℕ+ ×ₗ ℕ+) → Prop)) from rfl]
  rw [Ordinal.type_prod_lex, pnatLexOrderType, pnatOrderType]

/-- For Example 10.5 (5), if `2 ≤ n`, the order type of `ℕ+` is strictly less than
that of `Fin n ×ₗ ℕ+`. -/
theorem pnatType_lt_finPnatLexType (n : ℕ) (h_n : 2 ≤ n) :
    typeLT ℕ+ < typeLT (Fin n ×ₗ ℕ+) := by
  -- Rewrite both well-orders to their ordinal normal forms.
  rw [pnatOrderType, finPnatLexOrderType]
  -- The size hypothesis makes the right factor strictly larger than one.
  have h_one_nat : 1 < n := by
    omega
  have h_one : (1 : Ordinal) < n := by
    exact_mod_cast h_one_nat
  -- Positive left multiplication by `ω` preserves the strict inequality.
  simpa only [mul_one] using mul_lt_mul_of_pos_left h_one Ordinal.omega0_pos

/-- For Example 10.5 (6), if `2 ≤ n`, the order type of `Fin n ×ₗ ℕ+` is strictly
less than that of `ℕ+ ×ₗ ℕ+`. -/
theorem finPnatLexType_lt_pnatLexType (n : ℕ) (h_n : 2 ≤ n) :
    typeLT (Fin n ×ₗ ℕ+) < typeLT (ℕ+ ×ₗ ℕ+) := by
  -- The comparison holds for every finite `n`, so the source hypothesis is stronger than needed.
  have _sourceBound := h_n
  -- Rewrite the lexicographic orders to `ω * n` and `ω * ω`.
  rw [finPnatLexOrderType, pnatLexOrderType]
  -- Every finite ordinal is below `ω`, and multiplication by positive `ω` is strict.
  exact mul_lt_mul_of_pos_left (Ordinal.natCast_lt_omega0 n) Ordinal.omega0_pos

/-- For Example 10.5 (7), the order type of `ℕ+ ×ₗ ℕ+` is strictly less than that of
`ℕ+ ×ₗ (ℕ+ ×ₗ ℕ+)`, completing the distinction among the four displayed
well-orders. -/
theorem pnatLexType_lt_pnatTripleLexType :
    typeLT (ℕ+ ×ₗ ℕ+) < typeLT (ℕ+ ×ₗ (ℕ+ ×ₗ ℕ+)) := by
  -- Rewrite the two nested lexicographic orders to their ordinal products.
  rw [pnatLexOrderType, pnatTripleLexOrderType]
  -- Compare the terminal factors `1 < ω` after multiplying by positive `ω * ω`.
  simpa only [mul_one] using mul_lt_mul_of_pos_left Ordinal.one_lt_omega0
    (mul_pos Ordinal.omega0_pos Ordinal.omega0_pos)

/-- Example 10.5: For `2 ≤ n`, the four displayed countable well-orders have
strictly increasing order types. -/
theorem displayedOrderTypesStrictlyIncrease (n : ℕ) (h_n : 2 ≤ n) :
    typeLT ℕ+ < typeLT (Fin n ×ₗ ℕ+) ∧
      typeLT (Fin n ×ₗ ℕ+) < typeLT (ℕ+ ×ₗ ℕ+) ∧
        typeLT (ℕ+ ×ₗ ℕ+) < typeLT (ℕ+ ×ₗ (ℕ+ ×ₗ ℕ+)) := by
  -- Package the three adjacent comparisons into the source's single conclusion.
  constructor
  · exact pnatType_lt_finPnatLexType n h_n
  · constructor
    · exact finPnatLexType_lt_pnatLexType n h_n
    · exact pnatLexType_lt_pnatTripleLexType
