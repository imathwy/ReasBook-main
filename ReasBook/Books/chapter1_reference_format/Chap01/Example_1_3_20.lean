import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {F : Type u} [Field F] [Finite F]

/-- Example 1.3.20: if `d` divides `q - 1 = Nat.card F - 1`, then the number of elements of the
multiplicative group `Fˣ` having order exactly `d` is Euler's totient `Nat.totient d`; this is the
finite-field counting identity `ψ(d) = φ(d)` from the text. -/
-- Proof sketch: the unit group `Fˣ` of a finite field is cyclic and has cardinality
-- `Nat.card F - 1`. Apply the cyclic-group counting theorem
-- `IsCyclic.card_orderOf_eq_totient` to `Fˣ`.
theorem finiteField_units_card_orderOf_eq_totient {d : ℕ} (hd : d ∣ Nat.card F - 1) :
    Nat.card {a : Fˣ // orderOf a = d} = Nat.totient d := by
  classical
  letI := Fintype.ofFinite Fˣ
  letI := Fintype.ofFinite {a : Fˣ // orderOf a = d}
  have hd' : d ∣ Fintype.card Fˣ := by
    have hcard : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
    rw [← Nat.card_eq_fintype_card]
    rw [hcard]
    exact hd
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact IsCyclic.card_orderOf_eq_totient hd'

/-- A finite field has a unit whose order is the full size of its multiplicative group. -/
-- Proof sketch: use the cyclicity of `Fˣ` together with
-- `isCyclic_iff_exists_orderOf_eq_natCard`, then rewrite `Nat.card Fˣ` as `Nat.card F - 1` using
-- `Nat.card_units`.
theorem finiteField_exists_unit_of_order_card_sub_one :
    ∃ a : Fˣ, orderOf a = Nat.card F - 1 := by
  simpa [Nat.card_units F] using
    (show ∃ a : Fˣ, orderOf a = Nat.card Fˣ from
      isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic Fˣ))

end
