import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators PowerSeries

noncomputable section

namespace PowerSeries

universe u v

variable {R : Type u} [Semiring R] {ι : Type v}

/-- Definition I.1-extra-4: A family of formal power series is summable if, for every natural
cutoff `k`, only finitely many members of the family have order strictly smaller than `k`. -/
def SummableFamily (S : ι → R⟦X⟧) : Prop :=
  ∀ k : ℕ, Set.Finite { i | order (S i) < k }

/-- The source-facing order condition canonically packages a family of power series into the Hahn
series owner `HahnSeries.SummableFamily ℕ R ι`. -/
def toHahnSummableFamily (S : ι → R⟦X⟧) (hS : SummableFamily S) :
    HahnSeries.SummableFamily ℕ R ι where
  toFun i := HahnSeries.toPowerSeries.symm (S i)
  isPWO_iUnion_support' := Set.IsPWO.of_linearOrder _
  finite_co_support' n := by
    refine (hS (n + 1)).subset ?_
    intro i hi
    exact lt_of_le_of_lt
      (order_le n (by simpa [HahnSeries.coeff_toPowerSeries_symm] using hi))
      (by simpa using (Nat.cast_lt.mpr (Nat.lt_succ_self n)))

/-- The sum of a summable family of formal power series, defined by transporting the canonical
Hahn-series formal sum along the equivalence `R⟦ℕ⟧ ≃+* R⟦X⟧`. -/
def summableFamilySum (S : ι → R⟦X⟧) (hS : SummableFamily S) : R⟦X⟧ :=
  HahnSeries.toPowerSeries (toHahnSummableFamily S hS).hsum

/-- For a summable family of power series, only finitely many members contribute to a fixed
coefficient. -/
theorem finite_coeff_support {S : ι → R⟦X⟧} (hS : SummableFamily S) (n : ℕ) :
    Set.Finite { i | coeff n (S i) ≠ 0 } := by
  simpa [toHahnSummableFamily, HahnSeries.coeff_toPowerSeries_symm] using
    (toHahnSummableFamily S hS).finite_co_support n

/-- The coefficients of the sum of a summable family are the corresponding finite sums of
coefficients. -/
theorem coeff_summableFamilySum
    {S : ι → R⟦X⟧} (hS : SummableFamily S) (n : ℕ) :
    coeff n (summableFamilySum S hS) =
      ∑ i ∈ (finite_coeff_support hS n).toFinset, coeff n (S i) := by
  simpa [summableFamilySum, finite_coeff_support, toHahnSummableFamily,
    HahnSeries.coeff_toPowerSeries, HahnSeries.coeff_toPowerSeries_symm] using
    (toHahnSummableFamily S hS).coeff_hsum_eq_sum

end PowerSeries
