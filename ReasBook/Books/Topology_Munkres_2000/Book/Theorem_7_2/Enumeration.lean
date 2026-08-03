module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Nat.Nth

public section

namespace Set

private theorem Infinite.pnatPred {C : Set ℕ+} (hC : C.Infinite) :
    {n : ℕ | Nat.succPNat n ∈ C}.Infinite := by
  exact hC.preimage fun c hc ↦ ⟨c.natPred, by simp⟩

/-- The increasing enumeration of an infinite set of positive natural numbers. -/
noncomputable def leastUnused (C : Set ℕ+) (hC : C.Infinite) (i : ℕ+) : C :=
  ⟨Nat.succPNat (Nat.nth (fun n ↦ Nat.succPNat n ∈ C) i.natPred),
    Nat.nth_mem_of_infinite hC.pnatPred i.natPred⟩

/-- At each index, `C.leastUnused hC` selects the least element not selected earlier. -/
theorem leastUnused_isLeast (C : Set ℕ+) (hC : C.Infinite) (i : ℕ+) :
    IsLeast (Set.univ \ C.leastUnused hC '' Set.Iio i) (C.leastUnused hC i) := by
  -- Strict monotonicity ensures that the current value has not appeared earlier.
  constructor
  · refine ⟨Set.mem_univ _, ?_⟩
    rintro ⟨j, hji, hij⟩
    have hPred : j.natPred < i.natPred := by
      simpa using hji
    have hNth := (Nat.nth_strictMono hC.pnatPred) hPred
    have hEqual :
        Nat.nth (fun n ↦ Nat.succPNat n ∈ C) j.natPred =
          Nat.nth (fun n ↦ Nat.succPNat n ∈ C) i.natPred := by
      simpa [leastUnused] using congrArg Subtype.val hij
    exact hNth.ne hEqual
  · intro c hc
    obtain ⟨j, hj⟩ := (Nat.range_nth_of_infinite hC.pnatPred).symm.subset
      (show c.val.natPred ∈ {n : ℕ | Nat.succPNat n ∈ C} by simp [c.property])
    have hIndex : i.natPred ≤ j := by
      by_contra hji
      have hji' : j < i.natPred := Nat.lt_of_not_ge hji
      have hEarlier : Nat.succPNat j < i := by
        exact PNat.natPred_lt_natPred.mp (by simpa using hji')
      apply hc.2
      refine ⟨Nat.succPNat j, hEarlier, ?_⟩
      apply Subtype.ext
      calc
        Nat.succPNat (Nat.nth (fun n ↦ Nat.succPNat n ∈ C) j) =
            Nat.succPNat c.val.natPred := congrArg Nat.succPNat hj
        _ = c.val := PNat.succPNat_natPred c.val
    have hNat := Nat.nth_monotone hC.pnatPred hIndex
    rw [hj] at hNat
    exact PNat.natPred_le_natPred.mp (by simpa [leastUnused] using hNat)

/-- The least-unused specification uniquely determines an enumeration of `C`. -/
theorem leastUnused_unique (C : Set ℕ+) (hC : C.Infinite) (h : ℕ+ → C)
    (hh : ∀ i : ℕ+, IsLeast (Set.univ \ h '' Set.Iio i) (h i)) :
    h = C.leastUnused hC := by
  funext i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
      -- The induction hypothesis identifies the sets of values used before `i`.
      have hImage : h '' Set.Iio i = C.leastUnused hC '' Set.Iio i := by
        ext c
        constructor
        · rintro ⟨j, hji, rfl⟩
          exact ⟨j, hji, (ih j hji).symm⟩
        · rintro ⟨j, hji, rfl⟩
          exact ⟨j, hji, ih j hji⟩
      have hi := hh i
      rw [hImage] at hi
      exact hi.unique (C.leastUnused_isLeast hC i)

end Set
