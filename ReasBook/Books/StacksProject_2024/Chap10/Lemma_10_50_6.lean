import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open DirectedSystem
open Ring.DirectLimit

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (A : I → Type u) [∀ i, CommRing (A i)] [∀ i, IsDomain (A i)] [∀ i, ValuationRing (A i)]
variable (φ : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (φ · · ·)]

local notation "A∞" => Ring.DirectLimit A (fun i j h ↦ φ i j h)
local notation "of∞" => of A (fun i j h ↦ φ i j h)

/-- A directed ring direct limit of domains is again a domain. -/
instance : IsDomain A∞ := by
  haveI : Nontrivial A∞ := by
    obtain ⟨i⟩ := ‹Nonempty I›
    refine ⟨⟨0, 1, ?_⟩⟩
    change (0 : A∞) ≠ 1
    rw [← (of∞ i).map_one]
    intro h
    rcases of.zero_exact h.symm with ⟨j, hij, hj⟩
    rw [(φ i j hij).map_one] at hj
    exact one_ne_zero hj
  haveI : NoZeroDivisors A∞ := by
    constructor
    intro x y hxy
    induction x using induction_on with
    | ih i x =>
        induction y using induction_on with
        | ih j y =>
            rcases exists_ge_ge i j with ⟨k, hik, hjk⟩
            have hk : of∞ k (φ i k hik x * φ j k hjk y) = 0 := by
              simpa [map_mul, of_f] using hxy
            rcases of.zero_exact hk with ⟨l, hkl, hzero⟩
            have hprod : φ i l (le_trans hik hkl) x * φ j l (le_trans hjk hkl) y = 0 := by
              simpa [map_mul, map_map' φ hik hkl x, map_map' φ hjk hkl y] using hzero
            rcases eq_zero_or_eq_zero_of_mul_eq_zero hprod with hx | hy
            · left
              simpa [of_f] using congrArg (of∞ l) hx
            · right
              simpa [of_f] using congrArg (of∞ l) hy
  exact NoZeroDivisors.to_isDomain A∞

-- The total divisibility relation of a valuation ring descends along the directed colimit.
omit [DirectedSystem A (φ · · ·)] in
private theorem directedSystem_directLimit_dvdTotal : @Std.Total A∞ (· ∣ ·) := by
  constructor
  intro x y
  induction x using induction_on with
  | ih i x =>
      induction y using induction_on with
      | ih j y =>
          rcases exists_ge_ge i j with ⟨k, hik, hjk⟩
          rcases ValuationRing.cond (φ i k hik x) (φ j k hjk y) with ⟨z, hz | hz⟩
          · left
            refine ⟨of∞ k z, ?_⟩
            simpa [map_mul, of_f] using congrArg (of∞ k) hz.symm
          · right
            refine ⟨of∞ k z, ?_⟩
            simpa [map_mul, of_f] using congrArg (of∞ k) hz.symm

/-- Lemma 10.50.6: the direct limit of a directed system of valuation rings over a directed set is
again a valuation ring. -/
instance directedSystem_directLimit_valuationRing :
    ValuationRing A∞ :=
  ValuationRing.iff_dvd_total.mpr (directedSystem_directLimit_dvdTotal A φ)

end
