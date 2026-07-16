import LinearRepresentations_Serre_1977.Serre.Chap09.Exercise_9_9_1_3.SymmetricAdamsExponential

open scoped Representation

noncomputable section

universe u v w

namespace Representation

open PowerSeries

section

variable {k : Type} [Field k] [Algebra ℚ k]
variable {G : Type u} [Group G]
variable {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

local instance : CharZero k := algebraRat.charZero (R := k)

theorem nthSymmetricPowerCharacter_recurrence_aux (ρ : Representation k G V) (n : ℕ+) :
    (n : k) • (ρ.nthSymmetricPower n).character =
      Finset.sum (Finset.Icc 1 n) fun m ↦
        Ψ^m(ρ.character) * (ρ.nthSymmetricPower ((n : ℕ) - m)).character := by
  -- Differentiate the symmetric exponential identity and read off the coefficient of degree
  -- `n - 1`.
  have hmap : Finset.Icc 1 n = (Finset.range n).map ⟨Nat.succPNat, Nat.succPNat_injective⟩ := by
    -- The positive summation range is the successor image of `range n`.
    simpa using pnat_Icc_one_eq_map_range n
  ext s
  rw [hmap, Finset.sum_map]
  simp only [Pi.mul_apply, Finset.sum_apply]
  have hcoeff := congrArg (PowerSeries.coeff n.natPred) (derivative_symmetricPowerCharacterSeries ρ)
  rw [PowerSeries.coeff_derivative, coeff_symmetricPowerCharacterSeries, PowerSeries.coeff_mul] at hcoeff
  simp [coeff_derivative_psiGeneratingSeries] at hcoeff
  have hs := congrFun hcoeff s
  have hnat : (n : ℕ) = n.natPred + 1 := by
    exact (PNat.natPred_add_one n).symm
  have hcast' : ((n.natPred : k) + 1) = (n : k) := by
    rw [← Nat.cast_one]
    rw [← Nat.cast_add]
    rw [PNat.natPred_add_one]
  have hsCoeff :
      (n : k) * (ρ.nthSymmetricPower (n.natPred + 1)).character s =
        ∑ x ∈ Finset.range ↑n, (ρ.nthSymmetricPower (n.natPred - x)).character s *
          Ψ^x.succPNat(ρ.character) s := by
    calc
      (n : k) * (ρ.nthSymmetricPower (n.natPred + 1)).character s
          = ((n.natPred : k) + 1) * (ρ.nthSymmetricPower (n.natPred + 1)).character s := by
            rw [hcast']
      _ = ∑ x ∈ Finset.range ↑n, (ρ.nthSymmetricPower (n.natPred - x)).character s *
            Ψ^x.succPNat(ρ.character) s := by
          simpa [Finset.Nat.antidiagonal_eq_map', mul_comm] using hs
  calc
    (n : k) * (ρ.nthSymmetricPower n).character s
        = (n : k) * (ρ.nthSymmetricPower (n.natPred + 1)).character s := by
          rw [hnat]
    _ = ∑ x ∈ Finset.range ↑n, (ρ.nthSymmetricPower (n.natPred - x)).character s *
          Ψ^x.succPNat(ρ.character) s := by
        exact hsCoeff
    _ = ∑ x ∈ Finset.range ↑n, Ψ^x.succPNat(ρ.character) s *
          (ρ.nthSymmetricPower (↑n - (x + 1))).character s := by
        -- The range index `x` corresponds to the positive index `x + 1`, and commutativity lets
        -- us place the Adams term first to match the statement.
        refine Finset.sum_congr rfl ?_
        intro x hx
        have hxlt : x < n := Finset.mem_range.mp hx
        have hn : n.natPred + 1 = (n : ℕ) := by
          exact PNat.natPred_add_one n
        have hsub : n.natPred - x = (n : ℕ) - (x + 1) := by
          omega
        rw [hsub, mul_comm]

/-- The exterior-power characters satisfy the alternating Newton-style recursion
`n χ_λ^n = ∑_{k=1}^n (-1)^(k-1) Ψ^k(χ) χ_λ^{n-k}`. -/
theorem nthExteriorPowerCharacter_recurrence_aux (ρ : Representation k G V) (n : ℕ+) :
    (n : k) • (ρ.nthExteriorPower n).character =
      Finset.sum (Finset.Icc 1 n) fun m ↦
        (((-1 : k) ^ ((m : ℕ) - 1)) • Ψ^m(ρ.character)) *
          (ρ.nthExteriorPower ((n : ℕ) - m)).character := by
  -- The positive summation range is again the successor image of `range n`, so we can reindex
  -- the coefficient formula by predecessors.
  have hmap : Finset.Icc 1 n = (Finset.range n).map ⟨Nat.succPNat, Nat.succPNat_injective⟩ := by
    simpa using pnat_Icc_one_eq_map_range n
  ext s
  rw [hmap, Finset.sum_map]
  simp only [Pi.mul_apply, Finset.sum_apply]
  -- Read off the coefficient of degree `n - 1` in the differentiated alternating exponential
  -- identity.
  have hcoeff :=
    congrArg (PowerSeries.coeff n.natPred) (derivative_exteriorPowerCharacterSeries ρ)
  rw [PowerSeries.coeff_derivative, coeff_exteriorPowerCharacterSeries,
    PowerSeries.coeff_mul] at hcoeff
  simp only [coeff_derivative_alternatingPsiGeneratingSeries,
    coeff_exteriorPowerCharacterSeries] at hcoeff
  have hs := congrFun hcoeff s
  have hnat : (n : ℕ) = n.natPred + 1 := by
    exact (PNat.natPred_add_one n).symm
  have hcast' : ((n.natPred : k) + 1) = (n : k) := by
    rw [← Nat.cast_one]
    rw [← Nat.cast_add]
    rw [PNat.natPred_add_one]
  have hsCoeff :
      (n : k) * (ρ.nthExteriorPower (n.natPred + 1)).character s =
        ∑ x ∈ Finset.range ↑n, (ρ.nthExteriorPower (n.natPred - x)).character s *
          (((-1 : k) ^ x) • Ψ^x.succPNat(ρ.character)) s := by
    calc
      (n : k) * (ρ.nthExteriorPower (n.natPred + 1)).character s
          = ((n.natPred : k) + 1) * (ρ.nthExteriorPower (n.natPred + 1)).character s := by
            rw [hcast']
      _ = ∑ x ∈ Finset.range ↑n, (ρ.nthExteriorPower (n.natPred - x)).character s *
            (((-1 : k) ^ x) • Ψ^x.succPNat(ρ.character)) s := by
          simpa [Finset.Nat.antidiagonal_eq_map', mul_assoc, mul_left_comm, mul_comm] using hs
  calc
    (n : k) * (ρ.nthExteriorPower n).character s
        = (n : k) * (ρ.nthExteriorPower (n.natPred + 1)).character s := by
          rw [hnat]
    _ = ∑ x ∈ Finset.range ↑n, (ρ.nthExteriorPower (n.natPred - x)).character s *
          (((-1 : k) ^ x) • Ψ^x.succPNat(ρ.character)) s := by
        exact hsCoeff
    _ = ∑ x ∈ Finset.range ↑n, ((((-1 : k) ^ x) • Ψ^x.succPNat(ρ.character)) *
          (ρ.nthExteriorPower (↑n - (x + 1))).character) s := by
        -- Reindex from the predecessor `x` back to the positive integer `x + 1`; this also puts
        -- the signed Adams factor first to match the statement.
        refine Finset.sum_congr rfl ?_
        intro x hx
        have hsub : n.natPred - x = (n : ℕ) - (x + 1) := by
          omega
        simp only [Pi.mul_apply]
        rw [hsub]
        ac_rfl
end

end Representation
