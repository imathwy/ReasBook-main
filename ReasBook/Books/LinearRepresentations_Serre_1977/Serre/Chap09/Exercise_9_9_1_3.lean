import LinearRepresentations_Serre_1977.Serre.Chap09.Exercise_9_9_1_3.FiniteSetReindexing
import LinearRepresentations_Serre_1977.Serre.Chap09.Exercise_9_9_1_3.SymmetricExteriorProduct
import LinearRepresentations_Serre_1977.Serre.Chap09.Exercise_9_9_1_3.SymmetricAdamsExponential

open scoped Representation

noncomputable section

universe u v

namespace Representation

open PowerSeries

section

variable {k : Type} [Field k]
variable {G : Type u} [Monoid G]
variable {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Exercise 9-9.1-3: evaluating the symmetric-power character series at `s` gives the inverse
of the basis-free polynomial `((ρ s).charpoly.reverse : k[T]) = det(1 - ρ(s) T)`. -/
theorem symmetricPowerCharacterSeries_eval_eq_det_inv
    (ρ : Representation k G V) (s : G) :
    PowerSeries.map (Pi.evalRingHom _ s) σ_T(ρ) =
      (((ρ s).charpoly.reverse : Polynomial k) : PowerSeries k)⁻¹ :=
  -- Route correction: the remaining source-faithful work lives in the imported
  -- `SymmetricExteriorProduct` support file, not in this public wrapper; the new split-model
  -- transport plus quotient-trace transport there now reduce the live gap to the restriction-side
  -- trace of the first filtration piece.
  symmetricPowerCharacterSeries_eval_eq_det_inv_aux (ρ := ρ) s

/-- Evaluating the exterior-power character series at `s` gives the determinant
`det(1 + ρ(s) T)`, encoded basis-freely as `(-ρ s).charpoly.reverse`. -/
theorem exteriorPowerCharacterSeries_eval_eq_det
    (ρ : Representation k G V) (s : G) :
    PowerSeries.map (Pi.evalRingHom _ s) λ_T(ρ) =
      (((-ρ s).charpoly.reverse : Polynomial k) : PowerSeries k) :=
  exteriorPowerCharacterSeries_eval_eq_det_aux (ρ := ρ) s

end

section

variable {k : Type} [Field k] [Algebra ℚ k]
variable {G : Type u} [Group G]
variable {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The symmetric-power generating series is the exponential of the Adams-operation series. -/
theorem symmetricPowerCharacterSeries_eq_exp_subst (ρ : Representation k G V) :
    σ_T(ρ) =
      (exp (G → k)).subst (psiGeneratingSeries ρ.character) :=
  symmetricPowerCharacterSeries_eq_exp_subst_aux (ρ := ρ)

/-- The exterior-power generating series is the exponential of the alternating Adams-operation
series. -/
theorem exteriorPowerCharacterSeries_eq_exp_subst (ρ : Representation k G V) :
    λ_T(ρ) =
      (exp (G → k)).subst (alternatingPsiGeneratingSeries ρ.character) :=
  exteriorPowerCharacterSeries_eq_exp_subst_aux (ρ := ρ)

/-- The symmetric-power characters satisfy the Newton-style recursion
`n χ_σ^n = ∑_{k=1}^n Ψ^k(χ) χ_σ^{n-k}`. -/
theorem nthSymmetricPowerCharacter_recurrence (ρ : Representation k G V) (n : ℕ+) :
    (n : k) • (ρ.nthSymmetricPower n).character =
      Finset.sum (Finset.Icc 1 n) fun m ↦
        Ψ^m(ρ.character) * (ρ.nthSymmetricPower ((n : ℕ) - m)).character :=
  by
    -- Differentiate the symmetric exponential identity and read off the coefficient of degree
    -- `n - 1`.
    have hmap : Finset.Icc 1 n = (Finset.range n).map ⟨Nat.succPNat, Nat.succPNat_injective⟩ := by
      -- The positive summation range is the successor image of `range n`.
      simpa using pnat_Icc_one_eq_map_range n
    ext s
    rw [hmap, Finset.sum_map]
    simp only [Pi.mul_apply, Finset.sum_apply]
    have hcoeff :=
      congrArg (PowerSeries.coeff n.natPred) (derivative_symmetricPowerCharacterSeries ρ)
    rw [PowerSeries.coeff_derivative, coeff_symmetricPowerCharacterSeries, PowerSeries.coeff_mul]
      at hcoeff
    simp only [coeff_derivative_psiGeneratingSeries] at hcoeff
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
          -- Reindex by the predecessor `x` and put the Adams term first to match the statement.
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hsub : n.natPred - x = (n : ℕ) - (x + 1) := by
            omega
          rw [hsub, mul_comm]

/-- The exterior-power characters satisfy the alternating Newton-style recursion
`n χ_λ^n = ∑_{k=1}^n (-1)^(k-1) Ψ^k(χ) χ_λ^{n-k}`. -/
theorem nthExteriorPowerCharacter_recurrence (ρ : Representation k G V) (n : ℕ+) :
    (n : k) • (ρ.nthExteriorPower n).character =
      Finset.sum (Finset.Icc 1 n) fun m ↦
        (((-1 : k) ^ ((m : ℕ) - 1)) • Ψ^m(ρ.character)) *
          (ρ.nthExteriorPower ((n : ℕ) - m)).character :=
  by
    -- Reindex the differentiated alternating exponential identity by positive integers.
    have hmap : Finset.Icc 1 n = (Finset.range n).map ⟨Nat.succPNat, Nat.succPNat_injective⟩ := by
      simpa using pnat_Icc_one_eq_map_range n
    ext s
    rw [hmap, Finset.sum_map]
    simp only [Pi.mul_apply, Finset.sum_apply]
    have hcoeff :=
      congrArg (PowerSeries.coeff n.natPred) (derivative_exteriorPowerCharacterSeries ρ)
    rw [PowerSeries.coeff_derivative, coeff_exteriorPowerCharacterSeries, PowerSeries.coeff_mul]
      at hcoeff
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
          -- Reindex from predecessors to positive indices and move the signed Adams factor first.
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hsub : n.natPred - x = (n : ℕ) - (x + 1) := by
            omega
          simp only [Pi.mul_apply]
          rw [hsub]
          ac_rfl

end

end Representation
