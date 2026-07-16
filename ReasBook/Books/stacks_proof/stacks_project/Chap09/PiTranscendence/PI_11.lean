import Mathlib
import stacks_proof.stacks_project.Chap09.PiTranscendence.PI_08

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial
open scoped BigOperators

/- Domain-style sampling for PI-11:
- primary domain: denominator clearing for the canonical subset-sum `Polynomial.aeval` expression
  attached to a root enumeration of `P`;
- sampled owner declarations:
  `exists_uniform_leadingCoeff_power_denominator_control_for_subset_sum_aeval`,
  `Polynomial.aeval`,
  `Polynomial.leadingCoeff`,
  `nonzeroSumSubsets`;
- best owner abstraction: the denominator-clearing theorem from `PI_08`; `PI_11` should only add
  the arithmetic packaging needed for the source-facing denominator `D_p` and integer candidate
  `Z_p`, together with the bridge `D_p = P.leadingCoeff ^ e`;
- primitive data: the denominator `D_p`, the cleared subset-sum integer `Y_p`, and the integer
  candidate `Z_p`;
- derived API: the bridge exponent `e`, the relation `(D_p : ℂ) * T = Y_p`, and the resulting
  complex equality for `Z_p`.

Source/core/bridge triage:
- `source-facing`: the final integer-candidate statement for `Z_p`;
- `core/canonical`: the denominator-clearing owner theorem from `PI_08`;
- `bridge/view`: the explicit `D_p`, `Y_p` witnesses and arithmetic relation defining `Z_p`;
- `layer`: the first theorem is a `bridge/view` companion derived from `PI_08`, and the second
  theorem is the `source-facing` corollary used downstream.
-/

section

variable {P : ℤ[X]} {n : ℕ} {a : Fin n → ℂ}

/-- A companion form of the PI-11 integer candidate statement that keeps the auxiliary integer
`Y_p` and the denominator integer `D_p` explicit, so the later congruence argument can use the
formula `Z_p = D_p * C * n_p + p * Y_p` directly while still recording that
`D_p = P.leadingCoeff ^ e`. -/
theorem exists_integer_candidate_data_of_nonzero_subset_sums
    (ha : (List.ofFn a : Multiset ℂ) = P.aroots ℂ)
    (C n_p p : ℤ) (g_p : ℤ[X]) :
    ∃ D_p Y_p Z_p : ℤ, ∃ e : ℕ,
      let T : ℂ := ∑ s ∈ nonzeroSumSubsets a, aeval (s.sum a) g_p
      D_p = P.leadingCoeff ^ e ∧
      D_p ≠ 0 ∧
      ((D_p : ℂ) * T = (Y_p : ℂ)) ∧
      Z_p = D_p * C * n_p + p * Y_p := by
  obtain ⟨_, hden⟩ := exists_uniform_leadingCoeff_power_denominator_control_for_subset_sum_aeval ha
  obtain ⟨Y_p, e, hne, hY_p, _⟩ := hden g_p
  refine ⟨P.leadingCoeff ^ e, Y_p, P.leadingCoeff ^ e * C * n_p + p * Y_p, e, ?_⟩
  dsimp
  refine ⟨rfl, hne, ?_, rfl⟩
  simpa using hY_p

/-- Lemma PI-11: for every polynomial `g_p : ℤ[X]` to which the analytic approximation argument is
applied, one can choose integers `D_p` and `Z_p` and an exponent `e` such that
`D_p = P.leadingCoeff ^ e`, `D_p ≠ 0`, and
`(Z_p : ℂ) = (D_p : ℂ) * ((C : ℂ) * (n_p : ℂ) + (p : ℂ) *
∑ S in nonzeroSumSubsets a, Polynomial.aeval (S.sum a) g_p)`, so the denominator is directly a
named nonzero power of the leading coefficient of the original polynomial `P`. -/
theorem exists_integer_candidate_with_leadingCoeff_power_denominator
    (ha : (List.ofFn a : Multiset ℂ) = P.aroots ℂ)
    (C n_p p : ℤ) (g_p : ℤ[X]) :
    ∃ D_p Z_p : ℤ, ∃ e : ℕ,
      let T : ℂ := ∑ s ∈ nonzeroSumSubsets a, aeval (s.sum a) g_p
      D_p = P.leadingCoeff ^ e ∧
      D_p ≠ 0 ∧
      (Z_p : ℂ) =
        (D_p : ℂ) *
          ((C : ℂ) * (n_p : ℂ) + (p : ℂ) * T) := by
  obtain ⟨D_p, Y_p, Z_p, e, hD_p, hne, hY_p, hZ_p⟩ :=
    exists_integer_candidate_data_of_nonzero_subset_sums ha C n_p p g_p
  let T : ℂ := ∑ s ∈ nonzeroSumSubsets a, aeval (s.sum a) g_p
  have hY_p' : (Y_p : ℂ) = (D_p : ℂ) * T := by
    simpa [T] using hY_p.symm
  refine ⟨D_p, Z_p, e, ?_⟩
  dsimp
  refine ⟨hD_p, hne, ?_⟩
  calc
    (Z_p : ℂ) = ((D_p * C * n_p + p * Y_p : ℤ) : ℂ) := by
      simp [hZ_p]
    _ = (D_p : ℂ) * (C : ℂ) * (n_p : ℂ) + (p : ℂ) * (Y_p : ℂ) := by
      push_cast
      ring
    _ = (D_p : ℂ) * (C : ℂ) * (n_p : ℂ) + (p : ℂ) * ((D_p : ℂ) * T) := by
      rw [hY_p']
    _ = (D_p : ℂ) * ((C : ℂ) * (n_p : ℂ) + (p : ℂ) * T) := by
      ring
    _ = (D_p : ℂ) *
          ((C : ℂ) * (n_p : ℂ) + (p : ℂ) * (∑ s ∈ nonzeroSumSubsets a, aeval (s.sum a) g_p)) := by
      simp [T]

end
