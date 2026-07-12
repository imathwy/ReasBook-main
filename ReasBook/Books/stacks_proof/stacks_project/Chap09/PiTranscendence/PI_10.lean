import Mathlib
import StacksProject_2024.Chap09.PiTranscendence.PI_09

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for PI-10:
- primary domain: finite-sum norm bounds in a normed ring, specialized to the complex exponential
  relation used in the Hermite-Lindemann argument;
- sampled owner declarations:
  `norm_sum_exp_sub_sum_aeval_le`,
  `norm_sum_le`,
  `Finset.sum_le_sum`;
- best owner abstraction: the canonical finite-sum norm bound `norm_sum_le`, already exposed in the
  local source-facing bridge `norm_sum_exp_sub_sum_aeval_le` from `PI_09`;
- primitive data: the relation `(C : ℂ) + ∑ j, Complex.exp (β j) = 0` and the pointwise bounds
  `hβ`;
- derived API: the shifted norm bound for `(C : ℂ) * (n : ℂ) + (p : ℂ) * ∑ j, aeval (β j) g`.

Source/core/bridge triage:
- `source-facing`: the PI-10 inequality below;
- `core/canonical`: `norm_sum_le`;
- `bridge/view`: `norm_sum_exp_sub_sum_aeval_le`, together with the rewrite of the source relation
  into the summed-difference form;
- `layer`: `bridge/view`.
-/

/-- Lemma PI-10: if an integer constant `C` and a finite family `β : Fin m → ℂ` satisfy
`(C : ℂ) + ∑ j, Complex.exp (β j) = 0`, and each term satisfies the approximation bound
`‖(n : ℂ) * Complex.exp (β j) - (p : ℂ) * Polynomial.aeval (β j) g‖ ≤ ε`, then
`‖(C : ℂ) * (n : ℂ) + (p : ℂ) * ∑ j, Polynomial.aeval (β j) g‖ ≤ m * ε`. -/
theorem norm_int_mul_add_sum_aeval_le_of_exp_relation
    (m : ℕ) (C n p : ℤ) (β : Fin m → ℂ) (g : Polynomial ℤ) {ε : ℝ}
    (hC : (C : ℂ) + ∑ j, Complex.exp (β j) = 0)
    (hβ : ∀ j, ‖(n : ℂ) * Complex.exp (β j) - (p : ℂ) * Polynomial.aeval (β j) g‖ ≤ ε) :
    ‖(C : ℂ) * (n : ℂ) + (p : ℂ) * ∑ j, Polynomial.aeval (β j) g‖ ≤ m * ε := by
  have hCn :
      (C : ℂ) * (n : ℂ) = -((n : ℂ) * ∑ j, Complex.exp (β j)) := by
    have hCmul : ((C : ℂ) * (n : ℂ)) + (∑ j, Complex.exp (β j)) * (n : ℂ) = 0 := by
      simpa [add_mul] using congrArg (fun z : ℂ ↦ z * (n : ℂ)) hC
    calc
      (C : ℂ) * (n : ℂ) = -((∑ j, Complex.exp (β j)) * (n : ℂ)) :=
        eq_neg_of_add_eq_zero_left hCmul
      _ = -((n : ℂ) * ∑ j, Complex.exp (β j)) := by rw [mul_comm]
  calc
    ‖(C : ℂ) * (n : ℂ) + (p : ℂ) * ∑ j, Polynomial.aeval (β j) g‖
        = ‖-((n : ℂ) * ∑ j, Complex.exp (β j) -
            (p : ℂ) * ∑ j, Polynomial.aeval (β j) g)‖ := by
            congr 1
            rw [hCn]
            ring
    _ = ‖(n : ℂ) * ∑ j, Complex.exp (β j) - (p : ℂ) * ∑ j, Polynomial.aeval (β j) g‖ := by
          simpa using
            norm_neg ((n : ℂ) * ∑ j, Complex.exp (β j) -
              (p : ℂ) * ∑ j, Polynomial.aeval (β j) g)
    _ ≤ m * ε := norm_sum_exp_sub_sum_aeval_le m β n p g hβ
