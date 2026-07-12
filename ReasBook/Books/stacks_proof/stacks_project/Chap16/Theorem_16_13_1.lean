import Mathlib
import StacksProject_2024.Chap16.Lemma_16_14_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Algebra IsLocalRing
open MvPolynomial

section

variable {R : Type u} [CommRing R] [HenselianLocalRing R] [IsNoetherianRing R]

local notation "Rhat" => AdicCompletion (maximalIdeal R) R

/-- Helper for Theorem 16.13.1: equality after reduction modulo a positive maximal-ideal power
forces the corresponding difference in the completion to lie in the extended ideal power. -/
private lemma difference_mem_completionIdealPow_of_stageEq
    {N : ℕ+} {x : Rhat} {r : R}
    (hstage :
      AdicCompletion.evalₐ (maximalIdeal R) (N : ℕ) x =
        Ideal.Quotient.mk ((maximalIdeal R) ^ (N : ℕ)) r) :
    x - algebraMap R Rhat r ∈
      Ideal.map (algebraMap R Rhat) ((maximalIdeal R) ^ (N : ℕ)) := by
  -- Proof comment: rewrite the stage equality as vanishing of the reduced difference and then use
  -- the standard description of the kernel of the completion-stage map.
  have hker :
      x - algebraMap R Rhat r ∈
        RingHom.ker (AdicCompletion.evalₐ (maximalIdeal R) (N : ℕ)) := by
    rw [RingHom.mem_ker, map_sub, AdicCompletion.evalₐ_of]
    simpa [hstage]
  have hfg : (maximalIdeal R).FG := Ideal.fg_of_isNoetherianRing (maximalIdeal R)
  simpa [completionIdeal_pow_eq_ker_evalₐ (I := maximalIdeal R) hfg (N : ℕ)] using hker

-- Proof sketch: apply the general henselian-pair approximation theorem from Lemma `16.14.1` to
-- the pair `(R, maximalIdeal R)`. For positive `N`, convert the resulting equality modulo
-- `(maximalIdeal R)^N` into membership in the extended completion ideal. For `N = 0`, the target
-- ideal is `⊤`, so any exact solution suffices.
/-- Theorem 16.13.1: if `R` is a Noetherian henselian local ring whose completion map
`R → AdicCompletion (maximalIdeal R) R` has geometrically regular formal fibers, then every
solution in the maximal-ideal adic completion of a finite system of polynomial equations over `R`
is congruent modulo `(maximalIdeal R)^N` to a solution in `R`. -/
@[stacks 07QY]
theorem exists_solution_in_ring_of_adicCompletion_solution
    (hRhat : (algebraMap R Rhat).IsRegularRingMap)
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) R) (a : Fin n → Rhat)
    (ha : ∀ j, aeval a (f j) = 0) (N : ℕ) :
    ∃ b : Fin n → R,
      (∀ j, eval b (f j) = 0) ∧
        ∀ i, a i - algebraMap R Rhat (b i) ∈
          Ideal.map (algebraMap R Rhat) ((maximalIdeal R) ^ N) := by
  classical
  cases N with
  | zero =>
      obtain ⟨b, -, hbsol⟩ :=
        exists_polynomial_solution_of_adicCompletion_solution_of_isRegularRingMap
          (I := maximalIdeal R) hRhat f a ha (1 : ℕ+)
      refine ⟨b, hbsol, ?_⟩
      intro i
      simpa [pow_zero] using
        (show a i - algebraMap R Rhat (b i) ∈ (⊤ : Ideal Rhat) from by simp)
  | succ k =>
      obtain ⟨b, hstage, hbsol⟩ :=
        exists_polynomial_solution_of_adicCompletion_solution_of_isRegularRingMap
          (I := maximalIdeal R) hRhat f a ha ⟨Nat.succ k, Nat.succ_pos _⟩
      refine ⟨b, hbsol, ?_⟩
      intro i
      simpa using
        difference_mem_completionIdealPow_of_stageEq
          (R := R) (N := ⟨Nat.succ k, Nat.succ_pos _⟩) (x := a i) (r := b i) (hstage i)

end
