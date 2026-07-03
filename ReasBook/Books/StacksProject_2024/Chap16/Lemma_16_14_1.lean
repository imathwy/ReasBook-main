import Mathlib
import StacksProject_2024.Chap10.Lemma_10_166_5
import StacksProject_2024.Chap15.Definition_15_50_1
import StacksProject_2024.Chap15.Lemma_15_50_14
import StacksProject_2024.Chap15.Lemma_15_50_15
import StacksProject_2024.Chap15.Lemma_15_51_7

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open RingPairCat

universe u

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A)

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

/- Domain-style sampling:
- primary domain: Artin approximation for Noetherian henselian pairs, organized around the owner
  predicates `HenselianRing A I`, `IsRegularRingMap A (AdicCompletion I A)`, and the chosen
  pair-henselization owner API `henselizationRing (pairOfIdeal I)` and
  `(henselizationPair (pairOfIdeal I)).ideal`;
- sampled owner declarations in this domain:
  `IsRegularRingMap`,
  `IsGRing`,
  `(inferInstance : (algebraMap A (AdicCompletion I A)).IsRegularRingMap)`,
  `henselizationRing`,
  `henselizationPair`,
  `RingPairCat.pairHenselization_isGRing`;
- best owner abstraction: the source-facing lemma should expose the textbook alternatives on the
  henselian pair, while the regularity of `A → A^` remains the core/canonical bridge hypothesis;
- primitive vs. derived API: the approximation conclusion is source-facing, the regularity of the
  completion map is the core owner input, and both `IsGRing A` and the chosen pair-henselization
  of a `G`-ring are derived bridge hypotheses already absorbed upstream by Chapter 15. For the
  henselization case, the ring and ideal are derived from the canonical pair-henselization owners
  `henselizationRing (pairOfIdeal J)` and `(henselizationPair (pairOfIdeal J)).ideal`, so the
  theorem surface should use those owners directly rather than a parallel local wrapper.

Source/core/bridge triage:
- `source-facing`: the three approximation statements matching Stacks Lemma `16.14.1`, namely the
  regular-completion, `G`-ring, and henselization-of-a-`G`-ring cases;
- `core/canonical`: `HenselianRing A I` and `IsRegularRingMap A (AdicCompletion I A)`;
- `bridge/view`: the Chapter 15 owner instance
  `(inferInstance : (algebraMap A (AdicCompletion I A)).IsRegularRingMap)` and
  `RingPairCat.pairHenselization_isGRing`, which convert source alternatives to the canonical
  regularity hypothesis.
-/

-- Proof sketch: first reduce the source alternatives to the case where `A → A^` is a regular ring
-- map. Then apply Popescu to factor the completed solution through a smooth `A`-algebra carrying
-- an exact solution, lift the induced section modulo `I^N` along an étale neighborhood, and use
-- the henselian pair property to retract that neighborhood back to `A`.
/-- Lemma 16.14.1, regular-completion case: for a Noetherian henselian pair `(A, I)`, if the
completion map `A → A^` is regular, then every finite polynomial system over `A` with a solution
in the `I`-adic completion has, for each `N ≥ 1`, a solution in `A` congruent to the completed
solution modulo `I^N`. -/
theorem exists_polynomial_solution_of_adicCompletion_solution_of_isRegularRingMap
    [HenselianRing A I]
    (hreg : (algebraMap A (AdicCompletion I A)).IsRegularRingMap)
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) A)
    (aHat : Fin n → AdicCompletion I A)
    (hroots : ∀ j, MvPolynomial.aeval aHat (f j) = 0) (N : ℕ+) :
    ∃ a : Fin n → A,
      (∀ i,
        AdicCompletion.evalₐ I (N : ℕ) (aHat i) =
          Ideal.Quotient.mk (I ^ (N : ℕ)) (a i)) ∧
      ∀ j, MvPolynomial.eval a (f j) = 0 := sorry

/-- Lemma 16.14.1, `G`-ring case: if `A` is a `G`-ring, then the canonical regularity theorem for
`A → A^` reduces the approximation statement to the regular-completion case. -/
theorem exists_polynomial_solution_of_adicCompletion_solution
    [HenselianRing A I] [IsGRing A]
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) A)
    (aHat : Fin n → AdicCompletion I A)
    (hroots : ∀ j, MvPolynomial.aeval aHat (f j) = 0) (N : ℕ+) :
    ∃ a : Fin n → A,
      (∀ i,
        AdicCompletion.evalₐ I (N : ℕ) (aHat i) =
          Ideal.Quotient.mk (I ^ (N : ℕ)) (a i)) ∧
      ∀ j, MvPolynomial.eval a (f j) = 0 := by
  let hreg : (algebraMap A (AdicCompletion I A)).IsRegularRingMap := inferInstance
  simpa using
    exists_polynomial_solution_of_adicCompletion_solution_of_isRegularRingMap I
      hreg f aHat hroots N

section

variable {B : Type u} [CommRing B]
variable (J : Ideal B)

/-- Lemma 16.14.1, henselization case: if `(A, I)` is the chosen henselization of a pair
`(B, J)` with `B` a `G`-ring, then the upstream `G`-ring instance on the henselization
reduces the approximation statement to the `G`-ring case. -/
theorem exists_polynomial_solution_of_adicCompletion_solution_of_pairHenselization
    [IsGRing B]
    {m n : ℕ}
    (f : Fin m → MvPolynomial (Fin n) (henselizationRing (pairOfIdeal J)))
    (aHat : Fin n → AdicCompletion (henselizationPair (pairOfIdeal J)).ideal
      (henselizationRing (pairOfIdeal J)))
    (hroots : ∀ j, MvPolynomial.aeval aHat (f j) = 0)
    (N : ℕ+) :
    ∃ a : Fin n → henselizationRing (pairOfIdeal J),
      (∀ i,
        AdicCompletion.evalₐ (henselizationPair (pairOfIdeal J)).ideal (N : ℕ) (aHat i) =
          Ideal.Quotient.mk (((henselizationPair (pairOfIdeal J)).ideal) ^ (N : ℕ)) (a i)) ∧
      ∀ j, MvPolynomial.eval a (f j) = 0 := by
  let _ :
      HenselianRing (henselizationRing (pairOfIdeal J)) (henselizationPair (pairOfIdeal J)).ideal :=
    (henselization (pairOfIdeal J)).property
  simpa using
    exists_polynomial_solution_of_adicCompletion_solution
      ((henselizationPair (pairOfIdeal J)).ideal) f aHat hroots N

end

end
