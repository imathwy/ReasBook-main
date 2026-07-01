import Mathlib
import stacks_project.Chap10.Definition_10_161_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

/-
Domain triage: this file is in the commutative algebra of Japanese (`N-2`) domains in positive
characteristic, with the source test family restricted to finite purely inseparable fraction-field
extensions.

Owner abstractions sampled for this item:
- `IsN2Ring`, the source-facing owner from `Definition_10_161_1`;
- `IsN2Ring.integralClosure_finite_of_finiteDimensional`, the arbitrary-universe bridge theorem
  for finite normalization in finite fraction-field extensions;
- `IsIntegralClosure.finite`, recalled in `Lemma_10_161_8` for the separable step;
- `IsIntegralClosure.trans`, from `Lemma_10_36_16`, for closure-of-closure transitivity.

This file is `source-facing`: the textbook item is a characteristic-`p` test criterion for the
existing owner `IsN2Ring`, not a new owner. The primitive data are the Noetherian domain `R`, the
positive characteristic prime `p`, and the family of finite purely inseparable extensions of
`FractionRing R`. Finiteness of integral closures is derived API from `IsN2Ring` and the sampled
integral-closure owners, so no extra wrapper predicate should be introduced here.
-/
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable (p : ℕ) [Fact p.Prime] [CharP (FractionRing R) p]

-- Proof sketch: the forward implication is immediate by restricting the `N-2` finiteness
-- condition to finite purely inseparable extensions. For the converse, given a finite extension
-- `L / FractionRing R`, choose a finite normal extension `M / FractionRing R` containing `L`,
-- decompose `M` into a purely inseparable extension over its separable part, apply the hypothesis
-- to the purely inseparable step and Lemma `10.161.8` to the separable step, then combine
-- finiteness by transitivity and identify the iterated integral closure with the one-step
-- integral closure via Lemma `10.36.16`.
/-- Lemma 10.161.12: for a Noetherian domain whose fraction field has characteristic `p > 0`, the
`N-2` condition is equivalent to requiring finite integral closure only for finite purely
inseparable extensions of the fraction field. -/
theorem isN2Ring_iff_integralClosure_finite_for_finite_purelyInseparable_extensions
    :
    IsN2Ring R ↔
      ∀ (L : Type v) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
        [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
        [IsPurelyInseparable (FractionRing R) L],
        Module.Finite R (integralClosure R L) := by
  constructor
  · intro hR L _ _ _ _ _ _
    letI : IsN2Ring R := hR
    exact IsN2Ring.integralClosure_finite_of_finiteDimensional L
  · intro hpure
    exact IsN2Ring.mk fun L ↦ by
      sorry

end
