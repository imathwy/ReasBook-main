import StacksProject_2024.Chap15.Lemma_15_25_2
import StacksProject_2024.Chap15.Lemma_15_25_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

/- Domain triage:
* source-facing: graded finite-presentation descent for a flat finite-type graded algebra and its
  finite graded modules;
* core/canonical owners: `Algebra.FinitePresentation` and `Module.FinitePresentation`;
* bridge/view layer in this file: the graded hypotheses are source-facing data, while the actual
  finite-presentation conclusions are obtained through the chapter owners
  `finitePresentation_of_flat_of_finiteType_of_localizedAtPrimes_finitePresentation` and
  `finitePresentation_of_flat_of_localized_finitePresentation` /
  `finitePresentation_of_local_flat_finite_weighted_graded_mvPolynomial_module`;
* primitive grading data: `GradedAlgebra 𝒜`, `DirectSum.Decomposition ℳ`, and
  `SetLike.GradedSMul 𝒜 ℳ`;
* derived API: only the two finite-presentation conclusions below.

Source/core/bridge triage:
* `source-facing`: the two graded flat-descent theorems below;
* `core/canonical`: `Algebra.FinitePresentation` and `Module.FinitePresentation`;
* `bridge/view`: the local weighted-polynomial criterion from Lemma `15.25.3` and the global
  prime-local descent owners from Lemmas `15.25.1` and `15.25.2`.
-/

local instance : AddAction ℕ ℤ := AddAction.compHom ℤ Int.ofNatHom.toAddMonoidHom

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]
variable [Algebra.FiniteType R S] [Module.Finite R (𝒜 0)] [Module.Flat R S]
variable (hdetect : primeLocalizationsDetectEquality R)

-- Proof sketch: choose finitely many homogeneous generators of `S` over the finite `R`-algebra
-- `S₀ = 𝒜 0`, reduce to a finite graded module over a weighted polynomial ring over `R`, apply the
-- local weighted criterion of Lemma `15.25.3` after localizing at each prime of `R`, and then use
-- the canonical algebra-presentation descent theorem
-- `finitePresentation_of_flat_of_finiteType_of_localizedAtPrimes_finitePresentation`
-- from Lemma `15.25.2`.
/-- Lemma 15.25.4 (1): a graded `R`-algebra `S = ⨁_{n ≥ 0} Sₙ` that is of finite type over `R`,
whose degree-zero part `S₀` is finite over `R`, and for which a finite family of prime
localizations detects equality in `R`, is finitely presented over `R` if `S` is flat over
`R`. -/
theorem graded_algebra_finitePresentation_of_flat :
    Algebra.FinitePresentation R S := sorry

variable {M : Type w} [AddCommMonoid M] [Module S M] [Module R M] [IsScalarTower R S M]
variable (ℳ : ℤ → Submodule R M)
variable [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

-- Proof sketch: first apply part (1) to make `S` a finitely presented `R`-algebra. Then choose
-- homogeneous generators of the finite graded `S`-module `M`, reduce to the weighted polynomial
-- case handled locally by Lemma `15.25.3`, and descend the resulting local finite-presentation
-- statements through the chapter owner theorem `finitePresentation_of_flat_of_localized_finitePresentation`
-- from Lemma `15.25.1`. The source-facing statement is a graded-module finite-presentation claim,
-- so its public surface should stay at the canonical owner layer
-- `AddCommMonoid`/`Module.Finite`/`Module.Flat`/`Module.FinitePresentation` already used by the
-- weighted local theorem and the direct downstream valuation-ring application.
/-- Lemma 15.25.4 (2): if `M = ⨁_{d ∈ ℤ} M_d` is a graded `S`-module that is finite over the
graded `R`-algebra `S`, flat over `R`, and `S₀` is finite over `R` while finitely many prime
localizations detect equality in `R`, then `M` is finitely presented as an `S`-module. -/
theorem graded_module_finitePresentation_of_flat [Module.Flat R M] [Module.Finite S M] :
    Module.FinitePresentation S M := sorry

end
