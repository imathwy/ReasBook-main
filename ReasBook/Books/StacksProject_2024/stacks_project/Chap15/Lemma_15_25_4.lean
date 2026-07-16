import Mathlib
import StacksProject_2024.stacks_project.Chap15.Remark_15_25_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

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

/-- Helper for Lemma 15.25.4: if a surjective polynomial cover makes the target algebra
finitely presented as a module over the polynomial ring, then the algebra itself is finitely
presented. -/
theorem algebra_finitePresentation_of_surjective_polynomial_cover
    {A : Type*} [CommRing A] [Algebra R A]
    {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α)
    (hPA :
      let P := MvPolynomial (Fin n) R
      let _ : Module P A := Module.compHom A α.toRingHom
      Module.FinitePresentation P A) :
    Algebra.FinitePresentation R A := by
  let P := MvPolynomial (Fin n) R
  letI : Algebra.FinitePresentation R P := inferInstance
  letI : Algebra P A := α.toAlgebra
  letI : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun r ↦ by
    -- Proof comment: the scalar tower is the one induced by the chosen polynomial cover `α`.
    change algebraMap R A r = α (algebraMap R P r)
    exact (α.commutes r).symm
  letI : Module P A := Module.compHom A α.toRingHom
  letI : Module.FinitePresentation P A := by
    -- Proof comment: interpret the hypothesis as finite presentation for `A` over the chosen
    -- polynomial source ring.
    simpa [P] using hPA
  letI : Algebra.FinitePresentation P A := by
    -- Proof comment: a commutative algebra that is finitely presented as a module is already a
    -- finitely presented algebra over the same base ring.
    infer_instance
  -- Proof comment: combine the finitely presented polynomial source with the finitely presented
  -- algebra map `P → A`.
  exact Algebra.FinitePresentation.trans R P A

/-- Helper for Lemma 15.25.4: choose a single weighted polynomial cover whose variables map to
homogeneous generators of the graded algebra. -/
lemma exists_weighted_polynomial_cover :
    ∃ (n : ℕ) (w : Fin n → ℕ+) (α : MvPolynomial (Fin n) R →ₐ[R] S),
      Function.Surjective α ∧
        (∀ i, α (MvPolynomial.X i) ∈ 𝒜 (w i : ℕ)) ∧
        let _ : Module (MvPolynomial (Fin n) R) S := Module.compHom S α.toRingHom
        Module.Finite (MvPolynomial (Fin n) R) S := sorry

/-- Helper for Lemma 15.25.4: the localized graded algebra is finitely presented over the
localized base ring once the weighted polynomial cover is fixed. -/
lemma localized_graded_algebra_finitePresentation
    {n : ℕ} (w : Fin n → ℕ+) (α : MvPolynomial (Fin n) R →ₐ[R] S)
    (hα : Function.Surjective α) (hX : ∀ i, α (MvPolynomial.X i) ∈ 𝒜 (w i : ℕ)) :
    ∀ p : PrimeSpectrum R,
      Algebra.FinitePresentation (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[R] S) := sorry

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
    Algebra.FinitePresentation R S := by
  -- Proof comment: the source proof now has the expected global skeleton: fix one weighted
  -- polynomial cover and reduce the algebra statement to prime-local finite presentation of the
  -- localized graded algebra along that cover.
  -- TODO: once Lemma `15.25.2` is back in a compilable owner form, apply it here to the local
  -- witnesses coming from one weighted polynomial cover and then descend globally.
  sorry

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
    Module.FinitePresentation S M := by
  -- Proof comment: the source proof reduces the global module statement to globalizing these
  -- prime-local witnesses over a weighted polynomial cover, then descending finite presentation
  -- along the resulting surjective polynomial map.
  -- TODO: after restoring the chapter-local prime-local owner theorem, implement exactly that
  -- reduction and finish with the polynomial-cover descent step.
  sorry

end
