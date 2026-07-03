import Mathlib
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.GradedModule
import Mathlib.Data.PNat.Notation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Noetherian.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_25_1 (from Chap15) -/
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u w

section

variable {R : Type u} [CommRing R]
variable (n : ℕ)
variable {M : Type w} [AddCommGroup M]
variable [Module (MvPolynomial (Fin n) R) M] [Module R M]
variable [IsScalarTower R (MvPolynomial (Fin n) R) M]
variable [Module.Finite (MvPolynomial (Fin n) R) M] [Module.Flat R M]

/- Domain-style sampling:
* primary domain: finite-presentation descent for flat finite modules over polynomial algebras from
  prime-local finite-presentation data;
* sampled owner declarations:
  - `Module.FinitePresentation`,
  - `module_finitePresentation_of_localizationAway`,
  - `primeLocalizationsDetectEquality`,
  - `MvPolynomial.algebraTensorAlgEquiv`,
  - the chapter-local weighted graded specialization
    `finitePresentation_of_local_flat_finite_weighted_graded_mvPolynomial_module`;
* best owner abstraction: the canonical predicate
  `Module.FinitePresentation (MvPolynomial (Fin n) R) M`;
* primitive data: the polynomial-module structure on `M`, finite generation over
  `MvPolynomial (Fin n) R`, flatness over `R`, and the prime-local tensor-product base changes
  `((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] M`;
* derived API: only the global finite-presentation conclusion.

Source/core/bridge triage:
* `source-facing`: the descent theorem below;
* `core/canonical`: `Module.FinitePresentation` together with the localization owners behind
  tensor-product base change;
* `bridge/view`: `MvPolynomial.algebraTensorAlgEquiv`, identifying the tensor-base-change algebra
  `Localization.AtPrime p.asIdeal ⊗[R] MvPolynomial (Fin n) R` with the textbook polynomial ring
  `MvPolynomial (Fin n) (Localization.AtPrime p.asIdeal)`.
-/

-- Proof sketch: choose a finite presentation of `M` by a finite free `S`-module and let `K` be the
-- kernel. Use the local finite-presentation hypotheses to find a finitely generated submodule of
-- `K` that agrees with `K` after passing to the prime-local tensor-product base changes over
-- `Localization.AtPrime p.asIdeal ⊗[R] MvPolynomial (Fin n) R`, equivalently over
-- `MvPolynomial (Fin n) (Localization.AtPrime p.asIdeal)`, at the distinguished finitely
-- many primes and at the prime under a chosen prime of `S`. Replace `M` by the resulting
-- finite-presentation quotient,
-- use openness of flatness to preserve `R`-flatness after inverting one element of `S`, and then
-- apply injectivity of `R → ∏ R_{p_j}` together with flatness to deduce the quotient map is an
-- isomorphism after localizing away from that element. Conclude by the standard local criterion for
-- finite presentation.
/-- Lemma 15.25.1: let `S = R[x₁, …, xₙ]` and let `M` be a finite `S`-module that is flat over
`R` via the restricted scalar action along `R → S`. If there is a finite family of primes of `R`
whose product of localizations detects equality in `R`, and if for every prime `p` of `R` the
canonical tensor-product base change
`((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] M`,
equivalently the textbook localized module over `Rₚ[x₁, …, xₙ]`, is of finite presentation over
`(Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R`, then `M` is of finite
presentation over `S`. -/
theorem finitePresentation_of_flat_of_localized_finitePresentation
    (hdetect : primeLocalizationsDetectEquality R)
    (hloc :
      ∀ p : PrimeSpectrum R,
        Module.FinitePresentation
          ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
          (((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] M)) :
    Module.FinitePresentation (MvPolynomial (Fin n) R) M := sorry

end

/-! ### Lemma_15_25_2 (from Chap15) -/
open scoped TensorProduct
open PrimeSpectrum

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: choose a surjection `MvPolynomial (Fin n) R →ₐ[R] S` from the finite-type
-- hypothesis, view `S` as a finite `MvPolynomial (Fin n) R`-module via this quotient, and apply
-- Lemma `15.25.1` to that module. The localized finite-presentation assumption on
-- `Localization.AtPrime p.asIdeal ⊗[R] S` gives the module-theoretic local finite-presentation
-- hypothesis over `MvPolynomial (Fin n) (Localization.AtPrime p.asIdeal)`, and the conclusion
-- identifies `S` as a finitely presented `R`-algebra.
/-- Lemma 15.25.2: if `R → S` is of finite type, `S` is flat over `R`, a finite family of prime
localizations of `R` detects equality, and for every prime `p` of `R` the localized algebra
`Localization.AtPrime p.asIdeal ⊗[R] S` is of finite presentation over `Localization.AtPrime
p.asIdeal`, then `S` is of finite presentation over `R`. -/
theorem finitePresentation_of_flat_of_finiteType_of_localizedAtPrimes_finitePresentation
    (hdetect : primeLocalizationsDetectEquality R)
    [Algebra.FiniteType R S] [Module.Flat R S]
    (hloc :
      ∀ p : PrimeSpectrum R,
        Algebra.FinitePresentation (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[R] S)) :
    Algebra.FinitePresentation R S := sorry

end

/-! ### Lemma_15_25_3 (from Chap15) -/
universe u v

section

open MvPolynomial

/- Domain-style sampling:
* primary domain: finite-presentation criteria for flat finite modules over weighted-graded
  polynomial rings;
* sampled owner declarations:
  `Module.FinitePresentation`,
  `weightedHomogeneousSubmodule`,
  `DirectSum.Decomposition`,
  `GradedModule.linearEquiv`;
* best owner abstraction: the conclusion is the canonical owner
  `Module.FinitePresentation (MvPolynomial σ R) M`, and the graded-module structure is
  already expressed by mathlib's external owner pair
  `[DirectSum.Decomposition ℳ]` together with
  `[SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun i ↦ (w i : ℤ))) ℳ]`;
* primitive data: the weighted polynomial ring `MvPolynomial σ R` on a finite variable type `σ`,
  the positive weight function `w : σ → ℕ+`, and the `ℤ`-graded module structure `ℳ`;
* derived API: only the finite-presentation conclusion over `MvPolynomial σ R`;
* bridge/view: the source weights are positive naturals, viewed in the chapter's `ℤ`-graded
  module interface through the canonical coercion `ℕ+ → ℤ`.

Source/core/bridge triage:
* `source-facing`: the weighted-graded local finite-presentation theorem below;
* `core/canonical`: `Module.FinitePresentation` and the weighted grading owner
  `weightedHomogeneousSubmodule`;
* `bridge/view`: the passage from `w : σ → ℕ+` to the induced `ℤ`-grading. -/

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {σ : Type*} [Finite σ]
variable {M : Type v} [AddCommMonoid M] [Module R M] [Module (MvPolynomial σ R) M]
variable [IsScalarTower R (MvPolynomial σ R) M]

local notation "P" => MvPolynomial σ R

-- Proof sketch: choose homogeneous generators of the finite graded module `M` and present it by a
-- finite direct sum of weighted shifts of `MvPolynomial σ R`. Degreewise, the kernel has
-- short exact sequences whose middle and right terms are finite free over the local ring `R`, so
-- each graded piece of the kernel is finite free over `R`. After tensoring with the residue field,
-- the kernel over `MvPolynomial σ R ⊗[R] κ` is finitely generated because that polynomial
-- ring is Noetherian; then graded Nakayama lifts finitely many homogeneous generators back to the
-- kernel over `R`, giving a finite presentation of `M` over `MvPolynomial σ R`.
/-- Lemma 15.25.3: if `R` is a local ring, `MvPolynomial σ R` on a finite variable type `σ` is
given the weighted grading with variable-weights `w : σ → ℕ+` viewed as degrees in `ℤ`, and a
`ℤ`-graded module `M` over this polynomial ring is finite over `MvPolynomial σ R` and flat over
`R`, then `M` is finitely presented as an `MvPolynomial σ R`-module. -/
theorem finitePresentation_of_local_flat_finite_weighted_graded_mvPolynomial_module
    (w : σ → ℕ+) (ℳ : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun i ↦ (w i : ℤ))) ℳ]
    [Module.Finite P M] [Module.Flat R M] :
    Module.FinitePresentation P M := sorry

end

/-! ### Lemma_15_25_4 (from Chap15) -/
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

/-! ### Remark_15_25_5 (from Chap15) -/
universe u

section

variable (R : Type u) [CommRing R]

/- Domain-style sampling for Remark 15.25.5:
* primary domain: commutative algebra of prime localizations and weakly associated primes;
* sampled upstream owners:
  - `weaklyAssociatedPrimes R M` from Definition `10.66.1`,
  - `weaklyAssociatedPrimes_localizationMap_injective` from Lemma `10.66.17`,
  - `algebraMap_embedding_into_product_of_fields` from Lemma `10.25.2`,
  - `exists_injective_awayMap_atPrime_of_noetherian_or_reduced_finiteMinimalPrimes`
    from Lemma `10.31.9`;
* source-facing layer here: the existential condition that some finite family of prime
  localizations detects equality in `R`;
* best owner abstraction for that finite family: `Finset (PrimeSpectrum R)`, while the canonical
  chapter index owners for the main applications are `weaklyAssociatedPrimes R R` and
  `minimalPrimes R`;
* primitive data: only a finite family `s : Finset (PrimeSpectrum R)`;
* derived API: the injectivity of the induced map `R → ∀ p : s, Localization.AtPrime p.1.asIdeal`,
  together with the sufficient criteria below.
-/

/-- Remark 15.25.5: the condition used in Lemmas 15.25.1, 15.25.2, and 15.25.4 is that some
finite family of prime localizations of `R` detects equality in `R`. -/
def primeLocalizationsDetectEquality : Prop :=
  ∃ s : Finset (PrimeSpectrum R),
    Function.Injective
      (fun r : R ↦
        fun p : s ↦ algebraMap R (Localization.AtPrime p.1.asIdeal) r)

section Local

variable [IsLocalRing R]

-- Proof sketch: use the singleton family consisting of the maximal ideal of the local ring. Since
-- every element outside the maximal ideal is a unit, localization at that prime is canonically the
-- ring itself, so the localization map is injective.
/-- A local ring satisfies the finite-prime localization-detection condition. -/
theorem primeLocalizationsDetectEquality_of_isLocalRing :
    primeLocalizationsDetectEquality R := sorry

end Local

section Noetherian

variable [IsNoetherianRing R]

-- Proof sketch: in a Noetherian ring, associated primes and weakly associated primes of the
-- regular module coincide, hence there are finitely many weakly associated primes. Apply the
-- injectivity statement of Lemma 10.66.17 to the canonical owner
-- `weaklyAssociatedPrimes R R`.
/-- A Noetherian ring satisfies the finite-prime localization-detection condition. -/
theorem primeLocalizationsDetectEquality_of_isNoetherianRing :
    primeLocalizationsDetectEquality R := sorry

end Noetherian

section Domain

variable [IsDomain R]

-- Proof sketch: use the singleton family containing the zero prime. Localization at `(0)` is the
-- total quotient ring of the domain, and the canonical map from a domain to its fraction field is
-- injective.
/-- A domain satisfies the finite-prime localization-detection condition. -/
theorem primeLocalizationsDetectEquality_of_isDomain :
    primeLocalizationsDetectEquality R := sorry

end Domain

section Reduced

variable [IsReduced R]

-- Proof sketch: take the finite family of minimal primes. For a reduced ring, Lemma 10.25.2 gives
-- injectivity of the canonical map from `R` to the product of the localizations indexed by the
-- owner type `minimalPrimes R`.
/-- A reduced ring with finitely many minimal primes satisfies the finite-prime
localization-detection condition. -/
theorem primeLocalizationsDetectEquality_of_isReduced_of_finite_minimalPrimes
    (hfinite : (minimalPrimes R).Finite) :
    primeLocalizationsDetectEquality R := sorry

end Reduced

section WeakAss

-- Proof sketch: index the family by the weakly associated primes of the regular module `R` and
-- apply Lemma 10.66.17 specialized to the owner `weaklyAssociatedPrimes R R`.
/-- A ring with finitely many weakly associated primes satisfies the finite-prime
localization-detection condition. -/
theorem primeLocalizationsDetectEquality_of_finite_weaklyAssociatedPrimes
    (hfinite : (weaklyAssociatedPrimes R R).Finite) :
    primeLocalizationsDetectEquality R := sorry

end WeakAss

end

/-! ### Lemma_15_25_6 (from Chap15) -/
universe u v w

section

open Module

/- Domain-style sampling:
- primary domain: finite-presentation descent for finite type algebras and finite modules over a
  valuation ring;
- sampled owner API:
  `exists_graded_localization_model_of_finite_module`,
  `flat_iff_isTorsionFree_of_valuationRing`,
  `graded_algebra_finitePresentation_of_flat`,
  `graded_module_finitePresentation_of_flat`,
  `primeLocalizationsDetectEquality_of_isDomain`;
- best owner abstraction: the public conclusions are already the canonical owner predicates
  `Algebra.FinitePresentation A B` and `Module.FinitePresentation B M`;
- source/core/bridge triage:
  `source-facing`: the two valuation-ring descent statements in this file;
  `core/canonical`: `Algebra.FinitePresentation` and `Module.FinitePresentation`;
  `bridge/view`: the graded localization model
  `exists_graded_localization_model_of_finite_module`, the valuation-ring flat/torsion-free bridge
  `flat_iff_isTorsionFree_of_valuationRing`, the domain detection bridge
  `primeLocalizationsDetectEquality_of_isDomain`, and the graded descent theorems
  `graded_algebra_finitePresentation_of_flat` and `graded_module_finitePresentation_of_flat`.

The only primitive public data here are the finite type / finite module hypotheses and flatness.
The module theorem should therefore stay at the `AddCommMonoid` owner level of
`Module.Finite`, `Module.Flat`, and `Module.FinitePresentation`; the graded presentation data are
derived bridge data from the sampled owner API and should not be reintroduced as public wrapper
structures or stronger ambient additive assumptions in this file.
-/

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
variable {B : Type v} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]

-- Proof sketch: represent the finite type `A`-algebra `B` as the degree-zero localization of a
-- finite graded algebra over `A` via
-- `exists_graded_localization_model_of_finite_module`, replace the graded algebra by its
-- torsion-free quotient using `flat_iff_isTorsionFree_of_valuationRing`, apply
-- `graded_algebra_finitePresentation_of_flat` together with
-- `primeLocalizationsDetectEquality_of_isDomain`, and then localize the resulting finite
-- presentation.
/-- Lemma 15.25.6 (1): if `A` is a valuation ring, `A → B` is a finite type ring map, and `B` is
flat over `A`, then `B` is a finitely presented `A`-algebra. -/
theorem algebra_finitePresentation_of_finiteType_flat_over_valuationRing [Flat A B] :
    Algebra.FinitePresentation A B := sorry

variable {M : Type w} [AddCommMonoid M] [Module B M] [Module.Finite B M]
variable [Module A M] [IsScalarTower A B M]

-- Proof sketch: choose a graded presentation `M ≅ N_(f)` over a graded finite type algebra `S`
-- using `exists_graded_localization_model_of_finite_module`, replace `N` by its torsion-free
-- quotient using the quotient owner from Lemma `15.22.2` and
-- `flat_iff_isTorsionFree_of_valuationRing`, apply
-- `graded_module_finitePresentation_of_flat` over the graded model using
-- `primeLocalizationsDetectEquality_of_isDomain`, and then localize the resulting finite
-- presentation to `B`.
/-- Lemma 15.25.6 (2): if `A` is a valuation ring, `A → B` is a finite type ring map, `M` is a
finite `B`-module, and `M` is flat as an `A`-module, then `M` is finitely presented as a
`B`-module. -/
theorem module_finitePresentation_of_finite_flat_over_valuationRing [Flat A M] :
    Module.FinitePresentation B M := sorry

end

/-! ### Lemma_15_25_7 (from Chap15) -/
universe u v w

section

/- Domain-style sampling:
- primary domain: local commutative algebra over valuation rings, with source-facing conclusions in
  the canonical owners for essential finite presentation of algebras and finite presentation of
  modules;
- sampled owner declarations:
  `Algebra.EssFinitePresentation`,
  `Algebra.EssFiniteType.subalgebra`,
  `Algebra.EssFiniteType.submonoid`,
  `Algebra.EssFiniteType.isLocalization`,
  `Algebra.EssFinitePresentation.of_isLocalization`,
  `algebra_finitePresentation_of_finiteType_flat_over_valuationRing`,
  `Module.FinitePresentation`;
- best owner abstraction: `Algebra.EssFinitePresentation A B` for part (1), not an existential
  localization witness restated locally;
- primitive data: the valuation-ring base, the essentially-finite-type algebra `B`, the finite
  `B`-module `M`, and the flatness hypotheses;
- derived API: any explicit localization presentation of `B` by a finitely presented
  `A`-algebra. That witness belongs to the owner `Algebra.EssFinitePresentation` and should not
  remain the main public conclusion here.

Layering:
- `source-facing`: Lemma 15.25.7 itself;
- `core/canonical`: `Algebra.EssFinitePresentation` and `Module.FinitePresentation`;
- `bridge/view`: a chosen localization presentation of `B`, used only through the owner
  abstraction rather than as a parallel public API.
-/

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
variable {B : Type v} [CommRing B] [Algebra A B] [Algebra.EssFiniteType A B]

-- Proof sketch: use the canonical finite-type subalgebra owner
-- `Algebra.EssFiniteType.subalgebra A B`, whose localization at
-- `Algebra.EssFiniteType.submonoid A B` is `B`. The ambient flat `A`-module `B` is torsion-free
-- by `flat_iff_isTorsionFree_of_valuationRing`, so the finite-type subalgebra is torsion-free,
-- hence flat, over `A`. Apply Lemma `15.25.6 (1)` to that finite-type model and then use
-- `Algebra.EssFinitePresentation.of_isLocalization`.
/-- Lemma 15.25.7 (1): if `A` is a valuation ring, `A → B` is essentially of finite type, and `B`
is flat over `A`, then `B` is essentially of finite presentation over `A`. -/
theorem algebra_essFinitePresentation_of_essFiniteType_flat_over_valuationRing [Module.Flat A B] :
    Algebra.EssFinitePresentation A B := sorry

variable {M : Type w} [AddCommMonoid M] [Module B M] [Module.Finite B M]
variable [Module A M] [IsScalarTower A B M]

-- Proof sketch: present `B` as a localization of a finite type polynomial algebra over `A`, view
-- `M` as a finite module over that finite type model, descend a finite generating set for the
-- kernel before localization, use the valuation-ring finite-presentation result for finite flat
-- modules over finite type algebras, and localize the resulting presentation.
/-- Lemma 15.25.7 (2): if `A` is a valuation ring, `A → B` is essentially of finite type, `M` is
a finite `B`-module, and `M` is flat as an `A`-module, then `M` is finitely presented as a
`B`-module. -/
theorem module_finitePresentation_of_essFiniteType_finite_flat_over_valuationRing
    [Module.Flat A M] : Module.FinitePresentation B M := sorry

end
