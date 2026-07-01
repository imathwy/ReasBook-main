import Mathlib
import stacks_project.Chap10.Lemma_10_63_17

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open scoped TensorProduct nonZeroDivisors

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

local notation "R⁰" => nonZeroDivisors R
local notation "K" => FractionRing R
local notation "T" => Algebra.algebraMapSubmonoid S R⁰
local notation "Sₖ" => Localization T
local notation "Nₖ" => LocalizedModule T N

local instance instIsNoetherianRingBaseChange [IsNoetherianRing S] : IsNoetherianRing Sₖ :=
  IsLocalization.isNoetherianRing T Sₖ inferInstance

/- Domain triage:
- primary domain: commutative algebra of associated primes under localization/base change;
- `source-facing`: the exact-annihilator set `associatedPrimesOfModule`;
- `core/canonical`: the localization owner `LocalizedModule T N` together with mathlib's
  Noetherian owner set `associatedPrimes`;
- `bridge/view`: the tensor-base-change realization `(S ⊗[R] K) ⊗[S] N` and the textbook tensor
  model `N ⊗[R] K`.

In this file, `Nₖ` is the localization owner itself, so the public equalities reuse Lemmas
`10.63.16` and `10.63.17` directly. The only remaining private bridge passes from that owner to
the tensor-base-change and textbook tensor presentations.
-/

private noncomputable def localizedModuleFractionRingBaseChangeEquiv :
    Nₖ ≃ₗ[S] (S ⊗[R] K) ⊗[S] N :=
  IsLocalizedModule.iso T (TensorProduct.mk S (S ⊗[R] K) N 1)

private noncomputable def fractionRingTensorLinearEquiv : Nₖ ≃ₗ[S] N ⊗[R] K :=
  localizedModuleFractionRingBaseChangeEquiv ≪≫ₗ TensorProduct.comm S (S ⊗[R] K) N ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N K

/-- Lemma 10.65.4, first equality in canonical owner form: for an `S`-module `N` that is flat
over `R`, the associated primes of `N` over `S` agree with those of the canonical localization
owner `Nₖ = LocalizedModule T N`. -/
-- Proof sketch: this is the `R⁰` specialization of Lemma `10.63.17`, applied to the image of
-- `R⁰` in `S`; flatness over `R` says exactly that every nonzero element of `R` acts regularly on
-- `N`.
theorem associatedPrimesOfModule_eq_fractionRingBaseChange_as_SModule [Module.Flat R N] :
    associatedPrimesOfModule S N = associatedPrimesOfModule S Nₖ := by
  refine associatedPrimesOfModule_eq_associatedPrimesOfModule_localizedModule T ?_
  intro s
  rcases s.2 with ⟨r, hr, hs⟩
  simpa [hs] using
    (Module.Flat.isSMulRegular_of_nonZeroDivisors hr).map
      (algebraMap R S) fun m ↦ by simp

/- The textbook tensor model `N ⊗[R] K` and the canonical localization owner `Nₖ` are the same
`S`-module up to the standard fraction-ring base-change equivalence, so they have the same textbook associated
primes over `S`. -/
theorem associatedPrimesOfModule_baseChange_to_fractionRing_eq_canonicalBaseChange :
    associatedPrimesOfModule S (N ⊗[R] K) =
      associatedPrimesOfModule S Nₖ := by
  let e : Nₖ ≃ₗ[S] N ⊗[R] K := fractionRingTensorLinearEquiv
  exact
    (show associatedPrimesOfModule S (N ⊗[R] K) = associatedPrimesOfModule S Nₖ from
      (LinearEquiv.associatedPrimesOfModule_eq S Nₖ e).symm)

/-- Textbook tensor-model reformulation of the first equality of Lemma 10.65.4. -/
-- Proof sketch: first apply the canonical owner-level equality
-- `associatedPrimesOfModule_eq_fractionRingBaseChange_as_SModule`, then rewrite along the standard
-- tensor equivalence
-- `associatedPrimesOfModule_baseChange_to_fractionRing_eq_canonicalBaseChange`.
theorem associatedPrimesOfModule_eq_associatedPrimesOfModule_baseChange_to_fractionRing
    [Module.Flat R N] :
    associatedPrimesOfModule S N =
      associatedPrimesOfModule S (N ⊗[R] K) := by
  calc
    associatedPrimesOfModule S N = associatedPrimesOfModule S Nₖ :=
      associatedPrimesOfModule_eq_fractionRingBaseChange_as_SModule
    _ = associatedPrimesOfModule S (N ⊗[R] K) :=
      associatedPrimesOfModule_baseChange_to_fractionRing_eq_canonicalBaseChange.symm

/-- Noetherian specialization of the canonical owner form of the first equality of Lemma 10.65.4
in mathlib's `associatedPrimes` API. -/
theorem associatedPrimes_eq_fractionRingBaseChange_as_SModule
    [Module.Flat R N] [IsNoetherianRing S] :
    associatedPrimes S N = associatedPrimes S Nₖ := by
  rw [← associatedPrimesOfModule_eq_associatedPrimes S N,
    ← associatedPrimesOfModule_eq_associatedPrimes S Nₖ]
  exact associatedPrimesOfModule_eq_fractionRingBaseChange_as_SModule

/-- Noetherian specialization of the textbook tensor-model reformulation of the first equality of
Lemma 10.65.4 in mathlib's `associatedPrimes` API. -/
theorem associatedPrimes_eq_associatedPrimes_baseChange_to_fractionRing
    [Module.Flat R N] [IsNoetherianRing S] :
    associatedPrimes S N =
      associatedPrimes S (N ⊗[R] K) := by
  calc
    associatedPrimes S N = associatedPrimes S Nₖ :=
      associatedPrimes_eq_fractionRingBaseChange_as_SModule
    _ = associatedPrimes S (N ⊗[R] K) := by
      let e : Nₖ ≃ₗ[S] N ⊗[R] K := fractionRingTensorLinearEquiv
      simpa using LinearEquiv.AssociatedPrimes.eq e

/-
Lemma 10.65.4, second equality: the associated primes of the canonical base-change
`Nₖ` over `S` are exactly the contractions of its associated primes over `Sₖ`.
-/
-- Proof sketch: apply the textbook contraction statement for associated primes under restriction
-- of scalars along `S → Sₖ` to the localization owner from Lemma `10.63.16`.
omit [Module R N] [IsScalarTower R S N] in
theorem associatedPrimesOfModule_baseChange_to_fractionRing_eq_image_comap :
    associatedPrimesOfModule S Nₖ =
      Ideal.comap (algebraMap S Sₖ) '' associatedPrimesOfModule Sₖ Nₖ := by
  simpa using
    (associatedPrimesOfModule_localizedModule_eq_image_comap T).symm

/-- Rewriting the second equality of Lemma 10.65.4 through the standard identification of the
textbook tensor model with the canonical base-change model. -/
theorem associatedPrimesOfModule_baseChange_to_fractionRing_textbook_eq_image_comap :
    associatedPrimesOfModule S (N ⊗[R] K) =
      Ideal.comap (algebraMap S Sₖ) '' associatedPrimesOfModule Sₖ Nₖ := by
  rw [associatedPrimesOfModule_baseChange_to_fractionRing_eq_canonicalBaseChange]
  exact associatedPrimesOfModule_baseChange_to_fractionRing_eq_image_comap

/- Noetherian specialization of the textbook formulation of the second equality of
Lemma 10.65.4, obtained from the canonical base-change statement via the standard `S`-linear
identification of the two tensor models. -/
theorem associatedPrimes_baseChange_to_fractionRing_textbook_eq_image_comap
    [IsNoetherianRing S] :
    associatedPrimes S (N ⊗[R] K) =
      Ideal.comap (algebraMap S Sₖ) '' associatedPrimes Sₖ Nₖ := by
  let _ : IsNoetherianRing Sₖ := inferInstance
  simpa [associatedPrimesOfModule_eq_associatedPrimes] using
    (associatedPrimesOfModule_baseChange_to_fractionRing_textbook_eq_image_comap :
      associatedPrimesOfModule S (N ⊗[R] K) =
        Ideal.comap (algebraMap S Sₖ) '' associatedPrimesOfModule Sₖ Nₖ)

end
