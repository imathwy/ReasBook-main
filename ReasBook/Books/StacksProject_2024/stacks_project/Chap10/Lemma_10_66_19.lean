import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_66_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w x

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {R : Type w} [CommRing R] [Algebra k R]
variable {M : Type x} [AddCommGroup M] [Module R M]

local notation "Rₖ" => R ⊗[k] K
local notation "Mₖ" => Rₖ ⊗[R] M

/- Domain triage:
- primary domain: weakly associated primes under field extension/base change;
- `core/canonical`: the owner module `Mₖ = (R ⊗[k] K) ⊗[R] M`;
- `bridge/view`: the textbook tensor model `M ⊗[k] K`, compared to `Mₖ` through the standard
  base-change equivalence.

Primitive data are only the owner module `Mₖ` and the chapter owner set `weaklyAssociatedPrimes`.
The textbook tensor presentation is derived API, so the file keeps the owner theorem at the weaker
owner-module layer and adds the textbook comparison only in a stronger bridge section. -/
local instance : Module Rₖ Mₖ :=
  TensorProduct.leftModule

/- Lemma 10.66.19 is proved first at the `core/canonical` owner layer `Mₖ`. The textbook tensor
presentation `M ⊗[k] K` is handled separately as derived bridge API. -/
-- Proof sketch: first reduce to a finitely generated intermediate field extension and then to the
-- purely transcendental case, using flatness, going-down, and the finite-extension comparison for
-- weakly associated primes. After localizing at the contraction `q.under R`, show that every
-- element of `Rₖ \ (q.under R)Rₖ` acts as a nonzerodivisor on the base change, deduce that powers
-- of elements of `q.under R` annihilate a witness vector for `q`, and finally descend weak
-- association from the direct-sum decomposition of the scalar extension back to `M`.
/-- Lemma 10.66.19 in canonical owner form: if `q` is weakly associated to the canonical base
change `Mₖ = (R ⊗[k] K) ⊗[R] M`, then its contraction `q.under R` is weakly associated to
`M`. -/
theorem under_mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_baseChange
    (q : Ideal Rₖ) (hq : q ∈ weaklyAssociatedPrimes Rₖ Mₖ) :
    q.under R ∈ weaklyAssociatedPrimes R M := sorry

end

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {R : Type w} [CommRing R] [Algebra k R]
variable {M : Type x} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

local notation "Rₖ" => R ⊗[k] K
local notation "Mₖ" => Rₖ ⊗[R] M

local instance : Module Rₖ Mₖ :=
  TensorProduct.leftModule

private noncomputable def textbookBaseChangeAddEquiv : M ⊗[k] K ≃+ Mₖ :=
  ((Algebra.IsPushout.cancelBaseChange k K R Rₖ M).toAddEquiv.trans
    (TensorProduct.comm k K M).toAddEquiv).symm

private noncomputable local instance : Module Rₖ (M ⊗[k] K) :=
  (show M ⊗[k] K ≃+ Mₖ from textbookBaseChangeAddEquiv).module Rₖ

private noncomputable def textbookBaseChangeLinearEquiv : M ⊗[k] K ≃ₗ[Rₖ] Mₖ :=
  (show M ⊗[k] K ≃+ Mₖ from textbookBaseChangeAddEquiv).linearEquiv Rₖ

/-- The textbook tensor model `M ⊗[k] K` and the canonical owner base change `Mₖ` have the same
weakly associated primes over `R ⊗[k] K`. -/
theorem weaklyAssociatedPrimes_textbook_baseChange_eq_canonicalBaseChange :
    weaklyAssociatedPrimes Rₖ (M ⊗[k] K) = weaklyAssociatedPrimes Rₖ Mₖ := by
  simpa using LinearEquiv.weaklyAssociatedPrimes_eq textbookBaseChangeLinearEquiv

/-- Lemma 10.66.19 in the source-facing textbook tensor model: if `q ⊂ R ⊗[k] K` lies over
`p ⊂ R` and `q` is weakly associated to `M ⊗[k] K`, then `p` is weakly associated to `M`. -/
theorem mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_baseChange_of_liesOver
    (p : Ideal R) (q : Ideal Rₖ) (hqover : q.LiesOver p)
    (hq : q ∈ weaklyAssociatedPrimes Rₖ (M ⊗[k] K)) :
    p ∈ weaklyAssociatedPrimes R M := by
  letI : q.LiesOver p := hqover
  have hq' : q ∈ weaklyAssociatedPrimes Rₖ Mₖ := by
    rw [← weaklyAssociatedPrimes_textbook_baseChange_eq_canonicalBaseChange]
    exact hq
  simpa [q.over_def p] using
    under_mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_baseChange q hq'

end
