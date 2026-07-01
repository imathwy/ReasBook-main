import Mathlib
import stacks_project.Chap10.Definition_10_66_1

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial

attribute [local instance high] Semiring.toModule Algebra.toModule

universe u

noncomputable section

/-
Domain triage: this remark is in commutative algebra of weakly associated primes under scalar
restriction along a polynomial-ring map. The owner abstraction is the chapter declaration
`weaklyAssociatedPrimes R M`. The primitive data are the relation ideal defining the quotient ring
and the explicit source-facing ideal `q = Σ xᵢ S` in that quotient. The algebra structure from
`k[x₁, x₂, …]` is derived from the canonical `MvPolynomial.rename` map and the owner quotient
algebra instance, so it should stay local rather than as a parallel public wrapper.
-/

/-- The ideal `(xᵢ yᵢ \mid i \ge 0)` in
`k[x₁, x₂, x₃, \ldots, y₁, y₂, y₃, \ldots]`. -/
def pairwiseZeroProductRelationIdeal (k : Type u) [CommRing k] :
    Ideal (MvPolynomial (Sum ℕ ℕ) k) :=
  Ideal.span (Set.range fun n : ℕ ↦ X (Sum.inl n) * X (Sum.inr n))

/-- The quotient ring
`k[x₁, x₂, x₃, \ldots, y₁, y₂, y₃, \ldots] / (x₁ y₁, x₂ y₂, x₃ y₃, \ldots)`. -/
abbrev pairwiseZeroProductQuotient (k : Type u) [CommRing k] :=
  MvPolynomial (Sum ℕ ℕ) k ⧸ pairwiseZeroProductRelationIdeal k

/-- The ideal `q = Σ xᵢ S` in the quotient ring of Remark 10.66.10. -/
def pairwiseZeroProductXIdeal (k : Type u) [CommRing k] : Ideal (pairwiseZeroProductQuotient k) :=
  Ideal.span (Set.range fun n : ℕ ↦
    Ideal.Quotient.mk (pairwiseZeroProductRelationIdeal k) (X (Sum.inl n)))

/-- The ideal `(x₁, x₂, x₃, \ldots)` in `k[x₁, x₂, x₃, \ldots]`. -/
def infiniteVariableIdeal (k : Type u) [CommRing k] : Ideal (MvPolynomial ℕ k) :=
  Ideal.span (Set.range fun n : ℕ ↦ (X n : MvPolynomial ℕ k))

section

variable (k : Type u) [Field k]

local notation "R∞" => MvPolynomial ℕ k
local notation "S∞" => pairwiseZeroProductQuotient k

local instance : Algebra R∞ (MvPolynomial (Sum ℕ ℕ) k) :=
  RingHom.toAlgebra (rename Sum.inl).toRingHom

local instance : Algebra R∞ S∞ :=
  Ideal.Quotient.algebra R∞

/-- The source-facing ideal `q = Σ xᵢ S` is a prime ideal of the counterexample ring. -/
theorem pairwiseZeroProductXIdeal_isPrime :
    (pairwiseZeroProductXIdeal k).IsPrime := sorry

/-- The source-facing ideal `q = Σ xᵢ S` is weakly associated to `S` as an `S`-module. -/
theorem pairwiseZeroProductXIdeal_mem_weaklyAssociatedPrimes_self :
    pairwiseZeroProductXIdeal k ∈ weaklyAssociatedPrimes S∞ S∞ := sorry

/-- Contracting `q = Σ xᵢ S` along `k[x₁, x₂, x₃, \ldots] → S` gives `(x₁, x₂, x₃, \ldots)`. -/
theorem comap_pairwiseZeroProductXIdeal :
    Ideal.comap (algebraMap R∞ S∞) (pairwiseZeroProductXIdeal k) = infiniteVariableIdeal k := sorry

/-- The contracted ideal `(x₁, x₂, x₃, \ldots)` is not weakly associated to `S` as an
`k[x₁, x₂, x₃, \ldots]`-module. -/
theorem infiniteVariableIdeal_not_mem_weaklyAssociatedPrimes :
    infiniteVariableIdeal k ∉ weaklyAssociatedPrimes R∞ S∞ := sorry

/-- Remark 10.66.10: for the ring map
`k[x₁, x₂, x₃, \ldots] → k[x₁, x₂, x₃, \ldots, y₁, y₂, y₃, \ldots] / (x₁ y₁, x₂ y₂, x₃ y₃, \ldots)`
and `M = S`, the image of `WeakAss_S(M)` in `Spec(R)` need not lie in `WeakAss_R(M)`. This shows
the finite-map hypothesis in Lemma `10.66.13` is essential. -/
-- Proof sketch: let `q = Σ xᵢ S`. The remark explains that `q` is a minimal prime of `S`, hence a
-- weakly associated prime of `S` over itself, while its contraction `(x₁, x₂, x₃, \ldots)` is not
-- weakly associated to `S` as an `R`-module because annihilators of nonzero elements over `R` are
-- finitely generated.
theorem weaklyAssociatedPrimes_comap_image_not_subset_for_pairwiseZeroProductQuotient
    :
    ¬ Ideal.comap (algebraMap R∞ S∞) '' weaklyAssociatedPrimes S∞ S∞ ⊆
      weaklyAssociatedPrimes R∞ S∞ := by
  intro hsubset
  have hq :
      Ideal.comap (algebraMap R∞ S∞) (pairwiseZeroProductXIdeal k) ∈
        Ideal.comap (algebraMap R∞ S∞) '' weaklyAssociatedPrimes S∞ S∞ := by
    exact ⟨pairwiseZeroProductXIdeal k, pairwiseZeroProductXIdeal_mem_weaklyAssociatedPrimes_self k,
      rfl⟩
  have hmem :
      Ideal.comap (algebraMap R∞ S∞) (pairwiseZeroProductXIdeal k) ∈ weaklyAssociatedPrimes R∞ S∞ :=
    hsubset hq
  rw [comap_pairwiseZeroProductXIdeal k] at hmem
  exact infiniteVariableIdeal_not_mem_weaklyAssociatedPrimes k hmem

end

end
