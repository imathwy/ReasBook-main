import Mathlib
import stacks_project.Chap10.Lemma_10_155_1
import stacks_project.Chap15.Definition_15_107_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open scoped Unibranch
open Algebra.TensorProduct
open IsLocalRing

universe u

noncomputable section

section

variable (A Ah : Type u)
variable [CommRing A] [IsLocalRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

local notation "A′h" => A′ ⊗[A] Ah

/-
Domain-style sampling:
- primary domain: local commutative algebra of unibranch normalization, henselization, and prime
  spectra under tensor-product base change;
- sampled owner declarations of the same kind:
  `unibranchNormalization`,
  `IsHenselizationOf`,
  `minimalPrimes`,
  `Algebra.TensorProduct.includeRight`;
- best owner abstraction: the source-facing object is the chapter owner `A′ =
  unibranchNormalization A`, while the ideal-theoretic comparison statements are derived API on the
  canonical tensor-product base change `A′ ⊗[A] Ah`;
- primitive data: the local ring `A`, its chosen henselization `Ah`, and the owner `A′`;
- derived API: contraction along `A′ → A′h` and `Ah → A′h`, together with the canonical sets of
  maximal and minimal primes.

Source/core/bridge triage:
- `source-facing`: the four clauses of Lemma 15.107.2;
- `core/canonical`: `unibranchNormalization`, `IsHenselizationOf`, `Ideal.comap`,
  `minimalPrimes`, `Algebra.TensorProduct.includeRight`;
- `bridge/view`: the base-changed ring `A′h = A′ ⊗[A] Ah`.
-/

-- Proof sketch: reduce to the reduced case, identify the closed fiber of
-- `Anorm → Anormh = Anorm ⊗[A] Ah` with `Anorm ⊗[A] ResidueField A`, and use the trivial residue
-- field extension of a henselization together with integrality over the local base to show that
-- comap along `A' → (A')^h` gives a bijection on maximal ideals.
/-- Lemma 15.107.2 (1): for `A' = unibranchNormalization A` and `(A')^h = A' ⊗[A] A^h`, the map
`Spec((A')^h) → Spec(A')` is bijective on maximal ideals. -/
theorem unibranchNormalizationTensorHenselization_bijOn_maximalIdeals
    (hfinite : (minimalPrimes A).Finite) :
    Set.BijOn (Ideal.comap (includeLeftRingHom : A′ →+* A′h))
      {m : Ideal A′h | m.IsMaximal}
      {m : Ideal A′ | m.IsMaximal} := sorry

-- Proof sketch: compare minimal primes on both sides with the fibers over the minimal primes of
-- `A`, use that `A'` becomes the total ring of fractions after inverting non-zero-divisors, and
-- identify `(A')^h ⊗[A] Q(Ared)` with `A^h ⊗[A] Q(Ared)` to match the minimal-prime sets.
/-- Lemma 15.107.2 (2): for `A' = unibranchNormalization A` and `(A')^h = A' ⊗[A] A^h`, the map
`Spec((A')^h) → Spec(A^h)` is bijective on minimal primes. -/
theorem unibranchNormalizationTensorHenselization_bijOn_minimalPrimes
    (hfinite : (minimalPrimes A).Finite) :
    Set.BijOn
      (Ideal.comap ((includeRight : Ah →ₐ[A] A′h).toRingHom))
      (minimalPrimes A′h)
      (minimalPrimes Ah) := sorry

-- Proof sketch: `Anormh` is normal after base change to the henselization, so localizations at
-- maximal ideals are domains; combine this with henselian-pair connectivity of the closed fiber
-- to see that the connected closed subset cut out by a minimal prime meets the closed fiber in a
-- unique point, hence lies in a unique maximal ideal.
/-- Lemma 15.107.2 (3): every minimal prime of `(A')^h = A' ⊗[A] A^h` is contained in a unique
maximal ideal. -/
theorem unibranchNormalizationTensorHenselization_minimalPrime_existsUnique_maximalIdeal
    (hfinite : (minimalPrimes A).Finite)
    {p : Ideal A′h} (hp : p ∈ minimalPrimes A′h) :
    ∃! m : Ideal A′h, m.IsMaximal ∧ p ≤ m := sorry

-- Proof sketch: after the previous clause, each minimal prime determines a unique maximal ideal;
-- normality of the local rings of `Anormh` implies each maximal localization is a domain, so a
-- maximal ideal can contain only one minimal prime.
/-- Lemma 15.107.2 (4): every maximal ideal of `(A')^h = A' ⊗[A] A^h` contains exactly one
minimal prime. -/
theorem unibranchNormalizationTensorHenselization_maximalIdeal_existsUnique_minimalPrime
    (hfinite : (minimalPrimes A).Finite)
    {m : Ideal A′h} (hm : m.IsMaximal) :
    ∃! p : Ideal A′h, p ∈ minimalPrimes A′h ∧ p ≤ m := sorry

end
