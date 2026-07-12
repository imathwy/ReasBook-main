import StacksProject_2024.Chap10.Definition_10_43_1
import StacksProject_2024.Chap10.Lemma_10_25_2
import StacksProject_2024.Chap10.Lemma_10_43_2
import StacksProject_2024.Chap10.Lemma_10_44_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Algebra

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]

local instance (p : minimalPrimes S) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

-- Source-facing theorem with owner abstraction `Algebra.IsGeometricallyReduced`.
-- Proof sketch: first use `Algebra.isReduced_of_isGeometricallyReduced` on each minimal-prime
-- localization; the explicit reducedness hypothesis `hS : IsReduced S` is needed to apply the
-- canonical embedding into the product of these localizations from Lemma `10.25.2`. After
-- tensoring that embedding with `AlgebraicClosure k`, flatness preserves injectivity, while each
-- tensor factor is reduced by the geometric reducedness hypothesis on the corresponding
-- localization. Therefore `AlgebraicClosure k ⊗[k] S` is reduced.
/-- Lemma 10.43.7 (Tag 07K2): if a `k`-algebra is reduced and the localizations at all of its
minimal prime ideals are geometrically reduced over `k`, then the algebra is geometrically reduced
over `k`. -/
@[stacks 07K2]
theorem isGeometricallyReduced_of_forall_minimalPrime_localization
    (hS : IsReduced S)
    (hlocal :
      ∀ p : minimalPrimes S,
        IsGeometricallyReduced k (Localization.AtPrime p.1)) :
    IsGeometricallyReduced k S := sorry

end
