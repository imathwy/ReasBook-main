import Mathlib
import StacksProject_2024.Chap10.Definition_10_105_1
import StacksProject_2024.Chap10.Lemma_10_104_4
import StacksProject_2024.Chap10.Lemma_10_105_9
import StacksProject_2024.Chap10.Proposition_10_114_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Order Set

section

variable {k : Type u} [Field k]
variable {n : ℕ}

local notation "A" => MvPolynomial (Fin n) k

/- Domain-style sampling:
- primary domain: catenary prime-chain lengths in spectra of finite polynomial rings over a field;
- sampled owner declarations of the same kind:
  `IsCatenaryRing.maximalPrimeChainsHaveSameLength`,
  `CatenarySpace.maximalIrreducibleClosedChainsHaveLength`,
  `ringKrullDim_eq_ringKrullDim_atPrime_add_ringKrullDim_quotient_of_cohenMacaulayRing`,
  `universallyCatenaryRing_of_cohenMacaulayRing`;
- best owner abstraction: the interval-chain owner is `IsCatenaryRing A`; the polynomial-ring
  theorem below is a `source-facing` specialization of that catenary owner together with the local
  Cohen-Macaulay height formula;
- primitive data: the owner ring `A`, points `p q : PrimeSpectrum A`, the comparison `hpq : p ≤ q`,
  and a maximal chain `s` in `[p, q]`;
- derived API: catenarity of `A`, obtained from Proposition `10.114.2` through the chapter
  regular/Cohen-Macaulay/universally-catenary bridge, and the identification of the interval
  codimension with `q.asIdeal.height - p.asIdeal.height`.

Source/core/bridge triage:
* `source-facing`: the explicit textbook statement about maximal chains between two primes of
  `k[x₁, \ldots, xₙ]`;
* `core/canonical`: `IsCatenaryRing A` and the Chapter 5 catenary-space chain-length owner on
  intervals of `Spec A`;
* `bridge/view`: the local Cohen-Macaulay dimension formula computing that interval codimension as
  a height difference.

This file should remain a thin specialization of the existing catenary/Cohen-Macaulay owners, not
introduce a second local prime-chain owner for polynomial rings.
-/
-- Proof sketch: by Proposition `10.114.2`, every localization of
-- `MvPolynomial (Fin n) k` at a maximal ideal is a regular local ring of dimension `n`, hence
-- Cohen-Macaulay. Then Lemmas `10.104.3` and `10.104.4` identify the length of a maximal chain
-- in the interval `[p, q]` with the difference `height q - height p`.
/-- Lemma 10.114.3: if `p ≤ q` are prime ideals of the polynomial ring `k[x_1, \ldots, x_n]`,
then any maximal chain of primes between them has length `height(q) - height(p)`, equivalently,
it has `ENat.toNat (q.asIdeal.height - p.asIdeal.height) + 1` elements. -/
theorem maximal_prime_chain_encard_eq_height_sub_add_one_mvPolynomial
    (p q : PrimeSpectrum A) (hpq : p ≤ q)
    {s : Set (Set.Icc p q)} (hs : IsMaxChain (· ≤ ·) s) :
    s.encard = ENat.toNat (q.asIdeal.height - p.asIdeal.height) + 1 := sorry

end
