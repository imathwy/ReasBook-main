import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

section

open PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/- Domain triage:
* primary domain: primes of a finite type algebra lying over a fixed minimal prime;
* source-facing layer: the existence of `g ∉ p` making the localization `R_g → S_g` finite;
* core/canonical owner sampled for the finite fiber hypothesis: `Ideal.primesOver`;
* bridge/view relating the textbook fiber of `Spec(S) → Spec(R)` to that owner set:
  `PrimeSpectrum.primesOverOrderIsoFiber`.

Primitive data are `R`, `S`, the minimal prime `p`, and the canonical owner set
`p.asIdeal.primesOver S`. The finiteness hypothesis belongs on that owner set rather than on the
parallel raw subtype of `Spec(S)` points over `p`. -/

-- Proof sketch: by Lemma `10.122.4`, the finite-over-`p` hypothesis implies that the fiber
-- algebra `S ⊗[R] κ(p)` is finite over `κ(p)`, so a finite set of `R`-algebra generators of `S`
-- satisfies monic relations modulo `p`. Since `p` is minimal, Lemmas `10.25.1` and `10.32.3`
-- make the extended ideal `pS_p` locally nilpotent, so powers of those relations vanish in
-- `S_p`. Clearing denominators away from a suitable element `g ∉ p` then makes each generator
-- integral over `R_g`, and a finite type integral algebra is finite.
/-- Lemma 10.122.11: if `R → S` is of finite type, `p` is a minimal prime of `R`, and only
finitely many primes of `S` lie over `p`, then there exists `g ∈ R \ p` such that the localized
map `R_g → S_g` is finite. -/
theorem exists_notMem_and_away_finite_of_finite_primesOver_minimalPrime
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    (hfinite : Finite (p.asIdeal.primesOver S)) :
    ∃ g : R, g ∉ p.asIdeal ∧ (Localization.awayMapₐ (Algebra.ofId R S) g).Finite := sorry

end
