import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: quasi-finite finite-type ring maps and the algebraic Zariski main theorem;
- sampled owner API:
  `Algebra.ZariskisMainProperty`,
  `Algebra.ZariskisMainProperty.of_finiteType`,
  `Algebra.ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective`,
  `Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`;
- source-facing: the Stacks statement that for a finite type `R`-algebra `S` and a prime `q`,
  quasi-finiteness at `q` gives an element of `integralClosure R S` away from `q` with bijective
  away map;
- core/canonical owner: `Algebra.ZariskisMainProperty`;
- bridge/view: passing from `q : PrimeSpectrum S` to the owner input `q.asIdeal`.

Primitive data are only the finite-type algebra structure, the prime, and the canonical owner
`Algebra.QuasiFiniteAt`. The integral-closure witness and away-map bijectivity are already the
definition of `Algebra.ZariskisMainProperty`, so this file should recall the owner theorem directly
instead of keeping a parallel unpacked theorem.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/- Theorem 10.123.12 (Zariski's Main Theorem): for a finite type `R`-algebra `S` and a prime
`q ⊂ S`, if `R → S` is quasi-finite at `q`, then there exists an element of the integral closure
`S' = integralClosure R S` outside `q` such that the canonical away map `S'[1/g] → S[1/g]` is
bijection, equivalently `S'_g ≅ S_g`. This is exactly the canonical owner theorem
`Algebra.ZariskisMainProperty.of_finiteType`. -/
recall Algebra.ZariskisMainProperty.of_finiteType

end
