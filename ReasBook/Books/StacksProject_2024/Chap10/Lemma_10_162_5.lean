import Mathlib
import stacks_project.Chap10.Definition_10_122_3
import stacks_project.Chap10.Proposition_10_162_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: stability of the source-facing owner `NagataRing` under algebra extensions;
- sampled owner abstractions in the same chapter/project:
  - `Algebra.FiniteType.QuasiFinite`, the source-facing owner for quasi-finite finite-type
    extensions from `Definition_10_122_3`;
  - `NagataRing`, the source-facing owner from `Definition_10_162_1`;
  - `UniversallyJapaneseRing`, the companion owner derived from `NagataRing` in
    `Proposition_10_162_16`;
  - `nagataRing_of_finiteType`, the canonical chapter theorem proving finite-type stability of
    `NagataRing`.

Best owner abstraction:
- `NagataRing` is the owner of the property under discussion;
- `Algebra.FiniteType.QuasiFinite R S` is the source-facing owner for the hypothesis;
- `nagataRing_of_finiteType` is the canonical upstream stability theorem for the conclusion;
- the quasi-finite lemma below is therefore a `source-facing` bridge/view corollary, not a second
  owner-level theorem.

Primitive data vs derived API:
- primitive data: the rings `R`, `S`, the `R`-algebra structure, and the source-faithful
  source-facing quasi-finite owner `Algebra.FiniteType.QuasiFinite R S`;
- derived API: the conclusion `NagataRing S`, obtained directly from the upstream finite-type
  theorem.
-/
-- Proof sketch: quasi-finite morphisms are finite type, so `S` is Noetherian because `R` is.
-- For a prime ideal `q` of `S`, let `p = q ∩ R`. Then `(R ⧸ p) → (S ⧸ q)` is again quasi-finite,
-- and the source is `N-2` because `R` is Nagata. Apply Lemma `10.161.5` to conclude that
-- `S ⧸ q` is `N-2`, which is exactly the Nagata condition for `S`.
/-- Lemma 10.162.5: if `R` is a Nagata ring and `R → S` is quasi-finite, then `S` is a Nagata
ring as well. In particular, this applies to finite ring maps. -/
theorem nagataRing_of_quasiFinite (hRSqf : Algebra.FiniteType.QuasiFinite R S) [NagataRing R] :
    NagataRing S := by
  letI : Algebra.FiniteType R S := hRSqf.finiteType
  exact nagataRing_of_finiteType R

end
