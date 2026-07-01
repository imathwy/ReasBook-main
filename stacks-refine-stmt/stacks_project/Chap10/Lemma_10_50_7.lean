import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain triage:
* primary domain: valuation subrings of fields and their pullback along ring homomorphisms;
* owner abstraction: `ValuationSubring.comap`;
* sampled canonical declarations:
  `ValuationSubring`,
  `ValuationSubring.comap`,
  `ValuationSubring.mem_comap`,
  and the induced `ValuationRing` instance on any valuation subring;
* layer: `core/canonical`, since this item is only recalling the owner-side pullback construction and
  adds no new source-facing data.

Primitive-vs-derived split:
* primitive data: a valuation subring `B` of a field `L`, together with the ring map
  `algebraMap K L`;
* derived API: the contracted valuation subring `B.comap (algebraMap K L)` and the resulting
  `ValuationRing` structure on `K`.
-/
/- Lemma 10.50.7: if `L/K` is a field extension and `B` is a valuation subring of `L`, then the
intersection `K ∩ B` is the canonical pullback valuation subring `B.comap (algebraMap K L)` of
`K`. Since every valuation subring carries a `ValuationRing` instance, this is exactly the Stacks
Project statement that `K ∩ B` is a valuation ring. -/
recall ValuationSubring.comap
