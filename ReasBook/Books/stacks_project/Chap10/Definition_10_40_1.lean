import Mathlib.RingTheory.Support
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling for module support:
- primary domain: support of modules over a commutative ring, viewed on `PrimeSpectrum R`;
- sampled canonical declarations:
  `Module.support`,
  `Module.mem_support_iff`,
  `Module.support_eq_empty_iff`,
  `Module.support_eq_zeroLocus`;
- best owner abstraction: `Module.support R M`;
- primitive data: the owner set of primes where the localized module is nontrivial;
- derived API: membership reformulations such as `Module.mem_support_iff`, together with
  closedness and zero-locus descriptions under stronger finiteness hypotheses.

Source/core/bridge triage:
- `source-facing`: the textbook support `Supp(M)` as a subset of `Spec R`;
- `core/canonical`: `Module.support R M`;
- `bridge/view`: `Module.mem_support_iff`, identifying membership with nontriviality of `M_𝔭`.

This numbered definition introduces no new mathematical data beyond the owner set
`Module.support R M`, so the main entry should remain a direct canonical recall rather than a
parallel local alias or a large restatement theorem.
-/

section

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/- Definition 10.40.1, canonical main form: the support of an `R`-module `M` is the mathlib
definition `Module.support R M`, the set of primes `𝔭 ∈ PrimeSpectrum R` such that the
localization `M_𝔭` is nontrivial. -/
recall Module.support

variable {R M} {p : PrimeSpectrum R}

/- Companion recall: membership in `Module.support R M` is exactly the textbook condition
`M_𝔭 ≠ 0`, formalized in Lean as nontriviality of the localized module at `𝔭`. -/
recall Module.mem_support_iff

end
