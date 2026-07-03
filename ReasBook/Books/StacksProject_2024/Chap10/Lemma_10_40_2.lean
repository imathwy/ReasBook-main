import Mathlib.RingTheory.Support
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for module support and its emptiness criterion:
- primary domain: support of modules over a commutative ring, viewed as a subset of `Spec R`;
- sampled canonical declarations:
  `Module.support`,
  `Module.mem_support_iff`,
  `Module.support_eq_empty_iff`,
  `Module.nonempty_support_iff`;
- best owner abstraction: `Module.support R M`;
- primitive data: the support set itself;
- derived API: membership and emptiness/nonemptiness characterizations, in particular
  `Module.support_eq_empty_iff`.

Source/core/bridge triage:
- `source-facing`: the statement that an `R`-module has empty support exactly when it is the zero
  module;
- `core/canonical`: `Module.support R M`;
- `bridge/view`: the canonical emptiness criterion `Module.support_eq_empty_iff`.

This lemma introduces no new data beyond the existing support owner and its derived emptiness API,
so the refined main entry should remain a direct recall of the canonical theorem rather than a
parallel local wrapper.
-/

section

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/- Lemma 10.40.2, source-facing through the support owner abstraction: an `R`-module `M` is
the zero module if and only if its support `Module.support R M` is empty. This is exactly the
canonical theorem `Module.support_eq_empty_iff`, where `M = (0)` is expressed as
`Subsingleton M`. -/
recall Module.support_eq_empty_iff

end
