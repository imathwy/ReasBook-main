import Mathlib.Tactic.Recall
import stacks_project.Chap10.Lemma_10_123_9

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 10.123.10:
- primary domain: strong transcendence and quasi-finiteness in commutative algebra;
- sampled owner declarations:
  `IsStronglyTranscendental`,
  `Algebra.QuasiFiniteAt`,
  `not_quasiFiniteAt_of_isStronglyTranscendental_of_aeval_finite`;
- best owner abstraction: the chapter theorem
  `not_quasiFiniteAt_of_isStronglyTranscendental_of_aeval_finite` from Lemma `10.123.9`;
- primitive data: `x : S`, its strong transcendence over `R`, finiteness of `Polynomial.aeval x`,
  and the prime `q`;
- derived API: the reduced-ring wording from the source, whose extra reducedness and
  `FaithfulSMul` assumptions are redundant for the canonical conclusion.

Source/core/bridge triage:
- `source-facing`: the Stacks negation of quasi-finiteness for a ring finite over `R[x]`;
- `core/canonical`: `IsStronglyTranscendental`, `Algebra.QuasiFiniteAt`, and the owner theorem
  from Lemma `10.123.9`;
- `bridge/view`: this file is recall-only, since the canonical chapter theorem already has the
  mathematically correct public statement. -/

/- Lemma 10.123.10: the reduced-ring formulation is already covered by the canonical chapter
theorem `not_quasiFiniteAt_of_isStronglyTranscendental_of_aeval_finite`. The extra assumptions
`IsReduced R`, `IsReduced S`, and `FaithfulSMul R S` are redundant for the public API, so this
numbered item is refined to a direct recall of the owner theorem rather than a parallel wrapper. -/
recall not_quasiFiniteAt_of_isStronglyTranscendental_of_aeval_finite
