import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap15.Lemma_15_87_10

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling:
- primary domain: Milnor short exact sequences for sequential derived limits in `D(Ab)`;
- sampled owner API:
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.derivedLimitDifferenceMap`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `CategoryTheory.derivedLimit_cohomology_shortExact`;
- best owner abstraction: the source-facing content of this remark is already exactly the
  canonical theorem `CategoryTheory.derivedLimit_cohomology_shortExact`, with no extra
  source-defined data beyond a chosen derived-limit witness;
- source/core/bridge triage:
  `source-facing`: the Milnor short exact sequence for the chosen derived limit of a sequential
  tower in `D(\operatorname{Ab})`;
  `core/canonical`: `IsDerivedLimit`, `SequentialInverseSystem.firstDerivedLimit`, and the owner
  theorem `CategoryTheory.derivedLimit_cohomology_shortExact`;
  `bridge/view`: none in this file.

Primitive data are only the tower `(K_n)`, the chosen derived limit `K`, the witness that `K` is
a derived limit of the tower, and the cohomological degree `p`. Since the displayed short exact
sequence is already formalized upstream with exactly that interface, this file should recall the
canonical owner directly rather than introduce a parallel local theorem or compatibility wrapper.
-/

/- Remark 15.87.12: for a sequential inverse system `(K_n)` in `D(\operatorname{Ab})` with chosen
derived limit `K`, the canonical Milnor short exact sequence
`0 \to R^1 \!\varprojlim H^{p-1}(K_n) \to H^p(K) \to \varprojlim H^p(K_n) \to 0`
is already formalized by `CategoryTheory.derivedLimit_cohomology_shortExact`. This is the
concrete formal content retained from the remark; the preceding discussion about independence of
the lift
`M ∈ D(\operatorname{Ab}(\mathbf N))` explains why Lemma 15.87.10 applies to an arbitrary derived
limit of the tower. -/
recall CategoryTheory.derivedLimit_cohomology_shortExact
