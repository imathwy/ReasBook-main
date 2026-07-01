import Mathlib.RingTheory.Etale.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling:
- primary domain: formal étaleness of commutative algebras, specialized to localization;
- sampled owner API:
  `Algebra.FormallyEtale`,
  `Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth`,
  `Algebra.FormallyEtale.of_isLocalization`,
  `Algebra.FormallySmooth.of_isLocalization`;
- source-facing: the textbook lemma that the localization map `R → M⁻¹R` is formally étale;
- core/canonical: the mathlib owner class `Algebra.FormallyEtale`;
- bridge/view: none; the source statement is exactly the owner-level localization theorem.

Primitive data are the commutative ring, the multiplicative subset, and the localization instance.
Formal étaleness is derived API owned upstream by `Algebra.FormallyEtale.of_isLocalization`, so
this file should recall that owner theorem directly rather than keep any parallel local wrapper.
-/

/- Lemma 10.150.5: for a commutative ring `R` and a multiplicative subset `M`, the localization
map `R → M⁻¹R` is formally étale. This is exactly the canonical localization theorem
`Algebra.FormallyEtale.of_isLocalization`. -/
recall Algebra.FormallyEtale.of_isLocalization
