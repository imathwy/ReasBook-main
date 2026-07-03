import Mathlib.RingTheory.Support
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.40.9 (1): if `M` is a finite `R`-module and `I` is an ideal of `R`, then the support
of the quotient `M / IM`, written in Lean as `M ⧸ (I • ⊤ : Submodule R M)`, is the intersection
`Module.support R M ∩ PrimeSpectrum.zeroLocus I`. This is exactly the canonical theorem
`Module.support_quotient`. -/
recall Module.support_quotient

/- Lemma 10.40.9 (2): if `N` is a submodule of an `R`-module `M`, then
`Module.support R N ⊆ Module.support R M`. This is the canonical theorem
`Module.support_subset_of_injective`, specialized to the subtype map `N.subtype`. -/
recall Module.support_subset_of_injective

/- Lemma 10.40.9 (3): if `Q` is a quotient module of an `R`-module `M`, then
`Module.support R Q ⊆ Module.support R M`. This is the canonical theorem
`Module.support_subset_of_surjective`, specialized to the quotient map onto `Q`. -/
recall Module.support_subset_of_surjective

/- Lemma 10.40.9 (4): for a short exact sequence `0 → N → M → Q → 0` of `R`-modules, the support
of `M` is the union of the supports of `N` and `Q`. This is exactly the canonical theorem
`Module.support_of_exact`. -/
recall Module.support_of_exact
