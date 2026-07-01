import Mathlib.Algebra.Module.Injective
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 19.2.6 (Baer's criterion): for a ring `R` and an `R`-module `Q`, the module `Q` is
injective if and only if every `R`-linear map from an ideal `I : Ideal R` to `Q` extends along the
inclusion `I → R`. This is the canonical mathlib theorem `Module.Baer.iff_injective`, because
`Module.Baer R Q` is exactly the extension property for all ideals of `R`. -/
recall Module.Baer.iff_injective
