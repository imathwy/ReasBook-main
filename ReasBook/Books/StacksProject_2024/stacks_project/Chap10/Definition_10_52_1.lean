import Mathlib.RingTheory.Length
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section Length

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/- Domain triage:
* primary domain: module length and finite-length module theory over a ring;
* sampled owner API: `Module.length`, `Module.length_eq_coheight`,
  `Module.length_ne_top_iff`, and `Module.length_compositionSeries`;
* core/canonical owner: `Module.length R M`;
* layer split: the source-facing numerical invariant `length_R(M)` is the owner itself, while the
  coheight formula and finite-length criteria are derived API.
-/

/- Definition 10.52.1: for an `R`-module `M`, the Stacks-project length `length_R(M)` is the
canonical mathlib invariant `Module.length R M`. Mathlib defines this as the Krull dimension of
the lattice `Submodule R M`, packaging the textbook supremum over strict chains of submodules. -/
recall Module.length

/- Companion recall: the source formula
`sup {n | ∃ 0 = M₀ ⊂ M₁ ⊂ ⋯ ⊂ Mₙ = M}`
is the order-theoretic statement that `Module.length R M` is the coheight of `⊥` in
`Submodule R M`. -/
recall Module.length_eq_coheight

end Length
