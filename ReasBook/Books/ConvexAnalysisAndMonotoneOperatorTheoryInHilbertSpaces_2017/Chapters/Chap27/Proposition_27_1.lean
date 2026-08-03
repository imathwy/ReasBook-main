import Mathlib
import Mathlib.Tactic.Recall
import BauschkeLean.Chap12.Proposition_12_29
import BauschkeLean.Chap16.Proposition_16_33
import BauschkeLean.Chap17.Proposition_17_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 27.1 is a recap of four standard characterizations of minimizers
  for a `Γ₀(H)` function.
- `core/canonical`: the owner declarations are `Argmin`, `∂`, `Function.fixedPoints`, `Prox`,
  `Prox⋆`, and the zero-set owner `SetValuedOperator.zeros`.
- `bridge/view`: this file should therefore be recall-only; it does not own a new Chapter 27 API.

The earlier chapter owner theorems already express exactly these four characterizations, so the
refinement deletes the parallel Chapter 27 wrappers and reuses those owners directly. -/

/- Proposition 27.1 (1): for `f ∈ Γ₀(H)`, the minimizers of `f` are exactly the zeros of its
subdifferential. -/
recall argmin_eq_zeros_subdifferential

/- Proposition 27.1 (2): for `f ∈ Γ₀(H)`, the minimizers of `f` are exactly the
subdifferential of the Fenchel conjugate `f*` at `0`. -/
recall argmin_eq_subdifferential_gammaZeroConjugate_zero

/- Proposition 27.1 (3): for `f ∈ Γ₀(H)`, the fixed points of its proximity operator are exactly
the minimizers of `f`. -/
recall fixedPoints_proximityOperator_eq_argmin_of_mem_gammaZero

/- Proposition 27.1 (4): the canonical owner theorem already identifies the zeros of the
proximity operator of `f*` with the minimizers of `f`; this is the same mathematical content as
the textbook clause `Argmin f = zeros(Prox_{f*})`. -/
recall conjugateProximityOperator_zeroSet_eq_argmin_of_mem_gammaZero

end

end ERealFunction
