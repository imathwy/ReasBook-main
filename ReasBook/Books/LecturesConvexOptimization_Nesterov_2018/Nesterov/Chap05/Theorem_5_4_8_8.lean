import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_8_19

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 5.4.8.8 lies in the Chapter 5 finite exponential-sum convexity domain.

Sampled owner declarations:
* `sumOfExponentials` from `Definition_5_4_8_19`, the source-facing owner for the exponential sum
  `y ↦ ∑ⱼ αⱼ exp ⟪aⱼ, y⟫`;
* `sumOfExponentials_apply`, the defining evaluation bridge for that owner;
* `sumOfExponentials_convex`, the upstream chapter owner theorem proving whole-space convexity
  under the mathematically weaker nonnegativity hypothesis on the coefficients.

Best owner abstraction:
* source-facing: the textbook positive-coefficient convexity statement for `sumOfExponentials`;
* core/canonical: `sumOfExponentials_convex`;
* bridge/view: specializing the owner theorem from nonnegative coefficients to strictly positive
  coefficients.

Primitive data:
* the coefficient family `α₁, …, αᵣ`;
* the vectors `a₁, …, aᵣ`.

Derived API:
* the whole-space convexity conclusion for `sumOfExponentials`.

Source/core/bridge triage:
* source-facing: the positive-coefficient textbook theorem;
* core/canonical: `sumOfExponentials_convex`;
* bridge/view: the implication `0 < αⱼ → 0 ≤ αⱼ`.

This numbered item adds no new mathematical owner beyond the canonical theorem already proved in
`Definition_5_4_8_19`. Since the project already exposes the stronger reusable owner statement
with nonnegative coefficients, this file keeps only the direct recall surface; the textbook
strict-positivity specialization should be obtained from `sumOfExponentials_convex` at the call
site when needed.
-/

recall sumOfExponentials_convex
