import Mathlib.Tactic.Recall
import StacksProject_2024.Chap16.«16_3_1_1»

/- Domain-style sampling for `16_3_1_2`:
- primary domain: conormal exact sequences coming from presentations of algebras;
- sampled owner API:
  `presentation_conormal_tensor_sequence`,
  `Generators.Cotangent.exact`,
  `Function.Exact`,
  `Function.Surjective`;
- best owner abstraction: the chapter owner theorem
  `presentation_conormal_tensor_sequence`;
- primitive data: a presentation `P` of `A` over `R`, a presentation `Q` of `C` over `A`, a
  linear map `q` presenting the right-hand conormal term, and the comparison isomorphism `e`;
- derived API: exactness and surjectivity of the resulting presentation-conormal sequence.

Source/core/bridge triage:
- `source-facing`: the presentation-conormal sequence attached to `P`, `Q`, `q`, and `e`;
- `core/canonical`: the theorem `presentation_conormal_tensor_sequence`;
- `bridge/view`: its exactness and surjectivity conclusions in `Function.Exact` /
  `Function.Surjective` form.
-/

/- 16.3.1.2: the presentation-conormal tensor sequence with its presentation data is already
formalized in the preceding item. The correct refinement here is direct reuse of that owner theorem,
not a second public predicate on arbitrary linear maps. -/
recall presentation_conormal_tensor_sequence
