import Mathlib.Tactic.Recall
import Mathlib.Data.Complex.Basic
import Mathlib.RepresentationTheory.FiniteIndex

noncomputable section

universe u v

namespace Representation

variable {G : Type u} [Group G]
variable (H : Subgroup G) [H.FiniteIndex]
variable {W : Type v} [AddCommGroup W] [Module ℂ W]
variable (θ : Representation ℂ H W)

-- Semantic recall verified: `Representation.ind` is the canonical owner for induced
-- representations, and `Rep.indCoindIso` supplies the finite-index comparison with the textbook
-- coinduced function model.

/- Source/core/bridge triage:
- `source-facing`: Definition 4-43 introduces `Ind_H^G(W, θ)` and describes it by the function
  model `f : G → W` satisfying `f (t * u) = θ t (f u)`, with `G` acting by right translation;
- `core/canonical`: `Representation.ind H.subtype θ`;
- `bridge/view`: `Rep.indCoindIso (Rep.of θ)` identifies that canonical owner with
  `Representation.coind H.subtype θ`, while `Representation.mem_coindV` and
  `Representation.coind_apply` give the source-facing function-model formulas.

This item is therefore recall-only: the induced representation and its textbook finite-index
function model are already owned by the existing induced/coinduced API.
-/

/- Definition 4-43: the induced representation `Ind_H^G(W, θ)` is the canonical owner
`Representation.ind H.subtype θ`. -/
recall Representation.ind

/- For finite index, `Rep.indCoindIso (Rep.of θ)` is the canonical bridge from
`Representation.ind H.subtype θ` to the textbook coinduced function model
`Representation.coind H.subtype θ`. -/
recall Rep.indCoindIso

/- The textbook function-model condition
`f (t * u) = θ t (f u)` is exactly `Representation.mem_coindV` for `H.subtype`. -/
recall Representation.mem_coindV

/- The `G`-action on the textbook function model is right translation, recorded by
`Representation.coind_apply`. -/
recall Representation.coind_apply

end Representation
