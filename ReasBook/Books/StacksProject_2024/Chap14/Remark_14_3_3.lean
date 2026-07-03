import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open SimplicialObject

variable {C : Type u} [Category.{v} C]
variable (U : SimplicialObject C)

/- Domain-style sampling for Remark 14.3.3:
- primary domain: simplicial objects and the simplicial identities for their face and degeneracy
  maps;
- sampled owner API:
  `SimplicialObject.δ`,
  `SimplicialObject.σ`,
  `SimplicialObject.δ_comp_δ`,
  `SimplicialObject.δ_comp_σ_of_le`,
  `SimplicialObject.δ_comp_σ_self`,
  `SimplicialObject.δ_comp_σ_succ`,
  `SimplicialObject.δ_comp_σ_of_gt`,
  `SimplicialObject.σ_comp_σ`;
- source/core/bridge triage:
  `source-facing`: the textbook operators `d_i` and `s_i` and their relations for one simplicial
  object `U`;
  `core/canonical`: the mathlib owner declarations `U.δ`, `U.σ`, and the canonical simplicial
  identity theorems;
  `bridge/view`: local notation exposing the source operators directly as the canonical owner maps.
- primitive data: only the simplicial object `U`;
- derived API: the face maps, degeneracy maps, and all simplicial relations, which should be reused
  directly from the owner API rather than duplicated through new wrapper declarations.
- layer target: `bridge/view`, since the remark only rewrites the canonical owner maps and
  simplicial identities into the textbook notation for one fixed simplicial object.
-/

local notation "d_" i:arg => U.δ i
local notation "s_" i:arg => U.σ i

/- Remark 14.3.3 (1): for a simplicial object `U`, the face maps written in the text as
`d_i : U_n ⟶ U_{n - 1}` are the canonical morphisms `U.δ i`; the local notation `d_ i` exposes
that textbook surface. -/
recall SimplicialObject.δ
#check (fun {n : ℕ} (i : Fin (n + 2)) ↦ d_ i)

/- Remark 14.3.3 (2): likewise, the degeneracy maps written in the text as
`s_i : U_n ⟶ U_{n + 1}` are the canonical morphisms `U.σ i`; the local notation `s_ i` exposes
that textbook surface. -/
recall SimplicialObject.σ
#check (fun {n : ℕ} (i : Fin (n + 1)) ↦ s_ i)

/- Remark 14.3.3 (3): the first simplicial identity, namely
`d_i ∘ d_j = d_{j - 1} ∘ d_i` for `i < j`, whenever both composites are defined, is formalized by
`SimplicialObject.δ_comp_δ`, which reads in the source notation as follows. -/
#check (fun {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j) ↦
  (show d_ j.succ ≫ d_ i = d_ i.castSucc ≫ d_ j from U.δ_comp_δ h))

/- Remark 14.3.3 (4): the relation
`d_i ∘ s_j = s_{j - 1} ∘ d_i` for `i < j`, whenever both composites are defined, is formalized by
`SimplicialObject.δ_comp_σ_of_le`, which becomes the following source-facing equality. -/
#check (fun {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} (h : i ≤ j.castSucc) ↦
  (show s_ j.succ ≫ d_ i.castSucc = d_ i ≫ s_ j from U.δ_comp_σ_of_le h))

/- Remark 14.3.3 (5): the identity
`id = d_j ∘ s_j`, whenever the composite is defined, is formalized by
`SimplicialObject.δ_comp_σ_self`, equivalently `s_j ≫ d_j = 𝟙`. -/
#check (fun {n : ℕ} (j : Fin (n + 1)) ↦
  (show s_ j ≫ d_ j.castSucc = 𝟙 _ from U.δ_comp_σ_self))

/- Remark 14.3.3 (6): the identity
`id = d_{j + 1} ∘ s_j`, whenever the composite is defined, is formalized by
`SimplicialObject.δ_comp_σ_succ`, equivalently `s_j ≫ d_{j + 1} = 𝟙`. -/
#check (fun {n : ℕ} (j : Fin (n + 1)) ↦
  (show s_ j ≫ d_ j.succ = 𝟙 _ from U.δ_comp_σ_succ))

/- Remark 14.3.3 (7): the relation
`d_i ∘ s_j = s_j ∘ d_{i - 1}` for `i > j + 1`, whenever both composites are defined, is
formalized by `SimplicialObject.δ_comp_σ_of_gt`, which in the source notation is the relation
below. -/
#check (fun {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} (h : j.castSucc < i) ↦
  (show s_ j.castSucc ≫ d_ i.succ = d_ i ≫ s_ j from U.δ_comp_σ_of_gt h))

/- Remark 14.3.3 (8): the relation
`s_i ∘ s_j = s_{j + 1} ∘ s_i` for `i ≤ j`, whenever both composites are defined, is formalized by
`SimplicialObject.σ_comp_σ`, which becomes the following equality in the source notation. -/
#check (fun {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j) ↦
  (show s_ j ≫ s_ i.castSucc = s_ i ≫ s_ j.succ from U.σ_comp_σ h))

end CategoryTheory
