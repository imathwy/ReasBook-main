import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable (U : CosimplicialObject C)

/- Domain-style sampling for Remark 14.5.3:
- primary domain: cosimplicial objects and the cosimplicial identities for their coface and
  codegeneracy maps;
- sampled owner API:
  `CosimplicialObject.δ`,
  `CosimplicialObject.σ`,
  `CosimplicialObject.δ_comp_δ`,
  `CosimplicialObject.δ_comp_σ_of_le`,
  `CosimplicialObject.σ_comp_σ`;
- source/core/bridge triage:
  `source-facing`: the textbook operators `δ_i` and `σ_i` for one cosimplicial object `U`;
  `core/canonical`: the mathlib owner declarations `U.δ`, `U.σ`, and the canonical cosimplicial
  identity theorems;
  `bridge/view`: local notation exposing the source operators directly as those owner maps.
- primitive data: only the cosimplicial object `U`;
- derived API: the coface maps, codegeneracy maps, and all cosimplicial relations, which should be
  reused directly from the owner API rather than duplicated through local wrapper declarations.
- layer target: `bridge/view`, since the remark only rewrites the canonical owner data and
  identities into the textbook `δ_i`/`σ_i` notation for one fixed cosimplicial object.
-/

local notation "δ_" i:arg => U.δ i
local notation "σ_" i:arg => U.σ i

/- Remark 14.5.3 (1): for a cosimplicial object `U`, the coface maps written in the text as
`δ_i : U_n ⟶ U_{n + 1}` are the canonical morphisms `U.δ i`; the local notation `δ_ i` exposes
that textbook surface. -/
recall CosimplicialObject.δ
#check (fun {n : ℕ} (i : Fin (n + 2)) ↦ δ_ i)

/- Remark 14.5.3 (2): likewise, the codegeneracy maps written in the text as
`σ_i : U_{n + 1} ⟶ U_n` are the canonical morphisms `U.σ i`; the local notation `σ_ i` exposes
that textbook surface. -/
recall CosimplicialObject.σ
#check (fun {n : ℕ} (i : Fin (n + 1)) ↦ σ_ i)

/- Remark 14.5.3 (3): the first cosimplicial identity, namely
`δ_j ∘ δ_i = δ_i ∘ δ_{j - 1}` for `i < j`, whenever both composites are defined, is formalized by
`CosimplicialObject.δ_comp_δ`, which reads in the source notation as follows. -/
#check
  (show ∀ {n : ℕ} {i j : Fin (n + 2)}, i ≤ j → δ_ i ≫ δ_ (j.succ) = δ_ j ≫ δ_ (i.castSucc)
    from U.δ_comp_δ)

/- Remark 14.5.3 (4): the relation
`σ_j ∘ δ_i = δ_i ∘ σ_{j - 1}` for `i < j`, whenever both composites are defined, is formalized by
`CosimplicialObject.δ_comp_σ_of_le`, which becomes the following source-facing equality. -/
#check
  (show ∀ {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)},
      i ≤ j.castSucc → δ_ (i.castSucc) ≫ σ_ (j.succ) = σ_ j ≫ δ_ i
    from U.δ_comp_σ_of_le)

/- Remark 14.5.3 (5): the identity
`id = σ_j ∘ δ_j`, whenever the composite is defined, is formalized by
`CosimplicialObject.δ_comp_σ_self`, equivalently `δ_j ≫ σ_j = 𝟙`. -/
#check
  (show ∀ {n : ℕ} (j : Fin (n + 1)), δ_ (Fin.castSucc j) ≫ σ_ j = 𝟙 _ from
    fun j ↦ (U.δ_comp_σ_self : δ_ (Fin.castSucc j) ≫ σ_ j = 𝟙 _))

/- Remark 14.5.3 (6): the identity
`id = σ_j ∘ δ_{j + 1}`, whenever the composite is defined, is formalized by
`CosimplicialObject.δ_comp_σ_succ`, equivalently `δ_{j + 1} ≫ σ_j = 𝟙`. -/
#check
  (show ∀ {n : ℕ} (j : Fin (n + 1)), δ_ (j.succ) ≫ σ_ j = 𝟙 _ from
    fun j ↦ (U.δ_comp_σ_succ : δ_ (j.succ) ≫ σ_ j = 𝟙 _))

/- Remark 14.5.3 (7): the relation
`σ_j ∘ δ_i = δ_{i - 1} ∘ σ_j` for `i > j + 1`, whenever both composites are defined, is
formalized by `CosimplicialObject.δ_comp_σ_of_gt`, which in the source notation is the relation
below. -/
#check
  (show ∀ {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)},
      j.castSucc < i → δ_ (i.succ) ≫ σ_ (j.castSucc) = σ_ j ≫ δ_ i
    from U.δ_comp_σ_of_gt)

/- Remark 14.5.3 (8): the relation
`σ_j ∘ σ_i = σ_i ∘ σ_{j + 1}` for `i ≤ j`, whenever both composites are defined, is formalized by
`CosimplicialObject.σ_comp_σ`, which becomes the following equality in the source notation. -/
#check
  (show ∀ {n : ℕ} {i j : Fin (n + 1)},
      i ≤ j → σ_ (i.castSucc) ≫ σ_ j = σ_ (j.succ) ≫ σ_ i
    from U.σ_comp_σ)

end CategoryTheory
