import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.EpiMono
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open SimplicialObject

variable {C : Type u} [Category.{v} C]
variable (U : SimplicialObject C) {n : ℕ} (i : Fin (n + 1))

/- Domain-style sampling for Lemma 14.3.6:
- primary domain: simplicial identities for degeneracy morphisms in simplicial objects;
- sampled owner API:
  `SimplicialObject.σ`,
  `SimplicialObject.δ_comp_σ_self`,
  `CategoryTheory.SplitMono`,
  `CategoryTheory.SplitMono.mono`;
- source/core/bridge triage:
- `source-facing`: the degeneracy morphism `U.σ i` together with its canonical left inverse
    `U.δ i.castSucc`;
  - `core/canonical`: the category-theoretic split-mono witness `SplitMono (U.σ i)` and its
    derived `Mono (U.σ i)` consequence;
  - `bridge/view`: no extra local bridge is needed, since the simplicial identity
    `U.δ_comp_σ_self` feeds directly into the canonical `SplitMono` owner.
- primitive data: the simplicial object `U`, the index `i`, and the retraction identity
  `U.δ_comp_σ_self`;
- derived API: the canonical split-mono witness and the resulting `Mono` fact, obtained directly
  from `U.δ_comp_σ_self` rather than through local wrapper declarations.
- layer target: `source-facing`, with the theorem surface phrased for `U.σ i` and the proof
  centered on the owner lemma `U.δ_comp_σ_self`.
-/

/- Lemma 14.3.6: for a simplicial object `U`, the degeneracy morphism
`U.σ i : U _⦋n⦌ ⟶ U _⦋n + 1⦌` has left inverse `U.δ i.castSucc`, equivalently
`U.σ i ≫ U.δ (Fin.castSucc i) = 𝟙 _`. This is exactly the first half of the third simplicial
identity. -/
recall SimplicialObject.δ_comp_σ_self :
  U.σ i ≫ U.δ i.castSucc = 𝟙 _

/- Companion check: `U.δ i.castSucc` exhibits `U.σ i` as a split monomorphism. -/
#check
  SplitMono.mk (U.δ i.castSucc) U.δ_comp_σ_self

/- Companion check: hence degeneracy morphisms are monomorphisms. -/
#check
  SplitMono.mono (SplitMono.mk (U.δ i.castSucc) U.δ_comp_σ_self)

end CategoryTheory
