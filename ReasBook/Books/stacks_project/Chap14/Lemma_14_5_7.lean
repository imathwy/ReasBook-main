import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.EpiMono

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable (U : CosimplicialObject C) {n : ℕ} (i : Fin (n + 2))

/- Domain-style sampling for Lemma 14.5.7:
- primary domain: cosimplicial objects and the split-mono structure on their coface maps;
- sampled owner API:
  `CosimplicialObject.δ`,
  `CosimplicialObject.σ`,
  `CosimplicialObject.δ_comp_σ_self`,
  `CosimplicialObject.δ_comp_σ_succ`,
  `CategoryTheory.SplitMono.mk`,
  `CategoryTheory.SplitMono.mono`;
- best owner abstraction: the category-theoretic owner `SplitMono (U.δ i)`, with retraction
  chosen directly from the canonical codegeneracy maps of `U`;
- primitive data: the coface map `U.δ i`, the codegeneracy retraction
  `Fin.lastCases (U.σ (Fin.last n)) (fun j ↦ U.σ j) i`, and the two cosimplicial identities
  `U.δ_comp_σ_self` and `U.δ_comp_σ_succ`;
- derived API: the resulting `Mono (U.δ i)` fact, obtained from the `SplitMono` owner;
- source/core/bridge triage:
  `source-facing`: the textbook statement that every coface map has a left inverse, hence is
    monic;
  `core/canonical`: `SplitMono`;
  `bridge/view`: none, since the source retractions are already the canonical codegeneracy maps.
- layer target: `source-facing`, phrased directly in terms of the coface map `U.δ i` and the
  canonical categorical owner `SplitMono`.
-/

/- Lemma 14.5.7: for a cosimplicial object `U`, each coface morphism `U.δ i` has a canonical
left inverse, namely `U.σ j` when `i = j.castSucc` and `U.σ j` when `i = j.succ`. Equivalently,
the following term is the canonical split-mono witness for `U.δ i`. -/
#check
  let splitMonoδ : SplitMono (U.δ i) :=
    SplitMono.mk (Fin.lastCases (U.σ (Fin.last n)) (fun j ↦ U.σ j) i) <| by
      cases i using Fin.lastCases with
      | last =>
          simp only [Fin.lastCases_last]
          simpa using
            (show U.δ (Fin.last n).succ ≫ U.σ (Fin.last n) = 𝟙 _ from U.δ_comp_σ_succ)
      | cast j =>
          simp only [Fin.lastCases_castSucc]
          exact U.δ_comp_σ_self
  splitMonoδ

/- Companion check: hence every coface morphism in a cosimplicial object is monic. -/
#check
  let splitMonoδ : SplitMono (U.δ i) :=
    SplitMono.mk (Fin.lastCases (U.σ (Fin.last n)) (fun j ↦ U.σ j) i) <| by
      cases i using Fin.lastCases with
      | last =>
          simp only [Fin.lastCases_last]
          simpa using
            (show U.δ (Fin.last n).succ ≫ U.σ (Fin.last n) = 𝟙 _ from U.δ_comp_σ_succ)
      | cast j =>
          simp only [Fin.lastCases_castSucc]
          exact U.δ_comp_σ_self
  splitMonoδ.mono

end CategoryTheory
