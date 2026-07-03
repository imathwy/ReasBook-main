import Mathlib
import stacks_project.Chap18.Lemma_18_36_4
import stacks_project.Chap18.«18_40_2_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-
Domain-style sampling for Lemma 18.40.3:
- primary domain: point stalks of sheaves of commutative rings on a site, together with
  conservativity of point-fiber functors under enough points;
- sampled relevant declarations:
  `oneNeverZeroEqualizerMap`,
  `GrothendieckTopology.Point.sheafFiber`,
  `sourcePointRing`,
  `point_stalk_ring`,
  `GrothendieckTopology.HasEnoughPoints.exists_objectProperty`;
- best owner abstraction: the source-facing chapter map `oneNeverZeroEqualizerMap 𝒪`, with the
  stalk condition expressed through the chapter bridge owner `sourcePointRing 𝒪 p`, which is the
  commutative-ring view of `GrothendieckTopology.Point.sheafFiber`; `point_stalk_ring` is the
  presheaf-level ring-stalk companion in the same domain;
- primitive data: the sheaf `𝒪` and the point `p`;
- derived API: stalkwise nontriviality and the enough-points reflection equivalence.

Source/core/bridge triage:
- `source-facing`: the implication from the `18.40.2.1` isomorphism to nontriviality of every
  stalk, and the converse under enough points;
- `core/canonical`: `oneNeverZeroEqualizerMap`, `Point.sheafFiber`, and the enough-points
  conservativity machinery;
- `bridge/view`: the earlier ring-valued stalk abbreviations `sourcePointRing` and
  `point_stalk_ring`, which are derived views of `Point.sheafFiber` / `Point.presheafFiber`.

The old single conjunction-valued theorem bundled two mathematically separate clauses and repeated
the raw stalk object expression. This file should expose the two source-facing clauses as atomic
theorems, while stating the stalk condition through the canonical chapter bridge `sourcePointRing`.
-/

-- Proof sketch: apply the stalk functor at a point `p` to the canonical morphism
-- `\emptyset^\# \to \operatorname{Equalizer}(0,1 : * \to \mathcal O)`. The source stalk remains
-- initial, while the target stalk identifies with the equalizer of `0, 1 : PUnit ⟶ \mathcal O_p`,
-- which is empty exactly when `0 ≠ 1` in the stalk ring, i.e. exactly when the stalk is
-- nontrivial. This gives `(1) → (2)`. If `J` has enough points, then the stalk functors are
-- conservative on sheaves, so the converse follows by checking that the displayed map is an
-- isomorphism on every point stalk.
/-- Lemma 18.40.3, forward direction: if the canonical morphism
`\emptyset^\# \to \operatorname{Equalizer}(0,1 : * \to \mathcal O)` from `18.40.2.1` is an
isomorphism, then every point stalk `\mathcal O_p` is nonzero. -/
theorem stalkwise_nontrivial_of_isIso_oneNeverZeroEqualizerMap
    (𝒪 : Sheaf J CommRingCat.{max u v}) (h : IsIso (oneNeverZeroEqualizerMap 𝒪))
    (p : GrothendieckTopology.Point.{max u v} J) :
    Nontrivial (sourcePointRing 𝒪 p) := sorry

/-- Lemma 18.40.3: if `(\mathcal C, J)` has enough points, then the canonical morphism
`\emptyset^\# \to \operatorname{Equalizer}(0,1 : * \to \mathcal O)` from `18.40.2.1` is an
isomorphism exactly when every point stalk `\mathcal O_p` is nonzero. -/
theorem isIso_oneNeverZeroEqualizerMap_iff_stalkwise_nontrivial
    [GrothendieckTopology.HasEnoughPoints.{max u v} J]
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    IsIso (oneNeverZeroEqualizerMap 𝒪) ↔
      ∀ p : GrothendieckTopology.Point.{max u v} J,
        Nontrivial (sourcePointRing 𝒪 p) := sorry

end CategoryTheory
