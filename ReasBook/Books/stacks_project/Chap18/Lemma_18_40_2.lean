import Mathlib
import stacks_project.Chap18.Lemma_18_36_4
import stacks_project.Chap18.Definition_18_40_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 18.40.2:
- primary domain: point stalks of sheaves of commutative rings on a site, together with enough
  points and the chapter-local unit-dichotomy owner for ringed sites;
- sampled owner declarations:
  `HasLocalUnitDichotomy`,
  `GrothendieckTopology.Point.sheafFiber`,
  `sourcePointRing`,
  `GrothendieckTopology.HasEnoughPoints`,
  `IsLocalRing.of_isUnit_or_isUnit_one_sub_self`;
- best owner abstraction: the source-facing local section hypothesis is the chapter owner
  `HasLocalUnitDichotomy J 𝒪`; the chapter stalk-ring owner is `sourcePointRing`, so the theorem
  surface should use that owner directly rather than repeating the full typed fiber expression;
- primitive data: the sheaf `𝒪` and the point `p`;
- derived API: the stalkwise “zero or local” conclusion and its enough-points equivalence.

Source/core/bridge triage:
- `source-facing`: the forward implication and the enough-points equivalence below;
- `core/canonical`: `GrothendieckTopology.Point.sheafFiber` and
  `GrothendieckTopology.HasEnoughPoints`;
- `bridge/view`: `HasLocalUnitDichotomy`, the chapter stalk-ring bridge `sourcePointRing`, and the
  local-ring dichotomy on stalks.

The previous single conjunction-valued theorem repeated both the local-dichotomy hypothesis and the
raw stalk expression. This file should reuse the existing chapter owners and expose the two source-
facing clauses atomically.
-/

-- Proof sketch: represent a stalk element by a section, apply the local
-- invertibility/complement-invertibility cover from `HasLocalUnitDichotomy J 𝒪`, and use the point
-- axiom to refine to one member of the cover. This shows that every element of the stalk ring is
-- either a unit or has unit complement; Lemma `10.18.3` then yields that the stalk ring is either
-- trivial or local.
/-- Lemma 18.40.2, forward direction: if every local section is locally either a unit or has unit
complement, then every point stalk is either the zero ring or a local ring. -/
theorem stalkwise_zero_or_local_of_hasLocalUnitDichotomy
    (𝒪 : Sheaf J CommRingCat.{w}) (h : HasLocalUnitDichotomy J 𝒪)
    (p : J.Point) :
    Subsingleton (sourcePointRing 𝒪 p) ∨ IsLocalRing (sourcePointRing 𝒪 p) := sorry

-- Proof sketch: use Lemma `18.40.1` to identify `HasLocalUnitDichotomy J 𝒪` with local
-- surjectivity of the canonical binary factorization map, check this map is stalkwise surjective
-- because each stalk ring is zero or local by Lemma `10.18.3`, and then reflect local
-- surjectivity from stalks using enough points.
/-- Lemma 18.40.2: if the site has enough points, then the local unit dichotomy is equivalent to
every point stalk being either the zero ring or a local ring. -/
theorem hasLocalUnitDichotomy_iff_stalkwise_zero_or_local
    [GrothendieckTopology.HasEnoughPoints.{w} J]
    (𝒪 : Sheaf J CommRingCat.{w}) :
    HasLocalUnitDichotomy J 𝒪 ↔
      ∀ p : J.Point,
        Subsingleton (sourcePointRing 𝒪 p) ∨ IsLocalRing (sourcePointRing 𝒪 p) := sorry

end CategoryTheory
