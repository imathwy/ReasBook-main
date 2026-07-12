import Mathlib
import StacksProject_2024.Chap07.Definition_7_43_7
import StacksProject_2024.Chap07.Lemma_7_41_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

namespace MorphismOfTopoiIn

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (i : MorphismOfTopoiIn J K)

/- Domain-style sampling for Lemma 7.43.8:
- primary domain: closed immersions of topoi and the owner-level consequences for the direct-image
  functor and the adjunction counit;
- sampled owner API:
  `MorphismOfTopoiIn.IsClosedImmersion`,
  `MorphismOfTopoiIn.IsEmbedding`,
  `Adjunction.counit_isIso_of_R_fully_faithful`,
  the canonical implication theorems from `Lemma_7_41_1`;
- best owner abstraction: the source-facing class `MorphismOfTopoiIn.IsClosedImmersion i`, whose
  primitive data are only the embedding structure and the closed-subtopos condition on
  `(i _*).essImage`;
- primitive data: `i.IsClosedImmersion`;
- derived API: the canonical fully faithful structure on `(i _*)` together with the reflection and
  preservation properties on `(i _*)` that this lemma records for closed immersions.

Source/core/bridge triage:
- `source-facing`: the closed-immersion consequences listed in Lemma 7.43.8;
- `core/canonical`: `MorphismOfTopoiIn.IsEmbedding`, `(i _*).Full`,
  `(i _*).Faithful`, `IsIso i.adjunction.counit`, and the standard
  `Preserves`/`Reflects` owner classes on `(i _*)`;
- `bridge/view`: the passage from `i.IsClosedImmersion` to those owner-level consequences. -/

/-- Lemma 7.43.8 (1): for a closed immersion of topoi, the direct-image functor `i_*` is fully
faithful. -/
noncomputable instance closedImmersion_pushforwardFullyFaithful [i.IsClosedImmersion] :
    (i _*).FullyFaithful :=
  .ofFullyFaithful (i _*)

/-- Lemma 7.43.8 (2): for a closed immersion of topoi, the direct-image functor `i_*` sends
surjections to surjections. -/
instance closedImmersion_pushforwardPreservesEpimorphisms [i.IsClosedImmersion] :
    (i _*).PreservesEpimorphisms := sorry

/-- Lemma 7.43.8 (3): for a closed immersion of topoi, the direct-image functor `i_*` commutes
with coequalizers. -/
instance closedImmersion_pushforwardPreservesCoequalizers [i.IsClosedImmersion] :
    PreservesColimitsOfShape WalkingParallelPair (i _*) := sorry

/-- Lemma 7.43.8 (4): for a closed immersion of topoi, the direct-image functor `i_*` commutes
with pushouts. -/
instance closedImmersion_pushforwardPreservesPushouts [i.IsClosedImmersion] :
    PreservesColimitsOfShape WalkingSpan (i _*) := sorry

/-- Lemma 7.43.8 (5): for a closed immersion of topoi, the direct-image functor `i_*` reflects
injections. -/
instance closedImmersion_pushforwardReflectsMonomorphisms [i.IsClosedImmersion] :
    (i _*).ReflectsMonomorphisms := sorry

/-- Lemma 7.43.8 (6): for a closed immersion of topoi, the direct-image functor `i_*` reflects
surjections. -/
instance closedImmersion_pushforwardReflectsEpimorphisms [i.IsClosedImmersion] :
    (i _*).ReflectsEpimorphisms := sorry

/-- Lemma 7.43.8 (7): for a closed immersion of topoi, the direct-image functor `i_*` reflects
isomorphisms. -/
instance closedImmersion_pushforwardReflectsIsomorphisms [i.IsClosedImmersion] :
    (i _*).ReflectsIsomorphisms := sorry

end

end MorphismOfTopoiIn

end CategoryTheory
