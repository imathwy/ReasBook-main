import Mathlib
import StacksProject_2024.Chap06.Definition_6_15_1
import StacksProject_2024.Chap06.Lemma_6_13_1
import StacksProject_2024.Chap06.Lemma_6_21_5
import StacksProject_2024.Chap06.Lemma_6_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Set TopCat TopologicalSpace
open TopCat.Presheaf.stalkPushforward
open TopCat.Sheaf

noncomputable section

universe v u

section

variable {X : TopCat.{v}}
variable {C : Type u} [Category.{v} C]
variable {FC : C → C → Type v} {CC : C → Type v}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory.{v} C FC]
variable [IsAlgebraicStructure C (forget C)]
variable (Z : Set X)

/- Domain-style sampling for Lemma 6.32.4:
- primary domain: pushforward of sheaves along the inclusion of a closed subset in `TopCat`;
- sampled owner declarations:
  `TopCat.closedSubsetInclusion`,
  `TopCat.subsetInclusion`,
  `Sheaf.pushforward`,
  `Sheaf.pullbackPushforwardAdjunction`,
  `subsetSheaf_pullback_pushforward_counit_isIso`,
  `Adjunction.fullyFaithfulROfIsIsoCounit`,
  `filteredStalk`;
- owner abstraction: the ambient owner map is `X.subsetInclusion Z`, while the numbered Stacks
  item is its closed-subset specialization `X.closedSubsetInclusion Z`; the public theorem is the
  fully-faithfulness of the induced sheaf pushforward on algebraic-structure-valued sheaves;
- primitive data: the subset `Z : Set X`, its canonical inclusion into `X`, and the existing
  pullback/pushforward adjunction on sheaves for the algebraic-structure pair `(C, forget C)`;
- derived API: the subset-level fully faithful companion theorem obtained canonically from the
  counit-isomorphism owner theorem of Lemma `6.32.1`, the source-facing essential-image criterion
  in terms of `filteredStalk`, and the ordinary-stalk reformulation only as a bridge under the
  stronger `[HasColimits C]` hypothesis.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma about direct image from a closed subset;
- `core/canonical`: `X.subsetInclusion Z` together with `Sheaf.pushforward`;
- `bridge/view`: the closed-subset specialization `X.closedSubsetInclusion Z` and the adjunction
  theorem turning the counit isomorphism into full faithfulness. -/

local notation "sZ" => X.subsetInclusion Z

/-- Owner instance: pushforward along any subset inclusion is fully faithful for sheaves of
algebraic structures. -/
noncomputable instance subsetSheafPushforward_fullyFaithful [HasColimits.{v} C] :
    (Sheaf.pushforward C sZ).FullyFaithful := by
  have : ∀ ℱ : TopCat.Sheaf C (TopCat.of Z),
      IsIso ((Sheaf.pullbackPushforwardAdjunction C sZ).counit.app ℱ) := by
    intro ℱ
    exact subsetSheaf_pullback_pushforward_counit_isIso ℱ
  let _ : IsIso (Sheaf.pullbackPushforwardAdjunction C sZ).counit :=
    NatIso.isIso_of_isIso_app _
  exact (Sheaf.pullbackPushforwardAdjunction C sZ).fullyFaithfulROfIsIsoCounit

local notation "iZ" => X.closedSubsetInclusion Z

-- Proof sketch: for a pushforward from the closed subspace, stalks away from `Z` are terminal,
-- equivalently the canonical maps from those stalks to the terminal object are isomorphisms;
-- conversely, if these maps are isomorphisms away from `Z`, then the adjunction map from the
-- pushforward of the restriction back to the original sheaf is an isomorphism.

/-- Lemma 6.32.4 (1): a sheaf of algebraic structures on `X` lies in the essential image of
pushforward from a closed subset `Z` if and only if, at every point of `X \ Z`, the canonical map
from the filtered stalk to the terminal object is an isomorphism. This is the source-facing owner
statement; the ordinary-stalk reformulation is only a bridge once `[HasColimits C]` is available.
-/
theorem closedSubsetSheafPushforward_essImage_iff_filteredStalk_isTerminal_of_not_mem
    (hZ : IsClosed Z) (𝒢 : X.Sheaf C) :
    (Sheaf.pushforward C iZ).essImage 𝒢 ↔
      ∀ x : X, x ∉ Z → IsIso (terminal.from (filteredStalk x 𝒢.presheaf)) := by
  sorry

include FC CC

/-- Lemma 6.32.4 (2): a sheaf of algebraic structures on `X` lies in the essential image of
pushforward from a closed subset `Z` if and only if, at every point of `X \ Z`, the canonical map
from the ordinary stalk to the terminal object is an isomorphism. This is only the
`[HasColimits C]` bridge form of the filtered-stalk owner theorem above. -/
theorem closedSubsetSheafPushforward_essImage_iff_stalk_isTerminal_of_not_mem
    [HasColimits.{v} C]
    (hZ : IsClosed Z) (𝒢 : X.Sheaf C) :
    (Sheaf.pushforward C iZ).essImage 𝒢 ↔
      ∀ x : X, x ∉ Z → IsIso (terminal.from (𝒢.presheaf.stalk x)) := by
  simpa [filteredStalk_eq_stalk] using
    (closedSubsetSheafPushforward_essImage_iff_filteredStalk_isTerminal_of_not_mem
      Z hZ 𝒢)

omit FC CC

end
