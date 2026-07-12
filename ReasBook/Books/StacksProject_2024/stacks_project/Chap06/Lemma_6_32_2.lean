import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap06.Lemma_6_32_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

noncomputable section

universe u

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

section

variable {X : TopCat.{u}} {Z : Set X}

/- Domain-style sampling for Lemma 6.32.2:
- primary domain: pushforward of sheaves of sets along the inclusion of a closed subset in
  `TopCat`;
- sampled owner API:
  `TopCat.subsetInclusion`,
  `Sheaf.pushforward`,
  `subsetSheafPushforward_fullyFaithful`,
  `closedSubsetSheafPushforward_essImage_iff_stalk_isTerminal_of_not_mem`;
- owner abstraction: the owner is the subset inclusion `X.subsetInclusion Z` together with the
  canonical pushforward functor on sheaves; the source-facing closed-subset wording is handled by
  the essential-image theorem, while full faithfulness already lives upstream at the subset level
  in Lemma 6.32.4;
- primitive data: the subset `Z : Set X`, its inclusion into `X`, and the sheaf `𝒢`;
- derived API: the `Type` specialization of the owner theorem, which already lives on the
  canonical ordinary stalk.

Source/core/bridge triage:
- `source-facing`: the Stacks-project `Type`-valued formulation for closed subsets;
- `core/canonical`: the owner theorems of Lemma 6.32.4 for `Sheaf.pushforward` along
  `X.subsetInclusion Z`;
- `bridge/view`: the specialization to `C := Type u`. -/

local notation "iZ" => X.closedSubsetInclusion Z

/- Lemma 6.32.2: for a closed subset `Z ⊆ X` with inclusion `i : Z → X`, the pushforward
functor `i_* : Sh(Z) ⥤ Sh(X)` on sheaves of sets is fully faithful. This is the `Type`
specialization of `subsetSheafPushforward_fullyFaithful`. -/
recall subsetSheafPushforward_fullyFaithful

-- Proof sketch: specialize the owner theorem from Lemma 6.32.4 to `Type u`.
/-- Characterization of the essential image of pushforward from a closed subset in terms of stalks:
    a sheaf of sets on `X` lies in that essential image if and only if all of its stalks at points
    of `X \setminus Z` are singletons; canonically, this means the unique map from each such stalk
    to the terminal object is an isomorphism. -/
theorem closedSubsetTypeSheafPushforward_essImage_iff_stalk_isTerminal_of_not_mem
    (hZ : IsClosed Z) (𝒢 : X.Sheaf (Type u)) :
    (Sheaf.pushforward (Type u) iZ).essImage 𝒢 ↔
      ∀ x : X, x ∉ Z → IsIso (terminal.from (𝒢.presheaf.stalk x)) := by
  let _ : HasFilteredColimits (Type u) := hasFilteredColimitsOfSize_of_hasColimitsOfSize
  let _ : PreservesLimits (forget (Type u)) :=
    CategoryTheory.Types.instPreservesLimitsOfSizeForgetTypeHom
  let _ : PreservesFilteredColimits (forget (Type u)) := by
    let _ : PreservesColimits (forget (Type u)) :=
      CategoryTheory.Types.instPreservesColimitsOfSizeForgetTypeHom
    exact PreservesColimits.preservesFilteredColimits (forget (Type u))
  let _ : (forget (Type u)).ReflectsIsomorphisms :=
    CategoryTheory.instReflectsIsomorphismsForgetTypeHom
  let _ : IsAlgebraicStructure (Type u) (forget (Type u)) := inferInstance
  simpa using
    (closedSubsetSheafPushforward_essImage_iff_stalk_isTerminal_of_not_mem Z hZ 𝒢)

end
