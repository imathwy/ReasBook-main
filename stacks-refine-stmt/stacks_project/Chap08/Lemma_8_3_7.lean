import Mathlib
import stacks_project.Chap07.Definition_7_12_1
import stacks_project.Chap08.Lemma_8_3_3
import stacks_project.Chap08.Definition_8_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory
open CategoryTheory.Limits
namespace CategoryTheory

/- Domain-style sampling for Lemma 8.3.7:
- primary domain: effective descent for fixed-target covering families in a fibred category, and
  invariance of descent under refinement.
- inspected owner-level declarations:
  `SemiRepresentableFamily.Over`,
  `baseChange`,
  `pullbackFamilyDescentFunctor`,
  `familyDescentFunctor`,
  `Pseudofunctor.DescentData.isEquivalence_toDescentData_of_sieve_le`.
- best owner abstraction: the source-facing owner remains `familyDescentFunctor hc 𝒰`; the
  refinement comparison uses the bridge `pullbackFamilyDescentFunctor hc (𝟙 U) φ`, while the
  generic descent-stability machinery lives in the mathlib owner theorems for descent data.
- primitive data: two fixed-target families `𝒱 ⟶ 𝒰`, together with the canonical restricted
  families `𝒱_i := baseChange 𝒱 (𝒰.obj i).hom` and
  `𝒱_{ii'} := baseChange 𝒱 (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)`.
- derived API: the local fully faithful and faithful descent functors on the base-changed
  families, and the resulting equivalence for `familyDescentFunctor hc 𝒰`.

Source/core/bridge triage:
- `source-facing`: Lemma 8.3.7 itself, stated for a refinement `φ : 𝒱 ⟶ 𝒰` of fixed-target
  families.
- `core/canonical`: the generic descent-data functors and equivalence criteria in
  `Pseudofunctor.DescentData`.
- `bridge/view`: `familyDescentFunctor` and `pullbackFamilyDescentFunctor`, which specialize those
  owner constructions to the chapter's chosen-overlap family presentation.
-/

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)

open SemiRepresentableFamily.Over

namespace SemiRepresentableFamily.Over

/-- For a family `𝒱` over `U` and a member `Uᵢ ⟶ U` of `𝒰`, the restricted family `𝒱ᵢ` is the
base change of `𝒱` along `Uᵢ ⟶ U`. -/
abbrev memberBaseChange {U : C} (𝒱 𝒰 : SemiRepresentableFamily.Over U)
    [h : ∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    (i : 𝒰.index) : SemiRepresentableFamily.Over ((𝒰.obj i).left) :=
  @baseChange _ _ _ 𝒱 _ (𝒰.obj i).hom (h i)

/-- For a family `𝒱` over `U` and a pairwise overlap `Uᵢ ×[U] Uᵢ'` of `𝒰`, the restricted family
`𝒱ᵢᵢ'` is the base change of `𝒱` along `Uᵢ ×[U] Uᵢ' ⟶ U`. -/
abbrev overlapBaseChange {U : C} (𝒱 𝒰 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    [h : ∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    (i i' : 𝒰.index) : SemiRepresentableFamily.Over (𝒰.overlap i i') :=
  @baseChange _ _ _ 𝒱 _ (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) (h i i')

end SemiRepresentableFamily.Over

-- Proof sketch: pull a descent datum on `𝒰` back to one on `𝒱` along the refinement morphism
-- `φ : 𝒱 ⟶ 𝒰` using Lemma `8.3.3`; by
-- effectiveness for `𝒱`, it comes from a global object over `U`. The fully faithful local
-- functors for the families `𝒱_i` identify the restrictions of that global object with the given
-- local pieces over each `U_i`, and the faithfulness for `𝒱_{ii'}` forces compatibility on
-- pairwise overlaps. This yields essential surjectivity, while the same local full-faithfulness
-- and overlap faithfulness give full faithfulness of the canonical descent functor for `𝒰`.
/-- Lemma 8.3.7: let `φ : 𝒱 ⟶ 𝒰` be a refinement of fixed-target families over `U`, and for each
`i` and `(i,i')` write `𝒱_i = baseChange 𝒱 (𝒰.obj i).hom` and
`𝒱_{ii'} = baseChange 𝒱 (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)`. Assume descent data
are defined for `𝒰`, `𝒱`, every `𝒱_i`, and every `𝒱_{ii'}`. If `𝒮_U ⥤ DD(𝒱)` is an equivalence,
if each `𝒮_{U_i} ⥤ DD(𝒱_i)` is fully faithful, and if each
`𝒮_{U_i ×[U] U_{i'}} ⥤ DD(𝒱_{ii'})` is faithful, then `𝒮_U ⥤ DD(𝒰)` is an equivalence. -/
theorem familyDescentFunctor_isEquivalence_of_refinement
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    [∀ i : 𝒰.index,
      HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    [∀ i i' : 𝒰.index,
      HasDescentPullbacks (𝒱.overlapBaseChange 𝒰 i i')]
    [∀ i : 𝒰.index,
      Functor.Full (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    [∀ i : 𝒰.index,
      Functor.Faithful (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    [∀ i i' : 𝒰.index,
      Functor.Faithful (familyDescentFunctor hc (𝒱.overlapBaseChange 𝒰 i i'))]
    (φ : 𝒱 ⟶ 𝒰) [Functor.IsEquivalence (familyDescentFunctor hc 𝒱)] :
    Functor.IsEquivalence (familyDescentFunctor hc 𝒰) := sorry

end CategoryTheory
