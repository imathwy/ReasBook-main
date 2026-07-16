import Mathlib
import StacksProject_2024.stacks_project.Chap04.Lemma_4_35_7
import StacksProject_2024.stacks_project.Chap08.Definition_8_5_5
import StacksProject_2024.stacks_project.Chap08.Definition_8_6_1
import StacksProject_2024.stacks_project.Chap08.Lemma_8_5_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open StackInGroupoidsOver
open StackInGroupoidsOver.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

section

variable {S₁ S₂ T₁ : StackInGroupoidsOver J}
variable (F : S₂ ⟶ S₁) (G : T₁ ⟶ S₁)

/-
Domain-style sampling for Lemma 8.6.10:
- primary domain: stacks in groupoids/setoids over a site, together with canonical and arbitrary
  bicategorical `2`-fibre products;
- sampled owner-level declarations:
  `IsStackInSetoids`,
  `StackInGroupoidsOver.twoFibreProduct`,
  `StackInGroupoidsOver.twoFibreProductSquare`,
  `StackInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`,
  `StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects`,
  `BicategoricalTwoCommutativeSquare` and `Bicategory.IsFinal`;
- best owner abstraction: this lemma should be stated over the ambient stack morphisms
  `F : S₂ ⟶ S₁` and `G : T₁ ⟶ S₁`, with the canonical
  Chapter 8 pullback owner `StackInGroupoidsOver.twoFibreProduct F G` and its final square
  `StackInGroupoidsOver.twoFibreProductSquare F G` as the core model; arbitrary
  `2`-cartesian squares are then treated only as a bridge/view;
- primitive data: the stack morphisms `F` and `G`, the propositional full-faithfulness and local
  essential-surjectivity hypotheses on `F`, and the stack-in-setoids hypothesis on the canonical
  stack pullback apex `(twoFibreProduct F G).p`;
- derived API: transport of the explicit-pullback statement across a square carrying the owner
  predicate `Bicategory.IsFinal`.

Source/core/bridge triage:
- `source-facing`: the two descent lemmas below;
- `core/canonical`: `IsStackInSetoids`, `StackInGroupoidsOver.twoFibreProduct`,
  `StackInGroupoidsOver.twoFibreProductSquare`,
  `StackInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`,
  `StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects`, and `Bicategory.IsFinal`;
- `bridge/view`: the arbitrary-square theorem as transport of the explicit-pullback form. -/

-- Proof sketch: by Categories, Lemma `4.32.3`, the `2`-cartesian square may be replaced by the
-- explicit pullback `S₂ ×[S₁] T₁`, whose objects over `U` are triples `(x, y, f)` with
-- `x ∈ (S₂)_U`, `y ∈ (T₁)_U`, and `f : F(x) ≅ G(y)`. The local essential-image hypothesis on `F`
-- lets one lift any object `y` of `T₁` locally to an object of this pullback. Full faithfulness
-- of `F` makes the map on automorphism sheaves from the pullback object to `y` surjective, while
-- the pullback being a stack in setoids makes the source automorphism sheaf trivial. Hence every
-- automorphism sheaf in `T₁` is trivial, so each fiber of `T₁` is a setoid.
/-- Pullback-owner form of Lemma 8.6.10: it suffices to assume that the Chapter 8 canonical
stack pullback `twoFibreProduct F G` is a stack in setoids. The arbitrary-square form is obtained
by transporting this statement across any final square over `F` and `G`. -/
theorem isStackInSetoids_of_fullyFaithful_locallyEssentiallySurjective_pullback
    (hF : Nonempty F.toBasedFunctor.FullyFaithful)
    (hFess : F.LocallyEssentiallySurjectiveOnObjects)
    [IsStackInSetoids J (twoFibreProduct F G).p] :
    IsStackInSetoids J T₁.p := by
  sorry

/-- Lemma 8.6.10: for any bicategorical `2`-fibre product square `P` of stacks in groupoids over
`(C, J)` with left leg `F` and right leg `G`, if `F` is fully faithful and locally essentially
surjective on objects of the fibers, and if the apex of `P` is a stack in setoids, then `T₁` is
a stack in setoids. This is the bridge/view form of the pullback-owner theorem above, transported
from the canonical final square `twoFibreProductSquare F G`. -/
theorem isStackInSetoids_of_twoCartesian_of_fullyFaithful_locallyEssentiallySurjective
    (hF : Nonempty F.toBasedFunctor.FullyFaithful)
    (hFess : F.LocallyEssentiallySurjectiveOnObjects)
    (P : BicategoricalTwoCommutativeSquare F G)
    (hcart : Bicategory.IsFinal P)
    [IsStackInSetoids J P.obj.p] :
    IsStackInSetoids J T₁.p := by
  sorry

end

end CategoryTheory
