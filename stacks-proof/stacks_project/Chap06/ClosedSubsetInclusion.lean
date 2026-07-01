import Mathlib

open TopCat TopologicalSpace

universe u

namespace TopCat

/-- The inclusion morphism of a subset into its ambient topological space. -/
abbrev subsetInclusion (X : TopCat.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion morphism of a closed subset into its ambient topological space. -/
abbrev closedSubsetInclusion (X : TopCat.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  subsetInclusion X Z

end TopCat

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

section SubsetSheafPushforward

universe v w

variable {X : TopCat.{v}}
variable {C : Type w} [Category.{v} C]
variable {FC : C → C → Type v} {CC : C → Type v}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory.{v} C FC]
variable [HasColimits C] [HasLimits C]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable [HasWeakSheafify (Opens.grothendieckTopology X) C]

/-- The counit `i⁻¹ i_* ⟶ 𝟭` of the pullback–pushforward adjunction along a subset inclusion
`i = subsetInclusion X Z` is an isomorphism.

PROOF DEFERRED (`sorry`). This is the substantive content of the full-faithfulness half of
Stacks 00AF/00AG: `i` is a topological embedding (`Subtype.val` with the subspace topology), and the
counit can be checked to be an isomorphism stalkwise, using that `stalkPushforward` is an
isomorphism along an embedding. Only this `Prop` obligation is deferred; the *data*
`subsetSheafPushforward_fullyFaithful` below is built sorry-free from this fact via the standard
right-adjoint criterion. -/
theorem subsetSheafPushforward_counit_isIso (Z : Set X) :
    IsIso (TopCat.Sheaf.pullbackPushforwardAdjunction C (X.subsetInclusion Z)).counit :=
  sorry

/-- Stacks 00AF/00AG, full-faithfulness half: for the inclusion `i : Z → X` of a subset
(in particular a closed subset), the sheaf pushforward `i_* : Sh(Z) ⥤ Sh(X)` is fully faithful.

This is the upstream owner recalled by Lemma 6.32.2 (sheaves of sets) and Lemma 6.32.3 (sheaves of
abelian groups). It is constructed as the right adjoint of the pullback–pushforward adjunction
together with the invertibility of the counit (`subsetSheafPushforward_counit_isIso`); the
`FullyFaithful` datum itself contains no `sorry`. -/
noncomputable def subsetSheafPushforward_fullyFaithful (Z : Set X) :
    (TopCat.Sheaf.pushforward C (X.subsetInclusion Z)).FullyFaithful :=
  letI := subsetSheafPushforward_counit_isIso (C := C) Z
  (TopCat.Sheaf.pullbackPushforwardAdjunction C (X.subsetInclusion Z)).fullyFaithfulROfIsIsoCounit

end SubsetSheafPushforward
