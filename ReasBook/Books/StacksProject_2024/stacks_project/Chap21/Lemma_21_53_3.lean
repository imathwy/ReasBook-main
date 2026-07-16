import StacksProject_2024.stacks_project.Chap15.Definition_15_75_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_53_Support

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat Λ)]
variable [Abelian (Sheaf J (ModuleCat Λ))]
variable [∀ U : C, Abelian (Sheaf (J.over U) (ModuleCat Λ))]
variable [CategoryWithHomology (Sheaf J (ModuleCat Λ))]
variable [∀ U : C, CategoryWithHomology (Sheaf (J.over U) (ModuleCat Λ))]
variable [J.WEqualsLocallyBijective (ModuleCat Λ)]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective (ModuleCat Λ)]
variable [(constantSheaf J (ModuleCat Λ)).Additive]
variable [PreservesFiniteLimits (constantSheaf J (ModuleCat Λ))]
variable [PreservesFiniteColimits (constantSheaf J (ModuleCat Λ))]
variable [∀ U : C, (constantSheaf (J.over U) (ModuleCat Λ)).Additive]
variable [∀ U : C, PreservesFiniteLimits (constantSheaf (J.over U) (ModuleCat Λ))]
variable [∀ U : C, PreservesFiniteColimits (constantSheaf (J.over U) (ModuleCat Λ))]
variable [∀ U : C, (J.overPullback (ModuleCat Λ) U).Additive]
variable [∀ U : C, PreservesFiniteLimits (J.overPullback (ModuleCat Λ) U)]
variable [∀ U : C, PreservesFiniteColimits (J.overPullback (ModuleCat Λ) U)]

/- Domain-style sampling for Lemma 21.53.3:
- primary domain: restriction of constant derived sheaf objects to slice sites and comparison with
  the constant derived objects on those slice sites;
- sampled owner declarations:
  `constantSheaf`,
  `Sheaf.constantSheafOverObjIso`,
  `Functor.mapDerivedCategory`,
  `CategoryTheory.CommSq`;
- best owner abstraction:
  `source-facing`: the local claim that a restricted morphism between constant derived objects is,
  after comparison with the slice-site constant objects, induced by a morphism in `D(Λ)`;
  `core/canonical`: the ambient constant-sheaf derived functor, the slice constant-sheaf derived
  functors, and the slice restriction derived functors obtained from
  `Functor.mapDerivedCategory`;
  `bridge/view`: the comparison isomorphisms between restricted ambient constant objects and slice
  constant objects, now owned by `constantSheafOverIso` and `constantSheafOverDerivedIso` in
  `Lemma_21_53_Support`.
- primitive data: the fixed derived morphism `φ` and the inducing morphism `α`;
- derived API: the theorem now uses the canonical derived owners directly instead of theorem-local
  wrapper functors and explicit exactness/additivity parameters.

This item is therefore refined at the `bridge/view` layer: the theorem keeps the source-facing
local lifting statement, while deleting the parallel local wrapper API around the canonical derived
functors. -/

-- Proof sketch: choose a bounded finite-projective complex representing the perfect object `K`.
-- Apply Lemma `21.53.2` to obtain, after restricting to a cover of the terminal object, local
-- chain maps from the restricted constant complex of that representative. Degreewise, the source
-- terms are finite type locally constant, so Lemma `18.43.3` refines the cover until each local
-- chain map is induced by a chain map of constant sheaves. Passing to the derived category yields
-- local morphisms `α_i : K ⟶ L` whose constant-sheaf images agree with the restricted morphism.
/-- Lemma 21.53.3: if `X` is a final object of the site, `K, L ∈ D(Λ)`, `K` is perfect, and
`φ` is a morphism from the constant derived object of `K` to the constant derived object of `L`,
then after restricting to some covering of `X` each local morphism is induced by a morphism
`α_i : K ⟶ L` in `D(Λ)`. In Lean,
the theorem is stated directly with the canonical derived functors
`(constantSheaf J (ModuleCat Λ)).mapDerivedCategory`,
`(J.overPullback (ModuleCat Λ) U).mapDerivedCategory`,
`(constantSheaf (J.over U) (ModuleCat Λ)).mapDerivedCategory`, and the canonical bridge
`constantSheafOverDerivedIso`. -/
@[stacks 09BE]
theorem exists_cover_restriction_eq_constant_derived_map_of_perfect
    (X : C) (hX : IsTerminal X) (K L : DerivedCategory (ModuleCat Λ))
    (hK : K.IsPerfect)
    (φ :
      ((constantSheaf J (ModuleCat Λ)).mapDerivedCategory.obj K) ⟶
        ((constantSheaf J (ModuleCat Λ)).mapDerivedCategory.obj L)) :
    ∃ T : J.Cover X, ∀ I : T.Arrow,
      ∃ α : K ⟶ L,
        CommSq
          (((J.overPullback (ModuleCat Λ) I.Y).mapDerivedCategory).map φ)
          ((constantSheafOverDerivedIso I.Y).hom.app K)
          ((constantSheafOverDerivedIso I.Y).hom.app L)
          (((constantSheaf (J.over I.Y) (ModuleCat Λ)).mapDerivedCategory).map α) := by
  sorry

end

end CategoryTheory.Sheaf
