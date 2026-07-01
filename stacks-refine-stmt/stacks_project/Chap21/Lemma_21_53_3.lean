import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import stacks_project.Chap15.Definition_15_75_1

open CategoryTheory

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))]
variable [CategoryWithHomology (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, CategoryWithHomology (Sheaf (J.over U) (ModuleCat.{w} Λ))]

/-- The constant-sheaf functor on `\Lambda`-modules is additive. -/
instance constantSheaf_additive :
    @Functor.Additive (ModuleCat.{w} Λ) (Sheaf J (ModuleCat.{w} Λ)) _ _
      ModuleCat.abelian.toPreadditive
      ((inferInstance : Abelian (Sheaf J (ModuleCat.{w} Λ))).toPreadditive)
      (constantSheaf J (ModuleCat.{w} Λ)) := sorry

/-- The constant-sheaf functor on `\Lambda`-modules preserves finite limits. -/
instance constantSheaf_preservesFiniteLimits :
    Limits.PreservesFiniteLimits (constantSheaf J (ModuleCat.{w} Λ)) := sorry

/-- The constant-sheaf functor on `\Lambda`-modules preserves finite colimits. -/
instance constantSheaf_preservesFiniteColimits :
    Limits.PreservesFiniteColimits (constantSheaf J (ModuleCat.{w} Λ)) := sorry

/-- The constant-sheaf functor on the slice site over `U` is additive. -/
instance constantSheaf_over_additive (U : C) :
    @Functor.Additive (ModuleCat.{w} Λ) (Sheaf (J.over U) (ModuleCat.{w} Λ)) _ _
      ModuleCat.abelian.toPreadditive
      ((inferInstance : Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))).toPreadditive)
      (constantSheaf (J.over U) (ModuleCat.{w} Λ)) := sorry

/-- The constant-sheaf functor on the slice site over `U` preserves finite limits. -/
instance constantSheaf_over_preservesFiniteLimits (U : C) :
    Limits.PreservesFiniteLimits (constantSheaf (J.over U) (ModuleCat.{w} Λ)) := sorry

/-- The constant-sheaf functor on the slice site over `U` preserves finite colimits. -/
instance constantSheaf_over_preservesFiniteColimits (U : C) :
    Limits.PreservesFiniteColimits (constantSheaf (J.over U) (ModuleCat.{w} Λ)) := sorry

/-- Restriction of sheaves of `\Lambda`-modules from `(C, J)` to the localized site
`(C/U, J.over U)`. -/
abbrev localizedModuleRestriction (U : C) :
    Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ) :=
  J.overPullback (ModuleCat.{w} Λ) U

/-- Restriction to the slice site over `U` is additive. -/
instance localizedModuleRestriction_additive (U : C) :
    @Functor.Additive (Sheaf J (ModuleCat.{w} Λ)) (Sheaf (J.over U) (ModuleCat.{w} Λ)) _ _
      ((inferInstance : Abelian (Sheaf J (ModuleCat.{w} Λ))).toPreadditive)
      ((inferInstance : Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))).toPreadditive)
      ((localizedModuleRestriction U) :
        Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ)) := sorry

/-- Restriction to the slice site over `U` preserves finite limits. -/
instance localizedModuleRestriction_preservesFiniteLimits (U : C) :
    Limits.PreservesFiniteLimits
      ((localizedModuleRestriction U) :
        Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ)) := sorry

/-- Restriction to the slice site over `U` preserves finite colimits. -/
instance localizedModuleRestriction_preservesFiniteColimits (U : C) :
    Limits.PreservesFiniteColimits
      ((localizedModuleRestriction U) :
        Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ)) := sorry

/-- The exact functor on derived categories sending `K ∈ D(\Lambda)` to the constant sheaf
`\underline K ∈ D(\mathcal C, \Lambda)`. -/
abbrev constantModuleDerived :
    DerivedCategory (ModuleCat.{w} Λ) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{w} Λ)) :=
  Functor.mapDerivedCategory (constantSheaf J (ModuleCat.{w} Λ))

/-- The exact functor on derived categories sending `K ∈ D(\Lambda)` to the constant derived
object on the slice site `(C/U, J.over U)`. -/
abbrev constantModuleDerivedOver (U : C) :
    DerivedCategory (ModuleCat.{w} Λ) ⥤
      DerivedCategory (Sheaf (J.over U) (ModuleCat.{w} Λ)) :=
  Functor.mapDerivedCategory (constantSheaf (J.over U) (ModuleCat.{w} Λ))

/-- The exact restriction functor on derived categories from `(C, J)` to the localized site
`(C/U, J.over U)`. -/
abbrev localizedModuleRestrictionDerived (U : C) :
    DerivedCategory (Sheaf J (ModuleCat.{w} Λ)) ⥤
      DerivedCategory (Sheaf (J.over U) (ModuleCat.{w} Λ)) :=
  Functor.mapDerivedCategory (localizedModuleRestriction U)

/-- A restricted morphism of constant derived objects is induced by a fixed morphism
`α : K ⟶ L` in `D(\Lambda)` when, after identifying the restricted constant objects with the
constant derived objects on the slice site, it becomes the constant-sheaf image of `α`. -/
def IsLocalizedConstantDerivedMap
    (U : C) (K L : DerivedCategory (ModuleCat.{w} Λ)) (α : K ⟶ L)
    (φ :
      ((localizedModuleRestrictionDerived U).obj
        (((constantModuleDerived :
            DerivedCategory (ModuleCat.{w} Λ) ⥤
              DerivedCategory (Sheaf J (ModuleCat.{w} Λ))).obj K))) ⟶
        ((localizedModuleRestrictionDerived U).obj
          (((constantModuleDerived :
              DerivedCategory (ModuleCat.{w} Λ) ⥤
                DerivedCategory (Sheaf J (ModuleCat.{w} Λ))).obj L)))) : Prop :=
  ∃ eK :
      ((localizedModuleRestrictionDerived U).obj
        (((constantModuleDerived :
            DerivedCategory (ModuleCat.{w} Λ) ⥤
              DerivedCategory (Sheaf J (ModuleCat.{w} Λ))).obj K))) ≅
        ((constantModuleDerivedOver U).obj K),
    ∃ eL :
      ((localizedModuleRestrictionDerived U).obj
        (((constantModuleDerived :
            DerivedCategory (ModuleCat.{w} Λ) ⥤
              DerivedCategory (Sheaf J (ModuleCat.{w} Λ))).obj L))) ≅
        ((constantModuleDerivedOver U).obj L),
      φ = eK.hom ≫
        (constantModuleDerivedOver U).map α ≫
          eL.inv

-- Proof sketch: choose a bounded finite-projective complex representing the perfect object `K`.
-- Apply Lemma `21.53.2` to obtain, after restricting to a cover of the terminal object, local
-- chain maps from the restricted constant complex of that representative. Degreewise, the source
-- terms are finite type locally constant, so Lemma `18.43.3` refines the cover until each local
-- chain map is induced by a chain map of constant sheaves. Passing to the derived category yields
-- local morphisms `α_i : K ⟶ L` whose constant-sheaf images agree with the restricted morphism.
/-- Lemma 21.53.3: if `X` is a final object of the site, `K, L ∈ D(\Lambda)`, `K` is perfect, and
`\varphi : \underline K \to \underline L` is a morphism in `D(\mathcal C, \Lambda)`, then after
restricting to some covering of `X` each local morphism is induced by a morphism
`\alpha_i : K \to L` in `D(\Lambda)`. In Lean, because the identification between the restricted
constant objects and the constant objects on the slice site is not definitional, this is expressed
using the explicit comparison proposition `IsLocalizedConstantDerivedMap`. -/
theorem exists_cover_restriction_eq_constant_derived_map_of_perfect
    (X : C) (_hX : Limits.IsTerminal X)
    (K L : DerivedCategory (ModuleCat.{w} Λ))
    (hK : DerivedCategory.IsPerfect K)
    (φ :
      (((constantModuleDerived :
          DerivedCategory (ModuleCat.{w} Λ) ⥤
            DerivedCategory (Sheaf J (ModuleCat.{w} Λ))).obj K)) ⟶
        (((constantModuleDerived :
            DerivedCategory (ModuleCat.{w} Λ) ⥤
              DerivedCategory (Sheaf J (ModuleCat.{w} Λ))).obj L))) :
    ∃ T : J.Cover X, ∀ I : T.Arrow,
      ∃ α : K ⟶ L,
        IsLocalizedConstantDerivedMap I.Y K L α
          ((localizedModuleRestrictionDerived I.Y).map φ) := sorry

end

end CategoryTheory.Sheaf
