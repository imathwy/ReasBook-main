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

local instance : Limits.HasZeroMorphisms (Sheaf J (ModuleCat.{w} Λ)) :=
  Preadditive.preadditiveHasZeroMorphisms

local instance (U : C) : Limits.HasZeroMorphisms (Sheaf (J.over U) (ModuleCat.{w} Λ)) :=
  Preadditive.preadditiveHasZeroMorphisms

/-- The constant-sheaf functor on `\Lambda`-modules preserves zero morphisms. -/
instance constantSheaf_preservesZeroMorphisms :
    (constantSheaf J (ModuleCat.{w} Λ)).PreservesZeroMorphisms := sorry

/-- The functor sending a cochain complex of `\Lambda`-modules to the corresponding constant
complex of sheaves of `\Lambda`-modules on `(C, J)`. -/
abbrev constantModuleComplex :
    CochainComplex (ModuleCat.{w} Λ) ℤ ⥤
      CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ :=
  (constantSheaf J (ModuleCat.{w} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Restriction of sheaves of `\Lambda`-modules from `(C, J)` to the localized site
`(C/U, J.over U)`. -/
abbrev localizedModuleRestriction (U : C) :
    Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ) :=
  J.overPullback (ModuleCat.{w} Λ) U

/-- Restriction to the slice site over `U` preserves zero morphisms. -/
instance localizedModuleRestriction_preservesZeroMorphisms (U : C) :
    ((localizedModuleRestriction U) :
      Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ)).PreservesZeroMorphisms := sorry

/-- Restriction to the slice site over `U` is additive. -/
instance localizedModuleRestriction_additive (U : C) :
    ((localizedModuleRestriction U) :
      Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ)).Additive := sorry

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

/-- Restriction of cochain complexes of sheaves of `\Lambda`-modules to the localized site over
`U`. -/
abbrev localizedModuleRestrictionComplex (U : C) :
    CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ ⥤
      CochainComplex (Sheaf (J.over U) (ModuleCat.{w} Λ)) ℤ :=
  (((localizedModuleRestriction U) :
      Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ))).mapHomologicalComplex
    (ComplexShape.up ℤ)

-- Proof sketch: after restricting the constant complex associated with `K` and the target complex
-- `L` to a suitable covering of the final object `X`, choose local morphisms of complexes between
-- those restrictions. In the full theorem, these become the local chain-level representatives of a
-- restricted derived morphism.
/-- Lemma 21.53.2: if `X` is a final object of the site, `K^\bullet` is a bounded complex of
finite projective `\Lambda`-modules, and `\mathcal L^\bullet` is a complex of sheaves of
`\Lambda`-modules, then there exists a covering of `X` on whose members there are morphisms of
complexes `\underline{K}^\bullet|_{U_i} \to \mathcal L^\bullet|_{U_i}`. -/
theorem exists_cover_local_chain_map_of_isBoundedFiniteProjective
    (X : C) (_hX : Limits.IsTerminal X)
    (K : CochainComplex (ModuleCat.{w} Λ) ℤ) [K.IsBoundedFiniteProjective]
    (L : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) :
    ∃ T : J.Cover X, ∀ I : T.Arrow,
      Nonempty
        (((localizedModuleRestrictionComplex I.Y).obj (constantModuleComplex.obj K)) ⟶
          ((localizedModuleRestrictionComplex I.Y).obj L)) := sorry

end

end CategoryTheory.Sheaf
