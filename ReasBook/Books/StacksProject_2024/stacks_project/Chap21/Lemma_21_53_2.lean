import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap21.Lemma_21_53_Support

open CategoryTheory
open ComplexShape
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
variable [∀ U : C, (J.overPullback (ModuleCat Λ) U).Additive]
variable [∀ U : C, PreservesFiniteLimits (J.overPullback (ModuleCat Λ) U)]
variable [∀ U : C, PreservesFiniteColimits (J.overPullback (ModuleCat Λ) U)]

local notation "Mod" => Sheaf J (ModuleCat Λ)
local notation "ModOver[" U "]" => Sheaf (J.over U) (ModuleCat Λ)
local notation "CpxMod" => CochainComplex (ModuleCat Λ) ℤ
local notation "CpxSheaf" => CochainComplex Mod ℤ
local notation "CpxOver[" U "]" => CochainComplex ModOver[U] ℤ
local notation "res[" U "]" => (J.overPullback (ModuleCat Λ) U)

/-- The constant-sheaf functor on `Λ`-module complexes. -/
abbrev constantSheafComplexFunctor : CpxMod ⥤ CpxSheaf :=
  (constantSheaf J (ModuleCat Λ)).mapHomologicalComplex (up ℤ)

/-- Restrict a complex of sheaves of `Λ`-modules to the slice site over `U`. -/
abbrev restrictedSheafComplexFunctor (U : C) : CpxSheaf ⥤ CpxOver[U] :=
  (res[U]).mapHomologicalComplex (up ℤ)

/-- The ambient derived object represented by a complex of sheaves of `Λ`-modules. -/
abbrev derivedSheafObject (L : CpxSheaf) : DerivedCategory Mod :=
  DerivedCategory.Q.obj L

/-- The ambient derived object represented by the constant sheaf complex on `K`. -/
abbrev constantDerivedSheafObject (K : CpxMod) : DerivedCategory Mod :=
  derivedSheafObject (constantSheafComplexFunctor.obj K)

/-- Restrict a complex of sheaves of `Λ`-modules to the slice site over `U`. -/
abbrev restrictedSheafComplex (L : CpxSheaf) (U : C) : CpxOver[U] :=
  (restrictedSheafComplexFunctor U).obj L

/-- Restrict the constant sheaf complex on `K` to the slice site over `U`. -/
abbrev restrictedConstantSheafComplex (K : CpxMod) (U : C) : CpxOver[U] :=
  restrictedSheafComplex
    (constantSheafComplexFunctor.obj K) U

/- Domain-style sampling for Lemma 21.53.2:
- primary domain: restriction of derived morphisms of sheaf complexes on a site to slice sites and
  their local chain-level representatives;
- sampled owner declarations:
  `constantSheaf`,
  `Functor.mapDerivedCategory`,
  `Functor.mapDerivedCategoryFactors`,
  `DerivedCategory.Q`,
  `CategoryTheory.CommSq`;
- best owner abstraction:
  `source-facing`: a fixed derived morphism from a constant sheaf complex to a sheaf complex and
  local chain maps representing its restrictions;
  `core/canonical`: the slice restriction owner `J.overPullback (ModuleCat Λ) U`, the canonical
  derived quotient owner `DerivedCategory.Q`, and the induced derived functor
  `(J.overPullback (ModuleCat Λ) U).mapDerivedCategory`;
  `bridge/view`: the canonical comparison isomorphism
  `(J.overPullback (ModuleCat Λ) U).mapDerivedCategoryFactors` and the resulting `CommSq`
  relating restricted chain maps to restricted derived morphisms.

This item is therefore kept at the `source-facing` layer, while the statement itself binds the
canonical restriction owner and its derived bridge directly on the theorem surface, instead of
introducing theorem-local wrapper declarations. -/

/-- A derived morphism from the constant sheaf complex on `K` to `L` is locally represented by
chain maps if, after restricting to a cover of `X`, each restricted derived morphism fits into
the canonical `mapDerivedCategoryFactors` comparison square with a morphism of restricted
complexes. -/
def HasLocalChainMapRepresentation
    (X : C) (K : CpxMod) (L : CpxSheaf)
    (φ : constantDerivedSheafObject K ⟶ derivedSheafObject L) : Prop :=
  ∃ T : J.Cover X, ∀ I : T.Arrow,
    ∃ f : restrictedConstantSheafComplex K I.Y ⟶ restrictedSheafComplex L I.Y,
      CommSq
        (((res[I.Y]).mapDerivedCategory).map φ)
        (((res[I.Y]).mapDerivedCategoryFactors.app
          (constantSheafComplexFunctor.obj K)).hom)
        (((res[I.Y]).mapDerivedCategoryFactors.app L).hom)
        (DerivedCategory.Q.map f)

omit [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat Λ)]
  [CategoryWithHomology Mod]
  [∀ U : C, CategoryWithHomology (Sheaf (J.over U) (ModuleCat Λ))] in
/-- Unfolding `HasLocalChainMapRepresentation` gives the explicit cover-wise chain-map
representation criterion. -/
theorem hasLocalChainMapRepresentation_iff
    (X : C) (K : CpxMod) (L : CpxSheaf)
    (φ : constantDerivedSheafObject K ⟶ derivedSheafObject L) :
    HasLocalChainMapRepresentation X K L φ ↔
      ∃ T : J.Cover X, ∀ I : T.Arrow,
        ∃ f : restrictedConstantSheafComplex K I.Y ⟶ restrictedSheafComplex L I.Y,
          CommSq
            (((res[I.Y]).mapDerivedCategory).map φ)
            (((res[I.Y]).mapDerivedCategoryFactors.app
              (constantSheafComplexFunctor.obj K)).hom)
            (((res[I.Y]).mapDerivedCategoryFactors.app L).hom)
            (DerivedCategory.Q.map f) :=
  Iff.rfl

-- Proof sketch: once the additive constant-sheaf and restriction functors are available, form the
-- induced derived restriction functors and their comparison isomorphisms. The statement then says
-- that after passing to a cover of `X`, the restricted derived morphism fits into the canonical
-- comparison square with a local chain map.
/-- Lemma 21.53.2: if `K^•` is a bounded complex of finite projective `Λ`-modules and `L^•` is a
complex of sheaves of `Λ`-modules, then every derived morphism from the constant sheaf complex on
`K^•` to `L^•` is, after restricting to a cover of `X`, represented by morphisms of complexes on
the slice sites. In Lean, the restriction functor on derived categories is the canonical owner
`(res[U]).mapDerivedCategory`, its comparison with restricted complexes is
`(res[U]).mapDerivedCategoryFactors`, and the resulting compatibility is expressed by
`CategoryTheory.CommSq`. -/
@[stacks 09BD]
theorem exists_cover_local_chain_map_of_isBoundedFiniteProjective
    (X : C)
    (K : CpxMod) [K.IsBoundedFiniteProjective]
    (L : CpxSheaf)
    (φ : constantDerivedSheafObject K ⟶ derivedSheafObject L) :
    HasLocalChainMapRepresentation X K L φ := by
  sorry

end

end CategoryTheory.Sheaf
