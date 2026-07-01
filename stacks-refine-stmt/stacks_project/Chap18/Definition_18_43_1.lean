import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w w'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Sheaf

/- Domain-style sampling for Definition 18.43.1:
- primary domain: locally constant sheaves on a site and their finite variants.
- sampled owner-level declarations:
  `CategoryTheory.Sheaf.IsConstant`,
  `CategoryTheory.constantSheaf`,
  `GrothendieckTopology.over`,
  `GrothendieckTopology.overPullback`.
- best owner abstraction: `Sheaf.IsLocallyConstant`, built from the canonical restriction
  functors `F.over` and the owner predicate `Sheaf.IsConstant` on slice sites.
- primitive data: for each `U : C`, a covering in `J.over U` on which the restricted sheaf is
  constant.
- derived API: finite locally constant variants, obtained by adjoining finiteness conditions on
  the local constant models.

Source/core/bridge triage:
- `source-facing`: `Sheaf.IsLocallyConstant`, `Sheaf.IsFiniteLocallyConstant`,
  `Sheaf.IsFiniteLocallyConstantGrp`, `Sheaf.IsFiniteLocallyConstantAddCommGrp`,
  `Sheaf.IsFiniteTypeLocallyConstantModule`.
- `core/canonical`: `Sheaf.IsConstant`, `constantSheaf`, and sheaf restriction to slice sites.
- `bridge/view`: the constant-sheaf instances showing that a global constant sheaf is locally
  constant, and that finite constant models yield finite locally constant sheaves. -/

section Constant

variable {D : Type w} [Category.{w'} D] [HasWeakSheafify J D]

/- Constant sheaf recall: for a sheaf of sets, groups, abelian groups, rings, modules, and
similar algebraic objects on a site `(C, J)`, being a constant sheaf is the canonical mathlib
predicate `Sheaf.IsConstant`, meaning that the sheaf lies in the essential image of the constant
sheaf functor. -/
#check IsConstant

end Constant

section LocallyConstant

variable {D : Type w} [Category.{w'} D]
variable [HasWeakSheafify J D]
variable [∀ U : C, HasWeakSheafify (J.over U) D]

/-- Definition 18.43.1 (1): a sheaf on a site is locally constant if, after restricting to the
localized site above any object `U`, there is a covering family of `U` on which the further
restrictions become constant sheaves. -/
class IsLocallyConstant (F : Sheaf J D) : Prop where
  /-- Every object admits a covering on which the restriction of `F` is constant. -/
  exists_constant_cover :
    ∀ U : C,
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I, IsConstant (J.over (X i).left) (F.over (X i).left)

-- Proof sketch: for each object `U`, use the singleton covering of `U` by the identity
-- `𝟙_U : U ⟶ U`; the restriction of a constant sheaf to `U` is again constant by functoriality
-- of `constantSheaf` with respect to localization.
/-- A constant sheaf is locally constant. -/
instance isLocallyConstant_of_isConstant (F : Sheaf J D) [IsConstant J F] :
    IsLocallyConstant F := sorry

end LocallyConstant

section FiniteLocallyConstantTypes

variable [HasWeakSheafify J (Type w)]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]

/-- Definition 18.43.1 (2): a set-valued sheaf is finite locally constant if, locally on every
object of the site, it is isomorphic to a constant sheaf with finite value. -/
class IsFiniteLocallyConstant (F : Sheaf J (Type w)) : Prop extends IsLocallyConstant F where
  /-- Every object admits a covering on which the restriction of `F` is a constant sheaf with
  finite value. -/
  exists_finite_constant_cover :
    ∀ U : C,
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I,
          ∃ E : Type w, Finite E ∧
            Nonempty (F.over (X i).left ≅ (constantSheaf (J.over (X i).left) (Type w)).obj E)

-- Proof sketch: use the identity covering of each object `U`; the restriction of the constant
-- sheaf with value `E` is again the constant sheaf with value `E`, and the given `Finite E`
-- supplies the finiteness condition on the local model.
/-- A constant sheaf of finite sets is finite locally constant. -/
instance isFiniteLocallyConstant_of_constant (E : Type w) [Finite E] :
    IsFiniteLocallyConstant ((constantSheaf J (Type w)).obj E) := sorry

end FiniteLocallyConstantTypes

section FiniteLocallyConstantGroups

variable [HasWeakSheafify J GrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) GrpCat.{w}]

/-- Definition 18.43.1 (3): a group-valued sheaf is finite locally constant if, locally on every
object of the site, it is isomorphic to a constant sheaf with finite group value. -/
class IsFiniteLocallyConstantGrp (F : Sheaf J GrpCat.{w}) : Prop extends IsLocallyConstant F where
  /-- Every object admits a covering on which the restriction of `F` is a constant sheaf with
  finite group value. -/
  exists_finite_constant_cover :
    ∀ U : C,
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I,
          ∃ E : GrpCat.{w}, Finite E ∧
            Nonempty (F.over (X i).left ≅ (constantSheaf (J.over (X i).left) GrpCat.{w}).obj E)

-- Proof sketch: again use the identity covering of each object. Restricting a constant
-- `GrpCat`-valued sheaf preserves its constant value, and finiteness of the underlying group is
-- unchanged under this restriction.
/-- A constant sheaf of finite groups is finite locally constant. -/
instance isFiniteLocallyConstantGrp_of_constant (E : GrpCat.{w}) [Finite E] :
    IsFiniteLocallyConstantGrp ((constantSheaf J GrpCat.{w}).obj E) := sorry

end FiniteLocallyConstantGroups

section FiniteLocallyConstantAddCommGroups

variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

/-- Definition 18.43.1 (variant): an abelian-group-valued sheaf is finite locally constant if,
locally on every object of the site, it is isomorphic to a constant sheaf with finite abelian
group value. -/
class IsFiniteLocallyConstantAddCommGrp (F : Sheaf J AddCommGrpCat.{w}) : Prop
    extends IsLocallyConstant F where
  /-- Every object admits a covering on which the restriction of `F` is a constant sheaf with
  finite abelian-group value. -/
  exists_finite_constant_cover :
    ∀ U : C,
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I,
          ∃ A : AddCommGrpCat.{w}, Finite A ∧
            Nonempty (F.over (X i).left ≅
              (constantSheaf (J.over (X i).left) AddCommGrpCat.{w}).obj A)

-- Proof sketch: use the identity covering of each object. Restricting a constant abelian-group
-- sheaf preserves its constant value, and the given finiteness instance remains valid on every
-- slice site.
/-- A constant sheaf of finite abelian groups is finite locally constant. -/
instance isFiniteLocallyConstantAddCommGrp_of_constant
    (A : AddCommGrpCat.{w}) [Finite A] :
    IsFiniteLocallyConstantAddCommGrp ((constantSheaf J AddCommGrpCat.{w}).obj A) := sorry

end FiniteLocallyConstantAddCommGroups

section FiniteTypeLocallyConstantModules

variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]

/-- Definition 18.43.1 (variant): a `\Lambda`-module-valued sheaf is locally constant of finite
type if, locally on every object of the site, it is isomorphic to a constant sheaf with finite
type module value. -/
class IsFiniteTypeLocallyConstantModule (F : Sheaf J (ModuleCat.{w} Λ)) : Prop
    extends IsLocallyConstant F where
  /-- Every object admits a covering on which the restriction of `F` is a constant sheaf with
  finite type `\Lambda`-module value. -/
  exists_finite_constant_cover :
    ∀ U : C,
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I,
          ∃ M : ModuleCat.{w} Λ, Module.Finite Λ M ∧
            Nonempty (F.over (X i).left ≅
              (constantSheaf (J.over (X i).left) (ModuleCat.{w} Λ)).obj M)

-- Proof sketch: use the identity covering of each object. Restricting a constant sheaf with
-- value `M` preserves the same constant model, and the given `Module.Finite Λ M` instance
-- supplies the finite-type condition on each local chart.
/-- A constant sheaf of finite type `\Lambda`-modules is locally constant of finite type. -/
instance isFiniteTypeLocallyConstantModule_of_constant
    (M : ModuleCat.{w} Λ) [Module.Finite Λ M] :
    IsFiniteTypeLocallyConstantModule ((constantSheaf J (ModuleCat.{w} Λ)).obj M) := sorry

end FiniteTypeLocallyConstantModules

end Sheaf

end CategoryTheory
