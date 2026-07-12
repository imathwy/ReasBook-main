import StacksProject_2024.Chap18.Definition_18_43_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Sheaf

section FiniteLocallyConstantTypes

variable [HasWeakSheafify J (Type w)]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]

/-- Definition 18.43.1 (2): a set-valued sheaf is finite locally constant if, locally on every
object of the site, it is isomorphic to a constant sheaf with finite value. -/
@[stacks 093Q]
class IsFiniteLocallyConstant (F : Sheaf J (Type w)) : Prop where
  /-- Every object admits a covering on which the restriction of `F` is a constant sheaf with
  finite value. -/
  exists_finite_constant_cover (U : C) :
    ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
      ∀ i : I,
        ∃ E : Type w, Finite E ∧
          Nonempty (F.over (X i).left ≅ (constantSheaf (J.over (X i).left) (Type w)).obj E)

/-- The object property of finite locally constant set-valued sheaves. -/
abbrev finiteLocallyConstant (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)]
    [∀ U : C, HasWeakSheafify (J.over U) (Type w)] : ObjectProperty (Sheaf J (Type w)) :=
  fun F ↦ IsFiniteLocallyConstant F

/-- A finite locally constant sheaf of sets is locally constant. -/
instance isLocallyConstant_of_isFiniteLocallyConstant (F : Sheaf J (Type w))
    [IsFiniteLocallyConstant F] : IsLocallyConstant F := by
  -- We forget the finiteness part of the local models and keep the constant sheaf charts.
  refine isLocallyConstant_of_explicit_constant_models (J := J) (D := Type w) ?_
  intro U
  obtain ⟨I, X, hX, hconst⟩ :=
    IsFiniteLocallyConstant.exists_finite_constant_cover (F := F) U
  refine ⟨I, X, hX, ?_⟩
  intro i
  obtain ⟨E, _, hiso⟩ := hconst i
  exact ⟨E, hiso⟩

-- Proof sketch: use the identity covering of each object `U`; the restriction of the constant
-- sheaf with value `E` is again the constant sheaf with value `E`, and the given `Finite E`
-- supplies the finiteness condition on the local model.
/-- A constant sheaf of finite sets is finite locally constant. -/
instance isFiniteLocallyConstant_of_constant (E : Type w) [Finite E]
    [J.WEqualsLocallyBijective (Type w)]
    [∀ U : C, (J.over U).WEqualsLocallyBijective (Type w)] :
    IsFiniteLocallyConstant ((constantSheaf J (Type w)).obj E) := by
  refine ⟨?_⟩
  intro U
  -- The identity singleton cover keeps the same finite constant model on the slice site.
  refine ⟨PUnit, fun _ ↦ Over.mk (𝟙 U), identity_singleton_coversTop_over (J := J) U, ?_⟩
  intro i
  exact ⟨E, inferInstance,
    constant_sheaf_over_nonempty_iso (J := J) (D := Type w)
      (FD := fun X Y ↦ X ⟶ Y) (CD := fun X ↦ X) U E⟩

end FiniteLocallyConstantTypes

section FiniteLocallyConstantGroups

variable [HasWeakSheafify J GrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) GrpCat.{w}]

/-- Definition 18.43.1 (3): a group-valued sheaf is finite locally constant if, locally on every
object of the site, it is isomorphic to a constant sheaf with finite group value. -/
@[stacks 093Q]
class IsFiniteLocallyConstantGrp (F : Sheaf J GrpCat.{w}) : Prop where
  /-- Every object admits a covering on which the restriction of `F` is a constant sheaf with
  finite group value. -/
  exists_finite_constant_cover (U : C) :
    ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
      ∀ i : I,
        ∃ A : GrpCat.{w}, Finite A ∧
          Nonempty (F.over (X i).left ≅ (constantSheaf (J.over (X i).left) GrpCat.{w}).obj A)

/-- The object property of finite locally constant group-valued sheaves. -/
abbrev finiteLocallyConstantGrp (J : GrothendieckTopology C) [HasWeakSheafify J GrpCat.{w}]
    [∀ U : C, HasWeakSheafify (J.over U) GrpCat.{w}] : ObjectProperty (Sheaf J GrpCat.{w}) :=
  fun F ↦ IsFiniteLocallyConstantGrp F

/-- A finite locally constant sheaf of groups is locally constant. -/
instance isLocallyConstant_of_isFiniteLocallyConstantGrp
    (F : Sheaf J GrpCat.{w}) [IsFiniteLocallyConstantGrp F] :
    IsLocallyConstant F := by
  -- We forget the finiteness part of the local group models.
  refine isLocallyConstant_of_explicit_constant_models (J := J) (D := GrpCat.{w}) ?_
  intro U
  obtain ⟨I, X, hX, hconst⟩ :=
    IsFiniteLocallyConstantGrp.exists_finite_constant_cover (F := F) U
  refine ⟨I, X, hX, ?_⟩
  intro i
  obtain ⟨A, _, hiso⟩ := hconst i
  exact ⟨A, hiso⟩

-- Proof sketch: use the identity covering of each object. Restricting a constant group sheaf
-- preserves its constant value, and the given finiteness instance remains valid on every slice
-- site.
/-- A constant sheaf of finite groups is finite locally constant. -/
instance isFiniteLocallyConstantGrp_of_constant (A : GrpCat.{w}) [Finite A]
    [J.WEqualsLocallyBijective GrpCat.{w}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective GrpCat.{w}] :
    IsFiniteLocallyConstantGrp ((constantSheaf J GrpCat.{w}).obj A) := by
  refine ⟨?_⟩
  intro U
  -- The same finite group value trivializes the constant sheaf on the singleton cover.
  refine ⟨PUnit, fun _ ↦ Over.mk (𝟙 U), identity_singleton_coversTop_over (J := J) U, ?_⟩
  intro i
  exact ⟨A, inferInstance,
    constant_sheaf_over_nonempty_iso (J := J) (D := GrpCat.{w})
      (FD := fun X Y : GrpCat.{w} ↦ X →* Y) (CD := fun X ↦ X) U A⟩

end FiniteLocallyConstantGroups

section FiniteLocallyConstantAddCommGroups

variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

/-- Auxiliary specialization used later in Chapter 18: a sheaf of abelian groups is finite
locally constant if, locally on every object of the site, it is isomorphic to a constant sheaf
with finite abelian-group value. -/
class IsFiniteLocallyConstantAddCommGrp (F : Sheaf J AddCommGrpCat.{w}) : Prop where
  /-- Every object admits a covering on which the restriction of `F` is a constant sheaf with
  finite abelian-group value. -/
  exists_finite_constant_cover (U : C) :
    ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
      ∀ i : I,
        ∃ A : AddCommGrpCat.{w}, Finite A ∧
          Nonempty (F.over (X i).left ≅
            (constantSheaf (J.over (X i).left) AddCommGrpCat.{w}).obj A)

/-- The object property of finite locally constant abelian-group-valued sheaves. -/
abbrev finiteLocallyConstantAddCommGrp (J : GrothendieckTopology C)
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}] :
    ObjectProperty (Sheaf J AddCommGrpCat.{w}) :=
  fun F ↦ IsFiniteLocallyConstantAddCommGrp F

/-- An auxiliary finite locally constant sheaf of abelian groups is locally constant. -/
instance isLocallyConstant_of_isFiniteLocallyConstantAddCommGrp
    (F : Sheaf J AddCommGrpCat.{w}) [IsFiniteLocallyConstantAddCommGrp F] :
    IsLocallyConstant F := by
  -- We forget the finiteness part of the local abelian-group models.
  refine isLocallyConstant_of_explicit_constant_models (J := J) (D := AddCommGrpCat.{w}) ?_
  intro U
  obtain ⟨I, X, hX, hconst⟩ :=
    IsFiniteLocallyConstantAddCommGrp.exists_finite_constant_cover (F := F) U
  refine ⟨I, X, hX, ?_⟩
  intro i
  obtain ⟨A, _, hiso⟩ := hconst i
  exact ⟨A, hiso⟩

-- Proof sketch: use the identity covering of each object. Restricting a constant abelian-group
-- sheaf preserves its constant value, and the given finiteness instance remains valid on every
-- slice site.
/-- A constant sheaf of finite abelian groups satisfies the auxiliary finite locally constant
specialization. -/
instance isFiniteLocallyConstantAddCommGrp_of_constant
    (A : AddCommGrpCat.{w}) [Finite A]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] :
    IsFiniteLocallyConstantAddCommGrp ((constantSheaf J AddCommGrpCat.{w}).obj A) := by
  refine ⟨?_⟩
  intro U
  -- The same finite abelian group value trivializes the constant sheaf on the singleton cover.
  refine ⟨PUnit, fun _ ↦ Over.mk (𝟙 U), identity_singleton_coversTop_over (J := J) U, ?_⟩
  intro i
  exact ⟨A, inferInstance,
    constant_sheaf_over_nonempty_iso (J := J) (D := AddCommGrpCat.{w})
      (FD := fun X Y : AddCommGrpCat.{w} ↦ X →+ Y) (CD := fun X ↦ X) U A⟩

end FiniteLocallyConstantAddCommGroups

section FiniteTypeLocallyConstantModules

variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]

/-- Auxiliary notion used later in Chapters 18 and 21: a `\Lambda`-module-valued sheaf is locally
constant of finite type if, locally on every object of the site, it is isomorphic to a constant
sheaf with finite type module value. -/
class IsFiniteTypeLocallyConstantModule (F : Sheaf J (ModuleCat.{w} Λ)) : Prop where
  /-- Every object admits a covering on which the restriction of `F` is a constant sheaf with
  finite type `\Lambda`-module value. -/
  exists_finite_constant_cover (U : C) :
    ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
      ∀ i : I,
        ∃ M : ModuleCat.{w} Λ, Module.Finite Λ M ∧
          Nonempty (F.over (X i).left ≅
            (constantSheaf (J.over (X i).left) (ModuleCat.{w} Λ)).obj M)

/-- The object property of locally constant sheaves of finite type `\Lambda`-modules. -/
abbrev finiteTypeLocallyConstantModule (J : GrothendieckTopology C) (Λ : Type w) [Ring Λ]
    [HasWeakSheafify J (ModuleCat.{w} Λ)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)] :
    ObjectProperty (Sheaf J (ModuleCat.{w} Λ)) :=
  fun F ↦ IsFiniteTypeLocallyConstantModule F

/-- An auxiliary locally constant sheaf of finite type modules is locally constant. -/
instance isLocallyConstant_of_isFiniteTypeLocallyConstantModule
    (F : Sheaf J (ModuleCat.{w} Λ)) [IsFiniteTypeLocallyConstantModule F] :
    IsLocallyConstant F := by
  -- We forget the finite-type hypothesis and keep the explicit constant module charts.
  refine isLocallyConstant_of_explicit_constant_models (J := J) (D := ModuleCat.{w} Λ) ?_
  intro U
  obtain ⟨I, X, hX, hconst⟩ :=
    IsFiniteTypeLocallyConstantModule.exists_finite_constant_cover (F := F) U
  refine ⟨I, X, hX, ?_⟩
  intro i
  obtain ⟨M, _, hiso⟩ := hconst i
  exact ⟨M, hiso⟩

-- Proof sketch: use the identity covering of each object. Restricting a constant sheaf with
-- value `M` preserves the same constant model, and the given `Module.Finite Λ M` instance
-- supplies the finite-type condition on each local chart.
/-- A constant sheaf of finite type `\Lambda`-modules satisfies the auxiliary finite-type locally
constant condition. -/
instance isFiniteTypeLocallyConstantModule_of_constant
    (M : ModuleCat.{w} Λ) [Module.Finite Λ M]
    [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)]
    [∀ U : C, (J.over U).WEqualsLocallyBijective (ModuleCat.{w} Λ)] :
    IsFiniteTypeLocallyConstantModule ((constantSheaf J (ModuleCat.{w} Λ)).obj M) := by
  refine ⟨?_⟩
  intro U
  -- The same finite type module value trivializes the constant sheaf on the singleton cover.
  refine ⟨PUnit, fun _ ↦ Over.mk (𝟙 U), identity_singleton_coversTop_over (J := J) U, ?_⟩
  intro i
  exact ⟨M, inferInstance,
    constant_sheaf_over_nonempty_iso (J := J) (D := ModuleCat.{w} Λ)
      (FD := fun X Y : ModuleCat.{w} Λ ↦ X →ₗ[Λ] Y) (CD := fun X ↦ X) U M⟩

end FiniteTypeLocallyConstantModules

end Sheaf

end CategoryTheory
