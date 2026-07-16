import StacksProject_2024.stacks_project.Chap24.Definition_24_4_1
import StacksProject_2024.stacks_project.Chap24.Definition_24_8_1_Core

open CategoryTheory
open scoped SheafOfModules.RingedSite.GradedModuleSheaf

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "ModO" => ringedSiteModuleCategory J 𝒪
local notation "GModO" => GradedObject ℤ ModO

open scoped SheafOfModules.RingedSite.GradedBimodule

namespace GradedBimodule

/-- The underlying graded object of a graded bimodule. -/
abbrev toGradedObject
    {A B : GradedAlgebraSheaf 𝒪}
    (M : Mod(A, B)) :
    GModO :=
  M.toRightModule.toGradedObject

/-- A graded bimodule carries its underlying graded object. -/
instance instCoeOutGradedObject
    (A B : GradedAlgebraSheaf 𝒪) :
    CoeOut (Mod(A, B)) GModO where
  coe M := M.toGradedObject

/-- A graded bimodule can be evaluated degreewise as a graded family of `\mathcal O`-modules. -/
instance instCoeFun
    (A B : GradedAlgebraSheaf 𝒪) :
    CoeFun (Mod(A, B)) (fun _ ↦ ℤ → ModO) where
  coe M := M.toGradedObject

/-- The degree-`n` term of the underlying graded object of a graded bimodule is its degree-`n`
module sheaf. -/
@[simp]
theorem toGradedObject_apply
    {A B : GradedAlgebraSheaf 𝒪}
    (M : Mod(A, B)) (n : ℤ) :
    M.toGradedObject n = M n := rfl

/-- Coercion of a graded bimodule recovers its degree-`n` component. -/
@[simp]
theorem coe_apply
    {A B : GradedAlgebraSheaf 𝒪}
    (M : Mod(A, B)) (n : ℤ) :
    M n = M.toRightModule n := rfl

/-- The degree-`n` sections of a graded bimodule over an object of the site. -/
abbrev sections
    {A B : GradedAlgebraSheaf 𝒪}
    (M : Mod(A, B))
    (U : Cᵒᵖ) (n : ℤ) : Type (max u v) :=
  M.toRightModule.sections U n

/-- Associativity of the left graded action, rewritten as a transported equality of local
sections. -/
theorem left_assoc_cast
    {A B : GradedAlgebraSheaf 𝒪}
    (M : Mod(A, B)) (i j k : ℤ) (U : Cᵒᵖ)
    (a : A.sections U i) (a' : A.sections U j) (x : M.sections U k) :
    cast (by rw [Int.add_assoc])
      (M.leftMul (i + j) k U (A.mul U i j a a') x) =
        M.leftMul i (j + k) U a (M.leftMul j k U a' x) := by
  cases Int.add_assoc i j k
  simpa using M.left_assoc i j k U a a' x

/-- The identity section of `\mathcal A^0` acts as the identity after transporting along
`0 + n = n`. -/
theorem one_left_cast
    {A B : GradedAlgebraSheaf 𝒪}
    (M : Mod(A, B)) (n : ℤ) (U : Cᵒᵖ) (x : M.sections U n) :
    cast (by rw [Int.zero_add]) (M.leftMul 0 n U (A.one U) x) = x := by
  cases Int.zero_add n
  simpa using M.one_left n U x

/-- Compatibility of the left `\mathcal A`-action with the right `\mathcal B`-action, rewritten
as a transported equality of local sections. -/
theorem middle_assoc_cast
    {A B : GradedAlgebraSheaf 𝒪}
    (M : Mod(A, B)) (i j k : ℤ) (U : Cᵒᵖ)
    (a : A.sections U i) (x : M.sections U j) (b : B.sections U k) :
    cast (by rw [Int.add_assoc])
      (M.toRightModule.smul (i + j) k U (M.leftMul i j U a x) b) =
        M.leftMul i (j + k) U a (M.toRightModule.smul j k U x b) := by
  cases Int.add_assoc i j k
  simpa using M.middle_assoc i j k U a x b

/-- Definition 24.8.1 (2): a homomorphism of graded `(\mathcal A, \mathcal B)`-bimodules is a
homomorphism of the underlying right graded `\mathcal B`-modules that also commutes with the left
`\mathcal A`-action. -/
structure Hom
    {A B : GradedAlgebraSheaf 𝒪}
    (M N : Mod(A, B)) where
  /-- The underlying right graded `\mathcal B`-module homomorphism. -/
  toRightHom : M.toRightModule ⟶ N.toRightModule
  /-- Compatibility with the left `\mathcal A`-action. -/
  left_comm :
    ∀ n m (U : Cᵒᵖ) (a : A.sections U n) (x : M.sections U m),
      (((toRightHom.hom (n + m)).val.app U).hom) (M.leftMul n m U a x) =
        N.leftMul n m U a ((((toRightHom.hom m).val.app U).hom) x)

namespace Hom

/-- The identity homomorphism of a graded bimodule. -/
def id
    {A B : GradedAlgebraSheaf 𝒪}
    (M : Mod(A, B)) : Hom M M where
  toRightHom := 𝟙 M.toRightModule
  left_comm := by
    intro n m U a x
    rfl

/-- The composite of graded bimodule homomorphisms. -/
def comp
    {A B : GradedAlgebraSheaf 𝒪}
    {M N P : Mod(A, B)}
    (f : Hom M N) (g : Hom N P) : Hom M P where
  toRightHom := f.toRightHom ≫ g.toRightHom
  left_comm := by
    intro n m U a x
    simpa using
      (congrArg (((g.toRightHom.hom (n + m)).val.app U).hom) (f.left_comm n m U a x)).trans
        (g.left_comm n m U a ((((f.toRightHom.hom m).val.app U).hom) x))

/-- The underlying right graded-module morphism of the identity bimodule map is the identity. -/
@[simp]
theorem id_toRightHom
    {A B : GradedAlgebraSheaf 𝒪}
    (M : Mod(A, B)) :
    (id M).toRightHom = 𝟙 M.toRightModule := rfl

/-- The underlying right graded-module morphism of a composite is the composite of the
underlying right graded-module morphisms. -/
@[simp]
theorem comp_toRightHom
    {A B : GradedAlgebraSheaf 𝒪}
    {M N P : Mod(A, B)}
    (f : Hom M N) (g : Hom N P) :
    (comp f g).toRightHom = f.toRightHom ≫ g.toRightHom := rfl

end Hom

/-- A bimodule homomorphism carries its underlying right graded-module morphism. -/
instance instCoeOutHom
    {A B : GradedAlgebraSheaf 𝒪}
    {M N : Mod(A, B)} :
    CoeOut (Hom M N) (M.toRightModule ⟶ N.toRightModule) where
  coe f := f.toRightHom

/-- A bimodule homomorphism can be evaluated degreewise. -/
instance instCoeFunHom
    {A B : GradedAlgebraSheaf 𝒪}
    (M N : Mod(A, B)) :
    CoeFun (Hom M N) (fun _ ↦ ∀ n : ℤ, M n ⟶ N n) where
  coe f := f.toRightHom.hom

/-- Coercion of a bimodule homomorphism recovers its degree-`n` component. -/
@[simp]
theorem hom_coe_apply
    {A B : GradedAlgebraSheaf 𝒪}
    {M N : Mod(A, B)}
    (f : Hom M N) (n : ℤ) :
    f n = f.toRightHom.hom n := rfl

/-- The degree-`n` component of the identity bimodule homomorphism is the identity. -/
@[simp]
theorem id_hom
    {A B : GradedAlgebraSheaf 𝒪}
    (M : Mod(A, B)) (n : ℤ) :
    Hom.id M n = 𝟙 (M n) := rfl

/-- The degree-`n` component of a composite bimodule homomorphism is the composite of the
degree-`n` components. -/
@[simp]
theorem comp_hom
    {A B : GradedAlgebraSheaf 𝒪}
    {M N P : Mod(A, B)}
    (f : Hom M N) (g : Hom N P) (n : ℤ) :
    Hom.comp f g n = f n ≫ g n := rfl

/-- Two graded bimodule homomorphisms are equal when their degreewise components agree. -/
@[ext]
theorem hom_ext
    {A B : GradedAlgebraSheaf 𝒪}
    {M N : Mod(A, B)} (f g : Hom M N)
    (h : ∀ n : ℤ, f n = g n) : f = g := by
  sorry

/-- The underlying right graded-module morphism determines a bimodule homomorphism. -/
theorem toRightHom_injective
    {A B : GradedAlgebraSheaf 𝒪}
    {M N : Mod(A, B)} :
    Function.Injective (fun f : Hom M N ↦ f.toRightHom) := by
  intro f g h
  apply hom_ext f g
  intro n
  exact congrArg (fun k ↦ k.hom n) h

/-- Identity and composition of compatible right-module maps give graded bimodules their
canonical category structure. -/
@[stacks 0FR5, instance]
instance instCategory
    (A B : GradedAlgebraSheaf 𝒪) :
    Category (Mod(A, B)) where
  Hom M N := Hom M N
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro M N f
    cases f
    rfl
  comp_id := by
    intro M N f
    cases f
    rfl
  assoc := by
    intro M N P Q f g h
    cases f
    cases g
    cases h
    rfl

/-- The forgetful functor from graded `(\mathcal A, \mathcal B)`-bimodules to their underlying
right graded `\mathcal B`-modules. -/
def forgetToRightModule
    (A B : GradedAlgebraSheaf 𝒪) :
    Mod(A, B) ⥤ Mod(B) where
  obj M := M.toRightModule
  map f := f.toRightHom
  map_id := Hom.id_toRightHom
  map_comp := Hom.comp_toRightHom

/-- The forgetful map to right graded modules preserves identities. -/
@[simp]
theorem forgetToRightModule_map_id
    {A B : GradedAlgebraSheaf 𝒪}
    (M : Mod(A, B)) :
    (forgetToRightModule A B).map (𝟙 M) = 𝟙 M.toRightModule := rfl

/-- The forgetful map to right graded modules preserves composition. -/
@[simp]
theorem forgetToRightModule_map_comp
    {A B : GradedAlgebraSheaf 𝒪}
    {M N P : Mod(A, B)}
    (f : M ⟶ N) (g : N ⟶ P) :
    (forgetToRightModule A B).map (f ≫ g) =
      (forgetToRightModule A B).map f ≫ (forgetToRightModule A B).map g := rfl

/-- Forgetting a graded bimodule to its right graded module recovers the stored right-module
datum. -/
@[simp]
theorem forgetToRightModule_obj
    {A B : GradedAlgebraSheaf 𝒪}
    (M : Mod(A, B)) :
    (forgetToRightModule A B).obj M = M.toRightModule := rfl

/-- Forgetting a graded bimodule homomorphism to the right-module level recovers its underlying
right-module morphism. -/
@[simp]
theorem forgetToRightModule_map
    {A B : GradedAlgebraSheaf 𝒪}
    {M N : Mod(A, B)}
    (f : M ⟶ N) :
    (forgetToRightModule A B).map f = f.toRightHom := rfl

/-- Forgetting to the underlying right graded module is faithful. -/
instance forgetToRightModule_faithful
    (A B : GradedAlgebraSheaf 𝒪) :
    Functor.Faithful (forgetToRightModule A B) where
  map_injective := by
    intro M N f g h
    exact toRightHom_injective h

/-- The forgetful functor from graded `(\mathcal A, \mathcal B)`-bimodules to the underlying
graded family of `\mathcal O`-modules. -/
abbrev forgetToGraded
    (A B : GradedAlgebraSheaf 𝒪) :
    Mod(A, B) ⥤ GModO :=
  forgetToRightModule A B ⋙ GradedModuleSheaf.forgetToGraded B

/-- The forgetful map to graded objects preserves identities. -/
@[simp]
theorem forgetToGraded_map_id
    {A B : GradedAlgebraSheaf 𝒪}
    (M : Mod(A, B)) :
    (forgetToGraded A B).map (𝟙 M) = 𝟙 M.toGradedObject := rfl

/-- The forgetful map to graded objects preserves composition. -/
@[simp]
theorem forgetToGraded_map_comp
    {A B : GradedAlgebraSheaf 𝒪}
    {M N P : Mod(A, B)}
    (f : M ⟶ N) (g : N ⟶ P) :
    (forgetToGraded A B).map (f ≫ g) =
      (forgetToGraded A B).map f ≫ (forgetToGraded A B).map g := by
  ext n
  rfl

/-- The bimodule-to-graded-object forgetful functor factors through the canonical forgetful
functor to right graded `\mathcal B`-modules. -/
theorem forgetToGraded_def
    (A B : GradedAlgebraSheaf 𝒪) :
    forgetToGraded A B =
      forgetToRightModule A B ⋙ GradedModuleSheaf.forgetToGraded B :=
  rfl

/-- Forgetting a graded bimodule to graded objects recovers its underlying graded object. -/
@[simp]
theorem forgetToGraded_obj
    {A B : GradedAlgebraSheaf 𝒪}
    (M : Mod(A, B)) :
    (forgetToGraded A B).obj M = M.toGradedObject := rfl

/-- Forgetting a graded bimodule homomorphism to graded objects recovers its underlying
graded-object morphism. -/
@[simp]
theorem forgetToGraded_map
    {A B : GradedAlgebraSheaf 𝒪}
    {M N : Mod(A, B)} (f : M ⟶ N) :
    (forgetToGraded A B).map f = f.toRightHom.hom := rfl

/-- The underlying graded object of a graded bimodule evaluates degreewise to the same
`\mathcal O`-module sheaf. -/
@[simp]
theorem forgetToGraded_obj_apply
    {A B : GradedAlgebraSheaf 𝒪}
    (M : Mod(A, B)) (n : ℤ) :
    ((forgetToGraded A B).obj M) n = M n := rfl

/-- The degree-`n` component of the underlying graded-object morphism is the degree-`n`
component of the original graded bimodule homomorphism. -/
@[simp]
theorem forgetToGraded_map_apply
    {A B : GradedAlgebraSheaf 𝒪}
    {M N : Mod(A, B)} (f : M ⟶ N) (n : ℤ) :
    ((forgetToGraded A B).map f) n = f.toRightHom.hom n := rfl

/-- Forgetting to the underlying graded object is faithful. -/
instance forgetToGraded_faithful
    (A B : GradedAlgebraSheaf 𝒪) :
    Functor.Faithful (forgetToGraded A B) where
  map_injective := by
    intro M N f g h
    exact toRightHom_injective (GradedModuleSheaf.hom_injective (by simpa using h))

/- Definition 24.8.1 (3): with the identity and composition above, the source-facing category of
graded `(\mathcal A, \mathcal B)`-bimodules is the bundled owner `Mod(A, B)`. -/
variable (A B : GradedAlgebraSheaf 𝒪)

#check Mod(A, B)

end GradedBimodule

end

end SheafOfModules.RingedSite
