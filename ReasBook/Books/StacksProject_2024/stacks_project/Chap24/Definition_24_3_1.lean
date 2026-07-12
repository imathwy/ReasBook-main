import Mathlib.CategoryTheory.GradedObject
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

-- Semantic search note: `lean_leansearch` was unavailable in this environment, so the owner/API
-- choice was checked against the local precedents `Definition_24_17_1` and `Definition_24_13_1`.

/-- Definition 24.3.1 (1): a sheaf of graded `\mathcal O`-algebras on the ringed site
`(\mathcal C, \mathcal O)` is a `\mathbf Z`-graded family of `\mathcal O`-module sheaves with
sectionwise multiplication and unit data satisfying the usual restriction, associativity, and
identity axioms. -/
structure GradedAlgebraSheaf (𝒪 : Sheaf J CommRingCat.{max u v}) where
  /-- The degreewise family of `\mathcal O`-module sheaves. -/
  obj : ℤ → SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)
  /-- The degree-zero unit section. -/
  one : ∀ U : Cᵒᵖ, (obj 0).val.obj U
  /-- The degreewise multiplication on local sections. -/
  mul :
    ∀ (U : Cᵒᵖ) (n m : ℤ),
      (obj n).val.obj U →ₗ[𝒪.obj.obj U]
        (obj m).val.obj U →ₗ[𝒪.obj.obj U] (obj (n + m)).val.obj U
  /-- The unit section commutes with restriction maps. -/
  map_one :
    ∀ {U V : Cᵒᵖ} (f : U ⟶ V),
      ((obj 0).val.map f).hom (one U) = one V
  /-- The multiplication maps commute with restriction. -/
  map_mul :
    ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (n m : ℤ)
      (a : (obj n).val.obj U) (b : (obj m).val.obj U),
      ((obj (n + m)).val.map f).hom (mul U n m a b) =
        mul V n m (((obj n).val.map f).hom a) (((obj m).val.map f).hom b)
  /-- Multiplication is associative on local sections. -/
  mul_assoc :
    ∀ (U : Cᵒᵖ) (i j k : ℤ)
      (a : (obj i).val.obj U) (b : (obj j).val.obj U) (c : (obj k).val.obj U),
      HEq (mul U (i + j) k (mul U i j a b) c)
        (mul U i (j + k) a (mul U j k b c))
  /-- The unit acts as a left identity. -/
  one_mul :
    ∀ (U : Cᵒᵖ) (n : ℤ) (a : (obj n).val.obj U),
      HEq (mul U 0 n (one U) a) a
  /-- The unit acts as a right identity. -/
  mul_one :
    ∀ (U : Cᵒᵖ) (n : ℤ) (a : (obj n).val.obj U),
      HEq (mul U n 0 a (one U)) a

/-- A graded algebra sheaf can be evaluated at each integer degree. -/
instance gradedAlgebraSheafCoeFun :
    CoeFun (GradedAlgebraSheaf 𝒪)
      fun _ ↦ ℤ → SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪) where
  coe 𝒜 := 𝒜.obj

namespace GradedAlgebraSheaf

/-- The underlying `\mathbf Z`-graded object of `\mathcal O`-module sheaves of a graded algebra
sheaf. -/
abbrev toGradedObject (𝒜 : GradedAlgebraSheaf 𝒪) :
    GradedObject ℤ (SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)) :=
  𝒜.obj

/-- A graded algebra sheaf can be used through its underlying graded object. -/
instance instCoeOut :
    CoeOut (GradedAlgebraSheaf 𝒪)
      (GradedObject ℤ (SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪))) where
  coe 𝒜 := 𝒜.toGradedObject

/-- The degree-`n` term of the underlying graded object of a graded algebra sheaf is its
degree-`n` `\mathcal O`-module sheaf. -/
@[simp]
theorem toGradedObject_apply (𝒜 : GradedAlgebraSheaf 𝒪) (n : ℤ) :
    𝒜.toGradedObject n = 𝒜 n :=
  rfl

/-- The degree-`n` local sections of a graded algebra over an object of the site. -/
abbrev sections
    (𝒜 : GradedAlgebraSheaf 𝒪)
    (U : Cᵒᵖ) (n : ℤ) : Type (max u v) :=
  (𝒜 n).val.obj U

/-- Definition 24.3.1 (2): a homomorphism of graded `\mathcal O`-algebras on
`(\mathcal C, \mathcal O)` is a degreewise family of `\mathcal O`-module sheaf morphisms
compatible with the multiplication maps and unit sections. -/
structure Hom {𝒪 : Sheaf J CommRingCat.{max u v}}
    (𝒜 ℬ : GradedAlgebraSheaf 𝒪) where
  /-- The degreewise maps `f^n : \mathcal A^n \to \mathcal B^n`. -/
  hom : ∀ n : ℤ, 𝒜 n ⟶ ℬ n
  /-- The degree-zero map preserves the unit section. -/
  map_one :
    ∀ U : Cᵒᵖ,
      (((hom 0).val.app U).hom) (𝒜.one U) = ℬ.one U
  /-- The degreewise maps commute with the multiplication maps on local sections. -/
  map_mul :
    ∀ (U : Cᵒᵖ) (n m : ℤ) (a : (𝒜 n).val.obj U) (b : (𝒜 m).val.obj U),
      (((hom (n + m)).val.app U).hom) (𝒜.mul U n m a b) =
        ℬ.mul U n m ((((hom n).val.app U).hom) a) ((((hom m).val.app U).hom) b)

/-- A homomorphism of graded algebra sheaves can be evaluated degreewise. -/
instance gradedAlgebraSheafHomCoeFun {𝒪 : Sheaf J CommRingCat.{max u v}}
    (𝒜 ℬ : GradedAlgebraSheaf 𝒪) :
    CoeFun (Hom 𝒜 ℬ) fun _ ↦ ∀ n : ℤ, 𝒜 n ⟶ ℬ n where
  coe f := f.hom

namespace Hom

/-- The identity homomorphism of a graded algebra sheaf. -/
def id (𝒜 : GradedAlgebraSheaf 𝒪) : Hom 𝒜 𝒜 where
  hom := fun n ↦ 𝟙 (𝒜 n)
  map_one := by
    intro U
    rfl
  map_mul := by
    intro U n m a b
    rfl

/-- The composite of graded algebra sheaf homomorphisms. -/
def comp {𝒜 ℬ 𝒞 : GradedAlgebraSheaf 𝒪} (f : Hom 𝒜 ℬ) (g : Hom ℬ 𝒞) : Hom 𝒜 𝒞 where
  hom := fun n ↦ f.hom n ≫ g.hom n
  map_one := by
    intro U
    simpa using (congrArg (((g.hom 0).val.app U).hom) (f.map_one U)).trans (g.map_one U)
  map_mul := by
    intro U n m a b
    simpa using congrArg (((g.hom (n + m)).val.app U).hom) (f.map_mul U n m a b) |>.trans
      (g.map_mul U n m (((f.hom n).val.app U).hom a) (((f.hom m).val.app U).hom b))

/-- The degree-`n` component of the identity is the identity on the degree-`n` piece. -/
@[simp]
theorem id_hom (𝒜 : GradedAlgebraSheaf 𝒪) (n : ℤ) :
    (id 𝒜).hom n = 𝟙 (𝒜 n) := rfl

/-- The degree-`n` component of a composite is the composite of the degree-`n` components. -/
@[simp]
theorem comp_hom {𝒜 ℬ 𝒞 : GradedAlgebraSheaf 𝒪} (f : Hom 𝒜 ℬ) (g : Hom ℬ 𝒞) (n : ℤ) :
    (comp f g).hom n = f.hom n ≫ g.hom n := rfl

end Hom

/-- Coercion of a graded algebra sheaf homomorphism recovers its degree-`n` component. -/
@[simp]
theorem coe_apply {𝒪 : Sheaf J CommRingCat.{max u v}}
    {𝒜 ℬ : GradedAlgebraSheaf 𝒪} (f : Hom 𝒜 ℬ) (n : ℤ) :
    f n = f.hom n := rfl

/-- Two graded algebra sheaf homomorphisms are equal when their degreewise components agree. -/
@[ext]
theorem hom_ext {𝒪 : Sheaf J CommRingCat.{max u v}}
    {𝒜 ℬ : GradedAlgebraSheaf 𝒪} (f g : Hom 𝒜 ℬ)
    (h : ∀ n : ℤ, f.hom n = g.hom n) : f = g := by
  cases f with
  | mk homf map_onef map_mulf =>
      cases g with
      | mk homg map_oneg map_mulg =>
          dsimp at h
          have hhom : homf = homg := funext h
          subst hhom
          have hmap_one : map_onef = map_oneg := Subsingleton.elim _ _
          subst hmap_one
          have hmap_mul : map_mulf = map_mulg := Subsingleton.elim _ _
          subst hmap_mul
          rfl

/-- Degreewise identities and compositions give the canonical category structure on graded
`\mathcal O`-algebra sheaves. -/
instance gradedAlgebraSheafCategory {𝒪 : Sheaf J CommRingCat.{max u v}} :
    Category (GradedAlgebraSheaf 𝒪) where
  Hom 𝒜 ℬ := Hom 𝒜 ℬ
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := by
    intro 𝒜 ℬ f
    cases f
    rfl
  comp_id := by
    intro 𝒜 ℬ f
    cases f
    rfl
  assoc := by
    intro 𝒜 ℬ 𝒞 𝒟 f g h
    cases f
    cases g
    cases h
    rfl

/-- The forgetful functor from graded `\mathcal O`-algebra sheaves to their underlying graded
family of `\mathcal O`-module sheaves. -/
def forgetToGraded (𝒪 : Sheaf J CommRingCat.{max u v}) :
    GradedAlgebraSheaf 𝒪 ⥤
      GradedObject ℤ (SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)) where
  obj 𝒜 := 𝒜.toGradedObject
  map f := f.hom
  map_id := by
    intro 𝒜
    ext n
    rfl
  map_comp := by
    intro 𝒜 ℬ 𝒞 f g
    ext n
    rfl

/-- Forgetting to the underlying graded object is faithful. -/
instance forgetToGraded_faithful (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Functor.Faithful (forgetToGraded 𝒪) where
  map_injective := by
    intro 𝒜 ℬ f g h
    exact hom_ext f g (fun n ↦ congrArg (fun k ↦ k n) h)

/-- Forgetting a graded algebra sheaf to graded objects recovers its underlying graded object. -/
@[simp] theorem forgetToGraded_obj
    {𝒪 : Sheaf J CommRingCat.{max u v}} (𝒜 : GradedAlgebraSheaf 𝒪) :
    (forgetToGraded 𝒪).obj 𝒜 = 𝒜.toGradedObject :=
  rfl

/-- Forgetting a graded algebra sheaf homomorphism to graded objects recovers its underlying
graded-object morphism. -/
@[simp] theorem forgetToGraded_map
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    {𝒜 ℬ : GradedAlgebraSheaf 𝒪} (f : 𝒜 ⟶ ℬ) :
    (forgetToGraded 𝒪).map f = f.hom :=
  rfl

/-- The underlying graded object of a graded algebra sheaf evaluates degreewise to the same
module sheaf. -/
@[simp] theorem forgetToGraded_obj_apply
    {𝒪 : Sheaf J CommRingCat.{max u v}} (𝒜 : GradedAlgebraSheaf 𝒪) (n : ℤ) :
    ((forgetToGraded 𝒪).obj 𝒜) n = 𝒜 n :=
  rfl

/-- The degree-`n` component of the underlying graded-object morphism is the degree-`n`
component of the original graded algebra sheaf homomorphism. -/
@[simp] theorem forgetToGraded_map_apply
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    {𝒜 ℬ : GradedAlgebraSheaf 𝒪} (f : 𝒜 ⟶ ℬ) (n : ℤ) :
    ((forgetToGraded 𝒪).map f) n = f.hom n :=
  rfl

end GradedAlgebraSheaf

end

end SheafOfModules.RingedSite
