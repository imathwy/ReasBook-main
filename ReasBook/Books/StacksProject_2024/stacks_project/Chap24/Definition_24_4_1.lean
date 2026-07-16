import StacksProject_2024.stacks_project.Chap24.Definition_24_4_1_Core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

open scoped SheafOfModules.RingedSite.GradedModuleSheaf

namespace GradedModuleSheaf

/-- The underlying graded object of a graded module sheaf. -/
abbrev toGradedObject {𝒜 : GradedAlgebraSheaf 𝒪} (ℳ : Mod(𝒜)) :
    GradedObject ℤ (SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)) :=
  ℳ.obj

/-- A graded module sheaf carries its underlying graded object. -/
instance instCoeOut {𝒜 : GradedAlgebraSheaf 𝒪} :
    CoeOut (Mod(𝒜))
      (GradedObject ℤ (SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪))) where
  coe ℳ := ℳ.toGradedObject

/-- The degree-`n` term of the underlying graded object of a graded module sheaf is its
degree-`n` module sheaf. -/
@[simp]
theorem toGradedObject_apply {𝒜 : GradedAlgebraSheaf 𝒪} (ℳ : Mod(𝒜)) (n : ℤ) :
    ℳ.toGradedObject n = ℳ n := rfl

/-- Coercion of a graded module sheaf recovers its degree-`n` component. -/
@[simp]
theorem coe_apply {𝒜 : GradedAlgebraSheaf 𝒪} (ℳ : Mod(𝒜)) (n : ℤ) :
    ℳ n = ℳ.obj n := rfl

/-- Associativity of the graded action, rewritten as a transported equality of local sections. -/
theorem smul_assoc_cast {𝒜 : GradedAlgebraSheaf 𝒪}
    (ℳ : Mod(𝒜)) (n m l : ℤ) (U : Cᵒᵖ)
    (x : ℳ.sections U n) (a : 𝒜.sections U m) (b : 𝒜.sections U l) :
    cast (by rw [Int.add_assoc])
        (ℳ.smul (n + m) l U (ℳ.smul n m U x a) b) =
      ℳ.smul n (m + l) U x (𝒜.mul U m l a b) := by
  apply eq_of_heq
  exact HEq.trans (cast_heq (by rw [Int.add_assoc]) _) (ℳ.smul_assoc n m l U x a b)

/-- The identity section of `\mathcal A^0` acts as the identity after transporting along
`n + 0 = n`. -/
theorem smul_one_cast {𝒜 : GradedAlgebraSheaf 𝒪}
    (ℳ : Mod(𝒜)) (n : ℤ) (U : Cᵒᵖ) (x : ℳ.sections U n) :
    cast (by rw [Int.add_zero]) (ℳ.smul n 0 U x (𝒜.one U)) = x := by
  apply eq_of_heq
  exact HEq.trans (cast_heq (by rw [Int.add_zero]) _) (ℳ.smul_one n U x)

namespace Hom

/-- The identity homomorphism of a graded `\mathcal A`-module sheaf. -/
def id {𝒜 : GradedAlgebraSheaf 𝒪} (ℳ : Mod(𝒜)) : Hom ℳ ℳ where
  hom := fun n ↦ 𝟙 (ℳ n)
  comm := by
    intro n m U x a
    rfl

/-- The composite of graded `\mathcal A`-module sheaf homomorphisms. -/
def comp {𝒜 : GradedAlgebraSheaf 𝒪}
    {ℳ : Mod(𝒜)} {𝒩 : Mod(𝒜)} {P : Mod(𝒜)}
    (f : Hom ℳ 𝒩) (g : Hom 𝒩 P) : Hom ℳ P where
  hom := fun n ↦ f.hom n ≫ g.hom n
  comm := by
    intro n m U x a
    simpa using
      (congrArg (((g.hom (n + m)).val.app U).hom) (f.comm n m U x a)).trans
        (g.comm n m U (((f.hom n).val.app U).hom x) a)

/-- The degree-`n` component of the identity is the identity on the degree-`n` piece. -/
@[simp]
theorem id_hom {𝒜 : GradedAlgebraSheaf 𝒪} (ℳ : Mod(𝒜)) (n : ℤ) :
    (id ℳ).hom n = 𝟙 (ℳ n) := rfl

/-- The degree-`n` component of a composite is the composite of the degree-`n` components. -/
@[simp]
theorem comp_hom {𝒜 : GradedAlgebraSheaf 𝒪}
    {ℳ : Mod(𝒜)} {𝒩 : Mod(𝒜)} {P : Mod(𝒜)}
    (f : Hom ℳ 𝒩) (g : Hom 𝒩 P) (n : ℤ) :
    (comp f g).hom n = f.hom n ≫ g.hom n := rfl

end Hom

/-- Coercion of a graded module sheaf homomorphism recovers its degree-`n` component. -/
@[simp]
theorem hom_coe_apply {𝒜 : GradedAlgebraSheaf 𝒪}
    {ℳ 𝒩 : Mod(𝒜)} (f : Hom ℳ 𝒩) (n : ℤ) :
    f n = f.hom n := rfl

/-- Two graded module sheaf homomorphisms are equal when their degreewise components agree. -/
@[ext] theorem hom_ext {𝒜 : GradedAlgebraSheaf 𝒪}
    {ℳ 𝒩 : Mod(𝒜)} (f g : Hom ℳ 𝒩)
    (h : ∀ n : ℤ, f n = g n) : f = g := by
  cases f with
  | mk homf commf =>
      cases g with
      | mk homg commg =>
          dsimp at h
          have hhom : homf = homg := funext h
          subst hhom
          have hcomm : commf = commg := Subsingleton.elim _ _
          subst hcomm
          rfl

/-- The underlying graded-object morphism determines a graded module sheaf homomorphism. -/
theorem hom_injective {𝒜 : GradedAlgebraSheaf 𝒪} {ℳ 𝒩 : Mod(𝒜)} :
    Function.Injective (fun f : Hom ℳ 𝒩 ↦ f.hom) := by
  intro f g h
  apply hom_ext f g
  intro n
  exact congrArg (fun k ↦ k n) h

/-- Degreewise identities and compositions give the canonical category structure on graded
`\mathcal A`-modules. -/
instance instCategory (𝒜 : GradedAlgebraSheaf 𝒪) :
    Category (Mod(𝒜)) where
  Hom ℳ 𝒩 := Hom ℳ 𝒩
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro ℳ 𝒩 f
    cases f
    rfl
  comp_id := by
    intro ℳ 𝒩 f
    cases f
    rfl
  assoc := by
    intro ℳ 𝒩 P Q f g h
    cases f
    cases g
    cases h
    rfl

/-- Definition 24.4.1 (3): the category of graded `\mathcal A`-modules, i.e. the source-facing
owner for the textbook notation `\mathrm{Mod}(\mathcal A)`. -/
@[stacks 0FQZ]
abbrev moduleCategory (𝒜 : GradedAlgebraSheaf 𝒪) := Mod(𝒜)

/-- The source-facing category `moduleCategory 𝒜` is definitionally the canonical owner
`Mod(𝒜)`. -/
@[simp]
theorem moduleCategory_def (𝒜 : GradedAlgebraSheaf 𝒪) :
    moduleCategory 𝒜 = Mod(𝒜) :=
  rfl

/-- The forgetful functor from graded `\mathcal A`-modules to the underlying graded family of
`\mathcal O`-module sheaves. -/
def forgetToGraded (𝒜 : GradedAlgebraSheaf 𝒪) :
    Mod(𝒜) ⥤ GradedObject ℤ (SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)) where
  obj ℳ := ℳ.toGradedObject
  map f := f.hom
  map_id := by
    intro ℳ
    rfl
  map_comp := by
    intro ℳ 𝒩 P f g
    rfl

/-- Forgetting to the underlying graded object is faithful. -/
instance forgetToGraded_faithful (𝒜 : GradedAlgebraSheaf 𝒪) :
    Functor.Faithful (forgetToGraded 𝒜) where
  map_injective := by
    intro ℳ 𝒩 f g h
    exact hom_injective h

/-- The forgetful map to graded objects preserves identities. -/
@[simp]
theorem forgetToGraded_map_id {𝒜 : GradedAlgebraSheaf 𝒪}
    (ℳ : Mod(𝒜)) :
    (forgetToGraded 𝒜).map (𝟙 ℳ) = 𝟙 ℳ.toGradedObject := rfl

/-- The forgetful map to graded objects preserves composition. -/
@[simp]
theorem forgetToGraded_map_comp {𝒜 : GradedAlgebraSheaf 𝒪}
    {ℳ 𝒩 P : Mod(𝒜)} (f : ℳ ⟶ 𝒩) (g : 𝒩 ⟶ P) :
    (forgetToGraded 𝒜).map (f ≫ g) =
      (forgetToGraded 𝒜).map f ≫ (forgetToGraded 𝒜).map g := by
  ext n
  rfl

/-- Forgetting a graded module sheaf to graded objects recovers its underlying graded object. -/
@[simp]
theorem forgetToGraded_obj {𝒜 : GradedAlgebraSheaf 𝒪}
    (ℳ : Mod(𝒜)) :
    (forgetToGraded 𝒜).obj ℳ = ℳ.toGradedObject := rfl

/-- Forgetting a graded module sheaf homomorphism to graded objects recovers its underlying
graded-object morphism. -/
@[simp]
theorem forgetToGraded_map {𝒜 : GradedAlgebraSheaf 𝒪}
    {ℳ 𝒩 : Mod(𝒜)} (f : ℳ ⟶ 𝒩) :
    (forgetToGraded 𝒜).map f = f.hom := rfl

/-- The underlying graded object of a graded module sheaf evaluates degreewise to the same module
sheaf. -/
@[simp]
theorem forgetToGraded_obj_apply {𝒜 : GradedAlgebraSheaf 𝒪}
    (ℳ : Mod(𝒜)) (n : ℤ) :
    ((forgetToGraded 𝒜).obj ℳ) n = ℳ n := rfl

/-- The degree-`n` component of the underlying graded-object morphism is the degree-`n`
component of the original graded module sheaf homomorphism. -/
@[simp]
theorem forgetToGraded_map_apply {𝒜 : GradedAlgebraSheaf 𝒪}
    {ℳ 𝒩 : Mod(𝒜)} (f : ℳ ⟶ 𝒩) (n : ℤ) :
    ((forgetToGraded 𝒜).map f) n = f.hom n := rfl

end GradedModuleSheaf

end

end SheafOfModules.RingedSite
