import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomIdentityCoherence
import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part07

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-!
This file collects the small coherence adapters repeatedly needed in the later
`Lemma_8_11_8` parts.  It intentionally imports only through `Part07`, so both `Part08` and
later parts can use it without creating an import cycle.
-/

section CategoryAdapters

/-- Cancel a right isomorphism after postcomposition. -/
theorem comp_right_eq_of_iso {D : Type*} [Category D] {A B C : D}
    {f g : A ⟶ B} (e : B ≅ C) (h : f ≫ e.hom = g ≫ e.hom) : f = g := by
  simpa [Category.assoc] using congrArg (fun k => k ≫ e.inv) h

/-- Cancel a left isomorphism after precomposition. -/
theorem comp_left_eq_of_iso {D : Type*} [Category D] {A B C : D}
    (e : A ≅ B) {f g : B ⟶ C} (h : e.hom ≫ f = e.hom ≫ g) : f = g := by
  simpa [Category.assoc] using congrArg (fun k => e.inv ≫ k) h

/-- Remove an adjacent `hom ≫ inv` pair in the middle of a composite. -/
@[reassoc]
theorem iso_hom_inv_cancel_middle {D : Type*} [Category D] {A B X Y : D}
    (e : A ≅ B) (f : X ⟶ A) (g : A ⟶ Y) :
    (f ≫ e.hom) ≫ e.inv ≫ g = f ≫ g := by
  simp [Category.assoc]

/-- Remove an adjacent `inv ≫ hom` pair in the middle of a composite. -/
@[reassoc]
theorem iso_inv_hom_cancel_middle {D : Type*} [Category D] {A B X Y : D}
    (e : A ≅ B) (f : X ⟶ B) (g : B ⟶ Y) :
    (f ≫ e.inv) ≫ e.hom ≫ g = f ≫ g := by
  simp [Category.assoc]

end CategoryAdapters

namespace Functor

/-- Hom component of `mapIso` applied to a transitive isomorphism. -/
@[simp]
theorem mapIso_trans_hom_eq {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) {A B C : D} (e : A ≅ B) (f : B ≅ C) :
    (F.mapIso (e ≪≫ f)).hom = (F.mapIso e).hom ≫ (F.mapIso f).hom := by
  simp [Iso.trans_hom]

/-- Inverse component of `mapIso` applied to a transitive isomorphism. -/
@[simp]
theorem mapIso_trans_inv_eq {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) {A B C : D} (e : A ≅ B) (f : B ≅ C) :
    (F.mapIso (e ≪≫ f)).inv = (F.mapIso f).inv ≫ (F.mapIso e).inv := by
  simp [Iso.trans_inv]

/-- Hom component of `mapIso` applied to a threefold transitive isomorphism. -/
theorem mapIso_trans_trans_hom_eq {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) {A B C G : D} (e₁ : A ≅ B) (e₂ : B ≅ C) (e₃ : C ≅ G) :
    (F.mapIso (e₁ ≪≫ e₂ ≪≫ e₃)).hom =
      (F.mapIso e₁).hom ≫ (F.mapIso e₂).hom ≫ (F.mapIso e₃).hom := by
  simp [Iso.trans_hom]

/-- Inverse component of `mapIso` applied to a threefold transitive isomorphism. -/
theorem mapIso_trans_trans_inv_eq {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) {A B C G : D} (e₁ : A ≅ B) (e₂ : B ≅ C) (e₃ : C ≅ G) :
    (F.mapIso (e₁ ≪≫ e₂ ≪≫ e₃)).inv =
      (F.mapIso e₃).inv ≫ (F.mapIso e₂).inv ≫ (F.mapIso e₁).inv := by
  simp [Iso.trans_inv, Category.assoc]

/-- A functor maps the hom of a transitive isomorphism to the composite of mapped homs. -/
theorem map_iso_trans_hom {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) {A B C : D} (e : A ≅ B) (f : B ≅ C) :
    F.map (e ≪≫ f).hom = F.map e.hom ≫ F.map f.hom := by
  simp [Iso.trans_hom, Functor.map_comp]

/-- A functor maps the inverse of a transitive isomorphism to the composite of mapped inverses. -/
theorem map_iso_trans_inv {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) {A B C : D} (e : A ≅ B) (f : B ≅ C) :
    F.map (e ≪≫ f).inv = F.map f.inv ≫ F.map e.inv := by
  simp [Iso.trans_inv, Functor.map_comp]

end Functor

namespace Pseudofunctor

/-- Hom/inverse cancellation for two `mapComp'` cells with the same endpoints but different
proof-irrelevant witnesses. -/
@[reassoc]
theorem mapComp'_hom_inv_id_toNatTrans_app_of_witness
    {B : Type*} [Bicategory B] [Bicategory.Strict B]
    (F : Pseudofunctor B Cat) {b₀ b₁ b₂ : B}
    (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) {k : b₀ ⟶ b₂}
    (w w' : f ≫ g = k) (X : F.obj b₀) :
    (F.mapComp' f g k w).hom.toNatTrans.app X ≫
      (F.mapComp' f g k w').inv.toNatTrans.app X = 𝟙 _ := by
  have hw : w = w' := Subsingleton.elim _ _
  cases hw
  exact Cat.Hom.hom_inv_id_toNatTrans_app (F.mapComp' f g k w) X

/-- Inverse/hom cancellation for two `mapComp'` cells with the same endpoints but different
proof-irrelevant witnesses. -/
@[reassoc]
theorem mapComp'_inv_hom_id_toNatTrans_app_of_witness
    {B : Type*} [Bicategory B] [Bicategory.Strict B]
    (F : Pseudofunctor B Cat) {b₀ b₁ b₂ : B}
    (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) {k : b₀ ⟶ b₂}
    (w w' : f ≫ g = k) (X : F.obj b₀) :
    (F.mapComp' f g k w).inv.toNatTrans.app X ≫
      (F.mapComp' f g k w').hom.toNatTrans.app X = 𝟙 _ := by
  have hw : w = w' := Subsingleton.elim _ _
  cases hw
  exact Cat.Hom.inv_hom_id_toNatTrans_app (F.mapComp' f g k w) X

/-- Compare the inverse component of a strict `mapComp'` cell with the unprimed `mapComp` cell. -/
theorem mapComp'_inv_app_eq_mapComp_with_witness
    {B : Type*} [Bicategory B] [Bicategory.Strict B] (F : Pseudofunctor B Cat)
    {b₀ b₁ b₂ : B} {f : b₀ ⟶ b₁} {g : b₁ ⟶ b₂}
    {k : b₀ ⟶ b₂} {w : f ≫ g = k} {X : F.obj b₀} :
    (F.mapComp' f g k w).inv.toNatTrans.app X =
      (F.mapComp f g).inv.toNatTrans.app X ≫ eqToHom (by rw [w]) := by
  subst w
  simp only [Pseudofunctor.mapComp'_eq_mapComp, eqToHom_refl, Category.comp_id]

/-- Compare the hom component of a strict `mapComp'` cell with the unprimed `mapComp` cell. -/
theorem mapComp'_hom_app_eq_mapComp_with_witness
    {B : Type*} [Bicategory B] [Bicategory.Strict B] (F : Pseudofunctor B Cat)
    {b₀ b₁ b₂ : B} {f : b₀ ⟶ b₁} {g : b₁ ⟶ b₂}
    {k : b₀ ⟶ b₂} {w : f ≫ g = k} {X : F.obj b₀} :
    (F.mapComp' f g k w).hom.toNatTrans.app X =
      eqToHom (by rw [w]) ≫ (F.mapComp f g).hom.toNatTrans.app X := by
  subst w
  simp only [Pseudofunctor.mapComp'_eq_mapComp, eqToHom_refl, Category.id_comp]

end Pseudofunctor

section LocallyDiscreteOpposite

/-- Canonical `toLoc` witness for a composite in the opposite locally discrete base. -/
theorem op_toLoc_comp {X Y Z : C} (f : Y ⟶ Z) (g : X ⟶ Y) :
    f.op.toLoc ≫ g.op.toLoc = (g ≫ f).op.toLoc := by
  simp [← Quiver.Hom.comp_toLoc, ← op_comp]

/-- Canonical `toLoc` witness for a composite whose left factor is an identity after `op`. -/
theorem op_toLoc_id_comp {X Y : C} (f : X ⟶ Y) :
    (𝟙 Y).op.toLoc ≫ f.op.toLoc = f.op.toLoc := by
  simp

/-- Canonical `toLoc` witness for a composite whose right factor is an identity after `op`. -/
theorem op_toLoc_comp_id {X Y : C} (f : X ⟶ Y) :
    f.op.toLoc ≫ (𝟙 X).op.toLoc = f.op.toLoc := by
  simp

end LocallyDiscreteOpposite

section SheafExt

/-- Extensionality for morphisms of `Type`-valued sheaves, in the pointwise form used by the
identity-tail and owner-transport calculations. -/
theorem typeSheaf_hom_ext_app {U : C}
    {F G : Sheaf (J.over U) (Type w)} {f g : F ⟶ G}
    (h : ∀ T (α : F.1.obj T), (f.1.app T) α = (g.1.app T) α) : f = g := by
  apply Sheaf.hom_ext
  ext T α
  exact h T α

end SheafExt

end CategoryTheory
