import StacksProject_2024.Chap08.Lemma_8_8_1.Criteria
import StacksProject_2024.Chap07.Lemma_7_42_4.TypeLocalBijectivity
import Mathlib.CategoryTheory.Category.Cat

universe u v uX vX

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace Pseudofunctor.LocallyDiscreteOpToCat

variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vX, uX}}

set_option backward.isDefEq.respectTransparency false in
/-- Pulling a morphism in a Hom presheaf back along a further base morphism preserves
composition.  This is the owner-side form of the source proof's repeated "restrict the composite"
step. -/
theorem pullHom_comp
    {X₁ X₂ X₃ : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {M₃ : F.obj (.mk (op X₃))}
    {A₀ : C} {f₁ : A₀ ⟶ X₁} {f₂ : A₀ ⟶ X₂} {f₃ : A₀ ⟶ X₃}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶
      (F.map f₃.op.toLoc).toFunctor.obj M₃)
    {A₁ : C} (k : A₁ ⟶ A₀) (kf₁ : A₁ ⟶ X₁) (kf₂ : A₁ ⟶ X₂) (kf₃ : A₁ ⟶ X₃)
    (hkf₁ : k ≫ f₁ = kf₁ := by cat_disch) (hkf₂ : k ≫ f₂ = kf₂ := by cat_disch)
    (hkf₃ : k ≫ f₃ = kf₃ := by cat_disch) :
    pullHom (F := F) (X₁ := X₁) (X₂ := X₃) (M₁ := M₁) (M₂ := M₃)
        (f₁ := f₁) (f₂ := f₃) (Y' := A₁) (φ ≫ ψ) k kf₁ kf₃ hkf₁ hkf₃ =
      pullHom (F := F) (X₁ := X₁) (X₂ := X₂) (M₁ := M₁) (M₂ := M₂)
          (f₁ := f₁) (f₂ := f₂) (Y' := A₁) φ k kf₁ kf₂ hkf₁ hkf₂ ≫
        pullHom (F := F) (X₁ := X₂) (X₂ := X₃) (M₁ := M₂) (M₂ := M₃)
          (f₁ := f₂) (f₂ := f₃) (Y' := A₁) ψ k kf₂ kf₃ hkf₂ hkf₃ := by
  dsimp [pullHom]
  rw [Functor.map_comp]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The value of `pullHom` is independent of the proof terms witnessing the two base equalities. -/
theorem pullHom_proof_irrel
    {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {Y Y' : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (k : Y' ⟶ Y) (kf₁ : Y' ⟶ X₁) (kf₂ : Y' ⟶ X₂)
    (h₁ h₁' : k ≫ f₁ = kf₁) (h₂ h₂' : k ≫ f₂ = kf₂) :
    pullHom (F := F) φ k kf₁ kf₂ h₁ h₂ =
      pullHom (F := F) φ k kf₁ kf₂ h₁' h₂' := by
  congr

set_option backward.isDefEq.respectTransparency false in
/-- If two pullback-normalized morphisms agree using the same chosen composite base arrows, then
the corresponding functorial restrictions agree.  The proof absorbs the proof-term differences in
the two `pullHom` owners. -/
theorem map_eq_of_pullHom_eq
    {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {Y : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {φ ψ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂}
    {Y' : C} (g : Y' ⟶ Y)
    (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (hgf₁' : g ≫ f₁ = gf₁) (hgf₂' : g ≫ f₂ = gf₂)
    (hpull :
      pullHom (F := F) φ g gf₁ gf₂ hgf₁ hgf₂ =
        pullHom (F := F) ψ g gf₁ gf₂ hgf₁' hgf₂') :
    (F.map g.op.toLoc).toFunctor.map φ =
      (F.map g.op.toLoc).toFunctor.map ψ := by
  have hpullCommon :
      pullHom (F := F) φ g gf₁ gf₂ hgf₁ hgf₂ =
        pullHom (F := F) ψ g gf₁ gf₂ hgf₁ hgf₂ := by
    exact hpull.trans
      (pullHom_proof_irrel (F := F) ψ g gf₁ gf₂ hgf₁' hgf₁ hgf₂' hgf₂)
  have hmapφ :=
    map_eq_pullHom (F := F) (φ := φ) g gf₁ gf₂ hgf₁ hgf₂
  have hmapψ :=
    map_eq_pullHom (F := F) (φ := ψ) g gf₁ gf₂ hgf₁ hgf₂
  rw [hmapφ, hmapψ, hpullCommon]

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back along a base arrow written with a leading identity is the same `pullHom` as
pulling back along the base arrow itself. -/
theorem pullHom_id_comp_base
    {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {Y : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    {Y' : C} (q : Y' ⟶ Y) (qf₁ : Y' ⟶ X₁) (qf₂ : Y' ⟶ X₂)
    (h₁ : (𝟙 Y' ≫ q) ≫ f₁ = qf₁)
    (h₂ : (𝟙 Y' ≫ q) ≫ f₂ = qf₂) :
    pullHom (F := F) φ (𝟙 Y' ≫ q) qf₁ qf₂ h₁ h₂ =
      pullHom (F := F) φ q qf₁ qf₂
        (by simpa [Category.assoc] using h₁)
        (by simpa [Category.assoc] using h₂) := by
  simp only [Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Pulling a triple composite back along a further base morphism is the composite of the three
pulled-back morphisms. -/
theorem pullHom_comp₃
    {X₁ X₂ X₃ X₄ : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {M₃ : F.obj (.mk (op X₃))}
    {M₄ : F.obj (.mk (op X₄))}
    {A₀ : C} {f₁ : A₀ ⟶ X₁} {f₂ : A₀ ⟶ X₂} {f₃ : A₀ ⟶ X₃} {f₄ : A₀ ⟶ X₄}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶
      (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (χ : (F.map f₃.op.toLoc).toFunctor.obj M₃ ⟶
      (F.map f₄.op.toLoc).toFunctor.obj M₄)
    {A₁ : C} (k : A₁ ⟶ A₀) (kf₁ : A₁ ⟶ X₁) (kf₂ : A₁ ⟶ X₂)
    (kf₃ : A₁ ⟶ X₃) (kf₄ : A₁ ⟶ X₄)
    (hkf₁ : k ≫ f₁ = kf₁ := by cat_disch) (hkf₂ : k ≫ f₂ = kf₂ := by cat_disch)
    (hkf₃ : k ≫ f₃ = kf₃ := by cat_disch) (hkf₄ : k ≫ f₄ = kf₄ := by cat_disch) :
    pullHom (F := F) (X₁ := X₁) (X₂ := X₄) (M₁ := M₁) (M₂ := M₄)
        (f₁ := f₁) (f₂ := f₄) (Y' := A₁) (φ ≫ ψ ≫ χ) k kf₁ kf₄ hkf₁ hkf₄ =
      pullHom (F := F) (X₁ := X₁) (X₂ := X₂) (M₁ := M₁) (M₂ := M₂)
          (f₁ := f₁) (f₂ := f₂) (Y' := A₁) φ k kf₁ kf₂ hkf₁ hkf₂ ≫
        pullHom (F := F) (X₁ := X₂) (X₂ := X₃) (M₁ := M₂) (M₂ := M₃)
          (f₁ := f₂) (f₂ := f₃) (Y' := A₁) ψ k kf₂ kf₃ hkf₂ hkf₃ ≫
        pullHom (F := F) (X₁ := X₃) (X₂ := X₄) (M₁ := M₃) (M₂ := M₄)
          (f₁ := f₃) (f₂ := f₄) (Y' := A₁) χ k kf₃ kf₄ hkf₃ hkf₄ := by
  dsimp [pullHom]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Pulling a fourfold composite back along a further base morphism is the composite of the four
pulled-back morphisms. -/
theorem pullHom_comp₄
    {X₁ X₂ X₃ X₄ X₅ : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {M₃ : F.obj (.mk (op X₃))}
    {M₄ : F.obj (.mk (op X₄))} {M₅ : F.obj (.mk (op X₅))}
    {A₀ : C} {f₁ : A₀ ⟶ X₁} {f₂ : A₀ ⟶ X₂} {f₃ : A₀ ⟶ X₃}
    {f₄ : A₀ ⟶ X₄} {f₅ : A₀ ⟶ X₅}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶
      (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (χ : (F.map f₃.op.toLoc).toFunctor.obj M₃ ⟶
      (F.map f₄.op.toLoc).toFunctor.obj M₄)
    (ω : (F.map f₄.op.toLoc).toFunctor.obj M₄ ⟶
      (F.map f₅.op.toLoc).toFunctor.obj M₅)
    {A₁ : C} (k : A₁ ⟶ A₀) (kf₁ : A₁ ⟶ X₁) (kf₂ : A₁ ⟶ X₂)
    (kf₃ : A₁ ⟶ X₃) (kf₄ : A₁ ⟶ X₄) (kf₅ : A₁ ⟶ X₅)
    (hkf₁ : k ≫ f₁ = kf₁ := by cat_disch) (hkf₂ : k ≫ f₂ = kf₂ := by cat_disch)
    (hkf₃ : k ≫ f₃ = kf₃ := by cat_disch) (hkf₄ : k ≫ f₄ = kf₄ := by cat_disch)
    (hkf₅ : k ≫ f₅ = kf₅ := by cat_disch) :
    pullHom (F := F) (X₁ := X₁) (X₂ := X₅) (M₁ := M₁) (M₂ := M₅)
        (f₁ := f₁) (f₂ := f₅) (Y' := A₁) (φ ≫ ψ ≫ χ ≫ ω) k kf₁ kf₅ hkf₁ hkf₅ =
      pullHom (F := F) (X₁ := X₁) (X₂ := X₂) (M₁ := M₁) (M₂ := M₂)
          (f₁ := f₁) (f₂ := f₂) (Y' := A₁) φ k kf₁ kf₂ hkf₁ hkf₂ ≫
        pullHom (F := F) (X₁ := X₂) (X₂ := X₃) (M₁ := M₂) (M₂ := M₃)
          (f₁ := f₂) (f₂ := f₃) (Y' := A₁) ψ k kf₂ kf₃ hkf₂ hkf₃ ≫
        pullHom (F := F) (X₁ := X₃) (X₂ := X₄) (M₁ := M₃) (M₂ := M₄)
          (f₁ := f₃) (f₂ := f₄) (Y' := A₁) χ k kf₃ kf₄ hkf₃ hkf₄ ≫
        pullHom (F := F) (X₁ := X₄) (X₂ := X₅) (M₁ := M₄) (M₂ := M₅)
          (f₁ := f₄) (f₂ := f₅) (Y' := A₁) ω k kf₄ kf₅ hkf₄ hkf₅ := by
  dsimp [pullHom]
  simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Pulling a fivefold composite back along a further base morphism is the composite of the five
pulled-back morphisms. -/
theorem pullHom_comp₅
    {X₁ X₂ X₃ X₄ X₅ X₆ : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {M₃ : F.obj (.mk (op X₃))}
    {M₄ : F.obj (.mk (op X₄))} {M₅ : F.obj (.mk (op X₅))}
    {M₆ : F.obj (.mk (op X₆))}
    {A₀ : C} {f₁ : A₀ ⟶ X₁} {f₂ : A₀ ⟶ X₂} {f₃ : A₀ ⟶ X₃}
    {f₄ : A₀ ⟶ X₄} {f₅ : A₀ ⟶ X₅} {f₆ : A₀ ⟶ X₆}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶
      (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (χ : (F.map f₃.op.toLoc).toFunctor.obj M₃ ⟶
      (F.map f₄.op.toLoc).toFunctor.obj M₄)
    (ω : (F.map f₄.op.toLoc).toFunctor.obj M₄ ⟶
      (F.map f₅.op.toLoc).toFunctor.obj M₅)
    (τ : (F.map f₅.op.toLoc).toFunctor.obj M₅ ⟶
      (F.map f₆.op.toLoc).toFunctor.obj M₆)
    {A₁ : C} (k : A₁ ⟶ A₀) (kf₁ : A₁ ⟶ X₁) (kf₂ : A₁ ⟶ X₂)
    (kf₃ : A₁ ⟶ X₃) (kf₄ : A₁ ⟶ X₄) (kf₅ : A₁ ⟶ X₅) (kf₆ : A₁ ⟶ X₆)
    (hkf₁ : k ≫ f₁ = kf₁ := by cat_disch) (hkf₂ : k ≫ f₂ = kf₂ := by cat_disch)
    (hkf₃ : k ≫ f₃ = kf₃ := by cat_disch) (hkf₄ : k ≫ f₄ = kf₄ := by cat_disch)
    (hkf₅ : k ≫ f₅ = kf₅ := by cat_disch) (hkf₆ : k ≫ f₆ = kf₆ := by cat_disch) :
    pullHom (F := F) (X₁ := X₁) (X₂ := X₆) (M₁ := M₁) (M₂ := M₆)
        (f₁ := f₁) (f₂ := f₆) (Y' := A₁) (φ ≫ ψ ≫ χ ≫ ω ≫ τ)
        k kf₁ kf₆ hkf₁ hkf₆ =
      pullHom (F := F) (X₁ := X₁) (X₂ := X₂) (M₁ := M₁) (M₂ := M₂)
          (f₁ := f₁) (f₂ := f₂) (Y' := A₁) φ k kf₁ kf₂ hkf₁ hkf₂ ≫
        pullHom (F := F) (X₁ := X₂) (X₂ := X₃) (M₁ := M₂) (M₂ := M₃)
          (f₁ := f₂) (f₂ := f₃) (Y' := A₁) ψ k kf₂ kf₃ hkf₂ hkf₃ ≫
        pullHom (F := F) (X₁ := X₃) (X₂ := X₄) (M₁ := M₃) (M₂ := M₄)
          (f₁ := f₃) (f₂ := f₄) (Y' := A₁) χ k kf₃ kf₄ hkf₃ hkf₄ ≫
        pullHom (F := F) (X₁ := X₄) (X₂ := X₅) (M₁ := M₄) (M₂ := M₅)
          (f₁ := f₄) (f₂ := f₅) (Y' := A₁) ω k kf₄ kf₅ hkf₄ hkf₅ ≫
        pullHom (F := F) (X₁ := X₅) (X₂ := X₆) (M₁ := M₅) (M₂ := M₆)
          (f₁ := f₅) (f₂ := f₆) (Y' := A₁) τ k kf₅ kf₆ hkf₅ hkf₆ := by
  dsimp [pullHom]
  simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back a pseudofunctor composition comparison inverse gives the corresponding
composition comparison inverse on the smaller base. -/
theorem pullHom_mapComp'_inv
    {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (h : X₂ ⟶ X₀) (k : X₃ ⟶ X₂)
    (M : F.obj (.mk (op X₁))) :
    pullHom (F := F)
        ((F.mapComp' f.op.toLoc h.op.toLoc (f.op.toLoc ≫ h.op.toLoc) (by rfl)).inv.toNatTrans.app M)
        k (k ≫ h) ((k ≫ h) ≫ f) (by rfl) (by simp) =
      (F.mapComp' f.op.toLoc (h.op.toLoc ≫ k.op.toLoc)
        (f.op.toLoc ≫ h.op.toLoc ≫ k.op.toLoc) (by simp)).inv.toNatTrans.app M := by
  dsimp [pullHom]
  simpa using
    (F.mapComp'₀₁₃_inv_app f.op.toLoc h.op.toLoc k.op.toLoc
      (f.op.toLoc ≫ h.op.toLoc) (h.op.toLoc ≫ k.op.toLoc)
      (f.op.toLoc ≫ h.op.toLoc ≫ k.op.toLoc) (by rfl) (by rfl) (by simp) M).symm

set_option linter.unnecessarySimpa false in
set_option backward.isDefEq.respectTransparency false in
/-- The same as `pullHom_mapComp'_inv`, with the composite base arrow supplied by an explicit
factorization equality. -/
theorem pullHom_mapComp'_inv_of_fac
    {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (h : X₂ ⟶ X₀) (k : X₃ ⟶ X₂)
    (kh : X₃ ⟶ X₀) (hkh : k ≫ h = kh)
    (M : F.obj (.mk (op X₁))) :
    pullHom (F := F)
        ((F.mapComp' f.op.toLoc h.op.toLoc (f.op.toLoc ≫ h.op.toLoc) (by rfl)).inv.toNatTrans.app M)
        k kh (kh ≫ f) hkh (by simpa [Category.assoc] using congrArg (fun q => q ≫ f) hkh) =
      (F.mapComp' f.op.toLoc kh.op.toLoc (f.op.toLoc ≫ kh.op.toLoc) (by simp)).inv.toNatTrans.app M := by
  subst kh
  simpa using pullHom_mapComp'_inv (F := F) f h k M

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back the image under a pseudofunctor restriction functor is just the image under the
composite restriction functor. -/
theorem pullHom_map_of_fac
    {X₀ Y Z : C} (h : Y ⟶ X₀) (k : Z ⟶ Y) (kh : Z ⟶ X₀) (hkh : k ≫ h = kh)
    {M N : F.obj (.mk (op X₀))} (ψ : M ⟶ N) :
    pullHom (F := F) ((F.map h.op.toLoc).toFunctor.map ψ)
      k kh kh hkh hkh =
    (F.map kh.op.toLoc).toFunctor.map ψ := by
  subst kh
  dsimp [pullHom]
  rw [F.mapComp'_naturality_2]

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back a pseudofunctor composition comparison gives the corresponding comparison on the
smaller base. -/
theorem pullHom_mapComp'_hom
    {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (h : X₂ ⟶ X₀) (k : X₃ ⟶ X₂)
    (M : F.obj (.mk (op X₁))) :
    pullHom (F := F)
        ((F.mapComp' f.op.toLoc h.op.toLoc (f.op.toLoc ≫ h.op.toLoc) (by rfl)).hom.toNatTrans.app M)
        k ((k ≫ h) ≫ f) (k ≫ h) (by simp [Category.assoc]) (by rfl) =
      (F.mapComp' f.op.toLoc (h.op.toLoc ≫ k.op.toLoc)
        (f.op.toLoc ≫ h.op.toLoc ≫ k.op.toLoc) (by simp)).hom.toNatTrans.app M := by
  dsimp [pullHom]
  rw [F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
      f.op.toLoc h.op.toLoc k.op.toLoc
      (f.op.toLoc ≫ h.op.toLoc) (h.op.toLoc ≫ k.op.toLoc)
      (f.op.toLoc ≫ h.op.toLoc ≫ k.op.toLoc) (by rfl) (by rfl) (by simp) M]
  simp

set_option linter.unnecessarySimpa false in
set_option backward.isDefEq.respectTransparency false in
/-- The same as `pullHom_mapComp'_hom`, with the composite base arrow supplied by an explicit
factorization equality. -/
theorem pullHom_mapComp'_hom_of_fac
    {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (h : X₂ ⟶ X₀) (k : X₃ ⟶ X₂)
    (kh : X₃ ⟶ X₀) (hkh : k ≫ h = kh)
    (M : F.obj (.mk (op X₁))) :
    pullHom (F := F)
        ((F.mapComp' f.op.toLoc h.op.toLoc (f.op.toLoc ≫ h.op.toLoc) (by rfl)).hom.toNatTrans.app M)
        k (kh ≫ f) kh
        (by simpa [Category.assoc] using congrArg (fun q => q ≫ f) hkh) hkh =
      (F.mapComp' f.op.toLoc kh.op.toLoc (f.op.toLoc ≫ kh.op.toLoc) (by simp)).hom.toNatTrans.app M := by
  subst kh
  simpa using pullHom_mapComp'_hom (F := F) f h k M

end Pseudofunctor.LocallyDiscreteOpToCat

namespace FibredCategoryMor

set_option backward.isDefEq.respectTransparency false in
/-- Transporting the owner of a canonical pullback object along an equality of fibre objects
commutes with the chosen pullback map.  This small owner-transport lemma is used when comparing
explicit pullback objects rebuilt after a further restriction. -/
theorem canonicalPullbackChoice_map_eqToHom
    {T : Type uX} [Category.{vX} T] (p : T ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (h : x = y) :
    (eqToHom (congrArg (fun z : p.Fiber U => f ^*[canonicalPullbackChoice p] z) h) :
        f ^*[canonicalPullbackChoice p] x ⟶ f ^*[canonicalPullbackChoice p] y).1 ≫
      (canonicalPullbackChoice p).map f y =
        (canonicalPullbackChoice p).map f x ≫
          eqToHom (congrArg Subtype.val h) := by
  cases h
  change (𝟙 (f ^*[canonicalPullbackChoice p] x).1) ≫
      (canonicalPullbackChoice p).map f x =
    (canonicalPullbackChoice p).map f x ≫ 𝟙 x.1
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposing a normalized `pullHom` with the chosen cartesian map gives the same total
arrow as first pulling back the source object and then postcomposing the original morphism.

This is the source proof's basic restriction calculation in the canonical-fiber-pseudofunctor
language. -/
theorem canonicalFiberPseudofunctor_pullHom_postcompose_cartesian
    {T : Type uX} [Category.{vX} T] (p : T ⥤ C) [p.IsFibered]
    {X₁ X₂ Y Y' : C} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (k : Y' ⟶ Y)
    (kf₁ : Y' ⟶ X₁) (kf₂ : Y' ⟶ X₂)
    (hkf₁ : k ≫ f₁ = kf₁) (hkf₂ : k ≫ f₂ = kf₂)
    {M₁ : p.Fiber X₁} {M₂ : p.Fiber X₂}
    (φ : ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.obj M₂) :
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor p) φ k kf₁ kf₂ hkf₁ hkf₂).1 ≫
      (canonicalPullbackChoice p).map kf₂ M₂ =
    (((canonicalFiberPseudofunctor p).mapComp' f₁.op.toLoc k.op.toLoc kf₁.op.toLoc
        (comp_toLoc_eq f₁ k kf₁ hkf₁)).hom.toNatTrans.app M₁).1 ≫
      (canonicalPullbackChoice p).map k
        (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.obj M₁) ≫
      φ.1 ≫ (canonicalPullbackChoice p).map f₂ M₂ := by
  have hinv := canonicalFiberPseudofunctor_mapComp'_inv_app_fac p f₂ k kf₂ hkf₂ M₂
  have hmap := canonical_pullbackFunctor_map_fac p k φ
  dsimp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  let A := ((canonicalFiberPseudofunctor p).mapComp' f₁.op.toLoc k.op.toLoc kf₁.op.toLoc
    (comp_toLoc_eq f₁ k kf₁ hkf₁)).hom.toNatTrans.app M₁
  let B := ((canonicalFiberPseudofunctor p).map k.op.toLoc).toFunctor.map φ
  let D := ((canonicalFiberPseudofunctor p).mapComp' f₂.op.toLoc k.op.toLoc kf₂.op.toLoc
    (comp_toLoc_eq f₂ k kf₂ hkf₂)).inv.toNatTrans.app M₂
  change Functor.Fiber.fiberInclusion.map (A ≫ B ≫ D) ≫
      (canonicalPullbackChoice p).map kf₂ M₂ =
    A.1 ≫ (canonicalPullbackChoice p).map k
      (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.obj M₁) ≫
    φ.1 ≫ (canonicalPullbackChoice p).map f₂ M₂
  calc
    Functor.Fiber.fiberInclusion.map (A ≫ B ≫ D) ≫
        (canonicalPullbackChoice p).map kf₂ M₂
        = A.1 ≫ B.1 ≫ D.1 ≫ (canonicalPullbackChoice p).map kf₂ M₂ := by
          rw [Functor.map_comp, Functor.map_comp]
          simp only [Functor.Fiber.fiberInclusion]
          simp [Category.assoc]
    _ = A.1 ≫ B.1 ≫
          ((canonicalPullbackChoice p).map k
            (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.obj M₂) ≫
          (canonicalPullbackChoice p).map f₂ M₂) := by
          simpa [A, B, D, Category.assoc] using
            congrArg (fun t => A.1 ≫ B.1 ≫ t) hinv
    _ = A.1 ≫
          ((canonicalPullbackChoice p).map k
            (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.obj M₁) ≫ φ.1) ≫
          (canonicalPullbackChoice p).map f₂ M₂ := by
          simpa [A, B, Category.assoc] using
            congrArg
              (fun t => A.1 ≫ t ≫ (canonicalPullbackChoice p).map f₂ M₂)
              hmap
    _ = A.1 ≫ (canonicalPullbackChoice p).map k
          (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.obj M₁) ≫
          φ.1 ≫ (canonicalPullbackChoice p).map f₂ M₂ := by
          simp [Category.assoc]

/-- Helper for Chap08 Lemma 8 8 1: the co-Grothendieck fibred category attached to a
`Cat`-valued presheaf, used as the split source model in the naive stackification construction.
-/
abbrev catValuedCoGrothendieckModel (F : Cᵒᵖ ⥤ Cat.{vX, uX}) : FibredCategoryOver C :=
  FibredCategoryOver.ofFunctor
    (Pseudofunctor.CoGrothendieck.forget (F.toPseudofunctor'))

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 1: over the identity object of a slice site, the canonical
Hom-presheaf restriction is exactly the canonical pullback-functor action on a fiber morphism. -/
theorem presheafHom_map_identitySlice_hom
    {T : Type uX} [Category.{vX} T] (p : T ⥤ C) [p.IsFibered]
    {W Z : C} (g : Z ⟶ W)
    (M N : p.Fiber W)
    (φ : M ⟶ N) :
    ((canonicalFiberPseudofunctor p).presheafHom M N).map
        (Over.homMk g : Over.mk (g ≫ 𝟙 W) ⟶ Over.mk (𝟙 W)).op
        ((canonicalFiberPseudofunctor p).presheafHomObjHomEquiv φ) =
      ((canonicalFiberPseudofunctor p).map (g ≫ 𝟙 W).op.toLoc).toFunctor.map φ := by
  rw [Pseudofunctor.presheafHom_map]
  dsimp only []
  rw [Pseudofunctor.presheafHomObjHomEquiv_apply]
  dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  have hmid :
      ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op W))).hom.toNatTrans.app M ≫
          φ ≫
          ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op W))).inv.toNatTrans.app N =
        ((canonicalFiberPseudofunctor p).map (Over.mk (𝟙 W)).hom.op.toLoc).toFunctor.map φ := by
    rw [← (canonicalFiberPseudofunctor p).mapId'_eq_mapId (LocallyDiscrete.mk (op W)),
      ← Category.assoc,
      ← (canonicalFiberPseudofunctor p).mapId'_hom_naturality
        (𝟙 (LocallyDiscrete.mk (op W))) rfl φ,
      Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]
    rfl
  simp [hmid]

set_option backward.isDefEq.respectTransparency false in
/-- Variant of `presheafHom_map_identitySlice_hom` with the source object written as
`Over.mk g` rather than the default elaboration `Over.mk (g ≫ 𝟙 W)`. -/
theorem presheafHom_map_identitySlice_hom_overMk
    {T : Type uX} [Category.{vX} T] (p : T ⥤ C) [p.IsFibered]
    {W Z : C} (g : Z ⟶ W)
    (M N : p.Fiber W)
    (φ : M ⟶ N) :
    ((canonicalFiberPseudofunctor p).presheafHom M N).map
        (Over.homMk g : Over.mk g ⟶ Over.mk (𝟙 W)).op
        ((canonicalFiberPseudofunctor p).presheafHomObjHomEquiv φ) =
      ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ := by
  rw [Pseudofunctor.presheafHom_map]
  dsimp only []
  rw [Pseudofunctor.presheafHomObjHomEquiv_apply]
  dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  have hmid :
      ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op W))).hom.toNatTrans.app M ≫
          φ ≫
          ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op W))).inv.toNatTrans.app N =
        ((canonicalFiberPseudofunctor p).map (Over.mk (𝟙 W)).hom.op.toLoc).toFunctor.map φ := by
    rw [← (canonicalFiberPseudofunctor p).mapId'_eq_mapId (LocallyDiscrete.mk (op W)),
      ← Category.assoc,
      ← (canonicalFiberPseudofunctor p).mapId'_hom_naturality
        (𝟙 (LocallyDiscrete.mk (op W))) rfl φ,
      Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]
    rfl
  simp [hmid]

set_option backward.isDefEq.respectTransparency false in
/-- A cover of `W`, viewed as a covering family of the identity object of the slice site over
`W`. -/
theorem cover_overFamily_covering {W : C} (S : J.Cover W) :
    Sieve.ofArrows
      (fun I : S.Arrow => Over.mk I.f)
      (fun I => (Over.homMk I.f : Over.mk I.f ⟶ Over.mk (𝟙 W))) ∈
      (J.over W) (Over.mk (𝟙 W)) := by
  rw [GrothendieckTopology.mem_over_iff]
  have hEq :
      Sieve.overEquiv (Over.mk (𝟙 W))
        (Sieve.ofArrows
          (fun I : S.Arrow => Over.mk I.f)
          (fun I => (Over.homMk I.f : Over.mk I.f ⟶ Over.mk (𝟙 W)))) =
        Sieve.ofArrows (fun I : S.Arrow => I.Y) (fun I => I.f) := by
    ext A q
    rw [Sieve.overEquiv_iff, Sieve.mem_ofArrows_iff, Sieve.mem_ofArrows_iff]
    constructor
    · rintro ⟨I, a, hfac⟩
      refine ⟨I, a.left, ?_⟩
      exact congrArg (fun k => k.left) hfac
    · rintro ⟨I, a, hfac⟩
      refine ⟨I, Over.homMk a ?_, ?_⟩
      · simp [hfac]
      · ext
        exact hfac
  rw [hEq]
  rw [GrothendieckTopology.Cover.ofArrows_eq S]
  exact S.condition

theorem cover_overFamily_covering_id_comp {W : C} (S : J.Cover W) :
    Sieve.ofArrows
      (fun I : S.Arrow => Over.mk (𝟙 I.Y ≫ I.f))
      (fun I =>
        (Over.homMk (𝟙 I.Y ≫ I.f) :
          Over.mk (𝟙 I.Y ≫ I.f) ⟶ Over.mk (𝟙 W))) ∈
      (J.over W) (Over.mk (𝟙 W)) := by
  rw [GrothendieckTopology.mem_over_iff]
  have hEq :
      Sieve.overEquiv (Over.mk (𝟙 W))
        (Sieve.ofArrows
          (fun I : S.Arrow => Over.mk (𝟙 I.Y ≫ I.f))
          (fun I =>
            (Over.homMk (𝟙 I.Y ≫ I.f) :
              Over.mk (𝟙 I.Y ≫ I.f) ⟶ Over.mk (𝟙 W)))) =
        Sieve.ofArrows (fun I : S.Arrow => I.Y) (fun I => I.f) := by
    ext A q
    rw [Sieve.overEquiv_iff, Sieve.mem_ofArrows_iff, Sieve.mem_ofArrows_iff]
    constructor
    · rintro ⟨I, a, hfac⟩
      refine ⟨I, a.left, ?_⟩
      simpa [Category.assoc] using congrArg (fun k => k.left) hfac
    · rintro ⟨I, a, hfac⟩
      refine ⟨I, Over.homMk a ?_, ?_⟩
      · simp [hfac]
      · ext
        simpa [Category.assoc] using hfac
  rw [hEq]
  rw [GrothendieckTopology.Cover.ofArrows_eq S]
  exact S.condition

set_option backward.isDefEq.respectTransparency false in
/-- If the Hom presheaf is a sheaf, equality of two fiber morphisms can be checked after
restriction to a covering family. -/
theorem fiberHom_ext_of_cover
    {T : Type uX} [Category.{vX} T] (p : T ⥤ C) [p.IsFibered]
    {W : C} (S : J.Cover W)
    (M N : p.Fiber W)
    (hSheaf : Presheaf.IsSheaf (J.over W)
      ((canonicalFiberPseudofunctor p).presheafHom M N))
    {φ ψ : M ⟶ N}
    (h : ∀ I : S.Arrow,
      ((canonicalFiberPseudofunctor p).map I.f.op.toLoc).toFunctor.map φ =
        ((canonicalFiberPseudofunctor p).map I.f.op.toLoc).toFunctor.map ψ) :
    φ = ψ := by
  let P := (canonicalFiberPseudofunctor p).presheafHom M N
  let eφ := (canonicalFiberPseudofunctor p).presheafHomObjHomEquiv φ
  let eψ := (canonicalFiberPseudofunctor p).presheafHomObjHomEquiv ψ
  apply ((canonicalFiberPseudofunctor p).presheafHomObjHomEquiv).injective
  have hfun :
      (fun _ : PUnit => eφ) = (fun _ : PUnit => eψ) := by
    apply hSheaf.hom_ext_ofArrows
      (f := fun I : S.Arrow =>
        (Over.homMk I.f : Over.mk I.f ⟶ Over.mk (𝟙 W)))
      (hf := cover_overFamily_covering (J := J) S)
    intro I
    funext _
    change P.map (Over.homMk I.f : Over.mk I.f ⟶ Over.mk (𝟙 W)).op eφ =
      P.map (Over.homMk I.f : Over.mk I.f ⟶ Over.mk (𝟙 W)).op eψ
    rw [presheafHom_map_identitySlice_hom_overMk (p := p) I.f M N φ,
      presheafHom_map_identitySlice_hom_overMk (p := p) I.f M N ψ]
    exact h I
  exact congrFun hfun PUnit.unit

set_option backward.isDefEq.respectTransparency false in
/-- Variant of `fiberHom_ext_of_cover` where each cover arrow is presented as
`𝟙 I.Y ≫ I.f`.  This keeps later source-faithful refinements on the same formal owner as the
two-step restriction that produced them. -/
theorem fiberHom_ext_of_cover_id_comp
    {T : Type uX} [Category.{vX} T] (p : T ⥤ C) [p.IsFibered]
    {W : C} (S : J.Cover W)
    (M N : p.Fiber W)
    (hSheaf : Presheaf.IsSheaf (J.over W)
      ((canonicalFiberPseudofunctor p).presheafHom M N))
    {φ ψ : M ⟶ N}
    (h : ∀ I : S.Arrow,
      ((canonicalFiberPseudofunctor p).map (𝟙 I.Y ≫ I.f).op.toLoc).toFunctor.map φ =
        ((canonicalFiberPseudofunctor p).map (𝟙 I.Y ≫ I.f).op.toLoc).toFunctor.map ψ) :
    φ = ψ := by
  let P := (canonicalFiberPseudofunctor p).presheafHom M N
  let eφ := (canonicalFiberPseudofunctor p).presheafHomObjHomEquiv φ
  let eψ := (canonicalFiberPseudofunctor p).presheafHomObjHomEquiv ψ
  apply ((canonicalFiberPseudofunctor p).presheafHomObjHomEquiv).injective
  have hfun :
      (fun _ : PUnit => eφ) = (fun _ : PUnit => eψ) := by
    apply hSheaf.hom_ext_ofArrows
      (f := fun I : S.Arrow =>
        (Over.homMk (𝟙 I.Y ≫ I.f) :
          Over.mk (𝟙 I.Y ≫ I.f) ⟶ Over.mk (𝟙 W)))
      (hf := cover_overFamily_covering_id_comp (J := J) S)
    intro I
    funext _
    change P.map
      (Over.homMk (𝟙 I.Y ≫ I.f) :
        Over.mk (𝟙 I.Y ≫ I.f) ⟶ Over.mk (𝟙 W)).op eφ =
      P.map
      (Over.homMk (𝟙 I.Y ≫ I.f) :
        Over.mk (𝟙 I.Y ≫ I.f) ⟶ Over.mk (𝟙 W)).op eψ
    rw [presheafHom_map_identitySlice_hom_overMk (p := p) (𝟙 I.Y ≫ I.f) M N φ,
      presheafHom_map_identitySlice_hom_overMk (p := p) (𝟙 I.Y ≫ I.f) M N ψ]
    exact h I
  exact congrFun hfun PUnit.unit

noncomputable def overMapIdentitySliceIso {U V : C} (f : V ⟶ U) :
    (Over.map f).obj (Over.mk (𝟙 V)) ≅ Over.mk f :=
  Over.isoMk (Iso.refl V) (by dsimp [Over.mk, Over.map, Comma.mapRight])

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 1: at the identity object of the smaller slice, the Hom side of
`Pseudofunctor.overMapCompPresheafHomIso` is exactly the usual identity-slice Hom equivalence.
This is the base-change bridge used to pass the separatedness proof from identity slices to
arbitrary slice objects. -/
theorem overMapCompPresheafHomIso_hom_app_identitySlice
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vX, uX})
    {U V : C} (f : V ⟶ U) {M N : F.obj (.mk (op U))}
    (δ : (F.presheafHom M N).obj (op (Over.mk f))) :
    ((F.overMapCompPresheafHomIso M N f).hom.app (op (Over.mk (𝟙 V)))
        ((F.presheafHom M N).map (overMapIdentitySliceIso f).hom.op δ)) =
      F.presheafHomObjHomEquiv δ := by
  dsimp [Pseudofunctor.overMapCompPresheafHomIso, Pseudofunctor.presheafHom,
    Pseudofunctor.presheafHomObjHomEquiv, Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Iso.homCongr, Iso.homFromEquiv, Iso.homToEquiv, Equiv.trans, overMapIdentitySliceIso]
  let κ := F.mapComp' f.op.toLoc (𝟙 (LocallyDiscrete.mk (op V)))
    (f.op.toLoc ≫ 𝟙 (LocallyDiscrete.mk (op V))) rfl
  let e := F.mapId (LocallyDiscrete.mk (op V))
  let m := (F.map (𝟙 (LocallyDiscrete.mk (op V)))).toFunctor.map δ
  change (κ.inv.toNatTrans.app M ≫ κ.hom.toNatTrans.app M ≫ m ≫
        κ.inv.toNatTrans.app N) ≫ κ.hom.toNatTrans.app N =
      e.hom.toNatTrans.app ((F.map f.op.toLoc).toFunctor.obj M) ≫ δ ≫
        e.inv.toNatTrans.app ((F.map f.op.toLoc).toFunctor.obj N)
  have hmid :
      e.hom.toNatTrans.app ((F.map f.op.toLoc).toFunctor.obj M) ≫ δ ≫
          e.inv.toNatTrans.app ((F.map f.op.toLoc).toFunctor.obj N) = m := by
    dsimp only [m]
    simpa only [Functor.id_obj, Functor.id_map, Category.assoc,
      Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id, Over.mk_hom] using
      (e.hom.toNatTrans.naturality_assoc δ
        (e.inv.toNatTrans.app ((F.map f.op.toLoc).toFunctor.obj N))).symm
  rw [hmid]
  calc
    (κ.inv.toNatTrans.app M ≫ κ.hom.toNatTrans.app M ≫ m ≫
          κ.inv.toNatTrans.app N) ≫ κ.hom.toNatTrans.app N =
        m ≫ κ.inv.toNatTrans.app N ≫ κ.hom.toNatTrans.app N := by
          simpa only [Category.assoc, Category.id_comp] using
            congrArg
              (fun t => t ≫ m ≫ κ.inv.toNatTrans.app N ≫ κ.hom.toNatTrans.app N)
              (Cat.Hom.inv_hom_id_toNatTrans_app κ M)
    _ = m ≫ 𝟙 _ := by
          exact congrArg (fun t => m ≫ t) (Cat.Hom.inv_hom_id_toNatTrans_app κ N)
    _ = m := Category.comp_id _

end FibredCategoryMor

end CategoryTheory
