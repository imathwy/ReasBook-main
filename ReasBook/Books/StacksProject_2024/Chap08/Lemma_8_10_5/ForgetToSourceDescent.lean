import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Lemma_8_10_5.ForgetToSource

universe uC uX vC vX

namespace CategoryTheory

open FibredCategoryMor
open Functor IsStronglyCartesian
open StackInGroupoidsOver.Hom

section

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver J}

/-- Helper for Lemma 8.10.5: composing in `Yₛ.S` and then passing to the locally discrete
opposite is the same as composing the corresponding `toLoc` arrows in the owner order used by
`pullHom`. -/
private theorem inherited_comp_toLoc_eq
    {A B D : Yₛ.S} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf) :
    f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc := by
  -- Translate the composite equality to `LocallyDiscrete Yₛ.Sᵒᵖ`.
  simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
    congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hgf)

/-- Helper for Lemma 8.10.5: name the corrected comparison-conjugated overlap map obtained by
forgetting one `G F` descent-datum overlap morphism to `Xₛ`. -/
noncomputable abbrev inherited_basis_descent_hom
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : Yₛ.S} (q : Z ⟶ y) {i₁ i₂ : ι} (f₁ : Z ⟶ Y i₁) (f₂ : Z ⟶ Y i₂)
    (hf₁ : f₁ ≫ g i₁ = q := by cat_disch) (hf₂ : f₂ ≫ g i₂ = q := by cat_disch) :
    (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f₁).op.toLoc).toFunctor.obj
        (inherited_source_fiber_obj (F := F) (D.obj i₁))) ⟶
      (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f₂).op.toLoc).toFunctor.obj
        (inherited_source_fiber_obj (F := F) (D.obj i₂))) :=
  let e₁ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₁ (D.obj i₁)
  let e₂ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₂ (D.obj i₂)
  -- Route correction: the comparison iso goes from the forgotten `G F` pullback to the
  -- canonical `Xₛ` pullback, so the descent morphism must be conjugated by `inv ... hom`.
  e₁.inv ≫ (inherited_source_fiber_forget (F := F) _).map (D.hom q f₁ f₂ hf₁ hf₂) ≫ e₂.hom

/-- Helper for Lemma 8.10.5: after forgetting to `Xₛ`, the self-overlap morphism normalizes to
the identity once the corrected comparison shell is fixed. -/
theorem inherited_basis_descent_hom_self_normalize
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : Yₛ.S} (q : Z ⟶ y) {i : ι} (f : Z ⟶ Y i)
    (hf : f ≫ g i = q := by cat_disch) :
    inherited_basis_descent_hom (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f f hf hf = 𝟙 _ := by
  let e :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f (D.obj i)
  have hself :
      (inherited_source_fiber_forget (F := F) Z).map (D.hom q f f hf hf) =
        𝟙 (inherited_source_fiber_obj (F := F)
          ((((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj (D.obj i)))) := by
    -- Rewrite the forgotten middle term to the mapped identity before canceling the comparison.
    calc
      (inherited_source_fiber_forget (F := F) Z).map (D.hom q f f hf hf)
          =
            (inherited_source_fiber_forget (F := F) Z).map
              (𝟙
                ((((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj
                  (D.obj i)))) := by
                simpa using
                  congrArg (fun k ↦ (inherited_source_fiber_forget (F := F) Z).map k)
                    (D.hom_self q f hf)
      _ =
          𝟙 (inherited_source_fiber_obj (F := F)
            ((((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj
              (D.obj i)))) := by
            exact (inherited_source_fiber_forget (F := F) Z).map_id _
  -- Reduce to the literal `comparison.inv ≫ 𝟙 ≫ comparison.hom` cancellation shape.
  change e.inv ≫ (inherited_source_fiber_forget (F := F) Z).map (D.hom q f f hf hf) ≫ e.hom = 𝟙 _
  rw [hself]
  calc
    e.inv ≫ 𝟙 _ ≫ e.hom = e.inv ≫ e.hom := by simp
    _ = 𝟙 _ := e.inv_hom_id

/-- Helper for Lemma 8.10.5: after forgetting the source descent datum to the overlap fiber of
`Xₛ`, the source cocycle identity still holds before any pullback-comparison conjugation. -/
private theorem inherited_basis_descent_hom_mapped_source_cocycle
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : Yₛ.S} (q : Z ⟶ y) {i₁ i₂ i₃ : ι}
    (f₁ : Z ⟶ Y i₁) (f₂ : Z ⟶ Y i₂) (f₃ : Z ⟶ Y i₃)
    (hf₁ : f₁ ≫ g i₁ = q := by cat_disch) (hf₂ : f₂ ≫ g i₂ = q := by cat_disch)
    (hf₃ : f₃ ≫ g i₃ = q := by cat_disch) :
    (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
        (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₂ f₃ hf₂ hf₃) =
      (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₃ hf₁ hf₃) := by
  -- Map the source cocycle relation through the fixed forgetting functor on the overlap fiber.
  calc
    (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
        (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₂ f₃ hf₂ hf₃) =
      (inherited_source_fiber_forget (F := F) Z).map
        (D.hom q f₁ f₂ hf₁ hf₂ ≫ D.hom q f₂ f₃ hf₂ hf₃) := by
          rw [(inherited_source_fiber_forget (F := F) Z).map_comp]
    _ =
      (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₃ hf₁ hf₃) := by
        exact congrArg
          (fun k ↦ (inherited_source_fiber_forget (F := F) Z).map k)
          (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)

theorem inherited_basis_descent_hom_comp_normalize
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : Yₛ.S} (q : Z ⟶ y) {i₁ i₂ i₃ : ι}
    (f₁ : Z ⟶ Y i₁) (f₂ : Z ⟶ Y i₂) (f₃ : Z ⟶ Y i₃)
    (hf₁ : f₁ ≫ g i₁ = q := by cat_disch) (hf₂ : f₂ ≫ g i₂ = q := by cat_disch)
    (hf₃ : f₃ ≫ g i₃ = q := by cat_disch) :
    inherited_basis_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂ ≫
      inherited_basis_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₂ f₃ hf₂ hf₃ =
    inherited_basis_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₃ hf₁ hf₃ := by
  let e₁ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₁ (D.obj i₁)
  let e₂ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₂ (D.obj i₂)
  let e₃ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₃ (D.obj i₃)
  let m₁₂ := (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₂ hf₁ hf₂)
  let m₂₃ := (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₂ f₃ hf₂ hf₃)
  let m₁₃ := (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₃ hf₁ hf₃)
  have hmid : m₁₂ ≫ m₂₃ = m₁₃ :=
    inherited_basis_descent_hom_mapped_source_cocycle
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ f₃ hf₁ hf₂ hf₃
  have h1 :
      inherited_basis_descent_hom
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂ ≫
        inherited_basis_descent_hom
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₂ f₃ hf₂ hf₃ =
      e₁.inv ≫ m₁₂ ≫ e₂.hom ≫ e₂.inv ≫ m₂₃ ≫ e₃.hom := by
    simp only [inherited_basis_descent_hom, e₁, e₂, e₃, m₁₂, m₂₃, Category.assoc]
    rfl
  have h2 : e₂.hom ≫ e₂.inv ≫ m₂₃ ≫ e₃.hom = m₂₃ ≫ e₃.hom :=
    Iso.hom_inv_id_assoc e₂ (m₂₃ ≫ e₃.hom)
  have h3 := congrArg (fun k ↦ e₁.inv ≫ m₁₂ ≫ k) h2
  have h4 := congrArg (fun k ↦ e₁.inv ≫ k)
    ((Category.assoc m₁₂ m₂₃ e₃.hom).symm.trans
      (congrArg (fun k ↦ k ≫ e₃.hom) hmid))
  have h5 :
      e₁.inv ≫ m₁₃ ≫ e₃.hom =
        inherited_basis_descent_hom
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₃ hf₁ hf₃ := by
    simp only [inherited_basis_descent_hom, e₁, e₃, m₁₃, Category.assoc]
    rfl
  exact h1.trans (h3.trans (h4.trans h5))

end

end CategoryTheory
