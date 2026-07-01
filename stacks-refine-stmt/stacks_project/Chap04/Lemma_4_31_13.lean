import Mathlib
import stacks_project.Chap04.Definition_4_31_2
import stacks_project.Chap04.Lemma_4_31_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

namespace CategoryTheory.Limits

universe v₁ v₂ v u₁ u₂ u

variable {C₀ : Type u₁} [Category.{v₁} C₀]
variable {D₀ : Type u₂} [Category.{v₂} D₀]

/- Domain-style sampling for Lemma 4.31.13:
- primary domain: bicategorical `2`-fibre products in `Cat`, expressed through categorical
  pullbacks and the canonical diagonal into a self-pullback;
- sampled owner-level declarations:
  `Bicategory.IsFinal`,
  `CatCommSqOver.toBicategoricalSquare`,
  `CatCommSqOver.toFunctorToCategoricalPullback`,
  `CategoricalPullback.toCatCommSqOver`,
  the generic `CatCommSqOver.toFunctorToCategoricalPullback`-equivalence instance from
  `Lemma_4_31_11`,
  `two_fibre_product_map`;
- best owner abstraction: `CatCommSqOver` is the primitive categorical square data, while
  `Bicategory.IsFinal` of the associated `BicategoricalTwoCommutativeSquare` is the universal
  property owner;
- primitive data: the categorical square underlying the public owner
  `two_fibre_product_diagonal_square F G H`;
- derived API: the diagonal functor `Δₚ H`, obtained by applying
  `CatCommSqOver.toFunctorToCategoricalPullback` to the identity square over `H` and `H`; the
  short owner name
  `categorical_pullback_diagonal` is kept only as stable chapter vocabulary for this canonical
  comparison functor, together with the
  finality/equivalence consequences obtained from the owner square through the canonical
  comparison functor.

Source/core/bridge triage:
- `source-facing`: the displayed square with bottom map `Δₚ H`;
- `core/canonical`: `Bicategory.IsFinal (two_fibre_product_diagonal_square F G H)`;
- `bridge/view`: the direct canonical use of `CatCommSqOver.toFunctorToCategoricalPullback`
  applied to the identity square in `CatCommSqOver H H C₀` and to
  `two_fibre_product_diagonal_square_over F G H`. -/

/-- The canonical diagonal functor `Δₚ H : C ⥤ C ×[D] C` attached to a functor `H : C ⥤ D`. -/
abbrev categorical_pullback_diagonal (H : C₀ ⥤ D₀) : C₀ ⥤ H ⊡ H :=
  (toFunctorToCategoricalPullback H H C₀).obj
    { fst := 𝟭 C₀
      snd := 𝟭 C₀
      iso := Iso.refl _ }

@[inherit_doc categorical_pullback_diagonal]
scoped[CategoricalPullback] notation "Δₚ" => CategoryTheory.Limits.categorical_pullback_diagonal

open scoped CategoricalPullback
local notation "Δₚ" => CategoryTheory.Limits.categorical_pullback_diagonal

variable {A : Type (max u v)} [Category.{v} A]
variable {B : Type (max u v)} [Category.{v} B]
variable {C : Type (max u v)} [Category.{v} C]
variable {D : Type (max u v)} [Category.{v} D]

/- The functor from `A ×[C] B` to the base category `C`, obtained from the first projection. -/
private abbrev two_fibre_product_to_base (F : A ⥤ C) (G : B ⥤ C) :
    F ⊡ G ⥤ C :=
  π₁ F G ⋙ F

/- Postcomposing the comparison isomorphism with `H` induces a functor
`A ×[C] B ⥤ A ×[D] B`. -/
private abbrev two_fibre_product_postcompose (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    F ⊡ G ⥤ (F ⋙ H) ⊡ (G ⋙ H) :=
  two_fibre_product_map
    (Functor.leftUnitor (G ⋙ H))
    (Functor.leftUnitor (F ⋙ H)).symm

@[simp] private theorem two_fibre_product_postcompose_obj_fst
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) (X : F ⊡ G) :
    ((two_fibre_product_postcompose F G H).obj X).fst = X.fst := rfl

@[simp] private theorem two_fibre_product_postcompose_obj_snd
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) (X : F ⊡ G) :
    ((two_fibre_product_postcompose F G H).obj X).snd = X.snd := rfl

@[simp] private theorem two_fibre_product_postcompose_map_fst
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    {X Y : F ⊡ G} (f : X ⟶ Y) :
    ((two_fibre_product_postcompose F G H).map f).fst = f.fst := rfl

@[simp] private theorem two_fibre_product_postcompose_map_snd
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    {X Y : F ⊡ G} (f : X ⟶ Y) :
    ((two_fibre_product_postcompose F G H).map f).snd = f.snd := rfl

/-- The right vertical functor `A ×[D] B ⥤ C ×[D] C`. -/
abbrev two_fibre_product_right_vertical (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    (F ⋙ H) ⊡ (G ⋙ H) ⥤ H ⊡ H :=
  two_fibre_product_map
    (Functor.rightUnitor (G ⋙ H)).symm
    (Functor.rightUnitor (F ⋙ H))

@[simp] private theorem two_fibre_product_right_vertical_obj_fst
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (F ⋙ H) ⊡ (G ⋙ H)) :
    ((two_fibre_product_right_vertical F G H).obj X).fst = F.obj X.fst := rfl

@[simp] private theorem two_fibre_product_right_vertical_obj_snd
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (F ⋙ H) ⊡ (G ⋙ H)) :
    ((two_fibre_product_right_vertical F G H).obj X).snd = G.obj X.snd := rfl

@[simp] private theorem two_fibre_product_right_vertical_map_fst
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    {X Y : (F ⋙ H) ⊡ (G ⋙ H)} (f : X ⟶ Y) :
    ((two_fibre_product_right_vertical F G H).map f).fst = F.map f.fst := rfl

@[simp] private theorem two_fibre_product_right_vertical_map_snd
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    {X Y : (F ⋙ H) ⊡ (G ⋙ H)} (f : X ⟶ Y) :
    ((two_fibre_product_right_vertical F G H).map f).snd = G.map f.snd := rfl

private abbrev two_fibre_product_diagonal_square_top
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    F ⊡ G ⥤ H ⊡ H :=
  two_fibre_product_postcompose F G H ⋙ two_fibre_product_right_vertical F G H

private abbrev two_fibre_product_diagonal_square_bottom
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    F ⊡ G ⥤ H ⊡ H :=
  two_fibre_product_to_base F G ⋙ Δₚ H

/-- The first projected component of the diagonal square is the identity. -/
private abbrev two_fibre_product_diagonal_square_first_iso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    two_fibre_product_diagonal_square_top F G H ⋙ π₁ H H ≅
      two_fibre_product_diagonal_square_bottom F G H ⋙ π₁ H H :=
  NatIso.ofComponents (fun X ↦ Iso.refl _) (fun {X Y} f ↦ by
    simp [two_fibre_product_to_base])

/-- The second projected component of the diagonal square is the canonical comparison
isomorphism on `A ×[C] B`. -/
private abbrev two_fibre_product_diagonal_square_second_iso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    two_fibre_product_diagonal_square_top F G H ⋙ π₂ H H ≅
      two_fibre_product_diagonal_square_bottom F G H ⋙ π₂ H H :=
  by
    simpa [two_fibre_product_to_base] using
      (CatCommSq.iso (π₁ F G) (π₂ F G) F G).symm

/- The displayed square
`A ×[C] B ⥤ A ×[D] B`, `A ×[C] B ⥤ C`, `A ×[D] B ⥤ C ×[D] C`, `C ⥤ C ×[D] C`
is `2`-commutative. -/
private abbrev two_fibre_product_diagonal_square_iso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    two_fibre_product_diagonal_square_top F G H ≅
      two_fibre_product_diagonal_square_bottom F G H :=
  mkNatIso
    (two_fibre_product_diagonal_square_first_iso F G H)
    (two_fibre_product_diagonal_square_second_iso F G H)
    (by
      ext X
      sorry)

/- The given square regarded as an object of the categorical owner of commutative squares over the
cospan `A ×[D] B ⥤ C ×[D] C ← C`. This is the bridge/view layer; the owner-level finality
statement below is expressed directly on its associated `BicategoricalTwoCommutativeSquare`. -/
private abbrev two_fibre_product_diagonal_square_over
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    CatCommSqOver
      (two_fibre_product_right_vertical F G H) (Δₚ H)
      (F ⊡ G) :=
  { fst := two_fibre_product_postcompose F G H
    snd := two_fibre_product_to_base F G
    iso := two_fibre_product_diagonal_square_iso F G H }

open scoped Bicategory

/-- The square
`A ×[C] B ⥤ A ×[D] B`, `A ×[C] B ⥤ C`, `A ×[D] B ⥤ C ×[D] C`, `C ⥤ C ×[D] C`
with bottom map the diagonal `Δₚ H`, viewed as the chapter's bicategorical square in `Cat`. -/
abbrev two_fibre_product_diagonal_square
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    BicategoricalTwoCommutativeSquare
      (two_fibre_product_right_vertical F G H).toCatHom
      (Δₚ H).toCatHom :=
  (two_fibre_product_diagonal_square_over F G H).toBicategoricalSquare

/-- Lemma 4.31.13: the displayed square with bottom map the diagonal `Δ_{C/D}` is a
`2`-fibre product diagram, expressed through the chapter's owner predicate
`Bicategory.IsFinal`. -/
theorem two_fibre_product_diagonal_isTwoFibreProduct
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    Bicategory.IsFinal (two_fibre_product_diagonal_square F G H) := by
  sorry

/-- Lemma 4.31.13, restated as the canonical `IsFinal` instance on the public square
`two_fibre_product_diagonal_square F G H`. -/
noncomputable instance
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    Bicategory.IsFinal (two_fibre_product_diagonal_square F G H) :=
  two_fibre_product_diagonal_isTwoFibreProduct F G H

end CategoryTheory.Limits
