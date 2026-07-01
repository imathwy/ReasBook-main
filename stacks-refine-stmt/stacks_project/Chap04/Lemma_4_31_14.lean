import Mathlib
import stacks_project.Chap04.Lemma_4_31_6
import stacks_project.Chap04.Lemma_4_31_11
import stacks_project.Chap04.Lemma_4_31_13

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

namespace CategoryTheory.Limits

universe v u

noncomputable section

variable {U : Type (max u v)} [Category.{v} U]
variable {X : Type (max u v)} [Category.{v} X]
variable {V : Type (max u v)} [Category.{v} V]
variable {Y : Type (max u v)} [Category.{v} Y]

/- Domain-style sampling for Lemma 4.31.14:
- primary domain: bicategorical `2`-fibre products in `Cat`, now kept at the source-facing level
  of an arbitrary square `P : CatCommSqOver F G U` over `F : X ⥤ Y` and `G : V ⥤ Y`;
- sampled owner abstractions in this chapter/project:
  `CatCommSqOver`,
  `CatCommSqOver.toBicategoricalSquare`,
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`,
  the specialized comparison-equivalence instance from Lemma `4.31.11` for the
  `G₁ × G₂` / `Δ_S` model,
  and `categorical_pullback_diagonal`;
- best owner abstraction: the source-facing input is `P` together with
  `[Bicategory.IsFinal P.toBicategoricalSquare]`; the standard pullback model
  `U = X ×[Y] V` is only a bridge specialization, and the conversion from a categorical square to
  the chapter bicategorical owner is now reused directly from the `CatCommSqOver` owner layer;
- primitive data here: the original square `P`, the induced right-vertical functor on the
  self-pullback over `P.snd`, and the resulting `2`-commutative square with bottom map
  `Δ_F : X ⥤ X ×[Y] X`;
- derived API here: finality of that induced square; any comparison-equivalence statement to the
  categorical pullback model is obtained by direct reuse of
  `CatCommSqOver.toFunctorToCategoricalPullback` together with the generic owner-level bridge from
  Lemma `4.31.11`, rather than by a second local wrapper; the canonical model `U = X ×[Y] V` is
  accessed by specializing the same statements to the canonical square.

Source/core/bridge triage:
- `source-facing`: the induced square attached to an arbitrary `2`-fibre product square `P`;
- `core/canonical`: `Bicategory.IsFinal` of that induced square;
- `bridge/view`: the categorical-pullback comparison functor; the pullback model is obtained by
  taking `P` to be the canonical square on `X ×[Y] V`, not by introducing a second public owner. -/

variable {F : X ⥤ Y} {G : V ⥤ Y}

/-- For a square `U ⥤ V`, `U ⥤ X`, `V ⥤ Y`, `X ⥤ Y`, the left leg `U ⥤ X` induces the right
vertical functor `U ×[V] U ⥤ X ×[Y] X`. -/
abbrev two_fibre_product_left_leg_right_vertical
    (P : CatCommSqOver F G U) :
    P.snd ⊡ P.snd ⥤ F ⊡ F :=
  two_fibre_product_map P.iso P.iso.symm

/- The first projected component of the induced square is the identity on the left leg `U ⥤ X`. -/
private abbrev left_leg_diagonal_square_first_iso
    (P : CatCommSqOver F G U) :
    Δₚ P.snd ⋙
        two_fibre_product_left_leg_right_vertical P ⋙
        π₁ F F ≅
      P.fst ⋙ Δₚ F ⋙ π₁ F F :=
  Iso.refl _

/- The second projected component of the same square is also the identity on `U ⥤ X`. -/
private abbrev left_leg_diagonal_square_second_iso
    (P : CatCommSqOver F G U) :
    Δₚ P.snd ⋙
        two_fibre_product_left_leg_right_vertical P ⋙
        π₂ F F ≅
      P.fst ⋙ Δₚ F ⋙ π₂ F F :=
  Iso.refl _

/- Coherence of the projected isomorphisms for the diagonal square attached to the left leg of
`P`. After projecting to `Y`, both sides reduce to the structural `2`-commutativity of `P`. -/
private theorem left_leg_diagonal_square_coherence
    (P : CatCommSqOver F G U) :
    Functor.whiskerRight
        (left_leg_diagonal_square_first_iso P).hom F ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          (P.fst ⋙ Δₚ F)
          (CatCommSq.iso (π₁ F F) (π₂ F F) F F).hom ≫
        (Functor.associator _ _ _).inv =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          (Δₚ P.snd ⋙
            two_fibre_product_left_leg_right_vertical P)
          (CatCommSq.iso (π₁ F F) (π₂ F F) F F).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (left_leg_diagonal_square_second_iso P).hom F := sorry

/- The square
`U ⥤ U ×[V] U`, `U ⥤ X`, `U ×[V] U ⥤ X ×[Y] X`, `X ⥤ X ×[Y] X`
induced by the left leg of `P` is `2`-commutative. -/
private abbrev two_fibre_product_left_leg_diagonal_iso
    (P : CatCommSqOver F G U) :
    Δₚ P.snd ⋙
        two_fibre_product_left_leg_right_vertical P ≅
      P.fst ⋙ Δₚ F :=
  mkNatIso
    (left_leg_diagonal_square_first_iso P)
    (left_leg_diagonal_square_second_iso P)
    (left_leg_diagonal_square_coherence P)

/- The diagonal square over the cospan
`U ×[V] U ⥤ X ×[Y] X ← X`
attached to the left leg of `P`. -/
private abbrev two_fibre_product_left_leg_diagonal_square_over
    (P : CatCommSqOver F G U) :
    CatCommSqOver
      (two_fibre_product_left_leg_right_vertical P)
      (Δₚ F)
      U :=
  { fst := Δₚ P.snd
    snd := P.fst
    iso := two_fibre_product_left_leg_diagonal_iso P }

/-- For a square `U ⥤ V`, `U ⥤ X`, `V ⥤ Y`, `X ⥤ Y`, the induced square
`U ⥤ U ×[V] U`, `U ⥤ X`, `U ×[V] U ⥤ X ×[Y] X`, `X ⥤ X ×[Y] X`
viewed as the chapter's bicategorical square in `Cat`. -/
abbrev two_fibre_product_left_leg_diagonal_square
    (P : CatCommSqOver F G U) :
    BicategoricalTwoCommutativeSquare
      (two_fibre_product_left_leg_right_vertical P).toCatHom
      (Δₚ F).toCatHom :=
  (two_fibre_product_left_leg_diagonal_square_over P).toBicategoricalSquare

/-- Lemma 4.31.14: if `P` is a `2`-fibre product square over `F : X ⥤ Y` and `G : V ⥤ Y`, then
the induced square
`U ⥤ U ×[V] U`, `U ⥤ X`, `U ×[V] U ⥤ X ×[Y] X`, `X ⥤ X ×[Y] X`
is again a `2`-fibre product square. This is the source-facing main entry. -/
theorem two_fibre_product_left_leg_diagonal_isTwoFibreProduct
    (P : CatCommSqOver F G U)
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    Bicategory.IsFinal (two_fibre_product_left_leg_diagonal_square P) := sorry

/-- Lemma 4.31.14, restated as the canonical `IsFinal` instance on the induced square. -/
noncomputable instance
    (P : CatCommSqOver F G U)
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    Bicategory.IsFinal (two_fibre_product_left_leg_diagonal_square P) :=
  two_fibre_product_left_leg_diagonal_isTwoFibreProduct P

end

end CategoryTheory.Limits
