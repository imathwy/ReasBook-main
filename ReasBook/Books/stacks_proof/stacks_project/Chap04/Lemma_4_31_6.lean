import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {X : Type u₁} [Category.{v₁} X]
variable {Y : Type u₂} [Category.{v₂} Y]
variable {Z : Type u₃} [Category.{v₃} Z]
variable {A : Type u₄} [Category.{v₄} A]
variable {B : Type u₅} [Category.{v₅} B]
variable {C : Type u₆} [Category.{v₆} C]

/- Domain-style sampling for Lemma 4.31.6:
- primary domain: categorical pullbacks and their functoriality with respect to
  `2`-commutative cospan maps;
- sampled owner-level declarations:
  `CategoricalPullback.toCatCommSqOver`,
  `Limits.CatCospanTransform`,
  `CategoricalPullback.catCommSq`,
  `CategoricalPullback.CatCommSqOver.transform`,
  `CategoricalPullback.functorEquiv`,
  `CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback`;
- best owner abstraction: the primitive source data are a
  `Limits.CatCospanTransform H I F G`; applying `CatCommSqOver.transform` to the canonical source
  square `CategoricalPullback.catCommSq H I` produces the derived square in
  `CatCommSqOver F G (H ⊡ I)`;
- primitive data: the three component functors together with the two comparison squares, and the
  canonical source square over `H` and `I`;
- derived API: the transformed square over `F` and `G`, and then the induced functor between the
  categorical pullbacks of the source and target cospans through the owner equivalence
  `CategoricalPullback.functorEquiv`.

Source/core/bridge triage:
- `source-facing`: the textbook functor determined by isomorphisms
  `α : K ⋙ G ≅ I ⋙ M` and `β : H ⋙ M ≅ L ⋙ F`;
- `core/canonical`: `Limits.CatCospanTransform H I F G`;
- `bridge/view`: the induced square on pullback categories obtained by
  `CatCommSqOver.transform`, followed by the comparison functor
  `CatCommSqOver.toFunctorToCategoricalPullback`; the chapter's bicategorical square owner is a
  later companion view. -/

section

variable {H : X ⥤ Z} {I : Y ⥤ Z} {L : X ⥤ A} {K : Y ⥤ B}
variable {M : Z ⥤ C} {F : A ⥤ C} {G : B ⥤ C}

/- Primitive owner data for the induced map of categorical pullbacks are exactly the comparison
isomorphisms `α`, `β`, assembled directly into a `CatCospanTransform H I F G`. The public functor
`two_fibre_product_map` is then the canonical bridge obtained by transforming the canonical source
square in `CatCommSqOver H I (H ⊡ I)` and applying `toFunctorToCategoricalPullback`. -/

private abbrev two_fibre_product_cospanTransform
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F) :
    CatCospanTransform H I F G :=
  { left := L
    base := M
    right := K
    squareLeft := ⟨β⟩
    squareRight := ⟨α.symm⟩ }

private abbrev two_fibre_product_sourceSquare :
    CatCommSqOver H I (H ⊡ I) :=
  (toCatCommSqOver H I (H ⊡ I)).obj (𝟭 (H ⊡ I))

private abbrev two_fibre_product_targetSquare
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F) :
    CatCommSqOver F G (H ⊡ I) :=
  ((transform (H ⊡ I)).obj (two_fibre_product_cospanTransform α β)).obj
    two_fibre_product_sourceSquare

/-- Lemma 4.31.6: a `2`-commutative diagram with chosen isomorphisms
`α : K ⋙ G ≅ I ⋙ M` and `β : H ⋙ M ≅ L ⋙ F` induces a canonical functor
`X ×[Z] Y ⥤ A ×[C] B`. -/
@[stacks 02XA]
abbrev two_fibre_product_map
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F) :
    H ⊡ I ⥤ F ⊡ G :=
  (toFunctorToCategoricalPullback F G (H ⊡ I)).obj (two_fibre_product_targetSquare α β)

/-- The canonical `2`-fibre product map is obtained by applying the pullback comparison functor to
the transformed square determined by `α` and `β`. -/
theorem two_fibre_product_map_def
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F) :
    two_fibre_product_map α β =
      (toFunctorToCategoricalPullback F G (H ⊡ I)).obj (two_fibre_product_targetSquare α β) :=
  rfl

@[simp] theorem two_fibre_product_map_obj_fst
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F) (P : H ⊡ I) :
    ((two_fibre_product_map α β).obj P).fst = L.obj P.fst :=
  rfl

@[simp] theorem two_fibre_product_map_obj_snd
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F) (P : H ⊡ I) :
    ((two_fibre_product_map α β).obj P).snd = K.obj P.snd :=
  rfl

@[simp] theorem two_fibre_product_map_obj_iso_hom
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F) (P : H ⊡ I) :
    ((two_fibre_product_map α β).obj P).iso.hom =
      β.inv.app P.fst ≫ M.map P.iso.hom ≫ α.inv.app P.snd :=
  by
    cases α
    cases β
    simp [two_fibre_product_map, two_fibre_product_targetSquare,
      two_fibre_product_cospanTransform, CatCommSq.iso]

@[simp] theorem two_fibre_product_map_map_fst
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F)
    {P Q : H ⊡ I} (f : P ⟶ Q) :
    ((two_fibre_product_map α β).map f).fst = L.map f.fst :=
  rfl

@[simp] theorem two_fibre_product_map_map_snd
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F)
    {P Q : H ⊡ I} (f : P ⟶ Q) :
    ((two_fibre_product_map α β).map f).snd = K.map f.snd :=
  rfl

end

end CategoryTheory
