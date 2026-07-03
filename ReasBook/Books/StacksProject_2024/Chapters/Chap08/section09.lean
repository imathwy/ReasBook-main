import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_8_9_1 (from Chap08) -/
universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X : FibredInGroupoidsOver C}
variable {Y : StackInGroupoidsOver J}

/- Domain-style sampling for Lemma 8.9.1:
- primary domain: stackification of categories fibred in groupoids, specialized from the Chapter 8
  stackification theory for fibred categories;
- inspected owner-level declarations:
  `FibredCategoryMor.IsStackification`,
  `exists_stackification`,
  `stackification_unique_up_to_unique_twoIso`,
  `StackInGroupoidsOver.Hom.IsEquivalenceOverBase`;
- best owner abstraction: the stackification predicate should stay on the ambient owner
  `FibredCategoryMor.IsStackification` after passing from a morphism of fibred-in-groupoids to the
  canonical bridge `toStackFibredCategoryMor`; comparison morphisms between stackifications should
  reuse the owner hom type `Y₁ ⟶ Y₂`;
- primitive data: a target `Y : StackInGroupoidsOver J`, a morphism `G : FibredInGroupoidsMor X Y`,
  and the ambient stackification predicate on `G.toStackFibredCategoryMor`;
- derived API: the comparison equivalence-over-base predicate on owner homs in
  `StackInGroupoidsOver J` and the compatible comparison `2`-isomorphism inherited from the
  ambient stackification uniqueness theorem.

Source/core/bridge triage:
- `source-facing`: the existence and uniqueness statements for stackifications in groupoids;
- `core/canonical`: `FibredCategoryMor.IsStackification`, `exists_stackification`,
  `stackification_unique_up_to_unique_twoIso`, and
  `StackInGroupoidsOver.Hom.IsEquivalenceOverBase`;
- `bridge/view`: the canonical bridge `FibredInGroupoidsMor.toStackFibredCategoryMor` from the
  groupoid-specialized morphism to the ambient owner predicate. -/

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

variable (X : FibredInGroupoidsOver C)

-- Proof sketch: apply the generic stackification result of Lemma `8.8.1` to the underlying
-- fibred category of `X`, then use Lemma `8.5.2` to see that the resulting stack is again fibred
-- in groupoids. Since both source and target are now bundled in the groupoid-specific APIs, the
-- stackification morphism is canonically a `FibredInGroupoidsMor`.
/-- Lemma 8.9.1 (1): a category fibred in groupoids over a site admits a stackification by a
stack in groupoids, with the induced morphism presheaf maps identifying the target with the
sheafification of the source and with local essential surjectivity on objects in each fiber. -/
theorem exists_stackInGroupoids_stackification :
    ∃ Y : StackInGroupoidsOver J,
      ∃ G : FibredInGroupoidsMor X Y,
        FibredCategoryMor.IsStackification G.toStackFibredCategoryMor := sorry

-- Proof sketch: forget the two stackifications in groupoids to stackifications in the sense of
-- Lemma `8.8.1`, apply `stackification_unique_up_to_unique_twoIso` there, and lift the ambient
-- comparison back to the owner hom between stacks in groupoids.
/-- Lemma 8.9.1 (2): a stackification of a category fibred in groupoids by a stack in groupoids is
determined up to equivalence over the base together with compatible comparison `2`-isomorphism.
The raw type of compatible comparison isomorphisms for one fixed comparison morphism is not a
subsingleton in general; the unique-`2`-isomorphism clause is the comparison-pair uniqueness
recorded by the ambient stack theorem. -/
theorem stackInGroupoids_stackification_unique_up_to_unique_twoIso
    {Y₁ Y₂ : StackInGroupoidsOver J}
    (G₁ : FibredInGroupoidsMor X Y₁)
    (G₂ : FibredInGroupoidsMor X Y₂)
    (hG₁ : FibredCategoryMor.IsStackification G₁.toStackFibredCategoryMor)
    (hG₂ : FibredCategoryMor.IsStackification G₂.toStackFibredCategoryMor) :
    ∃ H : Y₁ ⟶ Y₂,
      StackInGroupoidsOver.Hom.IsEquivalenceOverBase H ∧
        let GH : FibredInGroupoidsMor X Y₂ :=
          G₁ ≫ StackInGroupoidsOver.Hom.toFibredInGroupoidsMor H
        Nonempty (GH ≅ G₂) := sorry

end

end CategoryTheory

/-! ### Lemma_8_9_2 (from Chap08) -/
universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredInGroupoidsOver C}
variable {S' X : StackInGroupoidsOver J}

/- Domain-style sampling for Lemma 8.9.2:
- primary domain: the universal property of stackification, specialized from stacks to stacks in
  groupoids;
- inspected owner-level declarations:
  `FibredCategoryMor.IsStackification`,
  `isStackification_exists_lift_to_stack`,
  `FibredInGroupoidsMor.ofAmbientHom`,
  `StackInGroupoidsOver.Hom.toFibredInGroupoidsMor`,
  `FibredInGroupoidsMor.toStackFibredCategoryMor`,
  `FibredInGroupoidsMor.ofFibredCategoryMorIso`.
- best owner abstraction: the ambient stackification owner is still
  `FibredCategoryMor.IsStackification`, and the present lemma should be only the groupoid-valued
  bridge that reuses `isStackification_exists_lift_to_stack` and returns the lifted morphism in
  the owner hom type `S' ⟶ X`;
- primitive data: a stackification morphism `G : S ⟶ S'`, the ambient stackification predicate on
  `G.toStackFibredCategoryMor`, and a target morphism `F : FibredInGroupoidsMor S X`;
- derived API: the lifted owner morphism `H : S' ⟶ X` and the resulting `2`-isomorphism at the
  underlying `FibredInGroupoidsMor` layer.

Source/core/bridge triage:
- `source-facing`: the groupoid-valued factorization statement of Lemma 8.9.2;
- `core/canonical`: `isStackification_exists_lift_to_stack`;
- `bridge/view`: the coercions from stacks in groupoids to stacks, together with the owner bridge
  `FibredInGroupoidsMor.toStackFibredCategoryMor` to the ambient stack theorem,
  `FibredInGroupoidsMor.ofAmbientHom` that packages the ambient lifted morphism as an owner hom,
  and
  `FibredInGroupoidsMor.ofFibredCategoryMorIso` that lifts ambient `2`-isomorphisms back to the
  groupoid-valued homs. -/

-- Proof sketch: apply Lemma `8.8.2` to the underlying stackification
-- `G.toStackFibredCategoryMor` and target morphism `F.toStackFibredCategoryMor`.
-- The resulting ambient lift is then promoted by `FibredInGroupoidsMor.ofAmbientHom` to the
-- owner morphism `S' ⟶ X`, and the ambient
-- `2`-isomorphism is lifted back with `FibredInGroupoidsMor.ofFibredCategoryMorIso`.
/-- Lemma 8.9.2: if `G : S ⟶ S'` exhibits the stack in groupoids `S'` as a stackification of the
category fibred in groupoids `S`, then every morphism `F : S ⟶ X` to a stack in groupoids `X`
factors through `S'` up to a `2`-isomorphism. -/
theorem isStackification_exists_lift_to_stackInGroupoids
    (G : FibredInGroupoidsMor S S')
    (hG : FibredCategoryMor.IsStackification G.toStackFibredCategoryMor)
    (F : FibredInGroupoidsMor S X) :
    ∃ H : S' ⟶ X,
      Nonempty (G ≫ H ≅ F) := by
  obtain ⟨H, hH⟩ :=
    isStackification_exists_lift_to_stack
      G.toStackFibredCategoryMor hG F.toStackFibredCategoryMor
  let H' : S' ⟶ X :=
    ⟨⟨FibredInGroupoidsMor.ofAmbientHom H.toHom, trivial⟩⟩
  refine ⟨H', ?_⟩
  rcases hH with ⟨e⟩
  exact ⟨FibredInGroupoidsMor.ofFibredCategoryMorIso (by simpa [H'] using e)⟩

end

end CategoryTheory

/-! ### Lemma_8_9_3 (from Chap08) -/
universe u v

namespace CategoryTheory

open StackInGroupoidsOver.Hom

/- Domain-style sampling for Lemma 8.9.3:
- primary domain: stackifications of `2`-fibre products in the stack-in-groupoids specialization
  of Chapter 8;
- inspected owner-level declarations:
  `FibredInGroupoidsOver.twoFibreProduct`,
  `StackInGroupoidsOver.twoFibreProduct`,
  `FibredCategoryMor.IsStackification`,
  `CategoryTheory.twoFibreProduct_of_stackifications_isStackification`;
- best owner abstraction: the numbered item should live at the groupoid-specialized source-facing
  layer, with the pullback objects owned by `FibredInGroupoidsOver.twoFibreProduct` on the source
  side and `StackInGroupoidsOver.twoFibreProduct` on the stack side, while the ambient fibred-
  category theorem is reused only as the proof engine;
- primitive data: the source morphisms in `FibredInGroupoidsMor`, the three stackification
  morphisms into stacks in groupoids, the lifted morphisms in `StackInGroupoidsOver`, and the
  comparison `2`-isomorphisms;
- derived API: the ambient fibred-category stackification theorem and the groupoid bridge
  `FibredInGroupoidsMor.toStackFibredCategoryMor`.

Source/core/bridge triage:
- `source-facing`: the groupoid-specialized stackification statement for `2`-fibre products;
- `core/canonical`: `CategoryTheory.twoFibreProduct_of_stackifications_isStackification`;
- `bridge/view`: the coercions from stacks in groupoids to stacks and from
  `FibredInGroupoidsMor` to the ambient owner predicate via
  `FibredInGroupoidsMor.toStackFibredCategoryMor`. -/

namespace FibredInGroupoidsMor

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y Z : FibredInGroupoidsOver C}
variable {X' Y' Z' : StackInGroupoidsOver J}

private def toStackAmbientIso
    {A : FibredInGroupoidsOver C}
    {S : StackInGroupoidsOver J}
    {u v : FibredInGroupoidsMor A S.toFibredInGroupoidsOver}
    (e : u ≅ v) :
    (show FibredCategoryMor (A : FibredCategoryOver C) (S : StackOver J) from u) ≅
      (show FibredCategoryMor (A : FibredCategoryOver C) (S : StackOver J) from v) := by
  simpa using
    Functor.mapIso
      (((fibredInGroupoidsOverSubTwoCategory C).hom A S.toFibredInGroupoidsOver).inclusion)
      e

/- The canonical comparison morphism from the `2`-fibre product of `f` and `g` to the
`2`-fibre product of the compatible lifted morphisms `f'` and `g'`. This is the groupoid-valued
bridge to the ambient fibred-category comparison morphism. -/
noncomputable abbrev twoFibreProductOfStackificationsHom
    (f : FibredInGroupoidsMor X Y)
    (g : FibredInGroupoidsMor Z Y)
    (i : FibredInGroupoidsMor X X')
    (j : FibredInGroupoidsMor Y Y')
    (k : FibredInGroupoidsMor Z Z')
    (f' : X' ⟶ Y')
    (g' : Z' ⟶ Y')
    (α : i ≫ f' ≅ f ≫ j)
    (β : k ≫ g' ≅ g ≫ j) :
    FibredInGroupoidsMor
      (FibredInGroupoidsOver.twoFibreProduct f g)
      (StackInGroupoidsOver.twoFibreProduct f' g') := by
  let αF :
      i.toStackFibredCategoryMor ≫ f'.toFibredCategoryMor ≅
        (show FibredCategoryMor (X : FibredCategoryOver C) (Y' : StackOver J) from f ≫ j) := by
    simpa [FibredInGroupoidsMor.toStackFibredCategoryMor] using toStackAmbientIso α
  let βF :
      k.toStackFibredCategoryMor ≫ g'.toFibredCategoryMor ≅
        (show FibredCategoryMor (Z : FibredCategoryOver C) (Y' : StackOver J) from g ≫ j) := by
    simpa [FibredInGroupoidsMor.toStackFibredCategoryMor] using toStackAmbientIso β
  let fS : (X' : StackOver J) ⟶ (Y' : StackOver J) :=
    InducedCategory.Hom.ofFibredCategoryMor f'.toFibredCategoryMor
  let gS : (Z' : StackOver J) ⟶ (Y' : StackOver J) :=
    InducedCategory.Hom.ofFibredCategoryMor g'.toFibredCategoryMor
  exact FibredInGroupoidsMor.ofAmbientHom <|
    CategoryTheory.twoFibreProductOfStackificationsHom
      f g i.toStackFibredCategoryMor j.toStackFibredCategoryMor k.toStackFibredCategoryMor
      fS gS αF βF

/- Lemma 8.9.3: the canonical comparison morphism from the `2`-fibre product of morphisms of
categories fibred in groupoids to the `2`-fibre product of compatible stackifications in
groupoids is itself a stackification. This is the source-facing groupoid specialization of the
ambient fibred-category theorem `twoFibreProduct_of_stackifications_isStackification`. -/
theorem twoFibreProduct_of_stackifications_isStackification
    (f : FibredInGroupoidsMor X Y)
    (g : FibredInGroupoidsMor Z Y)
    (i : FibredInGroupoidsMor X X')
    (j : FibredInGroupoidsMor Y Y')
    (k : FibredInGroupoidsMor Z Z')
    (f' : X' ⟶ Y')
    (g' : Z' ⟶ Y')
    (α : i ≫ f' ≅ f ≫ j)
    (β : k ≫ g' ≅ g ≫ j)
    (hi : FibredCategoryMor.IsStackification i.toStackFibredCategoryMor)
    (hj : FibredCategoryMor.IsStackification j.toStackFibredCategoryMor)
    (hk : FibredCategoryMor.IsStackification k.toStackFibredCategoryMor) :
    FibredCategoryMor.IsStackification
      (twoFibreProductOfStackificationsHom f g i j k f' g' α β).toStackFibredCategoryMor := by
  let αF :
      i.toStackFibredCategoryMor ≫ f'.toFibredCategoryMor ≅
        (show FibredCategoryMor (X : FibredCategoryOver C) (Y' : StackOver J) from f ≫ j) := by
    simpa [FibredInGroupoidsMor.toStackFibredCategoryMor] using toStackAmbientIso α
  let βF :
      k.toStackFibredCategoryMor ≫ g'.toFibredCategoryMor ≅
        (show FibredCategoryMor (Z : FibredCategoryOver C) (Y' : StackOver J) from g ≫ j) := by
    simpa [FibredInGroupoidsMor.toStackFibredCategoryMor] using toStackAmbientIso β
  let fS : (X' : StackOver J) ⟶ (Y' : StackOver J) :=
    InducedCategory.Hom.ofFibredCategoryMor f'.toFibredCategoryMor
  let gS : (Z' : StackOver J) ⟶ (Y' : StackOver J) :=
    InducedCategory.Hom.ofFibredCategoryMor g'.toFibredCategoryMor
  simpa only [twoFibreProductOfStackificationsHom] using
    (CategoryTheory.twoFibreProduct_of_stackifications_isStackification
      f g i.toStackFibredCategoryMor j.toStackFibredCategoryMor k.toStackFibredCategoryMor
      fS gS αF βF hi hj hk)

end

end FibredInGroupoidsMor

end CategoryTheory
