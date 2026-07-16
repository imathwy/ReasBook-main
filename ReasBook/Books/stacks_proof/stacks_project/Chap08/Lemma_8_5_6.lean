import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Internal.Chap08.StackInGroupoidsTwoFibreProductSquare
import stacks_proof.stacks_project.Chap04.Lemma_4_35_7
import stacks_proof.stacks_project.Chap08.Definition_8_5_5
import stacks_proof.stacks_project.Chap08.Lemma_8_4_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

namespace CategoryTheory

/-
Domain-style sampling for Lemma 8.5.6:
- primary domain: stacks in groupoids over a site and their bicategorical `2`-fibre products;
- inspected owner-level declarations:
  `FibredInGroupoidsOver.twoFibreProduct`,
  `FibredInGroupoidsOver.twoFibreProductSquare`,
  `StackInGroupoidsOver`,
  `stackTwoFibreProduct_isStack`,
  `CategoryOver.explicitTwoFibreProduct_isTwoFibreProduct`;
- best owner abstraction: the pullback object is owned upstream by
  `FibredInGroupoidsOver.twoFibreProduct F G`; this file should add only the owner-level
  rebundling `StackInGroupoidsOver.twoFibreProduct F G`, with the comparison square stated in the
  stack bicategory and its legs reused directly from the ambient owner projections;
- primitive data: the fibred-in-groupoids `2`-fibre product and its canonical projections;
- derived API: the owner-level bundled view `StackInGroupoidsOver.twoFibreProduct` and the
  resulting based-functor square.

Source/core/bridge triage:
- `source-facing`: `StackInGroupoidsOver.twoFibreProductSquare` and
  `StackInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`;
- `core/canonical`: `FibredInGroupoidsOver.twoFibreProduct F G`,
  `FibredInGroupoidsOver.twoFibreProductSquare F G`, and
  `CategoryOver.explicitTwoFibreProduct_isTwoFibreProduct`;
- `bridge/view`: the rebundled stack owner `StackInGroupoidsOver.twoFibreProduct F G`. -/

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y S : StackInGroupoidsOver J}
variable (F : X ⟶ S) (G : Y ⟶ S)

namespace StackInGroupoidsOver

/-- Helper for Chap08 Lemma 8 5 6: the explicit fibred `2`-fibre product of two stack
morphisms is again a stack on the site. -/
private theorem twoFibreProductProjection_isStackOnSite
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsStackOnSite J
      (FibredCategoryOver.twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p := by
  -- Rebundle the stack morphisms as morphisms in `StackOver J`, where the stack-stability
  -- theorem for fibred-category pullbacks applies directly.
  let Fₛ : X.toStackOver ⟶ S.toStackOver :=
    InducedCategory.Hom.ofFibredCategoryMor F.toFibredCategoryMor
  let Gₛ : Y.toStackOver ⟶ S.toStackOver :=
    InducedCategory.Hom.ofFibredCategoryMor G.toFibredCategoryMor
  change IsStackOnSite J
    (FibredCategoryOver.twoFibreProduct
      (InducedCategory.Hom.toFibredCategoryMor Fₛ)
      (InducedCategory.Hom.toFibredCategoryMor Gₛ)).p
  exact stackTwoFibreProduct_isStack Fₛ Gₛ

/-- The canonical `2`-fibre product of stacks in groupoids over `(C, J)`, obtained by bundling
the chapter-level owner `FibredInGroupoidsOver.twoFibreProduct` as an object of the full
sub-`2`-category `StackInGroupoidsOver J`. -/
noncomputable abbrev twoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    StackInGroupoidsOver J :=
  ⟨FibredInGroupoidsOver.twoFibreProduct F.toHom G.toHom,
    twoFibreProductProjection_isStackOnSite F G⟩

/- The canonical `2`-commutative square in the bicategory of stacks in groupoids over `(C, J)`,
formed by restricting the chapter-level pullback owner of the stack morphisms `F` and `G`. -/
noncomputable abbrev twoFibreProductSquare
    (F : X ⟶ S) (G : Y ⟶ S) :
    BicategoricalTwoCommutativeSquare F G :=
  let T := twoFibreProduct F G
  let p : T ⟶ X :=
    StackInGroupoidsOver.ofAmbientHom
      (FibredInGroupoidsOver.twoFibreProductLeftProjection F.toHom G.toHom)
  let q : T ⟶ Y :=
    StackInGroupoidsOver.ofAmbientHom
      (FibredInGroupoidsOver.twoFibreProductRightProjection F.toHom G.toHom)
  { obj := T
    p := p
    q := q
    ψ := StackInGroupoidsOver.Hom.ofAmbientHomIso
      (FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom).ψ }

/-- Helper for Chap08 Lemma 8 5 6: forget a square of stacks in groupoids to the ambient square
of categories fibred in groupoids. -/
private noncomputable abbrev toAmbientSquare
    {F : X ⟶ S} {G : Y ⟶ S}
    (P : BicategoricalTwoCommutativeSquare F G) :
    BicategoricalTwoCommutativeSquare F.toHom G.toHom where
  obj := P.obj.obj
  p := P.p.toHom
  q := P.q.toHom
  ψ :=
    Functor.mapIso (((stackInGroupoidsOverSubTwoCategory J).hom P.obj S).inclusion) P.ψ

/-- Helper for Chap08 Lemma 8 5 6: forget a morphism into the stack pullback square to the
ambient fibred-in-groupoids square. -/
private noncomputable abbrev toAmbientSquareHom
    {F : X ⟶ S} {G : Y ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    (u : P ⟶ twoFibreProductSquare F G) :
    toAmbientSquare (J := J) P ⟶
      FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom where
  hom := u.hom.toHom
  left := u.left.hom.hom
  right := u.right.hom.hom
  comm := by
    -- Forget the stack wrappers; the remaining equation is exactly the ambient square condition.
    exact congrArg (fun η ↦ η.hom.hom) u.comm

/-- Helper for Chap08 Lemma 8 5 6: rewrap an ambient square morphism into the stack pullback
square. -/
private noncomputable abbrev ofAmbientSquareHom
    {F : X ⟶ S} {G : Y ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    (u : toAmbientSquare (J := J) P ⟶
      FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom) :
    P ⟶ twoFibreProductSquare F G := by
  rcases u with ⟨hom, left, right, comm⟩
  refine
    { hom := StackInGroupoidsOver.ofAmbientHom hom
      left := ⟨ObjectProperty.homMk left, trivial⟩
      right := ⟨ObjectProperty.homMk right, trivial⟩
      comm := ?_ }
  -- Rebuild the owner square equation by stripping the stack and object-property wrappers.
  unfold_projs
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  exact comm

/-- Helper for Chap08 Lemma 8 5 6: forget a `2`-morphism between stack-square maps to the
ambient fibred-in-groupoids square. -/
private noncomputable abbrev toAmbientSquareTwoHom
    {F : X ⟶ S} {G : Y ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    {u v : P ⟶ twoFibreProductSquare F G}
    (η : u ⟶ v) :
    toAmbientSquareHom (J := J) u ⟶ toAmbientSquareHom (J := J) v where
  hom := η.hom.hom.hom
  left_comm := by
    -- Forget the stack-owner `2`-cell compatibility to its ambient left-leg equation.
    exact congrArg (fun α ↦ α.hom.hom) η.left_comm
  right_comm := by
    -- The right leg is transported through the same wrapper-forgetting map.
    exact congrArg (fun α ↦ α.hom.hom) η.right_comm

/-- Helper for Chap08 Lemma 8 5 6: lift an ambient `2`-morphism into the stack pullback square
back to a `2`-morphism of stack-square maps. -/
private noncomputable def ownerTwoHomOfAmbientSquareTwoHom
    {F : X ⟶ S} {G : Y ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    {u : P ⟶ twoFibreProductSquare F G}
    {v : toAmbientSquare (J := J) P ⟶
      FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom}
    (η : toAmbientSquareHom (J := J) u ⟶ v) :
    u ⟶ ofAmbientSquareHom (J := J) v := by
  refine
    { hom := ⟨ObjectProperty.homMk η.hom, trivial⟩
      left_comm := ?_
      right_comm := ?_ }
  · -- Strip both stack-wrapper layers until only the ambient left compatibility remains.
    unfold_projs
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    exact η.left_comm
  · -- The right compatibility is recovered by the identical ambient extensionality step.
    unfold_projs
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    exact η.right_comm

/-- Helper for Chap08 Lemma 8 5 6: the stack-level pullback square is final because the ambient
fibred-in-groupoids square is final. -/
private theorem square_isTwoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.IsFinal (twoFibreProductSquare F G) := by
  -- For each competing stack square, transport the ambient terminal morphism into the owner
  -- square and prove uniqueness after forgetting back to the ambient hom-category.
  refine ⟨?_⟩
  intro P
  let Q : BicategoricalTwoCommutativeSquare F.toHom G.toHom :=
    FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom
  letI : Bicategory.IsFinal Q :=
    FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct F.toHom G.toHom
  let targetAmbient : toAmbientSquare (J := J) P ⟶ Q := ⊤_ _
  let targetOwner : P ⟶ twoFibreProductSquare F G :=
    ofAmbientSquareHom (J := J) targetAmbient
  let htarget : Limits.IsTerminal targetAmbient := Limits.terminalIsTerminal
  exact
    ((Limits.IsTerminal.ofUniqueHom (Y := targetOwner)
      (fun u ↦ ownerTwoHomOfAmbientSquareTwoHom
        (J := J) (Limits.terminal.from (toAmbientSquareHom (J := J) u)))
      (fun u η ↦ by
        -- Equality of stack `2`-morphisms is detected after forgetting to the ambient square,
        -- where terminality gives uniqueness.
        apply BicategoricalTwoCommutativeSquare.TwoHom.ext
        repeat first | apply InducedWideCategory.Hom.ext | apply InducedCategory.Hom.ext
        exact congrArg (fun ζ ↦ ζ.hom.hom.hom.hom.hom)
          (htarget.hom_ext
            (toAmbientSquareTwoHom (J := J) η)
            (Limits.terminal.from (toAmbientSquareHom (J := J) u)))))).hasTerminal

/-- Chap08 Lemma 8 5 6: the canonical square `twoFibreProductSquare F G` is a bicategorical
`2`-fibre product in the bicategory of stacks in groupoids over `(C, J)`. -/
theorem twoFibreProduct_isTwoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.IsFinal (twoFibreProductSquare F G) := by
  -- The public theorem is the generic terminality transport specialized to the canonical
  -- stack-level pullback square.
  exact square_isTwoFibreProduct F G

end StackInGroupoidsOver

/- Lemma 8.5.6 reuses the ambient explicit `2`-fibre-product theorem from Categories,
Lemma `4.32.3`, already formalized as `CategoryOver.explicitTwoFibreProduct_isTwoFibreProduct`. -/
recall CategoryOver.explicitTwoFibreProduct_isTwoFibreProduct

end

end CategoryTheory
