import Mathlib
import StacksProject_2024.Internal.Chap04.FibredInSetoidsTwoFibreProduct
import StacksProject_2024.Internal.Chap08.StackInSetoidsTwoFibreProductSquare
import StacksProject_2024.Chap08.Lemma_8_5_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

namespace CategoryTheory

/-
Domain-style sampling for Lemma 8.6.6:
- primary domain: stacks in setoids over a site and their bicategorical `2`-fibre products;
- inspected owner-level declarations:
  `StackInSetoidsOver`,
  `FibredInSetoidsOver.twoFibreProduct`,
  `StackInGroupoidsOver.twoFibreProductSquare`,
  `StackInSetoidsOver.ofStackInGroupoidsSquare`,
  `Bicategory.IsFinal`;
- best owner abstraction: the source-facing square in `StackInSetoidsOver J` should be obtained by
  restricting the canonical stack-in-groupoids pullback square to the full sub-`2`-category of
  stacks in setoids, while the setoid-side primitive owner data is taken directly from the
  Chapter 4 owner `FibredInSetoidsOver.twoFibreProduct`;
- primitive data: the Chapter 4 setoid pullback owner `FibredInSetoidsOver.twoFibreProduct`
  together with the Chapter 8 ambient stack pullback square;
- derived API: the canonical square in `StackInSetoidsOver J` and the `Bicategory.IsFinal`
  statement expressing the `2`-fibre-product property.

Source/core/bridge triage:
- `source-facing`: `StackInSetoidsOver.twoFibreProduct`,
  `StackInSetoidsOver.twoFibreProductSquare`, and
  `StackInSetoidsOver.twoFibreProduct_isTwoFibreProduct`;
- `core/canonical`: `FibredInSetoidsOver.twoFibreProduct`,
  `StackInGroupoidsOver.twoFibreProductSquare`, and `Bicategory.IsFinal`;
- `bridge/view`: `StackInSetoidsOver.ofStackInGroupoidsSquare`, which restricts the ambient square
  to the full sub-`2`-category of stacks in setoids. -/

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y S : StackInSetoidsOver J}
variable (F : X ⟶ S) (G : Y ⟶ S)

namespace StackInSetoidsOver

-- Proof sketch: compare the Chapter 8 stack-in-groupoids pullback with the Chapter 4 owner
-- `FibredInSetoidsOver.twoFibreProduct`, whose projection is already fibred in setoids.
/-- The ambient stack-in-groupoids pullback of morphisms of stacks in setoids is fibred in
setoids. -/
private theorem ambientTwoFibreProduct_isFibredInSetoids
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInSetoids
      (StackInGroupoidsOver.twoFibreProduct
        (toStackInGroupoidsHom F)
        (toStackInGroupoidsHom G)).p := by
  -- Compare the ambient stack-in-groupoids pullback with the Chapter 4 pullback in
  -- `FibredInSetoidsOver`, whose projection already carries the setoid condition.
  let Fₛ : X.toFibredInSetoidsOver ⟶ S.toFibredInSetoidsOver := F
  let Gₛ : Y.toFibredInSetoidsOver ⟶ S.toFibredInSetoidsOver := G
  change IsFibredInSetoids (FibredInSetoidsOver.twoFibreProduct Fₛ Gₛ).p
  exact FibredInSetoidsOver.isFibredInSetoids_p (FibredInSetoidsOver.twoFibreProduct Fₛ Gₛ)

/-- The canonical `2`-fibre product of stacks in setoids over `(C, J)`, obtained by equipping the
Chapter 8 stack pullback owner `StackInGroupoidsOver.twoFibreProduct` with the fiberwise setoid
structure supplied by the Chapter 4 owner `FibredInSetoidsOver.twoFibreProduct`. -/
noncomputable abbrev twoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    StackInSetoidsOver J :=
  ⟨StackInGroupoidsOver.twoFibreProduct
      (toStackInGroupoidsHom F)
      (toStackInGroupoidsHom G),
    ambientTwoFibreProduct_isFibredInSetoids F G⟩

/- The ambient stack-in-groupoids pullback square, recorded with its exact owner-level type to
avoid repeated coercion and reduction work during elaboration. -/
private noncomputable abbrev ambientTwoFibreProductSquare
    (F : X ⟶ S) (G : Y ⟶ S) :
    BicategoricalTwoCommutativeSquare F.obj.obj G.obj.obj :=
  StackInGroupoidsOver.twoFibreProductSquare F.obj.obj G.obj.obj

-- Proof sketch: the apex of the canonical ambient stack-in-groupoids pullback square is the same
-- pullback owner as above, so its projection is again fibred in setoids.
/-- The apex of the canonical ambient stack-in-groupoids pullback square is fibred in setoids. -/
private theorem ambientTwoFibreProductSquare_isFibredInSetoids
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInSetoids
      (ambientTwoFibreProductSquare F G).obj.p := by
  -- The square apex is the same ambient pullback object, so reuse the previous projection proof.
  unfold ambientTwoFibreProductSquare StackInGroupoidsOver.twoFibreProductSquare
  exact ambientTwoFibreProduct_isFibredInSetoids F G

/-- The canonical `2`-commutative square in `StackInSetoidsOver J`, obtained by restricting the
canonical stack-in-groupoids pullback square to the full sub-`2`-category of stacks in setoids
through the Chapter 8 bridge `ofStackInGroupoidsSquare`. -/
noncomputable abbrev twoFibreProductSquare
    (F : X ⟶ S) (G : Y ⟶ S) :
    BicategoricalTwoCommutativeSquare F G :=
  ofStackInGroupoidsSquare (F := F) (G := G)
    (ambientTwoFibreProductSquare F G)
    (ambientTwoFibreProductSquare_isFibredInSetoids F G)

/-- Helper for Chap08 Lemma 8 6 6: forget a square of stacks in setoids to the ambient square
of stacks in groupoids. -/
private noncomputable abbrev toStackInGroupoidsSquare
    {F : X ⟶ S} {G : Y ⟶ S}
    (P : BicategoricalTwoCommutativeSquare F G) :
    BicategoricalTwoCommutativeSquare
      (toStackInGroupoidsHom F) (toStackInGroupoidsHom G) where
  obj := P.obj.toStackInGroupoidsOver
  p := toStackInGroupoidsHom P.p
  q := toStackInGroupoidsHom P.q
  ψ :=
    Functor.mapIso (((stackInSetoidsOverSubTwoCategory J).hom P.obj S).inclusion) P.ψ

/-- Helper for Chap08 Lemma 8 6 6: forget a morphism into the restricted pullback square to a
morphism into the ambient stack-in-groupoids pullback square. -/
private noncomputable abbrev toStackInGroupoidsSquareHom
    {F : X ⟶ S} {G : Y ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    (u : P ⟶ twoFibreProductSquare F G) :
    toStackInGroupoidsSquare (J := J) P ⟶ ambientTwoFibreProductSquare F G := by
  -- Forget the restricted-square wrappers; the remaining equality is the ambient equation.
  unfold twoFibreProductSquare ofStackInGroupoidsSquare at u
  exact
    { hom := toStackInGroupoidsHom u.hom
      left := u.left.hom.hom
      right := u.right.hom.hom
      comm := by
        exact congrArg (fun η ↦ η.hom.hom) u.comm }

/-- Helper for Chap08 Lemma 8 6 6: rewrap an ambient stack-in-groupoids square morphism as a
morphism into the restricted stack-in-setoids pullback square. -/
private noncomputable abbrev ofStackInGroupoidsSquareHom
    {F : X ⟶ S} {G : Y ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    (u : toStackInGroupoidsSquare (J := J) P ⟶ ambientTwoFibreProductSquare F G) :
    P ⟶ twoFibreProductSquare F G := by
  -- Rebuild the owner square map by adding the trivial full-subcategory membership proofs.
  unfold twoFibreProductSquare ofStackInGroupoidsSquare
  rcases u with ⟨hom, left, right, comm⟩
  refine
    { hom := StackInSetoidsOver.ofAmbientHom hom
      left := ⟨ObjectProperty.homMk left, trivial⟩
      right := ⟨ObjectProperty.homMk right, trivial⟩
      comm := ?_ }
  -- Strip the setoid-owner wrappers; the remaining equality is the ambient square equation.
  unfold_projs
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  exact comm

/-- Helper for Chap08 Lemma 8 6 6: forget a `2`-morphism between restricted square maps to the
corresponding ambient stack-in-groupoids `2`-morphism. -/
private noncomputable abbrev toStackInGroupoidsSquareTwoHom
    {F : X ⟶ S} {G : Y ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    {u v : P ⟶ twoFibreProductSquare F G}
    (η : u ⟶ v) :
    toStackInGroupoidsSquareHom (J := J) u ⟶
      toStackInGroupoidsSquareHom (J := J) v := by
  -- After unfolding the restricted square, each compatibility equation forgets directly.
  unfold toStackInGroupoidsSquareHom
  exact
    { hom := η.hom.hom.hom
      left_comm := by
        exact congrArg (fun α ↦ α.hom.hom) η.left_comm
      right_comm := by
        exact congrArg (fun α ↦ α.hom.hom) η.right_comm }

/-- Helper for Chap08 Lemma 8 6 6: lift an ambient stack-in-groupoids `2`-morphism back to a
`2`-morphism of restricted stack-in-setoids square maps. -/
private noncomputable def ownerTwoHomOfStackInGroupoidsSquareTwoHom
    {F : X ⟶ S} {G : Y ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    {u : P ⟶ twoFibreProductSquare F G}
    {v : toStackInGroupoidsSquare (J := J) P ⟶ ambientTwoFibreProductSquare F G}
    (η : toStackInGroupoidsSquareHom (J := J) u ⟶ v) :
    u ⟶ ofStackInGroupoidsSquareHom (J := J) v := by
  -- Add the trivial setoid-subcategory membership proof to the ambient apex `2`-cell.
  unfold toStackInGroupoidsSquareHom at η
  refine
    { hom := ⟨ObjectProperty.homMk η.hom, trivial⟩
      left_comm := ?_
      right_comm := ?_ }
  · -- Project to the ambient left-leg compatibility.
    unfold_projs
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    exact η.left_comm
  · -- The right-leg compatibility is transported through the same forgetful projection.
    unfold_projs
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    exact η.right_comm

/-- Helper for Chap08 Lemma 8 6 6: the ambient stack-in-groupoids pullback square is final. -/
private theorem ambientTwoFibreProductSquare_isFinal
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.IsFinal (ambientTwoFibreProductSquare F G) := by
  -- Normalize the local spelling of the ambient square to the owner theorem from Lemma 8.5.6.
  unfold ambientTwoFibreProductSquare
  exact
    StackInGroupoidsOver.twoFibreProduct_isTwoFibreProduct
      (toStackInGroupoidsHom F) (toStackInGroupoidsHom G)

/-- Helper for Chap08 Lemma 8 6 6: terminal uniqueness in the ambient square detects equality
of the corresponding owner `2`-morphisms after restricting to stacks in setoids. -/
private theorem ownerTerminalHom_ext
    {F : X ⟶ S} {G : Y ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    (targetAmbient :
      toStackInGroupoidsSquare (J := J) P ⟶ ambientTwoFibreProductSquare F G)
    (htarget : Limits.IsTerminal targetAmbient)
    (u : P ⟶ twoFibreProductSquare F G)
    (η : u ⟶ ofStackInGroupoidsSquareHom (J := J) targetAmbient) :
    η =
      ownerTwoHomOfStackInGroupoidsSquareTwoHom
        (J := J) (htarget.from (toStackInGroupoidsSquareHom (J := J) u)) := by
  -- Forget through the full sub-`2`-category; the ambient terminal object has a unique
  -- morphism in the resulting hom-category, and extensionality reflects that equality back.
  apply BicategoricalTwoCommutativeSquare.TwoHom.ext
  repeat first
    | apply InducedWideCategory.Hom.ext
    | apply InducedCategory.Hom.ext
  exact congrArg
    (fun ζ ↦
      ((⟨ObjectProperty.homMk ζ.hom, trivial⟩ :
          u.hom ⟶ (ofStackInGroupoidsSquareHom (J := J) targetAmbient).hom)).hom.hom.hom.hom.hom.hom.hom.hom)
    (htarget.hom_ext
      (toStackInGroupoidsSquareTwoHom (J := J) η)
      (htarget.from (toStackInGroupoidsSquareHom (J := J) u)))

/-- Helper for Chap08 Lemma 8 6 6: after forgetting a competing restricted square to the
ambient stack-in-groupoids square, the rewrapped ambient terminal morphism is terminal in the
restricted hom-category. -/
private theorem restrictedSquareHom_hasTerminal
    (F : X ⟶ S) (G : Y ⟶ S)
    (P : BicategoricalTwoCommutativeSquare F G) :
    Limits.HasTerminal (P ⟶ twoFibreProductSquare F G) := by
  -- Use ambient finality to choose the terminal comparison map after forgetting to stacks in
  -- groupoids, then reflect uniqueness back through the full sub-`2`-category.
  letI : Bicategory.IsFinal (ambientTwoFibreProductSquare F G) :=
    ambientTwoFibreProductSquare_isFinal F G
  let targetAmbient :
      toStackInGroupoidsSquare (J := J) P ⟶ ambientTwoFibreProductSquare F G := ⊤_ _
  let targetOwner : P ⟶ twoFibreProductSquare F G :=
    ofStackInGroupoidsSquareHom (J := J) targetAmbient
  let htarget : Limits.IsTerminal targetAmbient := Limits.terminalIsTerminal
  exact
    ((Limits.IsTerminal.ofUniqueHom (Y := targetOwner)
      (fun u ↦ ownerTwoHomOfStackInGroupoidsSquareTwoHom
        (J := J) (htarget.from (toStackInGroupoidsSquareHom (J := J) u)))
      (ownerTerminalHom_ext (J := J) targetAmbient htarget))).hasTerminal

/-- Helper for Chap08 Lemma 8 6 6: the restricted stack-in-setoids pullback square is final
because the ambient stack-in-groupoids pullback square is final. -/
private theorem squareHasTerminal
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.IsFinal (twoFibreProductSquare F G) := by
  -- For each competing setoid square, forget to stacks in groupoids, use ambient terminality,
  -- and rewrap the resulting terminal morphism in the full sub-`2`-category.
  refine ⟨?_⟩
  intro P
  exact restrictedSquareHom_hasTerminal F G P

-- Proof sketch: start from the canonical stack-in-groupoids pullback square, whose finality is
-- Lemma `8.5.6`, and restrict that universal property to the full sub-`2`-category of stacks in
-- setoids using the bridge `ofStackInGroupoidsSquare`.
/-- Chap08 Lemma 8 6 6: the `2`-category of stacks in setoids over the site `(C, J)` has `2`-fibre
products, and the canonical square `twoFibreProductSquare F G` is described by the same explicit
pullback model as in Categories, Lemma `4.32.3`. -/
@[stacks 0434]
theorem twoFibreProduct_isTwoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.IsFinal (twoFibreProductSquare F G) := by
  -- The public theorem is the full-subcategory terminality transport proved above.
  exact squareHasTerminal F G

end StackInSetoidsOver

end

end CategoryTheory
