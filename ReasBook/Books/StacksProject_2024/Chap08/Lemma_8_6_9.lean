import Mathlib
import StacksProject_2024.Chap04.Definition_4_31_2
import StacksProject_2024.Chap04.Lemma_4_35_7
import StacksProject_2024.Chap04.Lemma_4_35_9
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Lemma_8_4_2
import StacksProject_2024.Chap08.Lemma_8_4_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open FibredCategoryMor
open GrothendieckTopology.Cover
open Opposite

/-
Domain-style sampling for Lemma 8.6.9:
- primary domain: stacks in groupoids over a site, their morphisms, and bicategorical
  `2`-fibre-product squares;
- sampled owner declarations:
  the owner homs `S₂ ⟶ S₁`,
  `FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects`,
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`;
- sampled bridge/model declarations:
  `StackInGroupoidsOver.twoFibreProductSquare`,
  `StackInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`;
- best owner abstraction: the source-facing square should be organized around the stack-morphism
  owner `BicategoricalTwoCommutativeSquare F G`, with the local essential-image hypothesis stated
  directly as `F.LocallyEssentiallySurjectiveOnObjects`; the based-functor and fibred-category
  coercions are bridge/view data, while the canonical pullback square from Lemma `8.5.6` is only
  the comparison model used to prove this owner-level statement;
- primitive data: the stack morphisms `F`, `G`, `F'`, `G'`, the square `2`-isomorphism `α` on
  stack morphisms, the local essential-image hypothesis on `F`, and faithfulness of `F'`;
- derived API: transport of faithfulness across the owner `2`-cartesian square.

Source/core/bridge triage:
- `source-facing`: the faithfulness descent statement of Lemma `8.6.9`;
- `core/canonical`: the owner homs in `StackInGroupoidsOver J`,
  `FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects`,
  `BicategoricalTwoCommutativeSquare F G`, and `Bicategory.IsFinal`;
- `bridge/view`: coercions from stack morphisms to fibred-category morphisms and based functors,
  together with the canonical pullback square from Lemma `8.5.6`, used only as a model for the
  owner-level square statement. -/

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S₁ S₂ T₁ T₂ : StackInGroupoidsOver.{u, v, max u v, v} J}

section

variable (F : S₂ ⟶ S₁)
variable (G : T₁ ⟶ S₁)

/-- Helper for Lemma 8.6.9: the explicit fibred `2`-fibre product of `F` and `G`, rebundled as a
stack in groupoids using the stack property of pullbacks of stacks. -/
private noncomputable abbrev stack_pullback
    (F : S₂ ⟶ S₁) (G : T₁ ⟶ S₁) :
    StackInGroupoidsOver J :=
  ⟨FibredInGroupoidsOver.twoFibreProduct F.toHom G.toHom,
    show IsStackOnSite J
      (FibredCategoryOver.twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p from
        stackTwoFibreProduct_isStack F.toFibredCategoryMor G.toFibredCategoryMor⟩

/-- Helper for Lemma 8.6.9: the explicit stack-level pullback square obtained by reusing the
ambient Chapter 4 pullback square in categories fibred in groupoids. -/
private noncomputable abbrev stack_pullback_square
    (F : S₂ ⟶ S₁) (G : T₁ ⟶ S₁) :
    BicategoricalTwoCommutativeSquare F G :=
  let T := stack_pullback (J := J) F G
  let p : T ⟶ S₂ :=
    StackInGroupoidsOver.ofAmbientHom
      (FibredInGroupoidsOver.twoFibreProductLeftProjection F.toHom G.toHom)
  let q : T ⟶ T₁ :=
    StackInGroupoidsOver.ofAmbientHom
      (FibredInGroupoidsOver.twoFibreProductRightProjection F.toHom G.toHom)
  { obj := T
    p := p
    q := q
    ψ := StackInGroupoidsOver.Hom.ofAmbientHomIso
      (FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom).ψ }

/-- Helper for Lemma 8.6.9: forget a square of stacks in groupoids to the ambient square of
fibred categories in groupoids. -/
private noncomputable abbrev toAmbientSquare
    {F : S₂ ⟶ S₁} {G : T₁ ⟶ S₁}
    (P : BicategoricalTwoCommutativeSquare F G) :
    BicategoricalTwoCommutativeSquare F.toHom G.toHom where
  obj := P.obj.obj
  p := P.p.toHom
  q := P.q.toHom
  ψ :=
    Functor.mapIso (((stackInGroupoidsOverSubTwoCategory J).hom P.obj S₁).inclusion) P.ψ

/-- Helper for Lemma 8.6.9: forget a morphism into the explicit pullback square to the ambient
fibred-in-groupoids square. -/
private noncomputable abbrev toAmbientSquareHom
    {F : S₂ ⟶ S₁} {G : T₁ ⟶ S₁}
    {P : BicategoricalTwoCommutativeSquare F G}
    (u : P ⟶ stack_pullback_square (J := J) F G) :
    toAmbientSquare (J := J) P ⟶
      FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom where
  hom := u.hom.toHom
  left := u.left.hom.hom
  right := u.right.hom.hom
  comm := by
    exact congrArg (fun η ↦ η.hom.hom) u.comm

/-- Helper for Lemma 8.6.9: rewrap an ambient morphism into the explicit pullback square as an
owner square morphism. -/
private noncomputable abbrev ofAmbientSquareHom
    {F : S₂ ⟶ S₁} {G : T₁ ⟶ S₁}
    {P : BicategoricalTwoCommutativeSquare F G}
    (u : toAmbientSquare (J := J) P ⟶
      FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom) :
    P ⟶ stack_pullback_square (J := J) F G := by
  rcases u with ⟨hom, left, right, comm⟩
  refine
    { hom := StackInGroupoidsOver.ofAmbientHom hom
      left := ⟨ObjectProperty.homMk left, trivial⟩
      right := ⟨ObjectProperty.homMk right, trivial⟩
      comm := ?_ }
  -- Forget both wrapper layers to recover the ambient square equation.
  unfold_projs
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  exact comm

/-- Helper for Lemma 8.6.9: forget a `2`-morphism between owner square maps to the ambient
`2`-morphism between the corresponding ambient square maps. -/
private noncomputable abbrev toAmbientSquareTwoHom
    {F : S₂ ⟶ S₁} {G : T₁ ⟶ S₁}
    {P : BicategoricalTwoCommutativeSquare F G}
    {u v : P ⟶ stack_pullback_square (J := J) F G}
    (η : u ⟶ v) :
    toAmbientSquareHom (J := J) u ⟶ toAmbientSquareHom (J := J) v where
  hom := η.hom.hom.hom
  left_comm := by
    exact congrArg (fun α ↦ α.hom.hom) η.left_comm
  right_comm := by
    exact congrArg (fun α ↦ α.hom.hom) η.right_comm

/-- Helper for Lemma 8.6.9: an ambient `2`-morphism into the explicit pullback square lifts to
the owner-level square of stacks in groupoids. -/
private noncomputable def owner_twoHom_of_ambient_square_twoHom
    {F : S₂ ⟶ S₁} {G : T₁ ⟶ S₁}
    {P : BicategoricalTwoCommutativeSquare F G}
    {u : P ⟶ stack_pullback_square (J := J) F G}
    {v : toAmbientSquare (J := J) P ⟶
      FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom}
    (η : toAmbientSquareHom (J := J) u ⟶ v) :
    u ⟶ ofAmbientSquareHom (J := J) v := by
  refine
    { hom := ⟨ObjectProperty.homMk η.hom, trivial⟩
      left_comm := ?_
      right_comm := ?_ }
  · unfold_projs
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    exact η.left_comm
  · unfold_projs
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    exact η.right_comm

/-- Helper for Lemma 8.6.9: an isomorphism of stack morphisms induces an isomorphism of the
underlying based functors over the base category. -/
private noncomputable def basedFunctorIsoOfStackOwnerIso
    {X Y : StackInGroupoidsOver J}
    {H K : X ⟶ Y}
    (e : H ≅ K) :
    H.toBasedFunctor ≅ K.toBasedFunctor :=
  FibredInGroupoidsMor.basedFunctorIsoOfOwnerIso
    (Functor.mapIso (((stackInGroupoidsOverSubTwoCategory J).hom X Y).inclusion) e)

/-- Helper for Lemma 8.6.9: an isomorphism of underlying based functors lifts back to an
isomorphism of stack morphisms. -/
private noncomputable def stackOwnerIsoOfBasedFunctorIso
    {X Y : StackInGroupoidsOver J}
    {H K : X ⟶ Y}
    (e : H.toBasedFunctor ≅ K.toBasedFunctor) :
    H ≅ K := by
  let eCat : H.toFibredCategoryMor ≅ K.toFibredCategoryMor :=
    CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial
  let eGrp : H.toFibredInGroupoidsMor ≅ K.toFibredInGroupoidsMor :=
    CategoryTheory.isoMk (ObjectProperty.isoMk _ eCat) trivial trivial
  exact CategoryTheory.isoMk (ObjectProperty.isoMk _ eGrp) trivial trivial

/-- Helper for Lemma 8.6.9: forgetting the lifted stack isomorphism recovers the original
based-functor isomorphism. -/
private theorem stackOwnerIsoOfBasedFunctorIso_hom_hom_hom_hom_hom_hom_hom
    {X Y : StackInGroupoidsOver J}
    {H K : X ⟶ Y}
    (e : H.toBasedFunctor ≅ K.toBasedFunctor) :
    (stackOwnerIsoOfBasedFunctorIso (J := J) e).hom.hom.hom.hom.hom.hom.hom = e.hom := by
  rfl

/-- Helper for Lemma 8.6.9: every `2`-morphism between stack morphisms is invertible because its
components lie in fibers of a stack in groupoids. -/
private theorem stack_hom_isIso
    {X Y : StackInGroupoidsOver J}
    {H K : X ⟶ Y}
    (τ : H ⟶ K) :
    IsIso τ := by
  let τBased : H.toBasedFunctor ⟶ K.toBasedFunctor := τ.hom.hom.hom.hom.hom.hom
  have hBased : IsIso τBased := by
    letI : ∀ a : X.S, IsIso (τBased.toNatTrans.app a) := fun a ↦ by
      letI : Y.p.IsHomLift (𝟙 (X.p.obj a)) (τBased.toNatTrans.app a) := τBased.isHomLift' a
      haveI :
          IsIso (Functor.Fiber.homMk Y.p (X.p.obj a) (τBased.toNatTrans.app a)) :=
        IsFibredInGroupoids.hom_isIso (p := Y.p) (U := X.p.obj a)
          (Functor.Fiber.homMk Y.p (X.p.obj a) (τBased.toNatTrans.app a))
      haveI : IsIso (τBased.toNatTrans.app a) := by
        simpa using
          (inferInstance :
            IsIso
              (Functor.Fiber.fiberInclusion.map
                (Functor.Fiber.homMk Y.p (X.p.obj a) (τBased.toNatTrans.app a))))
      infer_instance
    letI : IsIso τBased.toNatTrans := by
      exact NatIso.isIso_of_isIso_app τBased.toNatTrans
    exact BasedNatIso.isIso_of_toNatTrans_isIso τBased
  let e : H.toBasedFunctor ≅ K.toBasedFunctor := asIso τBased
  let eOwner : H ≅ K := stackOwnerIsoOfBasedFunctorIso (J := J) e
  have hEq : eOwner.hom = τ := by
    repeat first
      | apply InducedWideCategory.Hom.ext
      | apply InducedCategory.Hom.ext
      | apply WideSubcategory.hom_ext
      | apply ObjectProperty.hom_ext
    change eOwner.hom.hom.hom.hom.hom.hom.hom = τBased
    exact stackOwnerIsoOfBasedFunctorIso_hom_hom_hom_hom_hom_hom_hom (J := J) e
  rw [← hEq]
  infer_instance

private noncomputable instance stack_hom_isGroupoid
    {X Y : StackInGroupoidsOver J} :
    IsGroupoid (X ⟶ Y) where
  all_isIso := stack_hom_isIso (J := J)

private instance stackInGroupoidsOver_isLocallyGroupoid :
    Bicategory.IsLocallyGroupoid (StackInGroupoidsOver J) :=
  fun X Y ↦ by infer_instance

/-- Helper for Lemma 8.6.9: the explicit stack pullback square is bicategorically final because
its ambient fibred-in-groupoids square already is. -/
private theorem stack_pullback_square_isTwoFibreProduct :
    Bicategory.IsFinal (stack_pullback_square (J := J) F G) := by
  refine ⟨?_⟩
  intro P
  let Q : BicategoricalTwoCommutativeSquare F.toHom G.toHom :=
    FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom
  letI : Bicategory.IsFinal Q :=
    FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct F.toHom G.toHom
  let targetAmbient : toAmbientSquare (J := J) P ⟶ Q := ⊤_ _
  let targetOwner : P ⟶ stack_pullback_square (J := J) F G :=
    ofAmbientSquareHom (J := J) targetAmbient
  let htarget : Limits.IsTerminal targetAmbient := Limits.terminalIsTerminal
  exact
    ((Limits.IsTerminal.ofUniqueHom (Y := targetOwner)
      (fun u ↦ owner_twoHom_of_ambient_square_twoHom
        (J := J) (Limits.terminal.from (toAmbientSquareHom (J := J) u)))
      (fun u η ↦ by
        apply BicategoricalTwoCommutativeSquare.TwoHom.ext
        repeat first | apply InducedWideCategory.Hom.ext | apply InducedCategory.Hom.ext
        exact congrArg (fun ζ ↦ ζ.hom.hom.hom.hom.hom)
          (htarget.hom_ext
            (toAmbientSquareTwoHom (J := J) η)
            (Limits.terminal.from (toAmbientSquareHom (J := J) u)))))).hasTerminal

/-- Helper for Lemma 8.6.9: the chosen comparison morphisms between two final squares give the
unit and counit isomorphisms on the corresponding apex maps. -/
private noncomputable def comparison_apex_unit_counit_of_two_final_squares
    {P Q : BicategoricalTwoCommutativeSquare F G}
    [Bicategory.IsFinal P] [Bicategory.IsFinal Q]
    (u : Q ⟶ P)
    (v : P ⟶ Q) :
    ((𝟙 Q.obj : Q.obj ⟶ Q.obj) ≅ u.hom ≫ v.hom) ×
      (v.hom ≫ u.hom ≅ (𝟙 P.obj : P.obj ⟶ P.obj)) := by
  -- Compare the two chosen terminal square morphisms in each endomorphism hom-category.
  let ηsq : (𝟙 Q : Q ⟶ Q) ≅ u ≫ v := by
    exact asIso ((Bicategory.IsFinal.homIsTerminal (x := Q) (y := Q) (f := u ≫ v)).from (𝟙 Q))
  let εsq : v ≫ u ≅ (𝟙 P : P ⟶ P) := by
    exact asIso ((Bicategory.IsFinal.homIsTerminal (x := P) (y := P) (f := 𝟙 P)).from (v ≫ u))
  -- Project the square-map isomorphisms to the apex morphisms.
  refine ⟨?_, ?_⟩
  · exact asIso ηsq.hom.hom
  · exact asIso εsq.hom.hom

/-- Helper for Lemma 8.6.9: when both the given square and the canonical pullback square are
final, the comparison from the canonical square to the given one is an equivalence over the
base. -/
private theorem canonical_pullback_apex_isEquivalenceOverBase_of_twoCartesian
    (F' : T₂ ⟶ S₂)
    (G' : T₂ ⟶ T₁)
    (α : F' ≫ F ≅ G' ≫ G)
    (hcart :
      Bicategory.IsFinal
        (⟨T₂, F', G', α⟩ : BicategoricalTwoCommutativeSquare F G)) :
    let P : BicategoricalTwoCommutativeSquare F G := ⟨T₂, F', G', α⟩
    let Q : BicategoricalTwoCommutativeSquare F G := stack_pullback_square (J := J) F G
    let u : Q ⟶ P := ⊤_ (Q ⟶ P)
    u.hom.IsEquivalenceOverBase := by
  let P : BicategoricalTwoCommutativeSquare F G := ⟨T₂, F', G', α⟩
  let Q :=
    stack_pullback_square
      (J := J) (S₁ := S₁) (S₂ := S₂) (T₁ := T₁) (F := F) (G := G)
  letI : Bicategory.IsFinal P := hcart
  letI : Bicategory.IsFinal Q := stack_pullback_square_isTwoFibreProduct (J := J) F G
  let u : Q ⟶ P := ⊤_ (Q ⟶ P)
  let v : P ⟶ Q := ⊤_ (P ⟶ Q)
  obtain ⟨η, ε⟩ :=
    comparison_apex_unit_counit_of_two_final_squares
      (J := J) (F := F) (G := G) u v
  -- Package the chosen comparison apex map with its quasi-inverse over the base.
  change BasedFunctor.IsEquivalenceOverBase u.hom.toBasedFunctor
  refine BasedFunctor.IsEquivalenceOverBase.mkPrime v.hom.toBasedFunctor ?_ ?_
  · -- The unit isomorphism is the apex projection of the terminal comparison in `Q ⟶ Q`.
    change (𝟙 Q.obj.toBasedCategory) ≅
      BasedFunctor.comp u.hom.toBasedFunctor v.hom.toBasedFunctor
    simpa [BasedFunctor.comp] using basedFunctorIsoOfStackOwnerIso (J := J) η
  · -- The counit isomorphism is the apex projection of the terminal comparison in `P ⟶ P`.
    change BasedFunctor.comp v.hom.toBasedFunctor u.hom.toBasedFunctor ≅
      (𝟙 P.obj.toBasedCategory)
    simpa [BasedFunctor.comp] using basedFunctorIsoOfStackOwnerIso (J := J) ε

/-- Helper for Lemma 8.6.9: the canonical left projection from the explicit stack pullback
inherits faithfulness from the left leg of any final square over `F` and `G`. -/
private theorem two_fibre_product_left_projection_faithful_of_twoCartesian
    (F' : T₂ ⟶ S₂)
    (G' : T₂ ⟶ T₁)
    (α : F' ≫ F ≅ G' ≫ G)
    (hcart :
      Bicategory.IsFinal
        (⟨T₂, F', G', α⟩ : BicategoricalTwoCommutativeSquare F G))
    (hF' : F'.toBasedFunctor.Faithful) :
    (stack_pullback_square (J := J) F G).p.toBasedFunctor.Faithful := by
  let P : BicategoricalTwoCommutativeSquare F G := ⟨T₂, F', G', α⟩
  let Q := stack_pullback_square (J := J) (F := F) (G := G)
  letI : Bicategory.IsFinal P := hcart
  letI : Bicategory.IsFinal Q := stack_pullback_square_isTwoFibreProduct (J := J) F G
  let u : Q ⟶ P := ⊤_ (Q ⟶ P)
  have huEq :
      u.hom.IsEquivalenceOverBase :=
    canonical_pullback_apex_isEquivalenceOverBase_of_twoCartesian
      (J := J) (F := F) (G := G) F' G' α hcart
  letI : u.hom.toBasedFunctor.IsEquivalence :=
    BasedFunctor.isEquivalence_of_isEquivalenceOverBase u.hom.toBasedFunctor huEq
  have hF'Functor : F'.toBasedFunctor.toFunctor.Faithful := by
    simpa using hF'
  letI : u.hom.toBasedFunctor.toFunctor.Faithful := by infer_instance
  letI : F'.toBasedFunctor.toFunctor.Faithful := hF'Functor
  letI : (u.hom.toBasedFunctor.toFunctor ⋙ F'.toBasedFunctor.toFunctor).Faithful := by infer_instance
  haveI : IsIso u.left := stack_hom_isIso (J := J) u.left
  let leftIso :
      BasedFunctor.comp u.hom.toBasedFunctor F'.toBasedFunctor ≅ Q.p.toBasedFunctor := by
    -- The left comparison `2`-cell of `u` identifies the canonical left projection with
    -- the composite through the original left leg `F'`.
    simpa [BasedFunctor.comp] using basedFunctorIsoOfStackOwnerIso (J := J) (asIso u.left)
  let leftIsoFunctor :
      u.hom.toBasedFunctor.toFunctor ⋙ F'.toBasedFunctor.toFunctor ≅
        Q.p.toBasedFunctor.toFunctor :=
    Functor.mapIso
      (BasedNatTrans.forgetful Q.obj.toBasedCategory S₂.toBasedCategory)
      leftIso
  -- Transport faithfulness across the left-leg comparison isomorphism.
  exact Functor.Faithful.of_iso leftIsoFunctor

/-- Helper for Lemma 8.6.9: the canonical pullback functor on fibers is characterized by the
fact that its image factors through the chosen strongly cartesian pullback arrows. -/
private theorem canonical_pullbackFunctor_map_fac
    {X : FibredCategoryOver C}
    {U V : C} (f : V ⟶ U) {x y : X.p.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
        (canonicalPullbackChoice X.p).map f y =
      (canonicalPullbackChoice X.p).map f x ≫ φ.1 := by
  -- Compare the chosen pullback morphism with the universal morphism into the target lift.
  letI : X.p.IsHomLift (𝟙 U) φ.1 := φ.2
  letI : X.p.IsHomLift f ((canonicalPullbackChoice X.p).map f x) :=
    (canonicalPullbackChoice X.p).isStronglyCartesian f x |>.toIsHomLift
  letI : X.p.IsHomLift f ((canonicalPullbackChoice X.p).map f x ≫ φ.1) :=
    IsHomLift.comp_lift_id_right' X.p f ((canonicalPullbackChoice X.p).map f x) U φ.1
  letI : X.p.IsStronglyCartesian f ((canonicalPullbackChoice X.p).map f y) :=
    (canonicalPullbackChoice X.p).isStronglyCartesian f y
  change
      Functor.IsStronglyCartesian.map X.p f ((canonicalPullbackChoice X.p).map f y)
        (Category.id_comp f).symm
        ((canonicalPullbackChoice X.p).map f x ≫ φ.1) ≫
          (canonicalPullbackChoice X.p).map f y =
        (canonicalPullbackChoice X.p).map f x ≫ φ.1
  exact
    (Functor.IsStronglyCartesian.fac X.p f ((canonicalPullbackChoice X.p).map f y)
      (Category.id_comp f).symm
      ((canonicalPullbackChoice X.p).map f x ≫ φ.1))

/-- Helper for Lemma 8.6.9: mapping a strongly cartesian lift over `f` along a fibred-category
morphism again yields a strongly cartesian lift over the same base arrow `f`. -/
private theorem fibredCategoryMor_map_stronglyCartesian_of_lift
    {X Y : FibredCategoryOver C}
    (H : X ⟶ Y) {a b : X.S} {U V : C} (f : V ⟶ U) (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian f φ) :
    Y.p.IsStronglyCartesian f (H.toHom.map φ) := by
  letI : X.p.IsHomLift f φ := hφ.toIsHomLift
  have hφ' : X.p.IsStronglyCartesian (X.p.map φ) φ := by
    subst_hom_lift X.p f φ
    simpa using hφ
  letI : Y.p.IsHomLift f (H.toHom.map φ) := by
    infer_instance
  have hY :
      Y.p.IsStronglyCartesian (Y.p.map (H.toHom.map φ)) (H.toHom.map φ) :=
    map_stronglyCartesian H φ hφ'
  subst_hom_lift Y.p f (H.toHom.map φ)
  exact hY

/-- Helper for Lemma 8.6.9: the canonical comparison isomorphism in the fiber over the domain of
`f`, identifying the chosen pullback of `G(y)` with the image under `G` of the chosen pullback of
`y`. -/
private noncomputable def pullbackComparison
    {X Y : FibredCategoryOver C}
    (H : X ⟶ Y) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    f ^*[canonicalPullbackChoice Y.p] ((H.toHom).fiberFunctor U).obj x ≅
      ((H.toHom).fiberFunctor V).obj (f ^*[canonicalPullbackChoice X.p] x) := by
  let hcX := canonicalPullbackChoice X.p
  let hcY := canonicalPullbackChoice Y.p
  let φ :
      (((H.toHom).fiberFunctor V).obj (f ^*[hcX] x)).1 ⟶
        (((H.toHom).fiberFunctor U).obj x).1 :=
    H.toHom.map (hcX.map f x)
  let ψ :
      (f ^*[hcY] (((H.toHom).fiberFunctor U).obj x)).1 ⟶
        (((H.toHom).fiberFunctor U).obj x).1 :=
    hcY.map f (((H.toHom).fiberFunctor U).obj x)
  have hφ : Y.p.IsStronglyCartesian f φ :=
    fibredCategoryMor_map_stronglyCartesian_of_lift
      (H := H) f (hcX.map f x) (hcX.isStronglyCartesian f x)
  have hψ : Y.p.IsStronglyCartesian f ψ :=
    hcY.isStronglyCartesian f (((H.toHom).fiberFunctor U).obj x)
  have hf : f = (Iso.refl V).hom ≫ f := by
    simp
  let e :
      (f ^*[hcY] (((H.toHom).fiberFunctor U).obj x)).1 ≅
        (((H.toHom).fiberFunctor V).obj (f ^*[hcX] x)).1 :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso Y.p hf φ ψ
  letI : Y.p.IsHomLift (𝟙 V) e.hom := by
    change Y.p.IsHomLift (Iso.refl V).hom e.hom
    exact Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift Y.p hf φ ψ
  letI : Y.p.IsHomLift (𝟙 V) e.inv := by
    change Y.p.IsHomLift (Iso.refl V).inv e.inv
    exact Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift Y.p hf φ ψ
  refine
    { hom := Functor.Fiber.homMk Y.p V e.hom
      inv := Functor.Fiber.homMk Y.p V e.inv
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        change e.hom ≫ e.inv = 𝟙 _
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        change e.inv ≫ e.hom = 𝟙 _
        exact e.inv_hom_id }

/-- Helper for Lemma 8.6.9: the underlying morphism of `pullbackComparison` becomes the chosen
strongly cartesian pullback arrow after postcomposition with the image of the chosen pullback
arrow in the source. -/
private theorem pullbackComparison_hom_postcompose
    {X Y : FibredCategoryOver C}
    (H : X ⟶ Y) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (pullbackComparison (H := H) f x).hom.1 ≫ H.toHom.map ((canonicalPullbackChoice X.p).map f x) =
      (canonicalPullbackChoice Y.p).map f (((H.toHom).fiberFunctor U).obj x) := by
  let hcX := canonicalPullbackChoice X.p
  let hcY := canonicalPullbackChoice Y.p
  let φ :
      (((H.toHom).fiberFunctor V).obj (f ^*[hcX] x)).1 ⟶
        (((H.toHom).fiberFunctor U).obj x).1 :=
    H.toHom.map (hcX.map f x)
  let ψ :
      (f ^*[hcY] (((H.toHom).fiberFunctor U).obj x)).1 ⟶
        (((H.toHom).fiberFunctor U).obj x).1 :=
    hcY.map f (((H.toHom).fiberFunctor U).obj x)
  have hφ : Y.p.IsStronglyCartesian f φ :=
    fibredCategoryMor_map_stronglyCartesian_of_lift
      (H := H) f (hcX.map f x) (hcX.isStronglyCartesian f x)
  have hψ : Y.p.IsStronglyCartesian f ψ :=
    hcY.isStronglyCartesian f (((H.toHom).fiberFunctor U).obj x)
  have hf : f = (Iso.refl V).hom ≫ f := by
    simp
  change (Functor.IsStronglyCartesian.domainIsoOfBaseIso Y.p hf φ ψ).hom ≫ φ = ψ
  exact Functor.IsStronglyCartesian.fac Y.p f φ hf ψ

/-- Helper for Lemma 8.6.9: applying `G` to a chosen pullback object yields an object canonically
isomorphic to the chosen pullback of the image object in the target fiber. -/
private noncomputable def fiber_pullback_comparison_iso
    {U V : C} (f : V ⟶ U) (y : T₁.p.Fiber U) :
    (((canonicalFiberPseudofunctor S₁.p).map f.op.toLoc).toFunctor.obj
        ((G.fiberFunctor U).obj y)) ≅
      (G.fiberFunctor V).obj
        (((canonicalFiberPseudofunctor T₁.p).map f.op.toLoc).toFunctor.obj y) := by
  simpa using
    pullbackComparison
      (H := G.toFibredCategoryMor) f y

/-- Helper for Lemma 8.6.9: `pullbackComparison` intertwines the pullback of a fiber morphism
with the image of the pulled-back morphism. -/
private theorem pullbackComparison_hom_naturality
    {U V : C} (f : V ⟶ U) {y y' : T₁.p.Fiber U} (γ : y ⟶ y') :
    (((canonicalFiberPseudofunctor S₁.p).map f.op.toLoc).toFunctor.map
        ((G.fiberFunctor U).map γ)) ≫
      (fiber_pullback_comparison_iso (G := G) f y').hom =
        (fiber_pullback_comparison_iso (G := G) f y).hom ≫
          (G.fiberFunctor V).map
            (((canonicalFiberPseudofunctor T₁.p).map f.op.toLoc).toFunctor.map γ) := by
  let η :
      ((canonicalFiberPseudofunctor S₁.p).map f.op.toLoc).toFunctor.obj ((G.fiberFunctor U).obj y) ⟶
        ((canonicalFiberPseudofunctor S₁.p).map f.op.toLoc).toFunctor.obj
          ((G.fiberFunctor U).obj y') :=
    ((canonicalFiberPseudofunctor S₁.p).map f.op.toLoc).toFunctor.map ((G.fiberFunctor U).map γ)
  let θ :
      (G.fiberFunctor V).obj
          (((canonicalFiberPseudofunctor T₁.p).map f.op.toLoc).toFunctor.obj y) ⟶
        (G.fiberFunctor V).obj
          (((canonicalFiberPseudofunctor T₁.p).map f.op.toLoc).toFunctor.obj y') :=
    (G.fiberFunctor V).map (((canonicalFiberPseudofunctor T₁.p).map f.op.toLoc).toFunctor.map γ)
  let hc := canonicalPullbackChoice T₁.p
  let φG :
      ((G.fiberFunctor V).obj (f ^*[hc] y')).1 ⟶ ((G.fiberFunctor U).obj y').1 :=
    G.toFibredCategoryMor.toHom.map (hc.map f y')
  have hφG : S₁.p.IsStronglyCartesian f φG := by
    change
      S₁.p.IsStronglyCartesian f
        (G.toFibredCategoryMor.toHom.map (hc.map f y'))
    exact
      fibredCategoryMor_map_stronglyCartesian_of_lift
        (H := G.toFibredCategoryMor) f (hc.map f y') (hc.isStronglyCartesian f y')
  letI : S₁.p.IsStronglyCartesian f φG := hφG
  letI : S₁.p.IsHomLift (𝟙 V) η.1 := η.2
  letI : S₁.p.IsHomLift (𝟙 V) θ.1 := θ.2
  letI : S₁.p.IsHomLift (𝟙 V) (fiber_pullback_comparison_iso (G := G) f y).hom.1 :=
    (fiber_pullback_comparison_iso (G := G) f y).hom.2
  letI : S₁.p.IsHomLift (𝟙 V) (fiber_pullback_comparison_iso (G := G) f y').hom.1 :=
    (fiber_pullback_comparison_iso (G := G) f y').hom.2
  letI :
      S₁.p.IsHomLift (𝟙 V)
        (η.1 ≫ (fiber_pullback_comparison_iso (G := G) f y').hom.1) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ S₁.p _ _ _ _ _
      (𝟙 V) η.1 η.2 V
      (fiber_pullback_comparison_iso (G := G) f y').hom.1
      (fiber_pullback_comparison_iso (G := G) f y').hom.2
  letI :
      S₁.p.IsHomLift (𝟙 V)
        ((fiber_pullback_comparison_iso (G := G) f y).hom.1 ≫ θ.1) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ S₁.p _ _ _ _ _
      (𝟙 V)
      (fiber_pullback_comparison_iso (G := G) f y).hom.1
      (fiber_pullback_comparison_iso (G := G) f y).hom.2
      V θ.1 θ.2
  have hcomp :
      η.1 ≫ (fiber_pullback_comparison_iso (G := G) f y').hom.1 ≫ φG =
        ((fiber_pullback_comparison_iso (G := G) f y).hom.1 ≫ θ.1) ≫ φG := by
    have hcompare_eq :
        (fiber_pullback_comparison_iso (G := G) f y).hom.1 =
          (pullbackComparison (H := G.toFibredCategoryMor) f y).hom.1 := by
      exact
        congrArg (fun e ↦ e.hom.1) (fiber_pullback_comparison_iso.eq_1 (G := G) (f := f) (y := y))
    have hpost_y' :
        η.1 ≫ (fiber_pullback_comparison_iso (G := G) f y').hom.1 ≫ φG =
          η.1 ≫ (canonicalPullbackChoice S₁.p).map f ((G.fiberFunctor U).obj y') := by
      simpa only [Category.assoc] using
        congrArg
          (fun k ↦ η.1 ≫ k)
          (pullbackComparison_hom_postcompose (H := G.toFibredCategoryMor) f y')
    have hpost_y :
        (canonicalPullbackChoice S₁.p).map f ((G.fiberFunctor U).obj y) ≫
            ((G.fiberFunctor U).map γ).1 =
          (((pullbackComparison (H := G.toFibredCategoryMor) f y).hom.1 ≫
              G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice T₁.p).map f y)) ≫
            ((G.fiberFunctor U).map γ).1) := by
      have hpost_y0 :
          (canonicalPullbackChoice S₁.p).map f ((G.fiberFunctor U).obj y) ≫
              ((G.fiberFunctor U).map γ).1 =
            ((pullbackComparison (H := G.toFibredCategoryMor) f y).hom.1 ≫
                G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice T₁.p).map f y)) ≫
              ((G.fiberFunctor U).map γ).1 :=
        congrArg
          (fun k ↦ k ≫ ((G.fiberFunctor U).map γ).1)
          (pullbackComparison_hom_postcompose (H := G.toFibredCategoryMor) f y).symm
      exact hpost_y0
    have hpost_y_fiber :
        (canonicalPullbackChoice S₁.p).map f ((G.fiberFunctor U).obj y) ≫
            ((G.fiberFunctor U).map γ).1 =
          (fiber_pullback_comparison_iso (G := G) f y).hom.1 ≫
            G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice T₁.p).map f y) ≫
              ((G.fiberFunctor U).map γ).1 := by
      calc
        (canonicalPullbackChoice S₁.p).map f ((G.fiberFunctor U).obj y) ≫
            ((G.fiberFunctor U).map γ).1
            = (((pullbackComparison (H := G.toFibredCategoryMor) f y).hom.1 ≫
                G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice T₁.p).map f y)) ≫
                ((G.fiberFunctor U).map γ).1) := hpost_y
        _ = (((fiber_pullback_comparison_iso (G := G) f y).hom.1 ≫
                G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice T₁.p).map f y)) ≫
              ((G.fiberFunctor U).map γ).1) := by
                rw [hcompare_eq]
                rfl
        _ = (fiber_pullback_comparison_iso (G := G) f y).hom.1 ≫
              G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice T₁.p).map f y) ≫
                ((G.fiberFunctor U).map γ).1 := by
                  rw [Category.assoc]
    have hpost_y_fiber' :
        (canonicalPullbackChoice S₁.p).map f ((G.fiberFunctor U).obj y) ≫
            ((G.fiberFunctor U).map γ).1 =
          (fiber_pullback_comparison_iso (G := G) f y).hom.1 ≫
            G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice T₁.p).map f y) ≫
              ((G.fiberFunctor U).map γ).1 :=
      hpost_y_fiber
    have hmid :
        η.1 ≫ (fiber_pullback_comparison_iso (G := G) f y').hom.1 ≫ φG =
          (fiber_pullback_comparison_iso (G := G) f y).hom.1 ≫
            G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice T₁.p).map f y) ≫
              ((G.fiberFunctor U).map γ).1 :=
      by
        have hmiddle :
            η.1 ≫ (fiber_pullback_comparison_iso (G := G) f y').hom.1 ≫ φG =
              (canonicalPullbackChoice S₁.p).map f ((G.fiberFunctor U).obj y) ≫
                ((G.fiberFunctor U).map γ).1 := by
          exact hpost_y'.trans <| by
            simpa [η, Category.assoc] using
              canonical_pullbackFunctor_map_fac
                (X := S₁.toFibredCategoryOver) f ((G.fiberFunctor U).map γ)
        exact hmiddle.trans hpost_y_fiber'
    have hmap_pullback :
        (fiber_pullback_comparison_iso (G := G) f y).hom.1 ≫
            G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice T₁.p).map f y) ≫
              ((G.fiberFunctor U).map γ).1 =
          (fiber_pullback_comparison_iso (G := G) f y).hom.1 ≫
            G.toFibredCategoryMor.toHom.map
                ((((canonicalFiberPseudofunctor T₁.p).map f.op.toLoc).toFunctor.map γ).1) ≫
              G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice T₁.p).map f y') := by
      have hcanon :
          G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice T₁.p).map f y) ≫
              ((G.fiberFunctor U).map γ).1 =
            G.toFibredCategoryMor.toHom.map
                ((((canonicalFiberPseudofunctor T₁.p).map f.op.toLoc).toFunctor.map γ).1) ≫
              G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice T₁.p).map f y') := by
        have hcanon0 :=
          congrArg
            (fun k ↦ G.toFibredCategoryMor.toHom.map k)
            (canonical_pullbackFunctor_map_fac
              (X := T₁.toFibredCategoryOver) f γ).symm
        change
          G.toFibredCategoryMor.toHom.map
              (((canonicalPullbackChoice T₁.p).map f y) ≫ γ.1) =
            G.toFibredCategoryMor.toHom.map
              (((((canonicalFiberPseudofunctor T₁.p).map f.op.toLoc).toFunctor.map γ).1) ≫
                (canonicalPullbackChoice T₁.p).map f y') at hcanon0
        rw [Functor.map_comp, Functor.map_comp] at hcanon0
        simpa only [Category.assoc] using hcanon0
      exact
        congrArg
          (fun k ↦ (fiber_pullback_comparison_iso (G := G) f y).hom.1 ≫ k)
          hcanon
    refine hmid.trans ?_
    change
      (fiber_pullback_comparison_iso (G := G) f y).hom.1 ≫
          G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice T₁.p).map f y) ≫
            ((G.fiberFunctor U).map γ).1 =
        ((fiber_pullback_comparison_iso (G := G) f y).hom.1 ≫
            G.toFibredCategoryMor.toHom.map
              ((((canonicalFiberPseudofunctor T₁.p).map f.op.toLoc).toFunctor.map γ).1)) ≫
          G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice T₁.p).map f y')
    rw [Category.assoc]
    exact hmap_pullback
  have hηcomparison :
      S₁.p.IsHomLift (𝟙 V)
        (η.1 ≫ (fiber_pullback_comparison_iso (G := G) f y').hom.1) := by
    infer_instance
  have hcomparisonθ :
      S₁.p.IsHomLift (𝟙 V)
        ((fiber_pullback_comparison_iso (G := G) f y).hom.1 ≫ θ.1) := by
    infer_instance
  apply Functor.Fiber.hom_ext
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ S₁.p _ _ _ _
      f φG inferInstance _ _ (𝟙 V)
      (η.1 ≫ (fiber_pullback_comparison_iso (G := G) f y').hom.1)
      ((fiber_pullback_comparison_iso (G := G) f y).hom.1 ≫ θ.1)
      hηcomparison hcomparisonθ <| by
        simpa [η, θ, Category.assoc] using hcomp

/-- Helper for Lemma 8.6.9: if `G(γ)` is the identity, then after pulling back along `f` the
endomorphism `γ` becomes the identity after transporting across `pullbackComparison`. -/
private theorem pullbackComparison_map_eq_of_vertical_endomorphism
    {U V : C} (f : V ⟶ U) {y : T₁.p.Fiber U} {γ : y ⟶ y}
    (hγ : (G.fiberFunctor U).map γ = 𝟙 _) :
    (fiber_pullback_comparison_iso (G := G) f y).hom ≫
      (G.fiberFunctor V).map
        (((canonicalFiberPseudofunctor T₁.p).map f.op.toLoc).toFunctor.map γ) ≫
        (fiber_pullback_comparison_iso (G := G) f y).inv = 𝟙 _ := by
  have hnat := pullbackComparison_hom_naturality (G := G) f γ
  rw [hγ] at hnat
  have hmap_id :
      ((canonicalFiberPseudofunctor S₁.p).map f.op.toLoc).toFunctor.map
          (𝟙 ((G.fiberFunctor U).obj y)) =
        𝟙 (((canonicalFiberPseudofunctor S₁.p).map f.op.toLoc).toFunctor.obj
          ((G.fiberFunctor U).obj y)) := by
    exact
      (((canonicalFiberPseudofunctor S₁.p).map f.op.toLoc).toFunctor.map_id
        ((G.fiberFunctor U).obj y))
  rw [hmap_id, Category.id_comp] at hnat
  have htransport :
      (fiber_pullback_comparison_iso (G := G) f y).hom ≫
          (fiber_pullback_comparison_iso (G := G) f y).inv =
        ((fiber_pullback_comparison_iso (G := G) f y).hom ≫
            (G.fiberFunctor V).map
              (((canonicalFiberPseudofunctor T₁.p).map f.op.toLoc).toFunctor.map γ)) ≫
          (fiber_pullback_comparison_iso (G := G) f y).inv :=
    congrArg
      (fun k ↦ k ≫ (fiber_pullback_comparison_iso (G := G) f y).inv)
      hnat
  calc
    (fiber_pullback_comparison_iso (G := G) f y).hom ≫
        (G.fiberFunctor V).map
          (((canonicalFiberPseudofunctor T₁.p).map f.op.toLoc).toFunctor.map γ) ≫
        (fiber_pullback_comparison_iso (G := G) f y).inv
        =
      ((fiber_pullback_comparison_iso (G := G) f y).hom ≫
          (G.fiberFunctor V).map
            (((canonicalFiberPseudofunctor T₁.p).map f.op.toLoc).toFunctor.map γ)) ≫
        (fiber_pullback_comparison_iso (G := G) f y).inv := by
          rw [Category.assoc]
    _ = (fiber_pullback_comparison_iso (G := G) f y).hom ≫
          (fiber_pullback_comparison_iso (G := G) f y).inv := by
            exact htransport.symm
    _ = 𝟙 _ := by simp

/-- Helper for Lemma 8.6.9: after identifying the fiber of the explicit pullback with the
categorical pullback of fibers, the first projection is faithful on every base fiber. -/
private theorem pullback_of_fibres_pi1_faithful_of_twoCartesian
    (F' : T₂ ⟶ S₂)
    (G' : T₂ ⟶ T₁)
    (α : F' ≫ F ≅ G' ≫ G)
    (hcart :
      Bicategory.IsFinal
        (⟨T₂, F', G', α⟩ : BicategoricalTwoCommutativeSquare F G))
    (hF' : F'.toBasedFunctor.Faithful)
    (U : C) :
    (Limits.CategoricalPullback.π₁ (F.fiberFunctor U) (G.fiberFunctor U)).Faithful := by
  let P : BicategoricalTwoCommutativeSquare F G := ⟨T₂, F', G', α⟩
  let T : StackInGroupoidsOver J :=
    ⟨FibredInGroupoidsOver.twoFibreProduct F.toHom G.toHom,
      by
        change IsStackOnSite J
          (FibredCategoryOver.twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p
        exact stackTwoFibreProduct_isStack F.toFibredCategoryMor G.toFibredCategoryMor⟩
  let p : T ⟶ S₂ :=
    StackInGroupoidsOver.ofAmbientHom
      (FibredInGroupoidsOver.twoFibreProductLeftProjection F.toHom G.toHom)
  let q : T ⟶ T₁ :=
    StackInGroupoidsOver.ofAmbientHom
      (FibredInGroupoidsOver.twoFibreProductRightProjection F.toHom G.toHom)
  let Q : BicategoricalTwoCommutativeSquare F G :=
    { obj := T
      p := p
      q := q
      ψ := StackInGroupoidsOver.Hom.ofAmbientHomIso
        (FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom).ψ }
  letI : Bicategory.IsFinal P := hcart
  letI : Bicategory.IsFinal Q := by
    change Bicategory.IsFinal (stack_pullback_square (J := J) F G)
    exact stack_pullback_square_isTwoFibreProduct (J := J) F G
  let u : Q ⟶ P := ⊤_ (Q ⟶ P)
  have huEq :
      u.hom.IsEquivalenceOverBase :=
    canonical_pullback_apex_isEquivalenceOverBase_of_twoCartesian
      (J := J) (F := F) (G := G) F' G' α hcart
  letI : u.hom.toBasedFunctor.IsEquivalence :=
    BasedFunctor.isEquivalence_of_isEquivalenceOverBase u.hom.toBasedFunctor huEq
  have hF'Functor : F'.toBasedFunctor.toFunctor.Faithful := by
    simpa using hF'
  letI : u.hom.toBasedFunctor.toFunctor.Faithful := by infer_instance
  letI : F'.toBasedFunctor.toFunctor.Faithful := hF'Functor
  letI : (u.hom.toBasedFunctor.toFunctor ⋙ F'.toBasedFunctor.toFunctor).Faithful := by infer_instance
  haveI : IsIso u.left := stack_hom_isIso (J := J) u.left
  let leftIso :
      BasedFunctor.comp u.hom.toBasedFunctor F'.toBasedFunctor ≅ Q.p.toBasedFunctor := by
    -- The left comparison `2`-cell identifies the canonical left projection with the composite
    -- through the given left leg `F'`.
    simpa [BasedFunctor.comp] using basedFunctorIsoOfStackOwnerIso (J := J) (asIso u.left)
  let leftIsoFunctor :
      u.hom.toBasedFunctor.toFunctor ⋙ F'.toBasedFunctor.toFunctor ≅
        Q.p.toBasedFunctor.toFunctor :=
    Functor.mapIso
      (BasedNatTrans.forgetful Q.obj.toBasedCategory S₂.toBasedCategory)
      leftIso
  have hQ :
      Q.p.toBasedFunctor.Faithful := by
    change Q.p.toBasedFunctor.toFunctor.Faithful
    exact Functor.Faithful.of_iso leftIsoFunctor
  have hK :
      (BasedFunctor.fiberFunctor
        (CategoryOver.explicitTwoFibreProductLeftProjection F.toBasedFunctor G.toBasedFunctor)
        U).Faithful := by
    change (Q.p.toBasedFunctor.fiberFunctor U).Faithful
    exact ((FibredInGroupoidsMor.faithful_iff_fiberwise
      (F := Q.p.toHom)).1 hQ U)
  let e := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
    F.toBasedFunctor G.toBasedFunctor U
  let K :=
    BasedFunctor.fiberFunctor
      (CategoryOver.explicitTwoFibreProductLeftProjection F.toBasedFunctor G.toBasedFunctor)
      U
  have hcomp :
      e.functor ⋙ Limits.CategoricalPullback.π₁ (F.fiberFunctor U) (G.fiberFunctor U) = K := by
    simpa [K] using
      (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₁
        (F := F.toBasedFunctor) (G := G.toBasedFunctor) U)
  letI : K.Faithful := hK
  let compIso :
      e.inverse ⋙ K ≅ Limits.CategoricalPullback.π₁ (F.fiberFunctor U) (G.fiberFunctor U) :=
    Functor.isoWhiskerLeft e.inverse (eqToIso hcomp.symm) ≪≫
      e.invFunIdAssoc (Limits.CategoricalPullback.π₁ (F.fiberFunctor U) (G.fiberFunctor U))
  letI : (e.inverse ⋙ K).Faithful := by infer_instance
  exact Functor.Faithful.of_iso compIso

/-- Helper for Lemma 8.6.9: a vertical endomorphism is the identity once all of its coverwise
restrictions become the identity morphism. -/
private theorem vertical_endomorphism_eq_id_of_coverwise_identity
    {U : C}
    (S : J.Cover U)
    {y : T₁.p.Fiber U}
    {γ : y ⟶ y}
    (hγ :
      ∀ I : S.Arrow,
        (((canonicalFiberPseudofunctor T₁.p).map I.f.op.toLoc).toFunctor.map γ) = 𝟙 _) :
    γ = 𝟙 y := by
  let Fp := canonicalFiberPseudofunctor T₁.p
  let Φ := Fp.toDescentData (fun I : S.Arrow ↦ I.f)
  letI : Φ.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      (J := J) (p := T₁.p)).1 inferInstance U S
  letI : Φ.Faithful := by infer_instance
  apply Φ.map_injective
  ext I
  have hmap_id_I :
      (Fp.map I.f.op.toLoc).toFunctor.map (𝟙 y) = 𝟙 _ := by
    exact ((Fp.map I.f.op.toLoc).toFunctor.map_id y)
  exact (hγ I).trans hmap_id_I.symm

/-- Helper for Lemma 8.6.9: the local-essential-image hypothesis produces a cover on which a
vertical endomorphism with trivial image in `S₁` restricts to the identity. -/
private theorem coverwise_identity_of_vertical_endomorphism_with_trivial_image
    (hF : StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects F)
    (F' : T₂ ⟶ S₂)
    (G' : T₂ ⟶ T₁)
    (α : F' ≫ F ≅ G' ≫ G)
    (hcart :
      Bicategory.IsFinal
        (⟨T₂, F', G', α⟩ : BicategoricalTwoCommutativeSquare F G))
    (hF' : F'.toBasedFunctor.Faithful)
    {U : C}
    (y : T₁.p.Fiber U)
    (γ : y ⟶ y)
    (hγ : (G.fiberFunctor U).map γ = 𝟙 _) :
    ∃ S : J.Cover U,
      ∀ I : S.Arrow,
        (((canonicalFiberPseudofunctor T₁.p).map I.f.op.toLoc).toFunctor.map γ) = 𝟙 _ := by
  obtain ⟨S, hS⟩ := hF U ((G.fiberFunctor U).obj y)
  refine ⟨S, ?_⟩
  intro I
  obtain ⟨x, ⟨e₀raw⟩⟩ := hS I
  let e₀ :
      (F.fiberFunctor I.Y).obj x ≅
        (((canonicalFiberPseudofunctor S₁.p).map I.f.op.toLoc).toFunctor.obj
          ((G.fiberFunctor U).obj y)) := by
    simpa using e₀raw
  let e :
      (F.fiberFunctor I.Y).obj x ≅
        (G.fiberFunctor I.Y).obj
          (((canonicalFiberPseudofunctor T₁.p).map I.f.op.toLoc).toFunctor.obj y) :=
    e₀ ≪≫ fiber_pullback_comparison_iso (G := G) I.f y
  let P : Limits.CategoricalPullback (F.fiberFunctor I.Y) (G.fiberFunctor I.Y) :=
    { fst := x
      snd := (((canonicalFiberPseudofunctor T₁.p).map I.f.op.toLoc).toFunctor.obj y)
      iso := e }
  have htransport :
      (fiber_pullback_comparison_iso (G := G) I.f y).hom =
        (fiber_pullback_comparison_iso (G := G) I.f y).hom ≫
          (G.fiberFunctor I.Y).map
            (((canonicalFiberPseudofunctor T₁.p).map I.f.op.toLoc).toFunctor.map γ) := by
    have h :=
      congrArg
        (fun k ↦ k ≫ (fiber_pullback_comparison_iso (G := G) I.f y).hom)
        (pullbackComparison_map_eq_of_vertical_endomorphism (G := G) I.f hγ)
    simpa [Category.assoc] using h.symm
  let δ : P ⟶ P :=
    { fst := 𝟙 x
      snd := (((canonicalFiberPseudofunctor T₁.p).map I.f.op.toLoc).toFunctor.map γ)
      w := by
        simpa [P, e, Category.assoc] using congrArg (fun k ↦ e₀.hom ≫ k) htransport }
  have hδid : δ = 𝟙 P := by
    let π₁ := Limits.CategoricalPullback.π₁ (F.fiberFunctor I.Y) (G.fiberFunctor I.Y)
    have hπ₁ : π₁.Faithful :=
      pullback_of_fibres_pi1_faithful_of_twoCartesian
        (J := J) (F := F) (G := G) F' G' α hcart hF' I.Y
    letI : π₁.Faithful := hπ₁
    apply π₁.map_injective
    change 𝟙 x = 𝟙 x
    simp
  simpa [δ] using congrArg Limits.CategoricalPullback.Hom.snd hδid

-- Proof sketch: replace the given `2`-cartesian square by the canonical explicit `2`-fibre
-- product `S₂ ×[S₁] T₁` from Lemma `8.5.6`. For a vertical morphism `γ : y ⟶ y` in a fiber of
-- `T₁` with trivial image in `S₁`, refine the base using the local essential-image hypothesis on
-- `F` so that `G(y)` becomes locally isomorphic to some `F(x)`. This turns `(1, γ)` into a
-- vertical endomorphism of the pullback object `(x, y, f)`. Faithfulness of the left projection
-- to `S₂`, transported back across the `2`-cartesian comparison square, forces `(1, γ)` to be
-- the identity, hence `γ = 𝟙`.
/-- Lemma 8.6.9: in a `2`-cartesian square of stacks in groupoids over `(C, J)`, if every object
of every fiber of `S₁` is locally in the essential image of `F : S₂ ⟶ S₁` and
`F' : T₂ ⟶ S₂` is faithful, then `G : T₁ ⟶ S₁` is faithful. -/
theorem faithful_of_twoCartesian_of_locallyEssentiallySurjective
    (hF : StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects F)
    (F' : T₂ ⟶ S₂)
    (G' : T₂ ⟶ T₁)
    (α : F' ≫ F ≅ G' ≫ G)
    (hcart :
      Bicategory.IsFinal
        (⟨T₂, F', G', α⟩ : BicategoricalTwoCommutativeSquare F G))
    (hF' : F'.toBasedFunctor.Faithful) :
    G.toBasedFunctor.Faithful := by
  -- First reduce global faithfulness of `G` to the fiberwise criterion from Lemma `4.35.9`.
  refine (FibredCategoryMor.faithful_iff_fiberwise (F := G.toFibredCategoryMor)).2 ?_
  intro U
  refine ⟨?_⟩
  intro y₁ y₂ γ₁ γ₂ hEq
  -- It suffices to show that the vertical difference `γ₁ ≫ inv γ₂` is trivial after applying `G`.
  let δ : y₁ ⟶ y₁ := γ₁ ≫ inv γ₂
  have hδ :
      (G.fiberFunctor U).map δ = 𝟙 _ := by
    letI : IsGroupoid (T₁.p.Fiber U) := inferInstance
    calc
      (G.fiberFunctor U).map δ
          = (G.fiberFunctor U).map γ₁ ≫ inv ((G.fiberFunctor U).map γ₂) := by
              simp [δ]
      _ = (G.fiberFunctor U).map γ₂ ≫ inv ((G.fiberFunctor U).map γ₂) := by
            rw [hEq]
      _ = 𝟙 _ := by simp
  obtain ⟨S, hS⟩ :=
    coverwise_identity_of_vertical_endomorphism_with_trivial_image
      (F := F) (G := G) hF F' G' α hcart hF' y₁ δ hδ
  have hδid : δ = 𝟙 y₁ :=
    vertical_endomorphism_eq_id_of_coverwise_identity
      (T₁ := T₁) (J := J) S hS
  letI : IsGroupoid (T₁.p.Fiber U) := inferInstance
  calc
    γ₁ = δ ≫ γ₂ := by
      simp [δ]
    _ = γ₂ := by simp [hδid]

end

end CategoryTheory
