import Mathlib
import StacksProject_2024.Chap04.Definition_4_31_2
import StacksProject_2024.Internal.Chap08.StackInGroupoidsTwoFibreProductSquare
import StacksProject_2024.Chap08.Lemma_8_4_6
import StacksProject_2024.Chap08.Definition_8_11_4

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackInGroupoidsOver.Hom

/-- Helper for Lemma 8.11.5: the explicit fibred `2`-fibre product of two stack morphisms is
again a stack on the site. -/
theorem twoFibreProductProjection_isStackOnSite
    {A B S : StackInGroupoidsOver J}
    (F : A ⟶ S) (G : B ⟶ S) :
    IsStackOnSite J
    (FibredCategoryOver.twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p := by
  -- Use the Chapter 8.4.6 stack-stability theorem for the underlying fibred-category pullback.
  let Fₛ : A.toStackOver ⟶ S.toStackOver :=
    InducedCategory.Hom.ofFibredCategoryMor F.toFibredCategoryMor
  let Gₛ : B.toStackOver ⟶ S.toStackOver :=
    InducedCategory.Hom.ofFibredCategoryMor G.toFibredCategoryMor
  change IsStackOnSite J
    (FibredCategoryOver.twoFibreProduct
      (InducedCategory.Hom.toFibredCategoryMor Fₛ)
      (InducedCategory.Hom.toFibredCategoryMor Gₛ)).p
  exact stackTwoFibreProduct_isStack Fₛ Gₛ

/-- Helper for Lemma 8.11.5: the explicit fibred `2`-fibre product rebundled as a stack in
groupoids. -/
noncomputable def stackTwoFibreProduct
    {A B S : StackInGroupoidsOver J}
    (F : A ⟶ S) (G : B ⟶ S) :
    StackInGroupoidsOver J :=
  ⟨FibredInGroupoidsOver.twoFibreProduct F.toHom G.toHom,
    show IsStackOnSite J
      (FibredCategoryOver.twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p from
        twoFibreProductProjection_isStackOnSite (J := J) F G⟩

/-- Helper for Lemma 8.11.5: a canonical stack-level `2`-fibre product square built from the
ambient fibred-in-groupoids pullback square. -/
noncomputable def stackTwoFibreProductSquare
    {A B S : StackInGroupoidsOver J}
    (F : A ⟶ S) (G : B ⟶ S) :
    BicategoricalTwoCommutativeSquare F G :=
  let T := stackTwoFibreProduct (J := J) F G
  let p : T ⟶ A :=
    StackInGroupoidsOver.ofAmbientHom
      (FibredInGroupoidsOver.twoFibreProductLeftProjection F.toHom G.toHom)
  let q : T ⟶ B :=
    StackInGroupoidsOver.ofAmbientHom
      (FibredInGroupoidsOver.twoFibreProductRightProjection F.toHom G.toHom)
  { obj := T
    p := p
    q := q
    ψ := StackInGroupoidsOver.Hom.ofAmbientHomIso
      (FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom).ψ }

/-- Helper for Lemma 8.11.5: forget a stack square to the ambient fibred-in-groupoids square. -/
noncomputable abbrev toAmbientSquare
    {A B S : StackInGroupoidsOver J}
    {F : A ⟶ S} {G : B ⟶ S}
    (P : BicategoricalTwoCommutativeSquare F G) :
    BicategoricalTwoCommutativeSquare F.toHom G.toHom where
  obj := P.obj.obj
  p := P.p.toHom
  q := P.q.toHom
  ψ :=
    Functor.mapIso (((stackInGroupoidsOverSubTwoCategory J).hom P.obj S).inclusion) P.ψ

/-- Helper for Lemma 8.11.5: forget a morphism into the canonical stack pullback square to the
ambient fibred-in-groupoids square. -/
noncomputable abbrev toAmbientSquareHom
    {A B S : StackInGroupoidsOver J}
    {F : A ⟶ S} {G : B ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    (u : P ⟶ stackTwoFibreProductSquare (J := J) F G) :
    toAmbientSquare (J := J) P ⟶
      FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom where
  hom := u.hom.toHom
  left := u.left.hom.hom
  right := u.right.hom.hom
  comm := by
    exact congrArg (fun η ↦ η.hom.hom) u.comm

/-- Helper for Lemma 8.11.5: rewrap an ambient square morphism into the canonical stack
pullback square. -/
noncomputable abbrev ofAmbientSquareHom
    {A B S : StackInGroupoidsOver J}
    {F : A ⟶ S} {G : B ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    (u : toAmbientSquare (J := J) P ⟶
      FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom) :
    P ⟶ stackTwoFibreProductSquare (J := J) F G := by
  rcases u with ⟨hom, left, right, comm⟩
  refine
    { hom := StackInGroupoidsOver.ofAmbientHom hom
      left := ⟨ObjectProperty.homMk left, trivial⟩
      right := ⟨ObjectProperty.homMk right, trivial⟩
      comm := ?_ }
  -- Forget the stack wrappers to recover the ambient square equation.
  unfold_projs
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  exact comm

/-- Helper for Lemma 8.11.5: forget a `2`-morphism between square maps to the ambient
fibred-in-groupoids `2`-morphism. -/
noncomputable abbrev toAmbientSquareTwoHom
    {A B S : StackInGroupoidsOver J}
    {F : A ⟶ S} {G : B ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    {u v : P ⟶ stackTwoFibreProductSquare (J := J) F G}
    (η : u ⟶ v) :
    toAmbientSquareHom (J := J) u ⟶ toAmbientSquareHom (J := J) v where
  hom := η.hom.hom.hom
  left_comm := by
    exact congrArg (fun α ↦ α.hom.hom) η.left_comm
  right_comm := by
    exact congrArg (fun α ↦ α.hom.hom) η.right_comm

/-- Helper for Lemma 8.11.5: lift an ambient `2`-morphism into the canonical stack pullback
square back to the owner square. -/
noncomputable def ownerTwoHomOfAmbientSquareTwoHom
    {A B S : StackInGroupoidsOver J}
    {F : A ⟶ S} {G : B ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    {u : P ⟶ stackTwoFibreProductSquare (J := J) F G}
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

/-- Helper for Lemma 8.11.5: an isomorphism of based functors over the site lifts to an
isomorphism of stack morphisms. -/
noncomputable def stackOwnerIsoOfBasedFunctorIso
    {A B : StackInGroupoidsOver J}
    {F G : A ⟶ B}
    (e : F.toBasedFunctor ≅ G.toBasedFunctor) :
    F ≅ G :=
  let eCat : F.toFibredCategoryMor ≅ G.toFibredCategoryMor :=
    CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial
  let eGrp : F.toFibredInGroupoidsMor ≅ G.toFibredInGroupoidsMor :=
    CategoryTheory.isoMk (ObjectProperty.isoMk _ eCat) trivial trivial
  CategoryTheory.isoMk (ObjectProperty.isoMk _ eGrp) trivial trivial

/-- Helper for Lemma 8.11.5: forgetting the lifted stack isomorphism recovers the original based
functor isomorphism. -/
theorem stackOwnerIsoOfBasedFunctorIso_hom_hom_hom_hom_hom_hom_hom
    {A B : StackInGroupoidsOver J}
    {F G : A ⟶ B}
    (e : F.toBasedFunctor ≅ G.toBasedFunctor) :
    (stackOwnerIsoOfBasedFunctorIso (J := J) e).hom.hom.hom.hom.hom.hom.hom = e.hom := by
  rfl

/-- Helper for Lemma 8.11.5: every `2`-morphism between stack morphisms is invertible because
its components are vertical morphisms in groupoid fibers. -/
theorem stackHom_isIso
    {A B : StackInGroupoidsOver J}
    {F G : A ⟶ B}
    (τ : F ⟶ G) :
    IsIso τ := by
  let τBased : F.toBasedFunctor ⟶ G.toBasedFunctor := τ.hom.hom.hom.hom.hom.hom
  have hBased : IsIso τBased := by
    letI : ∀ a : A.S, IsIso (τBased.toNatTrans.app a) := fun a ↦ by
      letI : B.p.IsHomLift (𝟙 (A.p.obj a)) (τBased.toNatTrans.app a) :=
        τBased.isHomLift' a
      letI :
          IsIso (Functor.Fiber.homMk B.p (A.p.obj a) (τBased.toNatTrans.app a)) :=
        IsFibredInGroupoids.hom_isIso (p := B.p) (U := A.p.obj a)
          (Functor.Fiber.homMk B.p (A.p.obj a) (τBased.toNatTrans.app a))
      letI : IsIso (τBased.toNatTrans.app a) := by
        simpa using
          (inferInstance :
            IsIso
              (Functor.Fiber.fiberInclusion.map
                (Functor.Fiber.homMk B.p (A.p.obj a) (τBased.toNatTrans.app a))))
      infer_instance
    letI : IsIso τBased.toNatTrans := by
      exact NatIso.isIso_of_isIso_app τBased.toNatTrans
    exact BasedNatIso.isIso_of_toNatTrans_isIso τBased
  let e : F.toBasedFunctor ≅ G.toBasedFunctor := asIso τBased
  let eOwner : F ≅ G := stackOwnerIsoOfBasedFunctorIso (J := J) e
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

/-- Helper for Lemma 8.11.5: hom-categories of stack morphisms are groupoids. -/
instance stackHomIsGroupoid
    {A B : StackInGroupoidsOver J} :
    IsGroupoid (A ⟶ B) where
  all_isIso := stackHom_isIso (J := J)

/-- Helper for Lemma 8.11.5: the bicategory of stacks in groupoids is locally a groupoid. -/
instance stackInGroupoidsOverIsLocallyGroupoid :
    Bicategory.IsLocallyGroupoid (StackInGroupoidsOver J) :=
  fun A B ↦ by infer_instance

/-- Helper for Lemma 8.11.5: the canonical stack `2`-fibre product square is bicategorically
final because the ambient fibred-in-groupoids square is final. -/
theorem stackTwoFibreProductSquare_isTwoFibreProduct
    {A B S : StackInGroupoidsOver J}
    (F : A ⟶ S) (G : B ⟶ S) :
    Bicategory.IsFinal (stackTwoFibreProductSquare (J := J) F G) := by
  refine ⟨?_⟩
  intro P
  let Q : BicategoricalTwoCommutativeSquare F.toHom G.toHom :=
    FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom
  letI : Bicategory.IsFinal Q :=
    FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct F.toHom G.toHom
  let targetAmbient : toAmbientSquare (J := J) P ⟶ Q := ⊤_ _
  let targetOwner : P ⟶ stackTwoFibreProductSquare (J := J) F G :=
    ofAmbientSquareHom (J := J) targetAmbient
  let htarget : Limits.IsTerminal targetAmbient := Limits.terminalIsTerminal
  exact
    ((Limits.IsTerminal.ofUniqueHom (Y := targetOwner)
      (fun u ↦ ownerTwoHomOfAmbientSquareTwoHom
        (J := J) (Limits.terminal.from (toAmbientSquareHom (J := J) u)))
      (fun u η ↦ by
        -- Forget to the ambient terminal square, where uniqueness is already known.
        apply BicategoricalTwoCommutativeSquare.TwoHom.ext
        repeat first | apply InducedWideCategory.Hom.ext | apply InducedCategory.Hom.ext
        exact congrArg (fun ζ ↦ ζ.hom.hom.hom.hom.hom)
          (htarget.hom_ext
            (toAmbientSquareTwoHom (J := J) η)
            (Limits.terminal.from (toAmbientSquareHom (J := J) u)))))).hasTerminal


end StackInGroupoidsOver.Hom

end

end CategoryTheory
