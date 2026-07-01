import Mathlib
import stacks_project.Chap04.Definition_4_31_2
import stacks_project.Chap04.Definition_4_35_6
import stacks_project.Chap04.Lemma_4_35_7
import stacks_project.Chap04.Lemma_4_35_9
import stacks_project.Chap08.Definition_8_5_5
import stacks_project.Chap08.Definition_8_6_1
import stacks_project.Chap08.Lemma_8_4_2
import stacks_project.Chap08.Lemma_8_4_6
import stacks_project.Chap08.Lemma_8_6_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open FibredCategoryMor
open Opposite
open StackInGroupoidsOver
open StackInGroupoidsOver.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

section

variable {S₁ S₂ T₁ : StackInGroupoidsOver.{u, v, max u v, v} J}
variable (F : S₂ ⟶ S₁) (G : T₁ ⟶ S₁)

/-- Helper for Lemma 8.6.10: the explicit fibred `2`-fibre product of two stacks in groupoids is
again a stack on the site, via the Chapter 8.4.6 pullback-stack bridge. -/
private theorem stack_pullback_projection_isStack
    (F : S₂ ⟶ S₁) (G : T₁ ⟶ S₁) :
    IsStackOnSite J
      (FibredCategoryOver.twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p := by
  -- Reuse the Chapter 8.4.6 pullback-stability theorem for stacks on the site.
  exact stackTwoFibreProduct_isStack F.toFibredCategoryMor G.toFibredCategoryMor

/-- Helper for Lemma 8.6.10: the explicit fibred `2`-fibre product of `F` and `G`, rebundled as a
stack in groupoids using the pullback stability of the stack condition. -/
private noncomputable def stack_pullback
    (F : S₂ ⟶ S₁) (G : T₁ ⟶ S₁) :
    StackInGroupoidsOver J :=
  ⟨FibredInGroupoidsOver.twoFibreProduct F.toHom G.toHom,
    show IsStackOnSite J
      (FibredCategoryOver.twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p from
        stack_pullback_projection_isStack (J := J) F G⟩

local notation "twoFibreProduct" => stack_pullback

/-- Helper for Lemma 8.6.10: the canonical stack-level pullback square obtained from the ambient
Chapter 4 `2`-fibre product of `F` and `G`. -/
private noncomputable def stack_pullback_square
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

/-- Helper for Lemma 8.6.10: forget a square of stacks in groupoids to the underlying ambient
square of fibred categories in groupoids. -/
private noncomputable abbrev toAmbientSquare
    {F : S₂ ⟶ S₁} {G : T₁ ⟶ S₁}
    (P : BicategoricalTwoCommutativeSquare F G) :
    BicategoricalTwoCommutativeSquare F.toHom G.toHom where
  obj := P.obj.obj
  p := P.p.toHom
  q := P.q.toHom
  ψ :=
    Functor.mapIso (((stackInGroupoidsOverSubTwoCategory J).hom P.obj S₁).inclusion) P.ψ

/-- Helper for Lemma 8.6.10: forget a morphism into the canonical stack pullback square to the
ambient fibred-in-groupoids square. -/
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

/-- Helper for Lemma 8.6.10: rewrap an ambient morphism into the explicit pullback square as a
square morphism of stacks in groupoids. -/
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

/-- Helper for Lemma 8.6.10: forget a `2`-morphism between square maps to the corresponding
ambient `2`-morphism. -/
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

/-- Helper for Lemma 8.6.10: an ambient `2`-morphism into the explicit pullback square lifts back
to the owner square of stacks in groupoids. -/
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

/-- Helper for Lemma 8.6.10: an isomorphism of stack morphisms induces an isomorphism of the
underlying based functors over the base site. -/
private noncomputable def basedFunctorIsoOfStackOwnerIso
    {X Y : StackInGroupoidsOver J}
    {H K : X ⟶ Y}
    (e : H ≅ K) :
    H.toBasedFunctor ≅ K.toBasedFunctor :=
  FibredInGroupoidsMor.basedFunctorIsoOfOwnerIso
    (Functor.mapIso (((stackInGroupoidsOverSubTwoCategory J).hom X Y).inclusion) e)

/-- Helper for Lemma 8.6.10: an isomorphism of underlying based functors lifts to an isomorphism
of stack morphisms. -/
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

/-- Helper for Lemma 8.6.10: forgetting the lifted stack isomorphism recovers the original
based-functor isomorphism. -/
private theorem stackOwnerIsoOfBasedFunctorIso_hom_hom_hom_hom_hom_hom_hom
    {X Y : StackInGroupoidsOver J}
    {H K : X ⟶ Y}
    (e : H.toBasedFunctor ≅ K.toBasedFunctor) :
    (stackOwnerIsoOfBasedFunctorIso (J := J) e).hom.hom.hom.hom.hom.hom.hom = e.hom := by
  rfl

/-- Helper for Lemma 8.6.10: every `2`-morphism between stack morphisms is invertible because its
components live in groupoid fibers. -/
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

/-- Helper for Lemma 8.6.10: the canonical stack pullback square is bicategorically final because
its ambient fibred-in-groupoids square already satisfies the Chapter 4 pullback universal
property. -/
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
        -- Forget to the ambient terminal square where uniqueness is already known.
        apply BicategoricalTwoCommutativeSquare.TwoHom.ext
        repeat first | apply InducedWideCategory.Hom.ext | apply InducedCategory.Hom.ext
        exact congrArg (fun ζ ↦ ζ.hom.hom.hom.hom.hom)
          (htarget.hom_ext
            (toAmbientSquareTwoHom (J := J) η)
            (Limits.terminal.from (toAmbientSquareHom (J := J) u)))))).hasTerminal

/-- Helper for Lemma 8.6.10: two chosen comparison morphisms between final squares produce unit
and counit isomorphisms on the corresponding apex maps. -/
private noncomputable def comparison_apex_unit_counit_of_two_final_squares
    {P Q : BicategoricalTwoCommutativeSquare F G}
    [Bicategory.IsFinal P] [Bicategory.IsFinal Q]
    (u : Q ⟶ P)
    (v : P ⟶ Q) :
    ((𝟙 Q.obj : Q.obj ⟶ Q.obj) ≅ u.hom ≫ v.hom) ×
      (v.hom ≫ u.hom ≅ (𝟙 P.obj : P.obj ⟶ P.obj)) := by
  -- Compare the unique endomorphisms in the two terminal hom-categories.
  let ηsq : (𝟙 Q : Q ⟶ Q) ≅ u ≫ v := by
    exact asIso ((Bicategory.IsFinal.homIsTerminal (x := Q) (y := Q) (f := u ≫ v)).from (𝟙 Q))
  let εsq : v ≫ u ≅ (𝟙 P : P ⟶ P) := by
    exact asIso ((Bicategory.IsFinal.homIsTerminal (x := P) (y := P) (f := 𝟙 P)).from (v ≫ u))
  -- Project these square isomorphisms to the apex morphisms.
  refine ⟨?_, ?_⟩
  · exact asIso ηsq.hom.hom
  · exact asIso εsq.hom.hom

/-- Helper for Lemma 8.6.10: any comparison between two final pullback squares is an equivalence
over the base on apex objects. -/
private theorem apex_isEquivalenceOverBase_of_two_final_squares
    (P Q : BicategoricalTwoCommutativeSquare F G)
    (hP : Bicategory.IsFinal P)
    (hQ : Bicategory.IsFinal Q)
    (u : Q ⟶ P) :
    u.hom.IsEquivalenceOverBase := by
  letI : Bicategory.IsFinal P := hP
  letI : Bicategory.IsFinal Q := hQ
  let v : P ⟶ Q := ⊤_ (P ⟶ Q)
  obtain ⟨η, ε⟩ :=
    comparison_apex_unit_counit_of_two_final_squares
      (J := J) (F := F) (G := G) u v
  -- Package the chosen comparison apex map with the terminally induced quasi-inverse.
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

/-- Helper for Lemma 8.6.10: a faithful functor reflects thinness from the target category. -/
private theorem isThin_of_faithful
    {A B : Type*} [Category A] [Category B]
    (H : A ⥤ B) [H.Faithful] [Quiver.IsThin B] :
    Quiver.IsThin A := by
  -- Any two source morphisms have the same image in the thin target, and faithfulness reflects
  -- that equality.
  intro a b
  refine ⟨?_⟩
  intro φ ψ
  exact H.map_injective (Subsingleton.elim _ _)

/-- Helper for Lemma 8.6.10: mapping a strongly cartesian lift over `f` along a fibred-category
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

/-- Helper for Lemma 8.6.10: for a fibred morphism `H`, the chosen pullback of `H(x)` is
canonically isomorphic to the image under `H` of the chosen pullback of `x`. -/
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
  -- Transport the chosen source pullback lift across `H`.
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
  -- The comparison lives in the fiber over `V`, so package its underlying isomorphism there.
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
        -- Forget to the total category, where this is just `e.hom_inv_id`.
        apply Functor.Fiber.hom_ext
        change e.hom ≫ e.inv = 𝟙 _
        exact e.hom_inv_id
      inv_hom_id := by
        -- The inverse identity is the same calculation on the underlying total-category morphism.
        apply Functor.Fiber.hom_ext
        change e.inv ≫ e.hom = 𝟙 _
        exact e.inv_hom_id }

/-- Helper for Lemma 8.6.10: full faithfulness of the left fiber functor lifts an endomorphism of
the right pullback component to an endomorphism of the whole categorical pullback object. -/
private theorem categorical_pullback_endomorphism_of_fullyFaithful_left
    {U : C}
    (hFFU : Nonempty ((F.toBasedFunctor.fiberFunctor U).FullyFaithful))
    (P : Limits.CategoricalPullback
      (F.toBasedFunctor.fiberFunctor U)
      (G.toBasedFunctor.fiberFunctor U))
    (γ : P.snd ⟶ P.snd) :
    ∃ δ : P ⟶ P, δ.snd = γ := by
  classical
  let hff := Classical.choice hFFU
  let target :
      (F.toBasedFunctor.fiberFunctor U).obj P.fst ⟶
        (F.toBasedFunctor.fiberFunctor U).obj P.fst :=
    P.iso.hom ≫ (G.toBasedFunctor.fiberFunctor U).map γ ≫ P.iso.inv
  obtain ⟨α, hα⟩ := (hff.map_bijective P.fst P.fst).2 target
  refine ⟨{ fst := α, snd := γ, w := ?_ }, rfl⟩
  -- Compare the left-component image with the pullback compatibility target.
  calc
    (F.toBasedFunctor.fiberFunctor U).map α ≫ P.iso.hom =
        target ≫ P.iso.hom := by simp [hα]
    _ = P.iso.hom ≫ (G.toBasedFunctor.fiberFunctor U).map γ := by
      simp [target, Category.assoc]

/-- Helper for Lemma 8.6.10: applying a stack morphism to a chosen pullback object is canonically
isomorphic to the chosen pullback of the image object. -/
private noncomputable def fiber_pullback_comparison_iso
    {U V : C} (f : V ⟶ U) (y : T₁.p.Fiber U) :
    (((canonicalFiberPseudofunctor S₁.p).map f.op.toLoc).toFunctor.obj
        ((G.toBasedFunctor.fiberFunctor U).obj y)) ≅
      (G.toBasedFunctor.fiberFunctor V).obj
        (((canonicalFiberPseudofunctor T₁.p).map f.op.toLoc).toFunctor.obj y) := by
  -- Route correction: rebuild the canonical pullback-comparison isomorphism directly from the
  -- chosen strongly cartesian lifts, matching the source pullback-comparison argument.
  simpa using
    pullbackComparison
      (H := G.toFibredCategoryMor) f y

/-- Helper for Lemma 8.6.10: the right projection from the canonical stack pullback is locally
essentially surjective on objects once `F` is. -/
private theorem canonical_pullback_right_projection_locallyEssentiallySurjective
    (hFess : F.LocallyEssentiallySurjectiveOnObjects) :
    (stack_pullback_square (J := J) F G).q.LocallyEssentiallySurjectiveOnObjects := by
  -- Lift the local essential-image witnesses for `F` on `G(y)` into the canonical pullback fiber.
  intro U y
  obtain ⟨S, hS⟩ := hFess U
    ((((show T₁ ⟶ S₁ from G).toBasedFunctor).fiberFunctor U).obj y)
  refine ⟨S, ?_⟩
  intro I
  obtain ⟨x, hx⟩ := hS I
  let e₀ :
      ((StackInGroupoidsOver.Hom.toBasedFunctor F).fiberFunctor I.Y).obj x ≅
        (((canonicalFiberPseudofunctor S₁.p).map I.f.op.toLoc).toFunctor.obj
          ((((show T₁ ⟶ S₁ from G).toBasedFunctor).fiberFunctor U).obj y)) :=
    Classical.choice hx
  let P :
      Limits.CategoricalPullback
        ((StackInGroupoidsOver.Hom.toBasedFunctor F).fiberFunctor I.Y)
        (((show T₁ ⟶ S₁ from G).toBasedFunctor).fiberFunctor I.Y) :=
    { fst := x
      snd := (((canonicalFiberPseudofunctor T₁.p).map I.f.op.toLoc).toFunctor.obj y)
      iso := e₀ ≪≫ fiber_pullback_comparison_iso (G := G) I.f y }
  let e := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
    F.toBasedFunctor G.toBasedFunctor I.Y
  refine ⟨e.inverse.obj P, ?_⟩
  -- Compare the right projection on the canonical pullback fiber with `π₂` through the standard
  -- equivalence between fibers of the explicit pullback and pullbacks of fibers.
  change Nonempty
    ((BasedFunctor.fiberFunctor
        (CategoryOver.explicitTwoFibreProductRightProjection F.toBasedFunctor G.toBasedFunctor)
        I.Y).obj (e.inverse.obj P) ≅ _)
  let hπ₂ :
      e.functor ⋙
          Limits.CategoricalPullback.π₂
            ((StackInGroupoidsOver.Hom.toBasedFunctor F).fiberFunctor I.Y)
            ((((show T₁ ⟶ S₁ from G).toBasedFunctor).fiberFunctor I.Y)) =
        BasedFunctor.fiberFunctor
          (CategoryOver.explicitTwoFibreProductRightProjection F.toBasedFunctor G.toBasedFunctor)
          I.Y :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₂
      F.toBasedFunctor G.toBasedFunctor I.Y
  refine ⟨(eqToIso (congrArg (fun H ↦ H.obj (e.inverse.obj P)) hπ₂.symm)) ≪≫ ?_⟩
  simpa [P] using
    Functor.mapIso
      (Limits.CategoricalPullback.π₂
        ((StackInGroupoidsOver.Hom.toBasedFunctor F).fiberFunctor I.Y)
        ((((show T₁ ⟶ S₁ from G).toBasedFunctor).fiberFunctor I.Y)))
      (e.counitIso.app P)

/-- Helper for Lemma 8.6.10: a vertical endomorphism is the identity once all of its pullbacks to
some cover become the identity. -/
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
  -- The canonical descent functor detects equality of vertical endomorphisms in a stack.
  apply Φ.map_injective
  ext I
  have hmap_id_I :
      (Fp.map I.f.op.toLoc).toFunctor.map (𝟙 y) = 𝟙 _ := by
    exact ((Fp.map I.f.op.toLoc).toFunctor.map_id y)
  exact (hγ I).trans hmap_id_I.symm

/-- Helper for Lemma 8.6.10: every vertical automorphism of an object of `T₁` becomes the
identity on a cover by lifting that object to the canonical pullback and using the setoidness of
the pullback fiber. -/
private theorem canonical_pullback_coverwise_identity_of_vertical_automorphism
    (hF : Nonempty F.toBasedFunctor.FullyFaithful)
    (hFess : F.LocallyEssentiallySurjectiveOnObjects)
    [IsStackInSetoids J (twoFibreProduct F G).p]
    {U : C} (y : T₁.p.Fiber U) (γ : y ⟶ y) :
    ∃ S : J.Cover U,
      ∀ I : S.Arrow,
        (((canonicalFiberPseudofunctor T₁.p).map I.f.op.toLoc).toFunctor.map γ) = 𝟙 _ := by
  classical
  -- Choose a cover on which `G(y)` comes from the left leg of the pullback.
  obtain ⟨S, hS⟩ := hFess U ((G.toBasedFunctor.fiberFunctor U).obj y)
  refine ⟨S, ?_⟩
  intro I
  obtain ⟨x, hx⟩ := hS I
  let e₀ :
      (F.toBasedFunctor.fiberFunctor I.Y).obj x ≅
        (((canonicalFiberPseudofunctor S₁.p).map I.f.op.toLoc).toFunctor.obj
          ((G.toBasedFunctor.fiberFunctor U).obj y)) :=
    Classical.choice hx
  let e :
      (F.toBasedFunctor.fiberFunctor I.Y).obj x ≅
        (G.toBasedFunctor.fiberFunctor I.Y).obj
          (((canonicalFiberPseudofunctor T₁.p).map I.f.op.toLoc).toFunctor.obj y) :=
    e₀ ≪≫ fiber_pullback_comparison_iso (G := G) I.f y
  let P :
      Limits.CategoricalPullback
        (F.toBasedFunctor.fiberFunctor I.Y)
        (G.toBasedFunctor.fiberFunctor I.Y) :=
    { fst := x
      snd := (((canonicalFiberPseudofunctor T₁.p).map I.f.op.toLoc).toFunctor.obj y)
      iso := e }
  have hFFI : Nonempty ((F.toBasedFunctor.fiberFunctor I.Y).FullyFaithful) := by
    -- Fiberwise full faithfulness is exactly the Chapter 4 owner criterion.
    simpa using
      (FibredCategoryMor.fullyFaithful_iff_fiberwise (F := F.toFibredCategoryMor)).1 hF I.Y
  let γI :
      (((canonicalFiberPseudofunctor T₁.p).map I.f.op.toLoc).toFunctor.obj y) ⟶
        (((canonicalFiberPseudofunctor T₁.p).map I.f.op.toLoc).toFunctor.obj y) :=
    (((canonicalFiberPseudofunctor T₁.p).map I.f.op.toLoc).toFunctor.map γ)
  obtain ⟨δ, hδsnd⟩ :=
    categorical_pullback_endomorphism_of_fullyFaithful_left
      (F := F) (G := G) hFFI P γI
  have hthinP :
      Quiver.IsThin
        (Limits.CategoricalPullback
          (F.toBasedFunctor.fiberFunctor I.Y)
          (G.toBasedFunctor.fiberFunctor I.Y)) := by
    let eFib := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      F.toBasedFunctor G.toBasedFunctor I.Y
    have hthinPullback :
        Quiver.IsThin
          ((CategoryOver.explicitTwoFibreProduct F.toBasedFunctor G.toBasedFunctor).p.Fiber I.Y) := by
      change Quiver.IsThin ((stack_pullback (J := J) F G).p.Fiber I.Y)
      infer_instance
    letI :
        Quiver.IsThin
          ((CategoryOver.explicitTwoFibreProduct F.toBasedFunctor G.toBasedFunctor).p.Fiber I.Y) :=
      hthinPullback
    letI : eFib.inverse.Faithful := by infer_instance
    exact isThin_of_faithful eFib.inverse
  letI :
      Quiver.IsThin
        (Limits.CategoricalPullback
          (F.toBasedFunctor.fiberFunctor I.Y)
          (G.toBasedFunctor.fiberFunctor I.Y)) := hthinP
  have hδid : δ = 𝟙 P := Subsingleton.elim _ _
  -- Read the identity back from the second pullback projection.
  calc
    (((canonicalFiberPseudofunctor T₁.p).map I.f.op.toLoc).toFunctor.map γ) = δ.snd := hδsnd.symm
    _ = 𝟙 _ := by
      simpa using congrArg Limits.CategoricalPullback.Hom.snd hδid

/-
Domain-style sampling for Lemma 8.6.10:
- primary domain: stacks in groupoids/setoids over a site, together with canonical and arbitrary
  bicategorical `2`-fibre products;
- sampled owner-level declarations:
  `IsStackInSetoids`,
  `StackInGroupoidsOver.twoFibreProduct`,
  `StackInGroupoidsOver.twoFibreProductSquare`,
  `StackInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`,
  `StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects`,
  `BicategoricalTwoCommutativeSquare` and `Bicategory.IsFinal`;
- best owner abstraction: this lemma should be stated over the ambient stack morphisms
  `F : S₂ ⟶ S₁` and `G : T₁ ⟶ S₁`, with the canonical
  Chapter 8 pullback owner `StackInGroupoidsOver.twoFibreProduct F G` and its final square
  `StackInGroupoidsOver.twoFibreProductSquare F G` as the core model; arbitrary
  `2`-cartesian squares are then treated only as a bridge/view;
- primitive data: the stack morphisms `F` and `G`, the propositional full-faithfulness and local
  essential-surjectivity hypotheses on `F`, and the stack-in-setoids hypothesis on the canonical
  stack pullback apex `(twoFibreProduct F G).p`;
- derived API: transport of the explicit-pullback statement across a square carrying the owner
  predicate `Bicategory.IsFinal`.

Source/core/bridge triage:
- `source-facing`: the two descent lemmas below;
- `core/canonical`: `IsStackInSetoids`, `StackInGroupoidsOver.twoFibreProduct`,
  `StackInGroupoidsOver.twoFibreProductSquare`,
  `StackInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`,
  `StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects`, and `Bicategory.IsFinal`;
- `bridge/view`: the arbitrary-square theorem as transport of the explicit-pullback form. -/

-- Proof sketch: by Categories, Lemma `4.32.3`, the `2`-cartesian square may be replaced by the
-- explicit pullback `S₂ ×[S₁] T₁`, whose objects over `U` are triples `(x, y, f)` with
-- `x ∈ (S₂)_U`, `y ∈ (T₁)_U`, and `f : F(x) ≅ G(y)`. The local essential-image hypothesis on `F`
-- lets one lift any object `y` of `T₁` locally to an object of this pullback. Full faithfulness
-- of `F` makes the map on automorphism sheaves from the pullback object to `y` surjective, while
-- the pullback being a stack in setoids makes the source automorphism sheaf trivial. Hence every
-- automorphism sheaf in `T₁` is trivial, so each fiber of `T₁` is a setoid.
/-- Pullback-owner form of Lemma 8.6.10: it suffices to assume that the Chapter 8 canonical
stack pullback `twoFibreProduct F G` is a stack in setoids. The arbitrary-square form is obtained
by transporting this statement across any final square over `F` and `G`. -/
theorem isStackInSetoids_of_fullyFaithful_locallyEssentiallySurjective_pullback
    (hF : Nonempty F.toBasedFunctor.FullyFaithful)
    (hFess : F.LocallyEssentiallySurjectiveOnObjects)
    [IsStackInSetoids J (twoFibreProduct F G).p] :
    IsStackInSetoids J T₁.p := by
  letI : IsFibredInSetoids T₁.p := by
    refine
      (isFibredInSetoids_iff_isFibredInGroupoids_and_fiber_subsingleton_aut T₁.p).2
        ⟨inferInstance, ?_⟩
    intro U y
    have hAut : ∀ α : Aut y, α.hom = 𝟙 y := by
      intro α
      -- Every automorphism is locally trivial after lifting to the canonical pullback.
      obtain ⟨S, hS⟩ :=
        canonical_pullback_coverwise_identity_of_vertical_automorphism
          (J := J) (F := F) (G := G) hF hFess y α.hom
      exact vertical_endomorphism_eq_id_of_coverwise_identity (J := J) (T₁ := T₁) S hS
    -- Fiberwise trivial automorphisms are exactly the setoid criterion.
    exact ⟨fun α β ↦ by
      apply Iso.ext
      simpa using (hAut α).trans (hAut β).symm⟩
  exact inferInstance

/-- Helper for Lemma 8.6.10: the local explicit pullback square has apex projection equal to the
local pullback owner projection used in the pullback-owner theorem. -/
private theorem stack_pullback_square_obj_p_eq_pullback_owner :
    (stack_pullback_square (J := J) F G).obj.p = (stack_pullback (J := J) F G).p := by
  -- The square was built from the local owner `stack_pullback`, so its apex projection is
  -- definitionally the pullback-owner projection.
  rfl

/-- Helper for Lemma 8.6.10: any final square over `F` and `G` transports stack-in-setoids to the
local explicit pullback square already proved final in this file. -/
private theorem stack_pullback_square_isStackInSetoids_of_twoCartesian
    (P : BicategoricalTwoCommutativeSquare F G)
    (hcart : Bicategory.IsFinal P)
    [IsStackInSetoids J P.obj.p] :
    IsStackInSetoids J (stack_pullback_square (J := J) F G).obj.p := by
  -- Route correction: stay with the source-faithful pullback-owner argument, but use the local
  -- explicit pullback square already proved final in this file instead of importing an
  -- unavailable compiled Chapter 8.5.6 wrapper.
  let Q : BicategoricalTwoCommutativeSquare F G :=
    stack_pullback_square (J := J) F G
  letI : Bicategory.IsFinal P := hcart
  letI : Bicategory.IsFinal Q :=
    stack_pullback_square_isTwoFibreProduct (J := J) (F := F) (G := G)
  let u : Q ⟶ P := ⊤_ _
  have hu : u.hom.IsEquivalenceOverBase :=
    apex_isEquivalenceOverBase_of_two_final_squares
      (J := J) (F := F) (G := G) P Q hcart inferInstance u
  -- Move the stack-in-setoids hypothesis back along the apex equivalence over the base site.
  exact
    (isStackInSetoids_iff_of_equivalence_over_base
      (J := J) (p₁ := Q.obj.p) (p₂ := P.obj.p) u.hom.toBasedFunctor hu).2 inferInstance

/-- Helper for Lemma 8.6.10: the local explicit pullback owner is a stack in setoids once any
final square over `F` and `G` has stack-in-setoids apex. -/
private theorem pullback_owner_isStackInSetoids_of_twoCartesian
    (P : BicategoricalTwoCommutativeSquare F G)
    (hcart : Bicategory.IsFinal P)
    [IsStackInSetoids J P.obj.p] :
    IsStackInSetoids J (stack_pullback (J := J) F G).p := by
  -- Rewrite the final local square back to the local owner consumed by the pullback theorem.
  simpa [stack_pullback_square_obj_p_eq_pullback_owner (J := J) (F := F) (G := G)]
    using
      stack_pullback_square_isStackInSetoids_of_twoCartesian F G P hcart

/-- Lemma 8.6.10: for any bicategorical `2`-fibre product square `P` of stacks in groupoids over
`(C, J)` with left leg `F` and right leg `G`, if `F` is fully faithful and locally essentially
surjective on objects of the fibers, and if the apex of `P` is a stack in setoids, then `T₁` is
a stack in setoids. This is the bridge/view form of the pullback-owner theorem above, transported
from the canonical final square `twoFibreProductSquare F G`. -/
theorem isStackInSetoids_of_twoCartesian_of_fullyFaithful_locallyEssentiallySurjective
    (hF : Nonempty F.toBasedFunctor.FullyFaithful)
    (hFess : F.LocallyEssentiallySurjectiveOnObjects)
    (P : BicategoricalTwoCommutativeSquare F G)
    (hcart : Bicategory.IsFinal P)
    [IsStackInSetoids J P.obj.p] :
    IsStackInSetoids J T₁.p := by
  let Q : BicategoricalTwoCommutativeSquare F G :=
    stack_pullback_square (J := J) (F := F) (G := G)
  letI : Bicategory.IsFinal P := hcart
  letI : Bicategory.IsFinal Q := stack_pullback_square_isTwoFibreProduct F G
  let u : Q ⟶ P := ⊤_ _
  have hu : u.hom.IsEquivalenceOverBase :=
    apex_isEquivalenceOverBase_of_two_final_squares
      (J := J) (F := F) (G := G) P Q hcart inferInstance u
  letI : IsStackInSetoids J Q.obj.p :=
    (isStackInSetoids_iff_of_equivalence_over_base
      (J := J) (p₁ := Q.obj.p) (p₂ := P.obj.p) u.hom.toBasedFunctor hu).2 inferInstance
  have hPullback : IsStackInSetoids J (stack_pullback F G).p := by
    -- Rewrite the transported square-apex instance to the exact pullback-owner projection.
    simpa [Q, stack_pullback_square_obj_p_eq_pullback_owner (J := J) (F := F) (G := G)]
      using (inferInstance : IsStackInSetoids J Q.obj.p)
  letI : IsStackInSetoids J (stack_pullback F G).p := hPullback
  -- With the pullback owner in setoids, the source-faithful pullback theorem closes the goal.
  exact isStackInSetoids_of_fullyFaithful_locallyEssentiallySurjective_pullback F G hF hFess

end

end CategoryTheory
