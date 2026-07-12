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

/-- Helper for Lemma 8.11.5: an isomorphism of stack morphisms gives the corresponding
isomorphism of underlying based functors over the site. -/
noncomputable def basedFunctorIsoOfStackHomIso
    {A B : StackInGroupoidsOver J} {F G : A ⟶ B} (e : F ≅ G) :
    F.toBasedFunctor ≅ G.toBasedFunctor :=
  FibredInGroupoidsMor.basedFunctorIsoOfOwnerIso
    (Functor.mapIso (((stackInGroupoidsOverSubTwoCategory J).hom A B).inclusion) e)

/-- Helper for Lemma 8.11.5: the forward component of a stack-morphism isomorphism is vertical
on each fiber. -/
theorem basedFunctorIsoOfStackHomIso_hom_isHomLift
    {A B : StackInGroupoidsOver J} {F G : A ⟶ B} (e : F ≅ G)
    {U : C} (x : A.p.Fiber U) :
    B.p.IsHomLift (𝟙 U) ((basedFunctorIsoOfStackHomIso (J := J) e).hom.app x.1) := by
  simpa using BasedNatTrans.isHomLift (basedFunctorIsoOfStackHomIso (J := J) e).hom x.2

/-- Helper for Lemma 8.11.5: the inverse component of a stack-morphism isomorphism is vertical
on each fiber. -/
theorem basedFunctorIsoOfStackHomIso_inv_isHomLift
    {A B : StackInGroupoidsOver J} {F G : A ⟶ B} (e : F ≅ G)
    {U : C} (x : A.p.Fiber U) :
    B.p.IsHomLift (𝟙 U) ((basedFunctorIsoOfStackHomIso (J := J) e).inv.app x.1) := by
  simpa using BasedNatTrans.isHomLift (basedFunctorIsoOfStackHomIso (J := J) e).inv x.2

/-- Helper for Lemma 8.11.5: the explicit fiber maps induced by a stack-morphism isomorphism
compose to the identity in the forward direction. -/
theorem fiberIsoOfStackHomIso_hom_inv_id
    {A B : StackInGroupoidsOver J} {F G : A ⟶ B} (e : F ≅ G)
    {U : C} (x : A.p.Fiber U) :
    let eBased := basedFunctorIsoOfStackHomIso (J := J) e
    letI : B.p.IsHomLift (𝟙 U) (eBased.hom.app x.1) :=
      basedFunctorIsoOfStackHomIso_hom_isHomLift (J := J) e x
    letI : B.p.IsHomLift (𝟙 U) (eBased.inv.app x.1) :=
      basedFunctorIsoOfStackHomIso_inv_isHomLift (J := J) e x
    Functor.Fiber.homMk B.p U (eBased.hom.app x.1) ≫
      Functor.Fiber.homMk B.p U (eBased.inv.app x.1) =
        𝟙 ((F.fiberFunctor U).obj x) := by
  dsimp
  apply Functor.Fiber.hom_ext
  exact NatTrans.congr_app
    (congrArg BasedNatTrans.toNatTrans
      (basedFunctorIsoOfStackHomIso (J := J) e).hom_inv_id) x.1

/-- Helper for Lemma 8.11.5: the explicit fiber maps induced by a stack-morphism isomorphism
compose to the identity in the inverse direction. -/
theorem fiberIsoOfStackHomIso_inv_hom_id
    {A B : StackInGroupoidsOver J} {F G : A ⟶ B} (e : F ≅ G)
    {U : C} (x : A.p.Fiber U) :
    let eBased := basedFunctorIsoOfStackHomIso (J := J) e
    letI : B.p.IsHomLift (𝟙 U) (eBased.hom.app x.1) :=
      basedFunctorIsoOfStackHomIso_hom_isHomLift (J := J) e x
    letI : B.p.IsHomLift (𝟙 U) (eBased.inv.app x.1) :=
      basedFunctorIsoOfStackHomIso_inv_isHomLift (J := J) e x
    Functor.Fiber.homMk B.p U (eBased.inv.app x.1) ≫
      Functor.Fiber.homMk B.p U (eBased.hom.app x.1) =
        𝟙 ((G.fiberFunctor U).obj x) := by
  dsimp
  apply Functor.Fiber.hom_ext
  exact NatTrans.congr_app
    (congrArg BasedNatTrans.toNatTrans
      (basedFunctorIsoOfStackHomIso (J := J) e).inv_hom_id) x.1

/-- Helper for Lemma 8.11.5: the component of an isomorphism of stack morphisms gives an
isomorphism in each fiber. -/
theorem fiberIsoOfStackHomIso_nonempty
    {A B : StackInGroupoidsOver J} {F G : A ⟶ B} (e : F ≅ G)
    {U : C} (x : A.p.Fiber U) :
    Nonempty ((F.fiberFunctor U).obj x ≅ (G.fiberFunctor U).obj x) := by
  let eBased := basedFunctorIsoOfStackHomIso (J := J) e
  letI : B.p.IsHomLift (𝟙 U) (eBased.hom.app x.1) := by
    simpa using BasedNatTrans.isHomLift eBased.hom x.2
  letI : B.p.IsHomLift (𝟙 U) (eBased.inv.app x.1) := by
    simpa using BasedNatTrans.isHomLift eBased.inv x.2
  refine
    ⟨{ hom := Functor.Fiber.homMk B.p U (eBased.hom.app x.1)
       inv := Functor.Fiber.homMk B.p U (eBased.inv.app x.1)
       hom_inv_id := by
         -- Forget to the total category, where this is the componentwise inverse identity.
         apply Functor.Fiber.hom_ext
         exact NatTrans.congr_app
           (congrArg BasedNatTrans.toNatTrans eBased.hom_inv_id) x.1
       inv_hom_id := by
         -- The inverse identity is again checked after forgetting the fiber packaging.
         apply Functor.Fiber.hom_ext
         exact NatTrans.congr_app
           (congrArg BasedNatTrans.toNatTrans eBased.inv_hom_id) x.1 }⟩

/-- Helper for Lemma 8.11.5: the chosen fiber isomorphism induced by an isomorphism of stack
morphisms. -/
noncomputable def fiberIsoOfStackHomIso
    {A B : StackInGroupoidsOver J} {F G : A ⟶ B} (e : F ≅ G)
    {U : C} (x : A.p.Fiber U) :
    (F.fiberFunctor U).obj x ≅ (G.fiberFunctor U).obj x :=
  let eBased := basedFunctorIsoOfStackHomIso (J := J) e
  letI : B.p.IsHomLift (𝟙 U) (eBased.hom.app x.1) :=
    basedFunctorIsoOfStackHomIso_hom_isHomLift (J := J) e x
  letI : B.p.IsHomLift (𝟙 U) (eBased.inv.app x.1) :=
    basedFunctorIsoOfStackHomIso_inv_isHomLift (J := J) e x
  { hom := Functor.Fiber.homMk B.p U (eBased.hom.app x.1)
    inv := Functor.Fiber.homMk B.p U (eBased.inv.app x.1)
    hom_inv_id := fiberIsoOfStackHomIso_hom_inv_id (J := J) e x
    inv_hom_id := fiberIsoOfStackHomIso_inv_hom_id (J := J) e x }

/-- Helper for Lemma 8.11.5: the forward fiber isomorphism induced by a stack-morphism
isomorphism has the expected underlying component. -/
theorem fiberIsoOfStackHomIso_hom_val
    {A B : StackInGroupoidsOver J} {F G : A ⟶ B} (e : F ≅ G)
    {U : C} (x : A.p.Fiber U) :
    (fiberIsoOfStackHomIso (J := J) e x).hom.1 =
      (basedFunctorIsoOfStackHomIso (J := J) e).hom.app x.1 := by
  letI : B.p.IsHomLift (𝟙 U) ((basedFunctorIsoOfStackHomIso (J := J) e).hom.app x.1) :=
    basedFunctorIsoOfStackHomIso_hom_isHomLift (J := J) e x
  dsimp [fiberIsoOfStackHomIso]
  exact
    Functor.Fiber.fiberInclusion_homMk B.p U
      ((basedFunctorIsoOfStackHomIso (J := J) e).hom.app x.1)

/-- Helper for Lemma 8.11.5: the inverse fiber isomorphism induced by a stack-morphism
isomorphism has the expected underlying component. -/
theorem fiberIsoOfStackHomIso_inv_val
    {A B : StackInGroupoidsOver J} {F G : A ⟶ B} (e : F ≅ G)
    {U : C} (x : A.p.Fiber U) :
    (fiberIsoOfStackHomIso (J := J) e x).inv.1 =
      (basedFunctorIsoOfStackHomIso (J := J) e).inv.app x.1 := by
  letI : B.p.IsHomLift (𝟙 U) ((basedFunctorIsoOfStackHomIso (J := J) e).inv.app x.1) :=
    basedFunctorIsoOfStackHomIso_inv_isHomLift (J := J) e x
  dsimp [fiberIsoOfStackHomIso]
  exact
    Functor.Fiber.fiberInclusion_homMk B.p U
      ((basedFunctorIsoOfStackHomIso (J := J) e).inv.app x.1)

/-- Helper for Lemma 8.11.5: a `2`-morphism of stack morphisms gives an isomorphism on every
fiber object, since stack fibers are groupoids. -/
theorem fiberIsoOfStackHom_nonempty
    {A B : StackInGroupoidsOver J} {F G : A ⟶ B} (τ : F ⟶ G)
    {U : C} (x : A.p.Fiber U) :
    Nonempty ((F.fiberFunctor U).obj x ≅ (G.fiberFunctor U).obj x) := by
  let τBased : F.toBasedFunctor ⟶ G.toBasedFunctor := τ.hom.hom.hom.hom.hom.hom
  letI : B.p.IsHomLift (𝟙 U) (τBased.app x.1) := by
    simpa using BasedNatTrans.isHomLift τBased x.2
  let τFiber : (F.fiberFunctor U).obj x ⟶ (G.fiberFunctor U).obj x :=
    Functor.Fiber.homMk B.p U (τBased.app x.1)
  haveI : IsIso τFiber :=
    IsFibredInGroupoids.hom_isIso (p := B.p) (U := U) τFiber
  -- Promote the vertical component to an isomorphism inside the fiber groupoid.
  exact ⟨asIso τFiber⟩

/-- Helper for Lemma 8.11.5: a chosen fiber isomorphism induced by a `2`-morphism of stack
morphisms. -/
noncomputable def fiberIsoOfStackHom
    {A B : StackInGroupoidsOver J} {F G : A ⟶ B} (τ : F ⟶ G)
    {U : C} (x : A.p.Fiber U) :
    (F.fiberFunctor U).obj x ≅ (G.fiberFunctor U).obj x :=
  let τBased : F.toBasedFunctor ⟶ G.toBasedFunctor := τ.hom.hom.hom.hom.hom.hom
  letI : B.p.IsHomLift (𝟙 U) (τBased.app x.1) :=
    BasedNatTrans.isHomLift τBased x.2
  let τFiber : (F.fiberFunctor U).obj x ⟶ (G.fiberFunctor U).obj x :=
    Functor.Fiber.homMk B.p U (τBased.app x.1)
  letI : IsIso τFiber :=
    IsFibredInGroupoids.hom_isIso (p := B.p) (U := U) τFiber
  asIso τFiber

/-- Helper for Lemma 8.11.5: the forward fiber isomorphism induced by a `2`-morphism has the
expected underlying component. -/
theorem fiberIsoOfStackHom_hom_val
    {A B : StackInGroupoidsOver J} {F G : A ⟶ B} (τ : F ⟶ G)
    {U : C} (x : A.p.Fiber U) :
    (fiberIsoOfStackHom (J := J) τ x).hom.1 =
      (τ.hom.hom.hom.hom.hom.hom : F.toBasedFunctor ⟶ G.toBasedFunctor).app x.1 := by
  let τBased : F.toBasedFunctor ⟶ G.toBasedFunctor := τ.hom.hom.hom.hom.hom.hom
  letI : B.p.IsHomLift (𝟙 U) (τBased.app x.1) :=
    BasedNatTrans.isHomLift τBased x.2
  let τFiber : (F.fiberFunctor U).obj x ⟶ (G.fiberFunctor U).obj x :=
    Functor.Fiber.homMk B.p U (τBased.app (x.1))
  haveI : IsIso τFiber :=
    IsFibredInGroupoids.hom_isIso (p := B.p) (U := U) τFiber
  change (asIso τFiber).hom.1 = τBased.app (x.1)
  change τFiber.1 = τBased.app (x.1)
  exact Functor.Fiber.fiberInclusion_homMk B.p U (τBased.app (x.1))

/-- Helper for Lemma 8.11.5: the fiber isomorphisms induced by a `2`-morphism are natural on
vertical morphisms in the source fiber. -/
theorem fiberIsoOfStackHom_hom_naturality
    {A B : StackInGroupoidsOver J} {F G : A ⟶ B} (τ : F ⟶ G)
    {U : C} {x y : A.p.Fiber U} (φ : x ⟶ y) :
    (F.fiberFunctor U).map φ ≫ (fiberIsoOfStackHom (J := J) τ y).hom =
      (fiberIsoOfStackHom (J := J) τ x).hom ≫ (G.fiberFunctor U).map φ := by
  -- Forget to the total category, where this is just naturality of the underlying based
  -- natural transformation.
  apply Functor.Fiber.hom_ext
  let τBased : F.toBasedFunctor ⟶ G.toBasedFunctor := τ.hom.hom.hom.hom.hom.hom
  rw [Functor.map_comp, Functor.map_comp]
  change
    F.toBasedFunctor.toFunctor.map φ.1 ≫ τBased.toNatTrans.app y.1 =
      τBased.toNatTrans.app x.1 ≫ G.toBasedFunctor.toFunctor.map φ.1
  exact τBased.toNatTrans.naturality φ.1

/-- Helper for Lemma 8.11.5: the fiber isomorphism induced by a `2`-morphism is compatible
with canonical pullback-comparison isomorphisms. -/
theorem fiberIsoOfStackHom_pullbackComparison_hom_naturality
    {A B : StackInGroupoidsOver J} {F G : A ⟶ B} (τ : F ⟶ G)
    {U V : C} (f : V ⟶ U) (x : A.p.Fiber U) :
    ((canonicalPullbackChoice B.p).pullbackFunctor f).map
        (fiberIsoOfStackHom (J := J) τ x).hom ≫
      (FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f x).hom =
        (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom ≫
          (fiberIsoOfStackHom (J := J) τ
            (((canonicalPullbackChoice A.p).pullbackFunctor f).obj x)).hom := by
  -- Forget to the total category and compare after the chosen target pullback arrow.
  apply Functor.Fiber.hom_ext
  let τBased : F.toBasedFunctor ⟶ G.toBasedFunctor := τ.hom.hom.hom.hom.hom.hom
  let η :
      ((canonicalPullbackChoice B.p).pullbackFunctor f).obj
          ((F.fiberFunctor U).obj x) ⟶
        ((canonicalPullbackChoice B.p).pullbackFunctor f).obj
          ((G.fiberFunctor U).obj x) :=
    ((canonicalPullbackChoice B.p).pullbackFunctor f).map
      (fiberIsoOfStackHom (J := J) τ x).hom
  let θ :=
    G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x)
  have hθ : B.p.IsStronglyCartesian f θ := by
    change
      B.p.IsStronglyCartesian f
        (G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x))
    exact
      FibredCategoryMor.map_stronglyCartesian_of_lift
        G.toFibredCategoryMor f ((canonicalPullbackChoice A.p).map f x)
        ((canonicalPullbackChoice A.p).isStronglyCartesian f x)
  letI : B.p.IsStronglyCartesian f θ := hθ
  have hpost :
      (η.1 ≫ (FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f x).hom.1) ≫
          θ =
        ((FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom.1 ≫
            (fiberIsoOfStackHom (J := J) τ
              (((canonicalPullbackChoice A.p).pullbackFunctor f).obj x)).hom.1) ≫
          θ := by
    have hη :
        η.1 ≫ (canonicalPullbackChoice B.p).map f ((G.fiberFunctor U).obj x) =
          (canonicalPullbackChoice B.p).map f ((F.fiberFunctor U).obj x) ≫
            (fiberIsoOfStackHom (J := J) τ x).hom.1 := by
      simpa only [η] using
        (canonicalPullbackChoice B.p).pullbackFunctor_map_fac f
          (fiberIsoOfStackHom (J := J) τ x).hom
    have hF :
        (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom.1 ≫
            F.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x) =
          (canonicalPullbackChoice B.p).map f ((F.fiberFunctor U).obj x) := by
      exact FibredCategoryMor.pullbackComparison_hom_postcompose
        F.toFibredCategoryMor f x
    have hG :
        (FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f x).hom.1 ≫
            G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x) =
          (canonicalPullbackChoice B.p).map f ((G.fiberFunctor U).obj x) := by
      exact FibredCategoryMor.pullbackComparison_hom_postcompose
        G.toFibredCategoryMor f x
    have hnaturality :
        F.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x) ≫
            τBased.toNatTrans.app x.1 =
          τBased.toNatTrans.app
              (((canonicalPullbackChoice A.p).pullbackFunctor f).obj x).1 ≫
            G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x) := by
      exact τBased.toNatTrans.naturality ((canonicalPullbackChoice A.p).map f x)
    have h₁ :
        (η.1 ≫ (FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f x).hom.1) ≫ θ =
          η.1 ≫
            ((FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f x).hom.1 ≫
              G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x)) :=
      Category.assoc _ _ _
    have h₂ :
        η.1 ≫
            ((FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f x).hom.1 ≫
              G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x)) =
          η.1 ≫ (canonicalPullbackChoice B.p).map f ((G.fiberFunctor U).obj x) :=
      congrArg (fun k ↦ η.1 ≫ k) hG
    have h₃ :
        (canonicalPullbackChoice B.p).map f ((F.fiberFunctor U).obj x) ≫
            (fiberIsoOfStackHom (J := J) τ x).hom.1 =
          ((FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom.1 ≫
              F.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x)) ≫
            (fiberIsoOfStackHom (J := J) τ x).hom.1 :=
      (congrArg
        (fun k ↦ k ≫ (fiberIsoOfStackHom (J := J) τ x).hom.1)
        hF).symm
    have h₄ :
        ((FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom.1 ≫
              F.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x)) ≫
            (fiberIsoOfStackHom (J := J) τ x).hom.1 =
          (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom.1 ≫
            (F.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x) ≫
              τBased.toNatTrans.app x.1) := by
      simp only [fiberIsoOfStackHom_hom_val, τBased, Category.assoc]
      rfl
    have h₅ :
        (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom.1 ≫
            (F.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x) ≫
              τBased.toNatTrans.app x.1) =
          (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom.1 ≫
            (τBased.toNatTrans.app
                (((canonicalPullbackChoice A.p).pullbackFunctor f).obj x).1 ≫
              G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x)) :=
      congrArg (fun k ↦ (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom.1 ≫ k)
        hnaturality
    have h₆ :
        (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom.1 ≫
            (τBased.toNatTrans.app
                (((canonicalPullbackChoice A.p).pullbackFunctor f).obj x).1 ≫
              G.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x)) =
          ((FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom.1 ≫
              (fiberIsoOfStackHom (J := J) τ
                (((canonicalPullbackChoice A.p).pullbackFunctor f).obj x)).hom.1) ≫
            θ := by
      simp only [fiberIsoOfStackHom_hom_val, τBased, θ, Category.assoc]
      rfl
    exact h₁.trans (h₂.trans (hη.trans (h₃.trans (h₄.trans (h₅.trans h₆)))))
  have hleft :
      B.p.IsHomLift (𝟙 V)
        (η.1 ≫ (FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f x).hom.1) := by
    exact (η ≫ (FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f x).hom).2
  have hright :
      B.p.IsHomLift (𝟙 V)
        ((FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom.1 ≫
          (fiberIsoOfStackHom (J := J) τ
            (((canonicalPullbackChoice A.p).pullbackFunctor f).obj x)).hom.1) := by
    exact ((FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom ≫
      (fiberIsoOfStackHom (J := J) τ
        (((canonicalPullbackChoice A.p).pullbackFunctor f).obj x)).hom).2
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ B.p _ _ _ _
      f θ hθ _ _ (𝟙 V)
      (η.1 ≫ (FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f x).hom.1)
      ((FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom.1 ≫
        (fiberIsoOfStackHom (J := J) τ
          (((canonicalPullbackChoice A.p).pullbackFunctor f).obj x)).hom.1)
      hleft hright hpost

/-- Helper for Lemma 8.11.5: the inverse fiber isomorphism induced by a `2`-morphism is also
compatible with canonical pullback-comparison isomorphisms. -/
theorem fiberIsoOfStackHom_pullbackComparison_inv_naturality
    {A B : StackInGroupoidsOver J} {F G : A ⟶ B} (τ : F ⟶ G)
    {U V : C} (f : V ⟶ U) (x : A.p.Fiber U) :
    ((canonicalPullbackChoice B.p).pullbackFunctor f).map
        (fiberIsoOfStackHom (J := J) τ x).inv ≫
      (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom =
        (FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f x).hom ≫
          (fiberIsoOfStackHom (J := J) τ
            (((canonicalPullbackChoice A.p).pullbackFunctor f).obj x)).inv := by
  -- Move the already proved hom-side comparison across the two inverse components.
  let e := fiberIsoOfStackHom (J := J) τ x
  let ePull :=
    fiberIsoOfStackHom (J := J) τ
      (((canonicalPullbackChoice A.p).pullbackFunctor f).obj x)
  have hhom :
      ((canonicalPullbackChoice B.p).pullbackFunctor f).map e.hom ≫
        (FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f x).hom =
          (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom ≫
            ePull.hom := by
    exact fiberIsoOfStackHom_pullbackComparison_hom_naturality (J := J) τ f x
  change
    ((canonicalPullbackChoice B.p).pullbackFunctor f).map e.inv ≫
      (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom =
        (FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f x).hom ≫ ePull.inv
  apply (Iso.eq_comp_inv ePull).2
  have h₁ :
      (((canonicalPullbackChoice B.p).pullbackFunctor f).map e.inv ≫
          (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom) ≫ ePull.hom =
        ((canonicalPullbackChoice B.p).pullbackFunctor f).map e.inv ≫
          ((FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom ≫ ePull.hom) :=
    Category.assoc _ _ _
  have h₂ :
      ((canonicalPullbackChoice B.p).pullbackFunctor f).map e.inv ≫
          ((FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom ≫ ePull.hom) =
        ((canonicalPullbackChoice B.p).pullbackFunctor f).map e.inv ≫
          (((canonicalPullbackChoice B.p).pullbackFunctor f).map e.hom ≫
            (FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f x).hom) := by
    exact congrArg
      (fun k ↦ ((canonicalPullbackChoice B.p).pullbackFunctor f).map e.inv ≫ k)
      hhom.symm
  have h₃ :
      ((canonicalPullbackChoice B.p).pullbackFunctor f).map e.inv ≫
          (((canonicalPullbackChoice B.p).pullbackFunctor f).map e.hom ≫
            (FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f x).hom) =
        (FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f x).hom := by
    rw [← Category.assoc, ← Functor.map_comp]
    simp only [Iso.inv_hom_id, Functor.map_id, Category.id_comp]
  exact h₁.trans (h₂.trans h₃)

/-- Helper for Lemma 8.11.5: the pullback-comparison isomorphism for a composite stack
morphism is the composite of the pullback-comparison isomorphisms of the two factors. -/
theorem pullbackComparison_comp_hom
    {A B S : StackInGroupoidsOver J}
    (E : A ⟶ B) (H : B ⟶ S)
    {U V : C} (f : V ⟶ U) (x : A.p.Fiber U) :
    (FibredCategoryMor.pullbackComparison H.toFibredCategoryMor f ((E.fiberFunctor U).obj x)).hom ≫
      (H.fiberFunctor V).map
        (FibredCategoryMor.pullbackComparison E.toFibredCategoryMor f x).hom =
    (FibredCategoryMor.pullbackComparison (E ≫ H).toFibredCategoryMor f x).hom := by
  let eF := FibredCategoryMor.pullbackComparison E.toFibredCategoryMor f x
  let eH := FibredCategoryMor.pullbackComparison H.toFibredCategoryMor f ((E.fiberFunctor U).obj x)
  let eHE := FibredCategoryMor.pullbackComparison (E ≫ H).toFibredCategoryMor f x
  apply Functor.Fiber.hom_ext
  let θ := (E ≫ H).toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x)
  have hθ : S.p.IsStronglyCartesian f θ := by
    change S.p.IsStronglyCartesian f
      (H.toFibredCategoryMor.toHom.map
        (E.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x)))
    exact
      FibredCategoryMor.map_stronglyCartesian_of_lift
        H.toFibredCategoryMor f
        (E.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x))
        (FibredCategoryMor.map_stronglyCartesian_of_lift
          E.toFibredCategoryMor f ((canonicalPullbackChoice A.p).map f x)
          ((canonicalPullbackChoice A.p).isStronglyCartesian f x))
  have hleft : S.p.IsHomLift (𝟙 V)
      (eH.hom.1 ≫ ((H.fiberFunctor V).map eF.hom).1) := by
    exact (eH.hom ≫ (H.fiberFunctor V).map eF.hom).2
  have hright : S.p.IsHomLift (𝟙 V) eHE.hom.1 := by
    exact eHE.hom.2
  have hpost :
      (eH.hom.1 ≫ ((H.fiberFunctor V).map eF.hom).1) ≫ θ =
        eHE.hom.1 ≫ θ := by
    have hF :
        eF.hom.1 ≫ E.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x) =
          (canonicalPullbackChoice B.p).map f ((E.fiberFunctor U).obj x) := by
      simpa only [eF] using
        FibredCategoryMor.pullbackComparison_hom_postcompose E.toFibredCategoryMor f x
    have hH :
        eH.hom.1 ≫ H.toFibredCategoryMor.toHom.map
            ((canonicalPullbackChoice B.p).map f ((E.fiberFunctor U).obj x)) =
          (canonicalPullbackChoice S.p).map f ((H.fiberFunctor U).obj ((E.fiberFunctor U).obj x)) := by
      simpa only [eH] using
        FibredCategoryMor.pullbackComparison_hom_postcompose H.toFibredCategoryMor f
          ((E.fiberFunctor U).obj x)
    have hHE :
        eHE.hom.1 ≫ θ =
          (canonicalPullbackChoice S.p).map f ((H.fiberFunctor U).obj ((E.fiberFunctor U).obj x)) := by
      simpa only [eHE, θ, BasedFunctor.comp] using
        FibredCategoryMor.pullbackComparison_hom_postcompose (E ≫ H).toFibredCategoryMor f x
    change (eH.hom.1 ≫ H.toFibredCategoryMor.toHom.map eF.hom.1) ≫
        H.toFibredCategoryMor.toHom.map
          (E.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x)) =
      eHE.hom.1 ≫ θ
    have hstep₁ :
        (eH.hom.1 ≫ H.toFibredCategoryMor.toHom.map eF.hom.1) ≫
            H.toFibredCategoryMor.toHom.map
              (E.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x)) =
          eH.hom.1 ≫
            H.toFibredCategoryMor.toHom.map
              (eF.hom.1 ≫ E.toFibredCategoryMor.toHom.map
                ((canonicalPullbackChoice A.p).map f x)) := by
      rw [Functor.map_comp]
      exact Category.assoc eH.hom.1
        (H.toFibredCategoryMor.toHom.map eF.hom.1)
        (H.toFibredCategoryMor.toHom.map
          (E.toFibredCategoryMor.toHom.map ((canonicalPullbackChoice A.p).map f x)))
    have hstep₂ :
        eH.hom.1 ≫
            H.toFibredCategoryMor.toHom.map
              (eF.hom.1 ≫ E.toFibredCategoryMor.toHom.map
                ((canonicalPullbackChoice A.p).map f x)) =
          eH.hom.1 ≫
            H.toFibredCategoryMor.toHom.map
              ((canonicalPullbackChoice B.p).map f ((E.fiberFunctor U).obj x)) := by
      exact congrArg (fun m ↦ eH.hom.1 ≫ H.toFibredCategoryMor.toHom.map m) hF
    exact hstep₁.trans (hstep₂.trans (hH.trans hHE.symm))
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ S.p _ _ _ _
      f θ hθ _ _ (𝟙 V)
      (eH.hom.1 ≫ ((H.fiberFunctor V).map eF.hom).1)
      eHE.hom.1 hleft hright hpost


end StackInGroupoidsOver.Hom

end

end CategoryTheory
