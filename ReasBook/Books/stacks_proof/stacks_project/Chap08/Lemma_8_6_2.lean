import Mathlib
import StacksProject_2024.Chap04.Example_4_38_5
import StacksProject_2024.Chap08.Lemma_8_4_2
import StacksProject_2024.Chap08.Definition_8_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace CategoryTheory

open CategoryOfElements Opposite Pseudofunctor
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]

section Auxiliary

variable (F : Presheaf.{w} C)

/-- Helper for Lemma 8.6.2: a section of `F` over `U` is the same thing as an object of the
fiber of the category-of-elements projection over `U`. -/
private noncomputable def presheaf_category_of_elements_fiber_equiv
    (U : Cᵒᵖ) :
    F.obj U ≃ (((π F).leftOp).Fiber (unop U)) where
  toFun a := Functor.Fiber.mk (a := op (F.elementsMk U a)) rfl
  invFun x := by
    -- Unpacking a fiber object over `unop U` recovers the stored section of `F`.
    let y := x.1.unop
    have hy : y.1 = U := by
      simpa [y, Functor.leftOp_obj, CategoryOfElements.π_obj] using x.2
    exact Eq.ndrec y.2 hy
  left_inv a := by
    -- The canonical fiber object remembers exactly the original section.
    rfl
  right_inv x := by
    -- Every fiber object over `unop U` is canonically of the form `op ⟨U, a⟩`.
    cases x with
    | mk x hx =>
        have hx' : x.unop.1 = U := by
          simpa [Functor.leftOp_obj, CategoryOfElements.π_obj] using hx
        cases hx'
        rfl

/-- Helper for Lemma 8.6.2: the explicit pullback arrow in the opposite category of elements is
strongly cartesian. -/
private theorem presheaf_category_of_elements_pullback_hom_isStronglyCartesian
    {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj U) :
    Functor.IsStronglyCartesian ((CategoryOfElements.π F).leftOp) f.unop
      (Quiver.Hom.op <|
        CategoryOfElements.homMk
          (F.elementsMk U a)
          (F.elementsMk V (F.map f a))
          f
          rfl) := by
  -- This is the textbook pullback arrow `f^* a ⟶ a` inside `F.Elementsᵒᵖ`.
  refine
    { toIsHomLift := ?_
      universal_property' := ?_ }
  · refine IsHomLift.of_fac' ((CategoryOfElements.π F).leftOp) f.unop _ rfl rfl ?_
    simp
  · intro a' g φ' hφ'
    let hgf : ((CategoryOfElements.π F).leftOp).obj a' ⟶ unop U := g ≫ f.unop
    have hComp :
        hgf = ((CategoryOfElements.π F).leftOp).map φ' := by
      exact
        @IsHomLift.eq_of_isHomLift _ _ _ _
          ((CategoryOfElements.π F).leftOp) _ _ hgf φ' hφ'
    have hVal : φ'.unop.val = f ≫ g.op := by
      simpa [hgf] using congrArg Quiver.Hom.op hComp.symm
    refine ⟨Quiver.Hom.op (CategoryOfElements.homMk _ _ g.op ?_), ⟨?_, ?_⟩, ?_⟩
    · simpa [FunctorToTypes.map_comp_apply, hVal] using φ'.unop.property
    · refine IsHomLift.of_fac' ((CategoryOfElements.π F).leftOp) g _ rfl rfl ?_
      simp
    · exact Quiver.Hom.unop_inj <| CategoryOfElements.ext F _ _ <| by
        simpa using hVal.symm
    · intro ψ hψ
      exact Quiver.Hom.unop_inj <| CategoryOfElements.ext F _ _ <| by
        have hBase : g = ((CategoryOfElements.π F).leftOp).map ψ := by
          exact
            @IsHomLift.eq_of_isHomLift _ _ _ _
              ((CategoryOfElements.π F).leftOp) _ _ g ψ hψ.1
        simpa using congrArg Quiver.Hom.op hBase.symm

/-- Helper for Lemma 8.6.2: restriction of a section corresponds to the canonical pullback
object in the fiber of the category of elements. -/
private theorem presheaf_category_of_elements_fiber_equiv_naturality
    {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj U) :
    presheaf_category_of_elements_fiber_equiv F V (F.map f a) =
      ((canonicalPullbackChoice ((CategoryOfElements.π F).leftOp)).pullbackFunctor f.unop).obj
        (presheaf_category_of_elements_fiber_equiv F U a) := by
  let hc := canonicalPullbackChoice ((CategoryOfElements.π F).leftOp)
  let φexp :
      op (F.elementsMk V (F.map f a)) ⟶ op (F.elementsMk U a) :=
    Quiver.Hom.op <|
      CategoryOfElements.homMk
        (F.elementsMk U a)
        (F.elementsMk V (F.map f a))
        f
        rfl
  let φcan :
      ((hc.pullbackFunctor f.unop).obj (presheaf_category_of_elements_fiber_equiv F U a)).1 ⟶
        (presheaf_category_of_elements_fiber_equiv F U a).1 :=
    hc.map f.unop (presheaf_category_of_elements_fiber_equiv F U a)
  have hφexp :
      Functor.IsStronglyCartesian ((CategoryOfElements.π F).leftOp) f.unop φexp :=
    presheaf_category_of_elements_pullback_hom_isStronglyCartesian F f a
  letI :
      Functor.IsStronglyCartesian ((CategoryOfElements.π F).leftOp) f.unop φexp :=
    hφexp
  have hCartExp :
      Functor.IsCartesian ((CategoryOfElements.π F).leftOp) f.unop φexp :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      (p := ((CategoryOfElements.π F).leftOp))
      (f := f.unop)
      (φ := φexp)
  have hStrongCan :
      Functor.IsStronglyCartesian ((CategoryOfElements.π F).leftOp) f.unop φcan :=
    hc.isStronglyCartesian f.unop (presheaf_category_of_elements_fiber_equiv F U a)
  letI :
      Functor.IsStronglyCartesian ((CategoryOfElements.π F).leftOp) f.unop φcan :=
    hStrongCan
  have hCartCan :
      Functor.IsCartesian ((CategoryOfElements.π F).leftOp) f.unop φcan :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      (p := ((CategoryOfElements.π F).leftOp))
      (f := f.unop)
      (φ := φcan)
  let e :=
    @Functor.IsCartesian.domainUniqueUpToIso _ _ _ _
      ((CategoryOfElements.π F).leftOp) _ _ _ _ f.unop φcan hCartCan _ φexp hCartExp
  have hHomLift :
      ((CategoryOfElements.π F).leftOp).IsHomLift (𝟙 (unop V)) e.hom := by
    simpa [e] using
      (@Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _
        ((CategoryOfElements.π F).leftOp) _ _ _ _ f.unop φcan hCartCan _ φexp hCartExp)
  have hInvLift :
      ((CategoryOfElements.π F).leftOp).IsHomLift (𝟙 (unop V)) e.inv := by
    simpa [e] using
      (@Functor.IsCartesian.domainUniqueUpToIso_hom_isHomLift _ _ _ _
        ((CategoryOfElements.π F).leftOp) _ _ _ _ f.unop φcan hCartCan _ φexp hCartExp)
  let eFiber :
      presheaf_category_of_elements_fiber_equiv F V (F.map f a) ≅
        ((hc.pullbackFunctor f.unop).obj (presheaf_category_of_elements_fiber_equiv F U a)) :=
    { hom := ⟨e.hom, hHomLift⟩
      inv := ⟨e.inv, hInvLift⟩
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }
  -- In a discrete fiber, the comparison isomorphism rigidifies to equality of objects.
  exact obj_ext_of_isDiscrete eFiber.hom

variable {J : GrothendieckTopology C} {U : C} (S : J.Cover U)

/-- Helper for Lemma 8.6.2: an object of the descent-data category for the cover `S` determines
the corresponding compatible family of local sections of `F`. -/
private noncomputable def category_of_elements_cover_compatible_family
    (D :
      (canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).DescentData
        (fun I : S.Arrow ↦ I.f)) :
    Subtype (Presieve.Arrows.Compatible F (fun I : S.Arrow ↦ I.f)) where
  val I := (presheaf_category_of_elements_fiber_equiv F (op I.Y)).symm (D.obj I)
  property := by
    intro I₁ I₂ Z g₁ g₂ h
    -- The descent comparison morphism is vertical in a discrete fiber, so it identifies the two
    -- pullback objects, which translates back to equality of local restrictions.
    let q : Z ⟶ U := g₁ ≫ I₁.f
    have h₁ : g₁ ≫ I₁.f = q := rfl
    have h₂ : g₂ ≫ I₂.f = q := by
      simpa [q] using h.symm
    have hObj :
        ((canonicalPullbackChoice ((CategoryOfElements.π F).leftOp)).pullbackFunctor g₁).obj
            (D.obj I₁) =
          ((canonicalPullbackChoice ((CategoryOfElements.π F).leftOp)).pullbackFunctor g₂).obj
            (D.obj I₂) := by
      exact obj_ext_of_isDiscrete (D.hom q g₁ g₂ h₁ h₂)
    have hFiber :
        presheaf_category_of_elements_fiber_equiv F (op Z)
            (F.map g₁.op ((presheaf_category_of_elements_fiber_equiv F (op I₁.Y)).symm (D.obj I₁))) =
          presheaf_category_of_elements_fiber_equiv F (op Z)
            (F.map g₂.op ((presheaf_category_of_elements_fiber_equiv F (op I₂.Y)).symm (D.obj I₂))) := by
      calc
        presheaf_category_of_elements_fiber_equiv F (op Z)
            (F.map g₁.op ((presheaf_category_of_elements_fiber_equiv F (op I₁.Y)).symm (D.obj I₁))) =
          ((canonicalPullbackChoice ((CategoryOfElements.π F).leftOp)).pullbackFunctor g₁).obj
            (presheaf_category_of_elements_fiber_equiv F (op I₁.Y)
              ((presheaf_category_of_elements_fiber_equiv F (op I₁.Y)).symm (D.obj I₁))) := by
                simpa using
                  presheaf_category_of_elements_fiber_equiv_naturality
                    (F := F) (f := g₁.op)
                    ((presheaf_category_of_elements_fiber_equiv F (op I₁.Y)).symm (D.obj I₁))
        _ = ((canonicalPullbackChoice ((CategoryOfElements.π F).leftOp)).pullbackFunctor g₁).obj
            (D.obj I₁) := by
              simp
        _ = ((canonicalPullbackChoice ((CategoryOfElements.π F).leftOp)).pullbackFunctor g₂).obj
            (D.obj I₂) := hObj
        _ = presheaf_category_of_elements_fiber_equiv F (op Z)
            (F.map g₂.op ((presheaf_category_of_elements_fiber_equiv F (op I₂.Y)).symm (D.obj I₂))) := by
              simpa using
                (presheaf_category_of_elements_fiber_equiv_naturality
                  (F := F) (f := g₂.op)
                  ((presheaf_category_of_elements_fiber_equiv F (op I₂.Y)).symm (D.obj I₂))).symm
    exact (presheaf_category_of_elements_fiber_equiv F (op Z)).injective hFiber

end Auxiliary

section DescentComparison

variable {J : GrothendieckTopology C}
variable (F : Presheaf.{w} C)

/-- Helper for Lemma 8.6.2: every category in the canonical fiber pseudofunctor of the
category-of-elements projection is discrete because the projection is fibred in sets. -/
private instance category_of_elements_canonicalFiber_isDiscrete
    (U : Cᵒᵖ) :
    IsDiscrete
      ↑((canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).obj { as := U }) := by
  -- The canonical fiber pseudofunctor is definitionally the fiber category over `unop U`.
  simpa using
    (inferInstance : IsDiscrete (((CategoryOfElements.π F).leftOp).Fiber (unop U)))

/-- Helper for Lemma 8.6.2: compatibility of a family of local sections identifies the two
corresponding pullback objects in the category-of-elements fiber over a common refinement. -/
private theorem category_of_elements_compatible_family_pullback_eq
    {U : C} (S : J.Cover U)
    (s : Subtype (Presieve.Arrows.Compatible F (fun I : S.Arrow ↦ I.f)))
    {Z : C} {I₁ I₂ : S.Arrow} (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (h : g₁ ≫ I₁.f = g₂ ≫ I₂.f) :
    presheaf_category_of_elements_fiber_equiv F (op Z) (F.map g₁.op (s.1 I₁)) =
      presheaf_category_of_elements_fiber_equiv F (op Z) (F.map g₂.op (s.1 I₂)) := by
  -- Apply the explicit fiber equivalence to the compatibility equality of the family `s`.
  apply congrArg (presheaf_category_of_elements_fiber_equiv F (op Z))
  exact s.2 I₁ I₂ Z g₁ g₂ h

/-- Helper for Lemma 8.6.2: the transition morphism of the backward descent datum is the
identity map between the equal pullback objects coming from compatibility. -/
private theorem compatible_family_to_category_of_elements_descent_data_hom_eq
    {U : C} (S : J.Cover U)
    (s : Subtype (Presieve.Arrows.Compatible F (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) :
    (((canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).map f₁.op.toLoc).toFunctor.obj
        (presheaf_category_of_elements_fiber_equiv F (op I₁.Y) (s.1 I₁))) =
      (((canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).map f₂.op.toLoc).toFunctor.obj
        (presheaf_category_of_elements_fiber_equiv F (op I₂.Y) (s.1 I₂))) := by
  -- Normalize both pullbacks to restricted local sections and then use compatibility.
  have hPull₁ :
      (((canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).map f₁.op.toLoc).toFunctor.obj
          (presheaf_category_of_elements_fiber_equiv F (op I₁.Y) (s.1 I₁))) =
        presheaf_category_of_elements_fiber_equiv F (op Y) (F.map f₁.op (s.1 I₁)) := by
    -- The first pullback object is the restricted section along `f₁`.
    simpa using
      (presheaf_category_of_elements_fiber_equiv_naturality
        (F := F) (f := f₁.op) (a := s.1 I₁)).symm
  have hCompat :
      presheaf_category_of_elements_fiber_equiv F (op Y) (F.map f₁.op (s.1 I₁)) =
        presheaf_category_of_elements_fiber_equiv F (op Y) (F.map f₂.op (s.1 I₂)) := by
    -- Compatibility identifies the two restricted sections over the common refinement `Y`.
    simpa [hf₁, hf₂] using
      (category_of_elements_compatible_family_pullback_eq
        (F := F) (S := S) (s := s) (g₁ := f₁) (g₂ := f₂)
        (h := by rw [hf₁, hf₂]))
  have hPull₂ :
      presheaf_category_of_elements_fiber_equiv F (op Y) (F.map f₂.op (s.1 I₂)) =
        (((canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).map f₂.op.toLoc).toFunctor.obj
          (presheaf_category_of_elements_fiber_equiv F (op I₂.Y) (s.1 I₂))) := by
    -- The second pullback object is the restricted section along `f₂`.
    simpa using
      presheaf_category_of_elements_fiber_equiv_naturality
        (F := F) (f := f₂.op) (a := s.1 I₂)
  exact hPull₁.trans (hCompat.trans hPull₂)

/-- Helper for Lemma 8.6.2: the backward descent datum is stable under further pullback because
all morphisms in the relevant fibers are unique. -/
private theorem compatible_family_to_category_of_elements_descent_data_pullHom_hom
    {U : C} (S : J.Cover U)
    (s : Subtype (Presieve.Arrows.Compatible F (fun I : S.Arrow ↦ I.f))) :
    ∀ ⦃Y' Y : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : g ≫ q = q')
      ⦃I₁ I₂ : S.Arrow⦄ (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
      (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
      (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂),
      pullHom
          (eqToHom
            (compatible_family_to_category_of_elements_descent_data_hom_eq
              (F := F) (S := S) (s := s) q f₁ f₂ hf₁ hf₂))
          g gf₁ gf₂ =
        eqToHom
          (compatible_family_to_category_of_elements_descent_data_hom_eq
            (F := F) (S := S) (s := s) q' gf₁ gf₂
            (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
            (by rw [← hq, ← hgf₂, Category.assoc, hf₂])) := by
  intro Y' Y g q q' hq I₁ I₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  -- Both sides are morphisms in a discrete fiber, so there is nothing left to check.
  exact Subsingleton.elim _ _

/-- Helper for Lemma 8.6.2: the identity condition for the backward descent datum is forced by
discreteness of the fibers. -/
private theorem compatible_family_to_category_of_elements_descent_data_hom_self
    {U : C} (S : J.Cover U)
    (s : Subtype (Presieve.Arrows.Compatible F (fun I : S.Arrow ↦ I.f))) :
    ∀ ⦃Y : C⦄ (q : Y ⟶ U) ⦃I : S.Arrow⦄ (g : Y ⟶ I.Y) (hg : g ≫ I.f = q),
      eqToHom
          (compatible_family_to_category_of_elements_descent_data_hom_eq
            (F := F) (S := S) (s := s) q g g hg hg) =
        𝟙 _ := by
  intro Y q I g hg
  -- The endomorphism of an object in a discrete fiber is unique.
  exact Subsingleton.elim _ _

/-- Helper for Lemma 8.6.2: the cocycle condition for the backward descent datum is again forced
by uniqueness of morphisms in the discrete fibers. -/
private theorem compatible_family_to_category_of_elements_descent_data_hom_comp
    {U : C} (S : J.Cover U)
    (s : Subtype (Presieve.Arrows.Compatible F (fun I : S.Arrow ↦ I.f))) :
    ∀ ⦃Y : C⦄ (q : Y ⟶ U) ⦃I₁ I₂ I₃ : S.Arrow⦄
      (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
      (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) (hf₃ : f₃ ≫ I₃.f = q),
      eqToHom
          (compatible_family_to_category_of_elements_descent_data_hom_eq
            (F := F) (S := S) (s := s) q f₁ f₂ hf₁ hf₂) ≫
          eqToHom
            (compatible_family_to_category_of_elements_descent_data_hom_eq
              (F := F) (S := S) (s := s) q f₂ f₃ hf₂ hf₃) =
        eqToHom
          (compatible_family_to_category_of_elements_descent_data_hom_eq
            (F := F) (S := S) (s := s) q f₁ f₃ hf₁ hf₃) := by
  intro Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
  -- Any two morphisms between these pullback objects agree because the ambient fiber is discrete.
  exact Subsingleton.elim _ _

/-- Helper for Lemma 8.6.2: a compatible family of local sections produces the corresponding
descent datum for the category-of-elements projection. -/
private noncomputable def compatible_family_to_category_of_elements_descent_data
    {U : C} (S : J.Cover U)
    (s : Subtype (Presieve.Arrows.Compatible F (fun I : S.Arrow ↦ I.f))) :
    (canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).DescentData
      (fun I : S.Arrow ↦ I.f) where
  obj I := presheaf_category_of_elements_fiber_equiv F (op I.Y) (s.1 I)
  hom := fun {_} q {I₁ I₂} f₁ f₂ hf₁ hf₂ ↦
    -- The transition map is the identity between the equal pullback objects.
    eqToHom
      (compatible_family_to_category_of_elements_descent_data_hom_eq
        (F := F) (S := S) (s := s) (q := q)
        (I₁ := I₁) (I₂ := I₂) (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂))
  pullHom_hom := fun {_ _} g q q' hq {I₁ I₂} f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ ↦
    -- Pulling back once more preserves this identity comparison.
    compatible_family_to_category_of_elements_descent_data_pullHom_hom
      (F := F) (S := S) (s := s) (g := g) (q := q) (q' := q') (hq := hq)
      (I₁ := I₁) (I₂ := I₂) (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)
      (gf₁ := gf₁) (gf₂ := gf₂) (hgf₁ := hgf₁) (hgf₂ := hgf₂)
  hom_self := fun {_} q {I} g hg ↦
    -- The identity law is automatic because the fiber is discrete.
    compatible_family_to_category_of_elements_descent_data_hom_self
      (F := F) (S := S) (s := s) (q := q) (I := I) (g := g) (hg := hg)
  hom_comp := fun {_} q {I₁ I₂ I₃} f₁ f₂ f₃ hf₁ hf₂ hf₃ ↦
    -- The cocycle law is likewise forced by uniqueness of morphisms in the fiber.
    compatible_family_to_category_of_elements_descent_data_hom_comp
      (F := F) (S := S) (s := s) (q := q)
      (I₁ := I₁) (I₂ := I₂) (I₃ := I₃)
      (f₁ := f₁) (f₂ := f₂) (f₃ := f₃)
      (hf₁ := hf₁) (hf₂ := hf₂) (hf₃ := hf₃)

/-- Helper for Lemma 8.6.2: any morphism of descent data induces equality of the corresponding
compatible families because every component map lies in a discrete fiber. -/
private theorem category_of_elements_cover_compatible_family_map_eq
    {U : C} (S : J.Cover U)
    {D₁ D₂ :
      (canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).DescentData
        (fun I : S.Arrow ↦ I.f)}
    (φ : D₁ ⟶ D₂) :
    category_of_elements_cover_compatible_family (F := F) S D₁ =
      category_of_elements_cover_compatible_family (F := F) S D₂ := by
  apply Subtype.ext
  funext I
  -- Compare the `I`-components through the fiber equivalence and use discreteness of the fiber.
  have hI : D₁.obj I = D₂.obj I := obj_ext_of_isDiscrete (φ.hom I)
  exact congrArg ((presheaf_category_of_elements_fiber_equiv F (op I.Y)).symm) hI

/-- Helper for Lemma 8.6.2: morphisms between descent data for the category-of-elements
projection are unique because each component lives in a discrete fiber. -/
private theorem category_of_elements_cover_descent_data_hom_subsingleton
    {U : C} (S : J.Cover U)
    (D₁ D₂ :
      (canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).DescentData
        (fun I : S.Arrow ↦ I.f)) :
    Subsingleton (D₁ ⟶ D₂) := by
  constructor
  intro φ ψ
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  exact Subsingleton.elim _ _

/-- Helper for Lemma 8.6.2: converting a compatible family to descent data and then back
recovers the original family. -/
private theorem category_of_elements_cover_compatible_family_inverse
    {U : C} (S : J.Cover U)
    (s : Subtype (Presieve.Arrows.Compatible F (fun I : S.Arrow ↦ I.f))) :
    category_of_elements_cover_compatible_family (F := F) S
        (compatible_family_to_category_of_elements_descent_data (F := F) S s) =
      s := by
  apply Subtype.ext
  funext I
  -- Each component is reconstructed by the explicit fiber equivalence.
  simpa [category_of_elements_cover_compatible_family,
    compatible_family_to_category_of_elements_descent_data] using
    (presheaf_category_of_elements_fiber_equiv F (op I.Y)).left_inv (s.1 I)

/-- Helper for Lemma 8.6.2: the backward construction recovers the original descent datum on
objects, component by component. -/
private theorem compatible_family_to_category_of_elements_descent_data_obj_eq
    {U : C} (S : J.Cover U)
    (D :
      (canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).DescentData
        (fun I : S.Arrow ↦ I.f))
    (I : S.Arrow) :
    (compatible_family_to_category_of_elements_descent_data (F := F) S
        (category_of_elements_cover_compatible_family (F := F) S D)).obj I =
      D.obj I := by
  -- The object component is exactly the two-sided inverse of the fiber equivalence.
  simpa [category_of_elements_cover_compatible_family,
    compatible_family_to_category_of_elements_descent_data] using
    (presheaf_category_of_elements_fiber_equiv F (op I.Y)).apply_symm_apply (D.obj I)

/-- Helper for Lemma 8.6.2: the fixed-cover comparison from descent data to compatible families
is functorial, with maps forced by equality in the discrete target. -/
private noncomputable def category_of_elements_cover_compatible_family_functor
    {U : C} (S : J.Cover U) :
    (canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).DescentData
        (fun I : S.Arrow ↦ I.f) ⥤
      Discrete (Subtype (Presieve.Arrows.Compatible F (fun I : S.Arrow ↦ I.f))) := by
  refine
    { obj := fun D ↦ Discrete.mk (category_of_elements_cover_compatible_family (F := F) S D)
      map := fun {D₁ D₂} φ ↦ ?_
      map_id := ?_
      map_comp := ?_ }
  · -- A descent-data morphism identifies the underlying compatible families componentwise.
    apply eqToHom
    exact congrArg Discrete.mk
      (category_of_elements_cover_compatible_family_map_eq (F := F) (S := S) φ)
  · intro D
    exact Subsingleton.elim _ _
  · intro D₁ D₂ D₃ φ ψ
    exact Subsingleton.elim _ _

/-- Helper for Lemma 8.6.2: the inverse fixed-cover comparison sends a compatible family back to
the descent datum it defines. -/
private noncomputable def compatible_family_to_category_of_elements_descent_data_functor
    {U : C} (S : J.Cover U) :
    Discrete (Subtype (Presieve.Arrows.Compatible F (fun I : S.Arrow ↦ I.f))) ⥤
      (canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).DescentData
        (fun I : S.Arrow ↦ I.f) := by
  refine
    { obj := fun s ↦ compatible_family_to_category_of_elements_descent_data (F := F) S s.as
      map := fun {s t} φ ↦ ?_
      map_id := ?_
      map_comp := ?_ }
  · -- After reducing a morphism in `Discrete`, the comparison map is the identity morphism.
    exact
      eqToHom <|
        congrArg
          (fun x : Discrete (Subtype (Presieve.Arrows.Compatible F (fun I : S.Arrow ↦ I.f))) ↦
            compatible_family_to_category_of_elements_descent_data (F := F) S x.as)
          (obj_ext_of_isDiscrete φ)
  · intro s
    exact
      (category_of_elements_cover_descent_data_hom_subsingleton
        (F := F) (S := S) _ _).elim _ _
  · intro s t u φ ψ
    exact
      (category_of_elements_cover_descent_data_hom_subsingleton
        (F := F) (S := S) _ _).elim _ _

/-- Helper for Lemma 8.6.2: the descent-data category for the cover `S` is equivalent to the
discrete category of compatible families of local sections. -/
private noncomputable def category_of_elements_cover_descent_data_equiv_compatible_families
    {U : C} (S : J.Cover U) :
    (canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).DescentData
        (fun I : S.Arrow ↦ I.f) ≌
      Discrete (Subtype (Presieve.Arrows.Compatible F (fun I : S.Arrow ↦ I.f))) where
  functor := category_of_elements_cover_compatible_family_functor (F := F) S
  inverse := compatible_family_to_category_of_elements_descent_data_functor (F := F) S
  unitIso := by
    -- On descent data, the inverse construction is objectwise inverse, and morphisms are unique.
    refine NatIso.ofComponents (fun D ↦ ?_) ?_
    · refine Pseudofunctor.DescentData.isoMk (fun I ↦ ?_) ?_
      · exact eqToIso <|
          (compatible_family_to_category_of_elements_descent_data_obj_eq
            (F := F) (S := S) D I).symm
      · intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
        exact Subsingleton.elim _ _
    · intro D₁ D₂ φ
      exact (category_of_elements_cover_descent_data_hom_subsingleton
        (F := F) (S := S) D₁
        ((category_of_elements_cover_compatible_family_functor (F := F) S ⋙
          compatible_family_to_category_of_elements_descent_data_functor (F := F) S).obj D₂)).elim
        _ _
  counitIso := by
    -- The source-compatible family is recovered exactly after going to descent data and back.
    refine Discrete.natIso ?_
    intro s
    apply eqToIso
    simpa [category_of_elements_cover_compatible_family_functor,
      compatible_family_to_category_of_elements_descent_data_functor] using
      congrArg Discrete.mk
        (category_of_elements_cover_compatible_family_inverse (F := F) (S := S) s.as)

/-- Helper for Lemma 8.6.2: on an ambient section `a`, the canonical descent datum for the
category-of-elements projection corresponds exactly to the usual compatible family of
restrictions of `a`. -/
private theorem category_of_elements_toDescentData_obj_eq_toCompatible
    {U : C} (S : J.Cover U) (a : F.obj (op U)) :
    category_of_elements_cover_compatible_family (F := F) S
        (((canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).toDescentData
          (fun I : S.Arrow ↦ I.f)).obj
          (presheaf_category_of_elements_fiber_equiv F (op U) a)) =
      Presieve.Arrows.toCompatible F (fun I : S.Arrow ↦ I.f) a := by
  apply Subtype.ext
  funext I
  -- Unfolding the ambient descent datum leaves exactly the restriction of `a` to `I.Y`.
  change
      (presheaf_category_of_elements_fiber_equiv F (op I.Y)).symm
        (((canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).map I.f.op.toLoc).toFunctor.obj
          (presheaf_category_of_elements_fiber_equiv F (op U) a)) =
      F.map I.f.op a
  have hNat :=
    presheaf_category_of_elements_fiber_equiv_naturality (F := F) (f := I.f.op) (a := a)
  exact (presheaf_category_of_elements_fiber_equiv F (op I.Y)).injective <| by
    simpa using hNat.symm

/-- Helper for Lemma 8.6.2: for any functor between discrete categories, equivalence of
categories is exactly bijectivity on objects. -/
private theorem isEquivalence_iff_bijective_obj_of_isDiscrete
    {A B : Type*} [Category A] [Category B] [IsDiscrete A] [IsDiscrete B]
    (G : A ⥤ B) :
    G.IsEquivalence ↔ Function.Bijective G.obj := by
  constructor
  · intro h
    let _ : G.IsEquivalence := h
    refine ⟨?_, ?_⟩
    · intro X Y hXY
      -- In a discrete source, any morphism witnessing equality of images rigidifies to object
      -- equality.
      exact obj_ext_of_isDiscrete (G.preimage (eqToHom hXY))
    · intro Y
      -- Essential surjectivity produces an object whose comparison isomorphism is an equality.
      rcases Functor.EssSurj.mem_essImage (F := G) Y with ⟨X, ⟨e⟩⟩
      exact ⟨X, obj_ext_of_isDiscrete e.hom⟩
  · intro hG
    -- Bijectivity on objects is enough because all hom-sets in discrete categories are
    -- subsingletons.
    let faithfulG : G.Faithful := ⟨fun {_ _} _ _ _ ↦ Subsingleton.elim _ _⟩
    let fullG : G.Full := ⟨fun {X Y} f ↦
      ⟨eqToHom (hG.1 (obj_ext_of_isDiscrete f)), Subsingleton.elim _ _⟩⟩
    let essSurjG : G.EssSurj := Functor.essSurj_of_surj hG.2
    exact { faithful := faithfulG, full := fullG, essSurj := essSurjG }

/-- Helper for Lemma 8.6.2: for a fixed cover, the canonical descent functor for the
category-of-elements projection is an equivalence exactly when `F` satisfies the usual sheaf
condition for the corresponding covering sieve. -/
private theorem category_of_elements_cover_toDescentData_isEquivalence_iff_isSheafFor
    {U : C} (J : GrothendieckTopology C) (S : J.Cover U) :
    ((canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).toDescentData
      (fun I : S.Arrow ↦ I.f)).IsEquivalence ↔
      Presieve.IsSheafFor F ((S : Sieve U).arrows) := by
  let DD :=
    (canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).DescentData
      (fun I : S.Arrow ↦ I.f)
  let compat :=
    Subtype (Presieve.Arrows.Compatible F (fun I : S.Arrow ↦ I.f))
  let G : DD ⥤ Discrete compat :=
    category_of_elements_cover_compatible_family_functor (F := F) S
  let E : DD ≌ Discrete compat :=
    category_of_elements_cover_descent_data_equiv_compatible_families (F := F) S
  let K :
      ↑((canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).obj { as := op U }) ⥤
        Discrete compat := by
    refine
      { obj := fun a ↦
          Discrete.mk <|
            Presieve.Arrows.toCompatible F (fun I : S.Arrow ↦ I.f)
              ((presheaf_category_of_elements_fiber_equiv F (op U)).symm a)
        map := fun {a b} φ ↦ ?_
        map_id := ?_
        map_comp := ?_ }
    · -- A morphism in the discrete fiber forces equality of the underlying global sections.
      apply eqToHom
      exact congrArg Discrete.mk <|
        congrArg
          (Presieve.Arrows.toCompatible F (fun I : S.Arrow ↦ I.f) ∘
            (presheaf_category_of_elements_fiber_equiv F (op U)).symm)
          (obj_ext_of_isDiscrete φ)
    · intro a
      exact Subsingleton.elim _ _
    · intro a b c φ ψ
      exact Subsingleton.elim _ _
  have hIso :
      (((canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).toDescentData
          (fun I : S.Arrow ↦ I.f)) ⋙ G) ≅ K := by
    refine NatIso.ofComponents (fun a ↦ ?_) ?_
    · -- The canonical descent datum on `a` records exactly the usual compatible family of
      -- restrictions of the corresponding section.
      apply eqToIso
      simpa [G, K, category_of_elements_cover_compatible_family_functor] using
        congrArg Discrete.mk
          (category_of_elements_toDescentData_obj_eq_toCompatible
            (F := F) (S := S)
            ((presheaf_category_of_elements_fiber_equiv F (op U)).symm a))
    · intro a b φ
      exact Subsingleton.elim _ _
  let Kobj' :
      ↑((canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).obj { as := op U }) →
        compat := fun a ↦
    Presieve.Arrows.toCompatible F (fun I : S.Arrow ↦ I.f)
      ((presheaf_category_of_elements_fiber_equiv F (op U)).symm a)
  have hDiscreteMk :
      Function.Bijective (fun s : compat ↦ (Discrete.mk s : Discrete compat)) := by
    constructor
    · intro s t hst
      cases hst
      rfl
    · intro s
      exact ⟨s.as, by cases s; rfl⟩
  have hObjBijDiscrete :
      Function.Bijective K.obj ↔ Function.Bijective Kobj' := by
    -- Forgetting the trivial `Discrete.mk` wrapper does not change bijectivity.
    simpa [K, Kobj', Function.comp] using
      (Function.Bijective.of_comp_iff' hDiscreteMk Kobj')
  have hObjBijFiber :
      Function.Bijective Kobj' ↔
        Function.Bijective (Presieve.Arrows.toCompatible F (fun I : S.Arrow ↦ I.f)) := by
    -- The fiber equivalence identifies global sections with objects of the fiber over `U`.
    convert
      (Function.Bijective.of_comp_iff
        (f := Presieve.Arrows.toCompatible F (fun I : S.Arrow ↦ I.f))
        (g := (presheaf_category_of_elements_fiber_equiv F (op U)).symm)
        ((presheaf_category_of_elements_fiber_equiv F (op U)).symm.bijective)) using 1
  have hObjBij :
      Function.Bijective K.obj ↔
        Function.Bijective (Presieve.Arrows.toCompatible F (fun I : S.Arrow ↦ I.f)) :=
    hObjBijDiscrete.trans hObjBijFiber
  have hDiscrete :
      K.IsEquivalence ↔
        Function.Bijective (Presieve.Arrows.toCompatible F (fun I : S.Arrow ↦ I.f)) := by
    -- Once both sides are discrete, equivalence is purely an objectwise bijectivity statement.
    rw [isEquivalence_iff_bijective_obj_of_isDiscrete (G := K), hObjBij]
  have hCompare :
      ((canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).toDescentData
          (fun I : S.Arrow ↦ I.f)).IsEquivalence ↔
        K.IsEquivalence := by
    constructor
    · intro hΦ
      let _ :
          ((canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).toDescentData
            (fun I : S.Arrow ↦ I.f)).IsEquivalence := hΦ
      let _ : G.IsEquivalence := E.isEquivalence_functor
      have hComp :
          ((((canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).toDescentData
              (fun I : S.Arrow ↦ I.f))) ⋙ G).IsEquivalence :=
        by infer_instance
      exact (Functor.isEquivalence_iff_of_iso hIso).1 hComp
    · intro hK
      let _ : K.IsEquivalence := hK
      have hComp :
          ((((canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).toDescentData
              (fun I : S.Arrow ↦ I.f))) ⋙ G).IsEquivalence :=
        (Functor.isEquivalence_iff_of_iso hIso).2 hK
      let _ : G.IsEquivalence := E.isEquivalence_functor
      exact Functor.isEquivalence_of_comp_right
        ((canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).toDescentData
          (fun I : S.Arrow ↦ I.f)) G
  rw [hCompare, hDiscrete]
  rw [← S.ofArrows_eq, ← Presieve.isSheafFor_iff_generate]
  exact
    (Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible
      (P := F) (π := fun I : S.Arrow ↦ I.f)).symm

/-- Helper for Lemma 8.6.2: the stack-on-site condition for the category-of-elements projection
is exactly the sheaf condition on the original presheaf. -/
private theorem presheaf_isSheaf_iff_categoryOfElements_isStackOnSite_aux
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsSheaf J F ↔ IsStackOnSite J ((π F).leftOp) := by
  -- Compare both source-facing owners cover by cover using Lemma `8.4.2`.
  rw [isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence]
  constructor
  · intro h U S
    have hS :
        Presieve.IsSheafFor F ((S : Sieve U).arrows) := by
      exact h.isSheafFor (S : Sieve U) S.condition
    exact
      (category_of_elements_cover_toDescentData_isEquivalence_iff_isSheafFor
        (F := F) (J := J) S).2 hS
  · intro h
    rw [isSheaf_iff_isSheaf_of_type]
    intro U R hR
    let S : J.Cover U := ⟨R, hR⟩
    have hS :
        ((canonicalFiberPseudofunctor ((CategoryOfElements.π F).leftOp)).toDescentData
          (fun I : S.Arrow ↦ I.f)).IsEquivalence := h U S
    simpa using
      (category_of_elements_cover_toDescentData_isEquivalence_iff_isSheafFor
        (F := F) (J := J) S).1 hS

/-- Helper for Lemma 8.6.2: for the category-of-elements projection of a presheaf, the
source-facing notions `IsStackOnSite` and `IsStackInSets` coincide because the projection is
already fibred in sets. -/
private theorem category_of_elements_stack_on_site_iff_stack_in_sets
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ Type w) :
    IsStackOnSite J ((π F).leftOp) ↔ IsStackInSets J ((π F).leftOp) := by
  constructor
  · intro h
    -- Reassemble `IsStackInSets` from the existing fibred-in-sets structure and the stack owner.
    let _ : IsStackOnSite J ((π F).leftOp) := h
    let _ : IsFibredInSets ((π F).leftOp) :=
      presheaf_categoryOfElementsProjection_isFibredInSets F
    exact inferInstance
  · intro h
    -- Forgetting the extra discrete-fiber owner recovers the ordinary stack-on-site condition.
    let _ : IsStackInSets J ((π F).leftOp) := h
    exact inferInstance

end DescentComparison

/- Domain-style sampling for Lemma 8.6.2:
- primary domain: stacks in sets on a site for the canonical category-of-elements projection
  attached to a set-valued presheaf.
- inspected owner-level declarations:
  `CategoryOfElements.π`,
  `presheaf_categoryOfElementsProjection_isFibredInSets`,
  `IsStackInSets`,
  `IsStackOnSite`.
- best owner abstraction: the chapter’s source-facing owner is `IsStackInSets J ((π F).leftOp)`;
  the weaker predicate `IsStackOnSite J ((π F).leftOp)` is only a derived bridge obtained from
  the already available fibred-in-sets structure on the category-of-elements projection.
- primitive data: a presheaf `F`.
- derived API: the companion bridge to `IsStackOnSite`, obtained by combining
  `presheaf_categoryOfElementsProjection_isFibredInSets` with the source-facing stack-in-sets
  theorem.

Source/core/bridge triage:
- `source-facing`: `presheaf_isSheaf_iff_categoryOfElements_isStackInSets`.
- `core/canonical`: `IsStackInSets J ((π F).leftOp)` together with the canonical instance
  `presheaf_categoryOfElementsProjection_isFibredInSets F`.
- `bridge/view`: `presheaf_isSheaf_iff_categoryOfElements_isStackOnSite`. -/

-- Proof sketch: the category-of-elements projection of `F` is canonically fibred in sets, so the
-- source statement should land directly in the chapter owner `IsStackInSets`. The weaker
-- stack-on-site predicate is then recovered as a thin companion bridge by inference.
/-- Lemma 8.6.2: under the equivalence of Lemma `4.38.6` between set-valued presheaves on `C` and
categories fibred in sets over `C`, a presheaf `F` is a sheaf for `J` exactly when the projection
of its category of elements is a stack in sets over `(C, J)`. -/
@[stacks 0430]
theorem presheaf_isSheaf_iff_categoryOfElements_isStackInSets
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsSheaf J F ↔ IsStackInSets J ((π F).leftOp) := by
  -- Route correction: first prove the coverwise stack-on-site comparison, then recover the
  -- source-facing `IsStackInSets` owner from the already known fibred-in-sets structure.
  exact
    (presheaf_isSheaf_iff_categoryOfElements_isStackOnSite_aux (J := J) (F := F)).trans
      (category_of_elements_stack_on_site_iff_stack_in_sets (J := J) (F := F))

/-- Companion bridge for Lemma 8.6.2: for a set-valued presheaf, the source-facing
`IsStackInSets` statement immediately implies and is implied by the underlying stack-on-site
predicate on the same category-of-elements projection. -/
theorem presheaf_isSheaf_iff_categoryOfElements_isStackOnSite
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsSheaf J F ↔ IsStackOnSite J ((π F).leftOp) := by
  -- The stack-on-site form is the fixed-cover comparison proved on the way to the source owner.
  simpa using presheaf_isSheaf_iff_categoryOfElements_isStackOnSite_aux (J := J) (F := F)

end CategoryTheory
