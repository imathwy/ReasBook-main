import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_8_6_1 (from Chap08) -/
universe u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/-
Domain-style sampling for Definition 8.6.1:
- primary domain: stacks on a site with additional fiberwise setoid/discrete conditions.
- inspected owner-level declarations:
  `IsStackInGroupoids`,
  `IsFibredInSetoids`,
  `IsFibredInSets`.
- best owner abstraction: this chapter already organizes stack-theoretic owners by the projection
  functor `p : S ⥤ C` through the owner `IsStackInGroupoids J p`, so the source-facing notions
  here should refine that owner by adjoining the stronger fiberwise setoid/discrete conditions.
- primitive data: `IsStackInGroupoids J p` together with `IsFibredInSetoids p`, and then
  `IsStackInGroupoids J p` together with `IsFibredInSets p`.
- derived API: the later bundled subcategory `StackInSetoidsOver`, together with the automatic
  bridge from stacks in sets to stacks in setoids.

Source/core/bridge triage:
- `source-facing`: `IsStackInSetoids J p` and `IsStackInSets J p`.
- `core/canonical`: `IsStackInGroupoids`, `IsFibredInSetoids`, `IsFibredInSets`.
- `bridge/view`: the later bundled owner `StackInSetoidsOver`. -/

/-- Definition 8.6.1 (1): a stack in setoids over the site `(C, J)` is a category over `C` whose
projection functor is a stack in groupoids over `(C, J)` and is fibred in setoids. Equivalently,
every fiber category over an object of `C` is a setoid `1`-category. -/
@[mk_iff isStackInSetoids_iff_isFibredInSetoids_and_isStackInGroupoids]
class IsStackInSetoids (J : GrothendieckTopology C) (p : S ⥤ C) : Prop
    extends IsFibredInSetoids p, IsStackInGroupoids J p

/-- A stack in groupoids whose fibers are setoids is a stack in setoids. -/
instance [IsFibredInSetoids p] [IsStackInGroupoids J p] : IsStackInSetoids J p where
  -- The source-facing owner is exactly the conjunction of the setoid-fiber owner and the
  -- inherited stack data carried by `IsStackInGroupoids`.
  toIsFibredInSetoids := inferInstance
  toIsStack := inferInstance

/-- Definition 8.6.1 (2): a stack in sets over `(C, J)` is a stack in groupoids over `(C, J)` whose
fiber category over every object of `C` is discrete. Equivalently, it is a stack in setoids whose
fibers are discrete, or a stack in discrete categories. -/
@[mk_iff isStackInSets_iff_isFibredInSets_and_isStackInGroupoids]
class IsStackInSets (J : GrothendieckTopology C) (p : S ⥤ C) : Prop
    extends IsFibredInSets p, IsStackInGroupoids J p

/-- A stack in groupoids whose fibers are discrete is a stack in sets. -/
instance [IsFibredInSets p] [IsStackInGroupoids J p] : IsStackInSets J p where
  -- The discrete-fiber case is packaged by the same owner-level inheritance pattern, reusing the
  -- stack data already present in `IsStackInGroupoids`.
  toIsFibredInSets := inferInstance
  toIsStack := inferInstance

/-- A stack in sets over `(C, J)` is canonically a stack in setoids. -/
instance [IsStackInSets J p] : IsStackInSetoids J p := by
  -- Route correction: the bridge stays owner-level, so first recover the thin-fiber owner.
  let _ : IsFibredInSetoids p := inferInstance
  -- With the stack and setoid-fiber owners now available, the constructor instance closes.
  exact inferInstance

end

end CategoryTheory

/-! ### Lemma_8_6_2 (from Chap08) -/
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

/-! ### Lemma_8_6_3 (from Chap08) -/
universe u v

namespace CategoryTheory

variable {C : Type u} {S : Type (max u v)} [Category.{v} C] [Category.{v} S]

/- Domain-style sampling for Lemma 8.6.3:
- primary domain: stack conditions on a site for categories fibred in setoids, compared with the
  canonical presheaf of fiberwise isomorphism classes;
- inspected owner-level declarations:
  `IsStackInSetoids`,
  `IsStackOnSite`,
  `Functor.fiberIsoClassPresheaf`,
  `FibredInSetoidsOver.ofFunctor`,
  `FibredInSetoidsOver.associatedFibredInSets`,
  `FibredInSetoidsOver.toFibredInSets`,
  `FibredInSetoidsOver.toFibredInSets_isEquivalenceOverBase`;
- best owner abstraction: the source-facing owner in this section is `IsStackInSetoids J p`; the
  underlying canonical owners are `IsStackOnSite J p` and the presheaf `fiberIsoClassPresheaf p`,
  while bundled `FibredInSetoidsOver` language is only a bridge view used internally;
- primitive data: a functor `p : S ⥤ C` with `[IsFibredInSetoids p]`;
- derived API: the comparison with `IsStackOnSite J p`, plus the bundled equivalence-over-base
  bridge through `FibredInSetoidsOver.ofFunctor p` and `X.associatedFibredInSets`.

Source/core/bridge triage:
- `source-facing`: `isStackInSetoids_iff_isoClassPresheaf_isSheaf`;
- `core/canonical`: `IsStackInSetoids`, `IsStackOnSite`, and `fiberIsoClassPresheaf`;
- `bridge/view`: any bundled reformulation using `FibredInSetoidsOver` or `FibredInSetsOver`. -/

-- Proof sketch: first rewrite `IsStackInSetoids` as the underlying owner `IsStackOnSite`. Then
-- compare `p` coverwise with the associated fibred-in-sets model supplied by Lemma `4.39.5`.
-- Finally identify that associated model with the category of elements of the iso-class
-- presheaf and apply Lemma `8.6.2` in its `IsStackOnSite` form.
/-- Helper for Lemma 8.6.3: for a fibred category in setoids, the source-facing owner
`IsStackInSetoids` is equivalent to the underlying owner `IsStackOnSite`. -/
private lemma stack_in_setoids_iff_stack_on_site
    (J : GrothendieckTopology C) (p : S ⥤ C) [IsFibredInSetoids p] :
    IsStackInSetoids J p ↔ IsStackOnSite J p := by
  constructor
  · intro h
    -- Forgetting from stacks in setoids only drops the explicit source-facing fiber condition.
    let _ : IsStackInSetoids J p := h
    exact inferInstance
  · intro h
    -- Reassemble the source-facing owner from the setoid-fiber hypothesis and `h`.
    let _ : IsStackOnSite J p := h
    exact inferInstance

/-- Helper for Lemma 8.6.3: the canonical associated fibred-in-sets replacement carries the same
stack-on-site condition as the original fibred category in setoids. -/
private lemma associated_sets_model_stack_on_site_iff
    (J : GrothendieckTopology C) (p : S ⥤ C) [IsFibredInSetoids p] :
    IsStackOnSite J p ↔
      IsStackOnSite J (FibredInSetoidsOver.ofFunctor p).associatedFibredInSets.p := by
  let X := FibredInSetoidsOver.ofFunctor p
  let F : BasedCategory.ofFunctor p ⥤ᵇ
      BasedCategory.ofFunctor X.associatedFibredInSets.p :=
    show BasedCategory.ofFunctor p ⥤ᵇ
        BasedCategory.ofFunctor X.associatedFibredInSets.p from
      FibredInSetoidsOver.toBasedFunctor X.toFibredInSets
  have hF : F.IsEquivalenceOverBase := by
    -- The canonical comparison is already proved to be an equivalence over the base.
    simpa [F] using (FibredInSetoidsOver.toFibredInSets_isEquivalenceOverBase X)
  -- Route correction: transport the owner `IsStackOnSite` across the canonical equivalence over
  -- the base instead of rebuilding fixed-cover descent transport locally.
  -- Apply the owner-level equivalence theorem from Lemma `8.4.4` to `X.toFibredInSets`.
  simpa [X] using
    (isStackOnSite_iff_of_equivalence_over_base J
      p X.associatedFibredInSets.p
      F hF)

/-- Helper for Lemma 8.6.3: the associated fibred-in-sets model of a fibred category in setoids is
the category of elements of its iso-class presheaf, so its stack-on-site condition is exactly the
sheaf condition on that presheaf. -/
private lemma associated_sets_model_stack_on_site_iff_iso_class_sheaf
    (J : GrothendieckTopology C) (p : S ⥤ C) [IsFibredInSetoids p] :
    IsStackOnSite J (FibredInSetoidsOver.ofFunctor p).associatedFibredInSets.p ↔
      Presheaf.IsSheaf J p.fiberIsoClassPresheaf := by
  let X := FibredInSetoidsOver.ofFunctor p
  let Y := X.associatedFibredInSets
  -- Identify the associated sets model with the category of elements of the iso-class presheaf.
  simpa [X, Y] using
    (presheaf_isSheaf_iff_categoryOfElements_isStackOnSite J p.fiberIsoClassPresheaf).symm

/-- Lemma 8.6.3: a category fibred in setoids over a site `(C, J)` admits a stack structure if
and only if the presheaf sending `U` to the set of isomorphism classes of objects of the fiber
over `U` is a sheaf. -/
theorem isStackInSetoids_iff_isoClassPresheaf_isSheaf
    (J : GrothendieckTopology C) (p : S ⥤ C) [IsFibredInSetoids p] :
    IsStackInSetoids J p ↔ Presheaf.IsSheaf J p.fiberIsoClassPresheaf := by
  -- First strip the source-facing owner to the underlying stack-on-site condition.
  have hSetoids :
      IsStackInSetoids J p ↔ IsStackOnSite J p :=
    stack_in_setoids_iff_stack_on_site (J := J) (p := p)
  have hTransport :
      IsStackOnSite J p ↔
        IsStackOnSite J (FibredInSetoidsOver.ofFunctor p).associatedFibredInSets.p :=
    associated_sets_model_stack_on_site_iff (J := J) (p := p)
  have hSheaf :
      IsStackOnSite J (FibredInSetoidsOver.ofFunctor p).associatedFibredInSets.p ↔
        Presheaf.IsSheaf J p.fiberIsoClassPresheaf :=
    associated_sets_model_stack_on_site_iff_iso_class_sheaf (J := J) (p := p)
  -- Compose the source-faithful route: setoids -> stack-on-site -> associated sets -> sheaf.
  exact hSetoids.trans (hTransport.trans hSheaf)

end CategoryTheory

/-! ### Lemma_8_6_4 (from Chap08) -/
universe u₁ u₂ u₃ v₁ v₂ v₃

namespace CategoryTheory

open BasedFunctor

section

variable {C : Type u₁} {S₁ : Type u₂} {S₂ : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} S₁] [Category.{v₃} S₂]
variable (J : GrothendieckTopology C)

variable (p₁ : S₁ ⥤ C) (p₂ : S₂ ⥤ C)

/- Domain-style sampling for Lemma 8.6.4:
- primary domain: stack conditions on a site for categories fibred in setoids, transported along
  equivalences over the base category;
- inspected owner-level declarations:
  `IsStackInSetoids`,
  `IsStackInGroupoids`,
  `BasedFunctor.isFibredInSetoids_iff_of_isEquivalenceOverBase`,
  `isStackInGroupoids_iff_of_equivalence_over_base`;
- best owner abstraction: the source-facing owner `IsStackInSetoids J p`; the conjunction
  `IsFibredInSetoids p ∧ IsStackOnSite J p` is derived API and should not remain the main public
  surface;
- primitive data: the projection functor `p : S ⥤ C` and the equivalence-over-base data `hF`;
- derived API: the transported fiberwise thinness, which combines with the existing owner theorem
  `isStackInGroupoids_iff_of_equivalence_over_base` to recover `IsStackInSetoids`.

Source/core/bridge triage:
- `source-facing`: `isStackInSetoids_iff_of_equivalence_over_base`;
- `core/canonical`: `IsStackInSetoids`, `IsStackInGroupoids`, and
  `BasedFunctor.isFibredInSetoids_iff_of_isEquivalenceOverBase`;
- `bridge/view`: transport of the owner components `IsStackInGroupoids` and
  `IsFibredInSetoids` along an equivalence over the base. -/

/-- Lemma 8.6.4: if `S₁` and `S₂` are equivalent as categories over the site `(C, J)`, then
`S₁` is a stack in setoids over `(C, J)` if and only if `S₂` is a stack in setoids over
`(C, J)`. -/
theorem isStackInSetoids_iff_of_equivalence_over_base
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) :
    IsStackInSetoids J p₁ ↔ IsStackInSetoids J p₂ := by
  constructor
  · intro h
    letI : IsStackInSetoids J p₁ := h
    letI : IsStackInGroupoids J p₂ :=
      (isStackInGroupoids_iff_of_equivalence_over_base J p₁ p₂ F hF).1 inferInstance
    have hthin₂ : ∀ U : C, Quiver.IsThin (p₂.Fiber U) := by
      intro U
      letI : (F.fiberFunctor U).IsEquivalence :=
        BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase F hF U
      let e := (F.fiberFunctor U).asEquivalence
      letI : Quiver.IsThin (p₁.Fiber U) := inferInstance
      have hthin : Quiver.IsThin (p₁.Fiber U) := inferInstance
      refine fun X Y ↦ ⟨fun f g ↦ ?_⟩
      have hmap : e.inverse.map f = e.inverse.map g := by
        exact @Subsingleton.elim (e.inverse.obj X ⟶ e.inverse.obj Y) (hthin _ _) _ _
      apply e.inverse.map_injective
      exact hmap
    have hsetoids₂ : IsFibredInSetoids p₂ := by
      letI : ∀ U : C, Quiver.IsThin (p₂.Fiber U) := hthin₂
      infer_instance
    letI : IsFibredInSetoids p₂ := hsetoids₂
    infer_instance
  · intro h
    letI : IsStackInSetoids J p₂ := h
    letI : IsStackInGroupoids J p₁ :=
      (isStackInGroupoids_iff_of_equivalence_over_base J p₁ p₂ F hF).2 inferInstance
    have hthin₁ : ∀ U : C, Quiver.IsThin (p₁.Fiber U) := by
      intro U
      letI : (F.fiberFunctor U).IsEquivalence :=
        BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase F hF U
      let e := (F.fiberFunctor U).asEquivalence
      letI : Quiver.IsThin (p₂.Fiber U) := inferInstance
      have hthin : Quiver.IsThin (p₂.Fiber U) := inferInstance
      refine fun X Y ↦ ⟨fun f g ↦ ?_⟩
      have hmap : e.functor.map f = e.functor.map g := by
        exact @Subsingleton.elim (e.functor.obj X ⟶ e.functor.obj Y) (hthin _ _) _ _
      apply e.functor.map_injective
      exact hmap
    have hsetoids₁ : IsFibredInSetoids p₁ := by
      letI : ∀ U : C, Quiver.IsThin (p₁.Fiber U) := hthin₁
      infer_instance
    letI : IsFibredInSetoids p₁ := hsetoids₁
    infer_instance

end

end CategoryTheory

/-! ### Definition_8_6_5 (from Chap08) -/
universe u v

namespace CategoryTheory

open Bicategory
open Bicategory.InducedBicategory
open ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 8.6.5:
- primary domain: stacks in setoids over a fixed site, organized as a full owner subcategory of
  stacks in groupoids.
- inspected owner-level declarations:
  `StackOver`,
  `StackInGroupoidsOver`,
  `FibredInSetoidsOver`,
  `IsStackInSetoids`.
- best owner abstraction: the primitive owner datum here is an object of `StackInGroupoidsOver J`
  together with the additional fiberwise condition `IsFibredInSetoids X.p`; the stack condition is
  already part of the ambient owner, so it should be derived rather than stored again as
  primitive data.
- primitive data: a bundled stack in groupoids over `(C, J)` and a proof that its projection is
  fibred in setoids.
- derived API: coercions to `StackOver J`, `FibredInSetoidsOver C`, the induced owner
  instance `IsStackInSetoids J X.p`, and the owner-hom bridge surface from `X ⟶ Y` to the
  ambient owner-hom and `FibredCategoryMor`/based-functor APIs.

Source/core/bridge triage:
- `source-facing`: `StackInSetoidsOver J`.
- `core/canonical`: `StackInGroupoidsOver J`, `FibredInSetoidsOver C`, `IsFibredInSetoids`, and
  `IsStackInSetoids`.
- `bridge/view`: the forgetful coercions to stacks over `(C, J)` and to categories fibred in
  setoids over `C`, together with the canonical morphism bridge to the ambient setoid-stack
  morphism APIs. -/

/-- Definition 8.6.5 (1): the `2`-category of stacks in setoids over the site `(C, J)` is the full
sub-`2`-category of stacks in groupoids over `(C, J)` cut out by the additional owner predicate
`IsFibredInSetoids X.p`. Equivalently, it is the full sub-`2`-category of stacks over `(C, J)`
whose projection functor satisfies `IsStackInSetoids J X.p`. -/
abbrev stackInSetoidsOverSubTwoCategory (J : GrothendieckTopology C) :
    SubTwoCategory (StackInGroupoidsOver J) where
  obj := fun X ↦ IsFibredInSetoids X.p
  hom _ _ := {
    obj := ⊤
    hom := ⊤
    hom_isMultiplicative := inferInstance
  }
  id_mem _ := by trivial
  comp_mem _ _ := by trivial
  whiskerLeft_mem _ _ _ _ := by trivial
  whiskerRight_mem _ _ _ _ := by trivial

/-- The owner predicate for the canonical sub-`2`-category of stacks in setoids is exactly
`IsFibredInSetoids` on the projection functor. -/
-- Proof sketch: this is immediate from the defining object predicate of
-- `stackInSetoidsOverSubTwoCategory`.
theorem stackInSetoidsOverSubTwoCategory_obj_iff
    (J : GrothendieckTopology C) (X : StackInGroupoidsOver J) :
    (stackInSetoidsOverSubTwoCategory J).obj X ↔ IsFibredInSetoids X.p := by
  -- Unfold the owner predicate of the defining full sub-`2`-category.
  rfl

/-- Definition 8.6.5 (2): the objects of the canonical owner sub-`2`-category
`stackInSetoidsOverSubTwoCategory J` are stacks in setoids over `(C, J)`. -/
abbrev StackInSetoidsOver (J : GrothendieckTopology C) :=
  (stackInSetoidsOverSubTwoCategory J).Obj

namespace StackInSetoidsOver

variable {J : GrothendieckTopology C}
variable {D : Type (max u v)} [Category.{v} D]

/-- Bundle a projection `p : D ⥤ C` that is already known to be a stack in setoids over
`(C, J)`. -/
abbrev ofProjection (J : GrothendieckTopology C) (p : D ⥤ C) [IsStackInSetoids J p] :
    StackInSetoidsOver J :=
  ⟨StackInGroupoidsOver.ofProjection J p, by
    simpa [StackInGroupoidsOver.p, StackInGroupoidsOver.ofProjection] using
      (inferInstance : IsFibredInSetoids p)⟩

/-- The underlying stack in groupoids over `(C, J)`. -/
abbrev toStackInGroupoidsOver (X : StackInSetoidsOver J) : StackInGroupoidsOver J :=
  X.obj

/-- The underlying stack over `(C, J)`. -/
abbrev toStackOver (X : StackInSetoidsOver J) : StackOver J :=
  X.toStackInGroupoidsOver.toStackOver

/-- The underlying category fibred in groupoids over `C`. -/
abbrev toFibredInGroupoidsOver (X : StackInSetoidsOver J) : FibredInGroupoidsOver C :=
  X.toStackInGroupoidsOver.toFibredInGroupoidsOver

/-- The underlying category fibred in setoids over `C`. -/
abbrev toFibredInSetoidsOver (X : StackInSetoidsOver J) : FibredInSetoidsOver C :=
  ⟨X.toFibredInGroupoidsOver, X.property⟩

/-- The underlying fibred category over `C`. -/
abbrev toFibredCategoryOver (X : StackInSetoidsOver J) : FibredCategoryOver C :=
  X.toStackInGroupoidsOver.toFibredCategoryOver

/-- The underlying category over `C`. -/
abbrev toCategoryOver (X : StackInSetoidsOver J) : CategoryOver C :=
  X.toStackInGroupoidsOver.toCategoryOver

/-- The total category of a bundled stack in setoids over `(C, J)`. -/
abbrev S (X : StackInSetoidsOver J) :=
  X.toStackInGroupoidsOver.S

/-- The projection functor of a bundled stack in setoids over `(C, J)`. -/
abbrev p (X : StackInSetoidsOver J) :=
  X.toStackInGroupoidsOver.p

/-- The underlying based category over `C` of a stack in setoids over `(C, J)`. -/
abbrev toBasedCategory (X : StackInSetoidsOver J) : BasedCategory C :=
  X.toStackInGroupoidsOver.toBasedCategory

instance : CoeOut (StackInSetoidsOver J) (StackInGroupoidsOver J) where
  coe X := X.toStackInGroupoidsOver

instance : CoeOut (StackInSetoidsOver J) (StackOver J) where
  coe X := X.toStackOver

instance : CoeOut (StackInSetoidsOver J) (FibredInGroupoidsOver C) where
  coe X := X.toFibredInGroupoidsOver

instance : CoeOut (StackInSetoidsOver J) (FibredInSetoidsOver C) where
  coe X := X.toFibredInSetoidsOver

instance : CoeOut (StackInSetoidsOver J) (FibredCategoryOver C) where
  coe X := X.toFibredCategoryOver

instance : CoeOut (StackInSetoidsOver J) (CategoryOver C) where
  coe X := X.toCategoryOver

instance : CoeOut (StackInSetoidsOver J) (BasedCategory C) where
  coe X := X.toBasedCategory

instance (X : StackInSetoidsOver J) : IsFibredInSetoids X.p := by
  simpa [StackInSetoidsOver.p, StackInGroupoidsOver.p] using X.property

instance (X : StackInSetoidsOver J) : IsStackInGroupoids J X.p := by
  change IsStackInGroupoids J X.obj.p
  infer_instance

instance (X : StackInSetoidsOver J) : IsStackInSetoids J X.p :=
  inferInstance

instance (X : StackInSetoidsOver J) : IsStackOnSite J X.p :=
  inferInstance

variable {X Y : StackInSetoidsOver J}

end StackInSetoidsOver

instance (J : GrothendieckTopology C) : Bicategory (StackInSetoidsOver J) :=
  SubTwoCategory.bicategoryObj (stackInSetoidsOverSubTwoCategory J)

instance (J : GrothendieckTopology C) : Strict (StackInSetoidsOver J) :=
  SubTwoCategory.strictObj (stackInSetoidsOverSubTwoCategory J)

instance (J : GrothendieckTopology C) : Bicategory.Strict (StackInSetoidsOver J) :=
  inferInstance

instance (J : GrothendieckTopology C) : Category (StackInSetoidsOver J) :=
  StrictBicategory.category (StackInSetoidsOver J)

instance stackInSetoidsOverHom₂IsMultiplicative
    (J : GrothendieckTopology C) (X Y : StackInSetoidsOver J) :
    ((stackInSetoidsOverSubTwoCategory J).hom X Y).hom.IsMultiplicative :=
  ((stackInSetoidsOverSubTwoCategory J).hom X Y).hom_isMultiplicative

instance stackInSetoidsOverHomInclusionFull
    (J : GrothendieckTopology C) (X Y : StackInSetoidsOver J) :
    (((stackInSetoidsOverSubTwoCategory J).hom X Y).inclusion).Full where
  map_surjective := by
    intro F G η
    refine ⟨⟨ObjectProperty.homMk η, trivial⟩, rfl⟩

namespace StackInSetoidsOver

variable {J : GrothendieckTopology C}
variable {X Y : StackInSetoidsOver J}

/-- Regard an ambient morphism in `StackInGroupoidsOver J` as the corresponding owner hom in the
full sub-`2`-category `StackInSetoidsOver J`. -/
abbrev ofAmbientHom
    (F : X.toStackInGroupoidsOver ⟶ Y.toStackInGroupoidsOver) :
    X ⟶ Y :=
  ⟨⟨F, trivial⟩⟩

abbrev toStackInGroupoidsHom (F : X ⟶ Y) :
    X.toStackInGroupoidsOver ⟶ Y.toStackInGroupoidsOver :=
  SubTwoCategory.Hom.toHom F

@[simp]
theorem toStackInGroupoidsHom_ofAmbientHom
    (F : X.toStackInGroupoidsOver ⟶ Y.toStackInGroupoidsOver) :
    toStackInGroupoidsHom (ofAmbientHom F) = F :=
  rfl

@[simp]
theorem toStackInGroupoidsHom_comp
    {Z : StackInSetoidsOver J}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    toStackInGroupoidsHom (F ≫ G) =
      toStackInGroupoidsHom F ≫ toStackInGroupoidsHom G :=
  rfl

@[simp]
theorem ofAmbientHom_comp_obj
    {Z : StackInSetoidsOver J}
    (F : X.toStackInGroupoidsOver ⟶ Y.toStackInGroupoidsOver)
    (G : Y ⟶ Z) :
    ((ofAmbientHom F) ≫ G).obj.obj = F ≫ G.obj.obj :=
  rfl

@[simp]
theorem comp_ofAmbientHom_obj
    {Z : StackInSetoidsOver J}
    (F : X ⟶ Y)
    (G : Y.toStackInGroupoidsOver ⟶ Z.toStackInGroupoidsOver) :
    (F ≫ ofAmbientHom G).obj.obj = F.obj.obj ≫ G :=
  rfl

set_option maxHeartbeats 1000000 in
/-- Convert an isomorphism between ambient stack-in-groupoids morphisms into an isomorphism in the
owner hom-category of stacks in setoids over `(C, J)`. -/
noncomputable def ofAmbientHomIso
    {F G : X ⟶ Y}
    (e : toStackInGroupoidsHom F ≅ toStackInGroupoidsHom G) :
    F ≅ G :=
  SubTwoCategory.Hom.isoMk e
    (show ((stackInSetoidsOverSubTwoCategory J).hom X Y).hom
        (ObjectProperty.homMk e.hom) from trivial)
    (show ((stackInSetoidsOverSubTwoCategory J).hom X Y).hom
        (ObjectProperty.homMk e.inv) from trivial)

end StackInSetoidsOver

variable {J : GrothendieckTopology C}
variable {X Y : StackInSetoidsOver J}

instance : CoeOut (X ⟶ Y)
    (X.toStackInGroupoidsOver ⟶ Y.toStackInGroupoidsOver) where
  coe F := StackInSetoidsOver.toStackInGroupoidsHom F

instance : CoeOut (X ⟶ Y)
    (FibredInGroupoidsMor X.toFibredInGroupoidsOver Y.toFibredInGroupoidsOver) where
  coe F :=
    StackInGroupoidsOver.Hom.toFibredInGroupoidsMor
      (show X.toStackInGroupoidsOver ⟶ Y.toStackInGroupoidsOver from F)

instance : CoeOut (X ⟶ Y)
    (X.toFibredInSetoidsOver ⟶ Y.toFibredInSetoidsOver) where
  coe F :=
    FibredInSetoidsOver.ofAmbientHom
      (show FibredInGroupoidsMor X.toFibredInGroupoidsOver Y.toFibredInGroupoidsOver from F)

instance : CoeOut (X ⟶ Y) (X.toStackOver ⟶ Y.toStackOver) where
  coe F :=
    show X.toStackOver ⟶ Y.toStackOver from
      InducedCategory.Hom.ofFibredCategoryMor
        (show FibredCategoryMor X.toStackOver.toFibredCategoryOver Y.toStackOver.toFibredCategoryOver from
          (show FibredInGroupoidsMor X.toFibredInGroupoidsOver Y.toFibredInGroupoidsOver from F).toHom)

end CategoryTheory

/-! ### Lemma_8_6_6 (from Chap08) -/
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
        (toStackInGroupoidsHom G)).p := sorry

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
      (ambientTwoFibreProductSquare F G).obj.p := sorry

/-- The canonical `2`-commutative square in `StackInSetoidsOver J`, obtained by restricting the
canonical stack-in-groupoids pullback square to the full sub-`2`-category of stacks in setoids
through the Chapter 8 bridge `ofStackInGroupoidsSquare`. -/
@[irreducible] noncomputable def twoFibreProductSquare
    (F : X ⟶ S) (G : Y ⟶ S) :
    BicategoricalTwoCommutativeSquare F G :=
  ofStackInGroupoidsSquare (F := F) (G := G)
    (ambientTwoFibreProductSquare F G)
    (ambientTwoFibreProductSquare_isFibredInSetoids F G)

-- Proof sketch: start from the canonical stack-in-groupoids pullback square, whose finality is
-- Lemma `8.5.6`, and restrict that universal property to the full sub-`2`-category of stacks in
-- setoids using the bridge `ofStackInGroupoidsSquare`.
/-- Lemma 8.6.6: the `2`-category of stacks in setoids over the site `(C, J)` has `2`-fibre
products, and the canonical square `twoFibreProductSquare F G` is described by the same explicit
pullback model as in Categories, Lemma `4.32.3`. -/
theorem twoFibreProduct_isTwoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.IsFinal (twoFibreProductSquare F G) := sorry

end StackInSetoidsOver

end

end CategoryTheory
