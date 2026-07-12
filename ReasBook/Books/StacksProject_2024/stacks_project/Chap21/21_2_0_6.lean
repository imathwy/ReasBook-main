import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace CategoryTheory
namespace Sheaf

noncomputable section

/- Domain-style sampling for 21.2.0.6:
- primary domain: global sheaf cohomology on a site, computed from a chosen injective resolution
  by the homology of the global-sections complex;
- sampled owner API:
  `CategoryTheory.Sheaf.H`,
  `CategoryTheory.Sheaf.cohomologyFunctor`,
  `CategoryTheory.Sheaf.Γ`,
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- best owner abstraction: the source-facing comparison between global sheaf cohomology and the
  degreewise homology of the global-sections complex of a chosen injective resolution, with a
  companion surface on `Sheaf.cohomologyFunctor`;
- primitive data: a site `(C, J)`, an abelian sheaf `F`, a chosen injective resolution
  `I : InjectiveResolution F`, and a degree `i : ℕ`.

Source/core/bridge triage:
- `source-facing`: the Stacks statement computing `H^i(\mathcal C, F)` from global sections of a
  chosen injective resolution;
- `core/canonical`: `CategoryTheory.Sheaf.H`, `CategoryTheory.Sheaf.cohomologyFunctor`;
- `bridge/view`: the generic comparison `CategoryTheory.InjectiveResolution.isoRightDerivedObj`
  specialized to the global-sections functor `CategoryTheory.Sheaf.Γ`.

This file keeps the source-facing comparison theorem as its main public entry and packages the
needed global-sections comparison directly from the constant-sheaf/global-sections adjunction. -/

/- 21.2.0.6: the homology of the global-sections complex of a chosen injective resolution
computes global sheaf cohomology on the site. -/

section

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{u}]
variable [HasGlobalSectionsFunctor J AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
variable {F : Sheaf J AddCommGrpCat.{u}}

local instance : HasWeakSheafify J AddCommGrpCat.{u} :=
  HasSheafify.isRightAdjoint

/-- Helper for 21.2.0.6: the constant integer sheaf on `(C, J)` used by
`Sheaf.cohomologyFunctor J`. -/
private abbrev constantIntegerSheaf : Sheaf J AddCommGrpCat.{u} :=
  (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))

/-- Helper for 21.2.0.6: `AddCommGrpCat` is additively corepresented by `ULift ℤ`. -/
private noncomputable def addCommGrpForgetCorepresentableByULiftIntAdditive
    (A : AddCommGrpCat.{u}) :
    A ≃+ (AddCommGrpCat.of (ULift ℤ) ⟶ A) where
  toFun x :=
    AddCommGrpCat.ofHom <|
      AddMonoidHom.mk'
        (fun n : ULift ℤ ↦ n.down • x)
        (fun m n ↦ by simp [add_zsmul])
  invFun f := f (ULift.up 1)
  left_inv x := by
    -- Evaluating the representing morphism at `1` recovers the chosen section.
    simp
  right_inv f := by
    -- A morphism out of `ULift ℤ` is determined by the image of `1`.
    ext n
    exact (by simpa using (map_zsmul (ConcreteCategory.hom f) n.down (1 : ULift ℤ)).symm)
  map_add' x y := by
    -- Pointwise, `n • (x + y)` splits as the sum of `n • x` and `n • y`.
    ext n
    simp

omit [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] in
/-- Helper for 21.2.0.6: the explicit `ULift ℤ` corepresentability is natural in the target
abelian group. -/
private theorem addCommGrpForgetCorepresentableByULiftIntAdditive_naturality
    {A B : AddCommGrpCat.{u}} (f : A ⟶ B) (x : A) :
    addCommGrpForgetCorepresentableByULiftIntAdditive B (f x) =
      addCommGrpForgetCorepresentableByULiftIntAdditive A x ≫ f := by
  -- Both explicit additive homs send `n` to `n • f x`.
  ext n
  change n.down • f x = f (n.down • x)
  exact (by simpa using (map_zsmul (ConcreteCategory.hom f) n.down x).symm)

/-- Helper for 21.2.0.6: the constant sheaf functor on abelian groups is additive. -/
private instance constantPresheafAdditive :
    (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u})).Additive where
  map_add := by
    intro X Y f g
    ext n
    rfl

/-- Helper for 21.2.0.6: the constant sheaf functor on abelian groups is additive. -/
private instance constantSheafAdditive :
    (constantSheaf J AddCommGrpCat.{u}).Additive := by
  -- `constantSheaf` is `Functor.const ⋙ presheafToSheaf`, and both factors are additive.
  dsimp [constantSheaf]
  letI : (presheafToSheaf J AddCommGrpCat.{u}).Additive := inferInstance
  infer_instance

/-- Helper for 21.2.0.6: global sections identify additively with morphisms from the constant
integer sheaf. -/
private noncomputable def globalSectionsAddEquivConstantIntegerSheafHom
    (F : Sheaf J AddCommGrpCat.{u}) :
    ((Γ J AddCommGrpCat.{u}).obj F) ≃+
      (constantIntegerSheaf (J := J) ⟶ F) :=
  -- Compose the explicit `ULift ℤ` corepresentability with the global-sections adjunction.
  (addCommGrpForgetCorepresentableByULiftIntAdditive _).trans
    ((constantSheafΓAdj J AddCommGrpCat.{u}).homAddEquiv _ F).symm

omit [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] in
/-- Helper for 21.2.0.6: the additive comparison `Γ ≃ Hom(constantIntegerSheaf,-)` is natural in
the sheaf variable. -/
private theorem globalSectionsAddEquivConstantIntegerSheafHom_naturality
    {F G : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ G)
    (x : (Γ J AddCommGrpCat.{u}).obj F) :
    globalSectionsAddEquivConstantIntegerSheafHom (J := J) G
        ((Γ J AddCommGrpCat.{u}).map f x) =
      globalSectionsAddEquivConstantIntegerSheafHom (J := J) F x ≫ f := by
  -- Unfold the additive bridge to the explicit `ULift ℤ`-indexed morphism in global sections.
  simp only [globalSectionsAddEquivConstantIntegerSheafHom, AddEquiv.trans_apply]
  rw [addCommGrpForgetCorepresentableByULiftIntAdditive_naturality
    ((Γ J AddCommGrpCat.{u}).map f) x]
  -- Then move postcomposition along `f` through the inverse adjunction map.
  simpa using
    (constantSheafΓAdj J AddCommGrpCat.{u}).homEquiv_naturality_right_symm
      (addCommGrpForgetCorepresentableByULiftIntAdditive
        ((Γ J AddCommGrpCat.{u}).obj F) x) f

/-- Helper for 21.2.0.6: global sections identify additively with the degree-zero Ext functor
from the constant integer sheaf. -/
private noncomputable def globalSectionsAddEquivExtZeroConstantSheaf
    (F : Sheaf J AddCommGrpCat.{u}) :
    ((Γ J AddCommGrpCat.{u}).obj F) ≃+
      ((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0).obj F) :=
  (globalSectionsAddEquivConstantIntegerSheafHom (J := J) F).trans
    Abelian.Ext.addEquiv₀.symm

omit [HasGlobalSectionsFunctor J AddCommGrpCat.{u}] in
/-- Helper for 21.2.0.6: under `Ext.addEquiv₀`, the degree-zero Ext map is ordinary
postcomposition. -/
private theorem extZero_addEquiv₀_map
    {F G : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ G)
    (e : Abelian.Ext (constantIntegerSheaf (J := J)) F 0) :
    Abelian.Ext.addEquiv₀
        (((Abelian.Ext.mk₀ f).postcomp (constantIntegerSheaf (J := J)) (add_zero 0)) e) =
      Abelian.Ext.addEquiv₀ e ≫ f := by
  obtain ⟨g, rfl⟩ := Abelian.Ext.homEquiv₀.symm.surjective e
  -- Replace the class by an actual morphism and compute the Yoneda product explicitly.
  rw [← Abelian.Ext.homEquiv₀_symm_apply]
  change
    Abelian.Ext.addEquiv₀
        ((Abelian.Ext.mk₀ g).comp (Abelian.Ext.mk₀ f) (add_zero 0)) =
      Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g) ≫ f
  rw [Abelian.Ext.mk₀_comp_mk₀]
  have hg₀ : Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g) = g := by
    apply Abelian.Ext.homEquiv₀.symm.injective
    simp [Abelian.Ext.homEquiv₀_symm_apply]
  apply Abelian.Ext.homEquiv₀.symm.injective
  simp [Abelian.Ext.homEquiv₀_symm_apply, hg₀]

/-- Helper for 21.2.0.6: the additive comparison `Γ ≃ Ext^0(constantIntegerSheaf,-)` is natural
in the sheaf variable. -/
private theorem globalSectionsAddEquivExtZeroConstantSheaf_naturality
    {F G : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ G)
    (x : (Γ J AddCommGrpCat.{u}).obj F) :
    globalSectionsAddEquivExtZeroConstantSheaf (J := J) G
        ((Γ J AddCommGrpCat.{u}).map f x) =
      ((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0).map f)
        (globalSectionsAddEquivExtZeroConstantSheaf (J := J) F x) := by
  -- Apply the degree-zero `Ext = Hom` bridge so the target map becomes postcomposition.
  apply Abelian.Ext.addEquiv₀.injective
  calc
    Abelian.Ext.addEquiv₀
        (globalSectionsAddEquivExtZeroConstantSheaf (J := J) G
          ((Γ J AddCommGrpCat.{u}).map f x)) =
      globalSectionsAddEquivConstantIntegerSheafHom (J := J) G
        ((Γ J AddCommGrpCat.{u}).map f x) := by
          simpa [globalSectionsAddEquivExtZeroConstantSheaf] using
            (AddEquiv.apply_symm_apply Abelian.Ext.addEquiv₀
              ((globalSectionsAddEquivConstantIntegerSheafHom (J := J) G)
                ((Γ J AddCommGrpCat.{u}).map f x)))
    _ = globalSectionsAddEquivConstantIntegerSheafHom (J := J) F x ≫ f := by
          exact globalSectionsAddEquivConstantIntegerSheafHom_naturality (J := J) f x
    _ = Abelian.Ext.addEquiv₀
          (globalSectionsAddEquivExtZeroConstantSheaf (J := J) F x) ≫ f := by
          symm
          simpa [globalSectionsAddEquivExtZeroConstantSheaf] using
            congrArg (fun t => t ≫ f)
              (AddEquiv.apply_symm_apply Abelian.Ext.addEquiv₀
                ((globalSectionsAddEquivConstantIntegerSheafHom (J := J) F) x))
    _ = Abelian.Ext.addEquiv₀
          (((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0).map f)
            (globalSectionsAddEquivExtZeroConstantSheaf (J := J) F x)) := by
          symm
          simpa using
            extZero_addEquiv₀_map (J := J) f
              (globalSectionsAddEquivExtZeroConstantSheaf (J := J) F x)

/-- Helper for 21.2.0.6: package `Γ ≅ Ext^0(constantIntegerSheaf,-)` as a natural isomorphism of
additive functors. -/
private noncomputable def globalSectionsIsoExtZeroConstantSheaf :
    Γ J AddCommGrpCat.{u} ≅
      Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0 :=
  NatIso.ofComponents
    (fun F ↦ (globalSectionsAddEquivExtZeroConstantSheaf (J := J) F).toAddCommGrpIso)
    (fun f ↦ by
      -- Naturality is checked elementwise on global sections.
      ext x
      exact globalSectionsAddEquivExtZeroConstantSheaf_naturality (J := J) f x)

omit [HasGlobalSectionsFunctor J AddCommGrpCat.{u}] in
/-- Helper for 21.2.0.6: `Sheaf.cohomologyFunctor J i` is definitionally the Ext functor from the
constant integer sheaf. -/
private theorem cohomologyFunctor_eq_extFunctorObj_constantIntegerSheaf
    (i : ℕ) :
    Sheaf.cohomologyFunctor J i =
      Abelian.extFunctorObj (constantIntegerSheaf (J := J)) i := by
  -- `Sheaf.cohomologyFunctor` is introduced exactly as this Ext owner.
  rfl

/-- Helper for 21.2.0.6: isomorphisms on source and target induce an additive equivalence on the
corresponding Hom groups. -/
private theorem isoHomCongrAddEquivMapAdd
    {C : Type*} [Category C] [Preadditive C] {X Y X' Y' : C}
    (eX : X ≅ X') (eY : Y ≅ Y') (f g : X ⟶ Y) :
    eX.homCongr eY (f + g) = eX.homCongr eY f + eX.homCongr eY g := by
  -- Additivity is exactly bilinearity of composition inside `Iso.homCongr`.
  simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-- Helper for 21.2.0.6: isomorphisms on source and target induce an additive equivalence on the
corresponding Hom groups. -/
private noncomputable def isoHomCongrAddEquiv
    {C : Type*} [Category C] [Preadditive C] {X Y X' Y' : C}
    (eX : X ≅ X') (eY : Y ≅ Y') :
    (X ⟶ Y) ≃+ (X' ⟶ Y') where
  toEquiv := eX.homCongr eY
  map_add' := isoHomCongrAddEquivMapAdd eX eY

/-- Helper for 21.2.0.6: for a chosen injective resolution, the degree-`n` term of the mapped
degree-zero Ext cocomplex already identifies with the corresponding degree of the restricted Hom
complex. -/
private noncomputable def mappedExtZeroCocomplexXIsoRestrictedHomX
    (F : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution F) (n : ℕ) :
    ((((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).X n) ≅
      ((CochainComplex.HomComplex
          ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
            (constantIntegerSheaf (J := J)))
          I.cochainComplex).restriction ComplexShape.embeddingUpNat).X n := by
  let hext :
      ((((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex).X n) ≅
        AddCommGrpCat.of ((constantIntegerSheaf (J := J)) ⟶ I.cocomplex.X n) := by
    -- The mapped cocomplex term is definitionally the degree-zero `Ext` object at `I^n`.
    simpa [CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
      (Abelian.Ext.addEquiv₀
        (X := (constantIntegerSheaf (J := J))) (Y := I.cocomplex.X n)).toAddCommGrpIso
  let htransport :
      AddCommGrpCat.of ((constantIntegerSheaf (J := J)) ⟶ I.cocomplex.X n) ≅
        AddCommGrpCat.of ((constantIntegerSheaf (J := J)) ⟶ I.cochainComplex.X (n : ℤ)) := by
    -- The resolution term in degree `n` is the same object viewed inside the extended
    -- `ℤ`-indexed cochain complex.
    simpa using
      (isoHomCongrAddEquiv (Iso.refl (constantIntegerSheaf (J := J)))
        (I.cochainComplexXIso (n : ℤ) n rfl).symm).toAddCommGrpIso
  let hcochain :
      AddCommGrpCat.of ((constantIntegerSheaf (J := J)) ⟶ I.cochainComplex.X (n : ℤ)) ≅
        (CochainComplex.HomComplex
          ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
            (constantIntegerSheaf (J := J)))
          I.cochainComplex).X (ComplexShape.embeddingUpNat.f n) := by
    -- Degree-`n` cochains from the single complex are literally maps into `I^n`.
    simpa using
      ((CochainComplex.HomComplex.Cochain.fromSingleEquiv
          (K := I.cochainComplex)
          (X := (constantIntegerSheaf (J := J)))
          (p := 0) (q := (n : ℤ)) (n := (n : ℤ))
          (by simp)).symm.toAddCommGrpIso)
  -- Compose the four source-faithful bridges: `Ext^0 = Hom`, transport along the chosen
  -- extension to a `ℤ`-indexed complex, identify degree-`n` cochains, then restrict back.
  exact
    hext ≪≫ htransport ≪≫ hcochain ≪≫
      ((CochainComplex.HomComplex
          ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
            (constantIntegerSheaf (J := J)))
          I.cochainComplex).restrictionXIso ComplexShape.embeddingUpNat rfl).symm

omit [HasGlobalSectionsFunctor J AddCommGrpCat.{u}] in
/-- Helper for 21.2.0.6: after forgetting the final restriction transport, the degreewise
`Ext^0 = Hom` comparison sends the generator `Ext.mk₀ g` to the single-supported cochain
determined by `g`. -/
private theorem mappedExtZeroComponentToFullHomApplyMk₀
    (F : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution F) (n : ℕ)
    (g : (constantIntegerSheaf (J := J)) ⟶ I.cocomplex.X n) :
    (((mappedExtZeroCocomplexXIsoRestrictedHomX (J := J) F I n).hom ≫
        ((CochainComplex.HomComplex
            ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
              (constantIntegerSheaf (J := J)))
            I.cochainComplex).restrictionXIso ComplexShape.embeddingUpNat rfl).hom)
        (Abelian.Ext.mk₀ g)) =
      CochainComplex.HomComplex.Cochain.fromSingleMk
        (g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv) (by simp) := by
  let e :
      ((CochainComplex.HomComplex
          ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
            (constantIntegerSheaf (J := J)))
          I.cochainComplex).X (ComplexShape.embeddingUpNat.f n)) ≃+
        ((constantIntegerSheaf (J := J)) ⟶ I.cochainComplex.X (n : ℤ)) :=
    CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (K := I.cochainComplex)
      (X := (constantIntegerSheaf (J := J)))
      (p := 0) (q := (n : ℤ)) (n := (n : ℤ))
      (by simp)
  -- Apply the single-supported cochain equivalence so each factor of the composite can be
  -- simplified independently.
  apply e.injective
  have hmk : Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g) = g := by
    -- `Ext.addEquiv₀` sends `Ext.mk₀ g` back to the morphism `g`.
    apply Abelian.Ext.homEquiv₀.symm.injective
    exact (by simpa using (Abelian.Ext.mk₀_addEquiv₀_apply (Abelian.Ext.mk₀ g)))
  -- The source composite is exactly `Ext.addEquiv₀`, transport along `I.cochainComplexXIso`,
  -- and then the inverse of `fromSingleEquiv`.
  calc
    e
        (((mappedExtZeroCocomplexXIsoRestrictedHomX (J := J) F I n).hom ≫
            ((CochainComplex.HomComplex
                ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
                  (constantIntegerSheaf (J := J)))
                I.cochainComplex).restrictionXIso ComplexShape.embeddingUpNat rfl).hom)
          (Abelian.Ext.mk₀ g)) =
      (isoHomCongrAddEquiv (Iso.refl (constantIntegerSheaf (J := J)))
          ((I.cochainComplexXIso (n : ℤ) n rfl).symm))
        (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g)) := by
          simpa [Function.comp, e, mappedExtZeroCocomplexXIsoRestrictedHomX,
            isoHomCongrAddEquiv, HomologicalComplex.restrictionXIso] using
            (AddEquiv.apply_symm_apply e
              ((isoHomCongrAddEquiv (Iso.refl (constantIntegerSheaf (J := J)))
                ((I.cochainComplexXIso (n : ℤ) n rfl).symm))
                (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g))))
    _ = g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv := by
          rw [hmk]
          simp [isoHomCongrAddEquiv]
    _ = e
          (CochainComplex.HomComplex.Cochain.fromSingleMk
            (g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv) (by simp)) := by
          symm
          simpa [e] using
            (AddEquiv.apply_symm_apply e
              (g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv))

omit [HasGlobalSectionsFunctor J AddCommGrpCat.{u}] in
/-- Helper for 21.2.0.6: on the mapped degree-zero Ext cocomplex, the successor differential
sends the generator `Ext.mk₀ g` to the generator coming from postcomposition by the cocomplex
differential. -/
private theorem mappedExtZeroCocomplexDApplyMk₀
    (F : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution F) (n : ℕ)
    (g : (constantIntegerSheaf (J := J)) ⟶ I.cocomplex.X n) :
    (((((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex).d n (n + 1))
      (Abelian.Ext.mk₀ g)) =
        Abelian.Ext.mk₀ (g ≫ I.cocomplex.d n (n + 1)) := by
  have hmk₀Apply {Y : Sheaf J AddCommGrpCat.{u}}
      (h : (constantIntegerSheaf (J := J)) ⟶ Y) :
      Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ h) = h := by
    -- `Ext.addEquiv₀` is inverse to the degree-zero constructor `Ext.mk₀`.
    apply Abelian.Ext.homEquiv₀.symm.injective
    simp [Abelian.Ext.homEquiv₀_symm_apply]
  -- Reduce the mapped cocomplex differential to the owner map
  -- `(Abelian.extFunctorObj ... 0).map (I.cocomplex.d n (n + 1))`.
  apply Abelian.Ext.addEquiv₀.injective
  calc
    Abelian.Ext.addEquiv₀
        (((((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj I.cocomplex).d n (n + 1))
          (Abelian.Ext.mk₀ g)) =
      Abelian.Ext.addEquiv₀
        (((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0).map
            (I.cocomplex.d n (n + 1)))
          (Abelian.Ext.mk₀ g)) := by
          rfl
    _ = Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g) ≫ I.cocomplex.d n (n + 1) := by
          exact extZero_addEquiv₀_map (J := J) (I.cocomplex.d n (n + 1)) (Abelian.Ext.mk₀ g)
    _ = g ≫ I.cocomplex.d n (n + 1) := by rw [hmk₀Apply g]
    _ = Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ (g ≫ I.cocomplex.d n (n + 1))) := by
          rw [hmk₀Apply (g ≫ I.cocomplex.d n (n + 1))]

omit [HasGlobalSectionsFunctor J AddCommGrpCat.{u}] in
/-- Helper for 21.2.0.6: after transporting the degree-zero Ext generator into the full Hom
complex, the full differential is computed by the usual single-supported cochain formula. -/
private theorem mappedExtZeroFullHomDApplyMk₀
    (F : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution F) (n : ℕ)
    (g : (constantIntegerSheaf (J := J)) ⟶ I.cocomplex.X n) :
    ((CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
          (constantIntegerSheaf (J := J)))
        I.cochainComplex).d (n : ℤ) ((n + 1 : ℕ) : ℤ))
        ((((mappedExtZeroCocomplexXIsoRestrictedHomX (J := J) F I n).hom ≫
            ((CochainComplex.HomComplex
                ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
                  (constantIntegerSheaf (J := J)))
                I.cochainComplex).restrictionXIso ComplexShape.embeddingUpNat rfl).hom)
          (Abelian.Ext.mk₀ g))) =
      CochainComplex.HomComplex.Cochain.fromSingleMk
        (((g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv) ≫
            I.cochainComplex.d (n : ℤ) ((n + 1 : ℕ) : ℤ)))
        (by simp) := by
  -- First normalize the transported Ext class to the corresponding single-supported cochain.
  rw [mappedExtZeroComponentToFullHomApplyMk₀ (J := J) F I n g]
  -- Then the full Hom-complex differential is exactly `δ_fromSingleMk`.
  simpa [Category.assoc] using
    (CochainComplex.HomComplex.Cochain.δ_fromSingleMk
      (K := I.cochainComplex)
      (X := (constantIntegerSheaf (J := J)))
      (p := 0)
      (f := g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv)
      (n := (n : ℤ))
      (h := by simp)
      (((n + 1 : ℕ) : ℤ))
      (((n + 1 : ℕ) : ℤ))
      (by simp))

omit [HasGlobalSectionsFunctor J AddCommGrpCat.{u}] in
/-- Helper for 21.2.0.6: in successor degree, the transported Ext generator is already in the
target `fromSingleMk` normal form after forgetting the restriction transport. -/
private theorem mappedExtZeroSuccessorComponentToFullHomApplyMk₀
    (F : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution F) (n : ℕ)
    (g : (constantIntegerSheaf (J := J)) ⟶ I.cocomplex.X n) :
    (((mappedExtZeroCocomplexXIsoRestrictedHomX (J := J) F I (n + 1)).hom ≫
        ((CochainComplex.HomComplex
            ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
              (constantIntegerSheaf (J := J)))
            I.cochainComplex).restrictionXIso ComplexShape.embeddingUpNat rfl).hom)
        (Abelian.Ext.mk₀ (g ≫ I.cocomplex.d n (n + 1)))) =
      CochainComplex.HomComplex.Cochain.fromSingleMk
        ((g ≫ I.cocomplex.d n (n + 1)) ≫
          (I.cochainComplexXIso ((n + 1 : ℕ) : ℤ) (n + 1) rfl).inv)
        (by simp) := by
  -- Reuse the degreewise `Ext^0 = Hom` normal form at the successor term.
  simpa using
    mappedExtZeroComponentToFullHomApplyMk₀ (J := J) F I (n + 1)
      (g ≫ I.cocomplex.d n (n + 1))

omit [HasGlobalSectionsFunctor J AddCommGrpCat.{u}] in
/-- Helper for 21.2.0.6: after whiskering the desired differential square with the successor
`restrictionXIso`, the comparison can be checked on the generator `Ext.mk₀ g`. -/
private theorem mappedExtZeroComponentDCommApplyMk₀
    (F : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution F) (n : ℕ)
    (g : (constantIntegerSheaf (J := J)) ⟶ I.cocomplex.X n) :
    (((mappedExtZeroCocomplexXIsoRestrictedHomX (J := J) F I n).hom ≫
        ((CochainComplex.HomComplex
            ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
              (constantIntegerSheaf (J := J)))
            I.cochainComplex).restriction ComplexShape.embeddingUpNat).d n (n + 1) ≫
        ((CochainComplex.HomComplex
            ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
              (constantIntegerSheaf (J := J)))
            I.cochainComplex).restrictionXIso ComplexShape.embeddingUpNat rfl).hom)
        (Abelian.Ext.mk₀ g)) =
      (((((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex).d n (n + 1) ≫
          (mappedExtZeroCocomplexXIsoRestrictedHomX (J := J) F I (n + 1)).hom ≫
          ((CochainComplex.HomComplex
              ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
                (constantIntegerSheaf (J := J)))
              I.cochainComplex).restrictionXIso ComplexShape.embeddingUpNat rfl).hom)
        (Abelian.Ext.mk₀ g)) := by
  let K :=
    CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
        (constantIntegerSheaf (J := J)))
      I.cochainComplex
  -- Expand the restricted differential once so both sides live in the same full Hom complex.
  rw [HomologicalComplex.restriction_d_eq
    (K := K) (e := ComplexShape.embeddingUpNat) (i' := (n : ℤ))
    (j' := ((n + 1 : ℕ) : ℤ)) rfl rfl]
  simp
  -- The left side is now the full Hom differential of the transported generator.
  trans CochainComplex.HomComplex.Cochain.fromSingleMk
      (((g ≫ (I.cochainComplexXIso (n : ℤ) n rfl).inv) ≫
          I.cochainComplex.d (n : ℤ) ((n + 1 : ℕ) : ℤ)))
      (by simp)
  · simpa [K] using mappedExtZeroFullHomDApplyMk₀ (J := J) F I n g
  trans CochainComplex.HomComplex.Cochain.fromSingleMk
      ((g ≫ I.cocomplex.d n (n + 1)) ≫
        (I.cochainComplexXIso ((n + 1 : ℕ) : ℤ) (n + 1) rfl).inv)
      (by simp)
  · rw [I.cochainComplex_d (n : ℤ) ((n + 1 : ℕ) : ℤ) n (n + 1) rfl rfl]
    simp [Category.assoc]
  change
    CochainComplex.HomComplex.Cochain.fromSingleMk
        ((g ≫ I.cocomplex.d n (n + 1)) ≫
          (I.cochainComplexXIso ((n + 1 : ℕ) : ℤ) (n + 1) rfl).inv)
        (show (0 : ℤ) + ((n + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) by simp) =
      (((((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).d n (n + 1)) ≫
      (mappedExtZeroCocomplexXIsoRestrictedHomX (J := J) F I (n + 1)).hom ≫
      (K.restrictionXIso ComplexShape.embeddingUpNat rfl).hom)
    (Abelian.Ext.mk₀ g))
  rw [mappedExtZeroCocomplexDApplyMk₀ (J := J) F I n g]
  -- The successor term is already the standard generator under the degreewise comparison.
  simpa [K, Category.assoc] using
    (mappedExtZeroComponentToFullHomApplyMk₀ (J := J) F I (n + 1)
      (g ≫ I.cocomplex.d n (n + 1))).symm

omit [HasGlobalSectionsFunctor J AddCommGrpCat.{u}] in
/-- Helper for 21.2.0.6: the degreewise `Ext^0 = Hom` comparison intertwines the successor
differential of the mapped Ext cocomplex with the successor differential of the restricted Hom
complex. -/
private theorem mappedExtZeroCocomplexComponentDComm
    (F : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution F) (n : ℕ) :
    (mappedExtZeroCocomplexXIsoRestrictedHomX (J := J) F I n).hom ≫
        ((CochainComplex.HomComplex
            ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
              (constantIntegerSheaf (J := J)))
            I.cochainComplex).restriction ComplexShape.embeddingUpNat).d n (n + 1) =
      (((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex).d n (n + 1) ≫
        (mappedExtZeroCocomplexXIsoRestrictedHomX (J := J) F I (n + 1)).hom := by
  -- Route correction: isolate the generator computation behind
  -- `mappedExtZeroComponentDCommApplyMk₀`, then cancel the final restriction isomorphism.
  let K :=
    CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
        (constantIntegerSheaf (J := J)))
      I.cochainComplex
  apply (cancel_mono (K.restrictionXIso ComplexShape.embeddingUpNat rfl).hom).1
  ext e
  obtain ⟨g, hg⟩ := Abelian.Ext.homEquiv₀.symm.surjective e
  have hg' : Abelian.Ext.mk₀ g = e := by
    simpa [Abelian.Ext.homEquiv₀_symm_apply] using hg
  rw [← hg']
  simpa [K] using mappedExtZeroComponentDCommApplyMk₀ (J := J) F I n g

/-- Helper for 21.2.0.6: for a chosen injective resolution, the mapped degree-zero Ext cocomplex
is the restriction of the usual Hom complex from the degree-zero single complex on the constant
integer sheaf. -/
private noncomputable def mappedExtZeroCocomplexIsoRestrictedHomComplex
    (F : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution F) :
    (((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex) ≅
      (CochainComplex.HomComplex
          ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
            (constantIntegerSheaf (J := J)))
          I.cochainComplex).restriction ComplexShape.embeddingUpNat := by
  -- First upgrade the degreewise `Ext^0 = Hom` identification to a cochain complex isomorphism.
  refine HomologicalComplex.Hom.isoOfComponents
    (mappedExtZeroCocomplexXIsoRestrictedHomX (J := J) F I) ?_
  intro i j hij
  obtain rfl : j = i + 1 := (ComplexShape.up ℕ).next_eq hij rfl
  -- The componentwise differential square was isolated above.
  exact mappedExtZeroCocomplexComponentDComm (J := J) F I i

/-- Helper for 21.2.0.6: for a chosen injective resolution, the homology of the mapped
degree-zero Ext cocomplex identifies with the homology of the restricted Hom complex. -/
private noncomputable def mappedExtZeroHomologyAddEquivRestrictedHom
    (F : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution F) (i : ℕ) :
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) i).obj
      ((((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex))) ≃+
      ((CochainComplex.HomComplex
          ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
            (constantIntegerSheaf (J := J)))
          I.cochainComplex).restriction ComplexShape.embeddingUpNat).homology i :=
  -- Transport homology across the cochain-level comparison established just above.
  (HomologicalComplex.homologyMapIso
    (mappedExtZeroCocomplexIsoRestrictedHomComplex (J := J) F I) i).addCommGroupIsoToAddEquiv

/-- Helper for 21.2.0.6: in positive degrees, restricting the full Hom complex along
`embeddingUpNat` does not change homology. -/
private noncomputable def restrictedHomComplexHomologyIsoNatSucc
    (F : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution F) (n : ℕ) :
    ((CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
          (constantIntegerSheaf (J := J)))
        I.cochainComplex).restriction ComplexShape.embeddingUpNat).homology (n + 1) ≅
      (CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
          (constantIntegerSheaf (J := J)))
        I.cochainComplex).homology (((n + 1 : ℕ) : ℤ)) := by
  let K :=
    CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
        (constantIntegerSheaf (J := J)))
      I.cochainComplex
  -- In successor degree, both neighboring degrees lie in the image of `embeddingUpNat`, so the
  -- standard restriction/homology comparison applies directly.
  simpa [K] using
    (HomologicalComplex.restrictionHomologyIso
      K ComplexShape.embeddingUpNat n (n + 1) (n + 2)
      (by simp) (by simp)
      (by simp : ComplexShape.embeddingUpNat.f n = (n : ℤ))
      (by simp : ComplexShape.embeddingUpNat.f (n + 1) = ((n + 1 : ℕ) : ℤ))
      (by norm_num : ComplexShape.embeddingUpNat.f (n + 2) = ((n + 2 : ℕ) : ℤ))
      (by simp)
      (by
        calc
          (ComplexShape.up ℤ).next (((n + 1 : ℕ) : ℤ)) = (((n + 1 : ℕ) : ℤ) + 1) := by
            exact (by simpa using (CochainComplex.next ℤ (((n + 1 : ℕ) : ℤ))))
          _ = ((n + 2 : ℕ) : ℤ) := by omega))

omit [HasGlobalSectionsFunctor J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] in
/-- Helper for 21.2.0.6: the degree `-1` term of the full Hom complex vanishes because the
injective-resolution cochain complex is zero in negative degrees. -/
private theorem fullHomComplexNegOneIsZero
    (F : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution F) :
    IsZero
      ((CochainComplex.HomComplex
          ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
            (constantIntegerSheaf (J := J)))
          I.cochainComplex).X (-1)) := by
  let K :=
    CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
        (constantIntegerSheaf (J := J)))
      I.cochainComplex
  let e :
      K.X (-1) ≃+ ((constantIntegerSheaf (J := J)) ⟶ I.cochainComplex.X (-1)) :=
    CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (K := I.cochainComplex)
      (X := (constantIntegerSheaf (J := J)))
      (p := 0) (q := (-1 : ℤ)) (n := (-1 : ℤ))
      (by simp)
  let hneg : IsZero (I.cochainComplex.X (-1)) :=
    CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 (-1) (by omega)
  have hsubHom : Subsingleton ((constantIntegerSheaf (J := J)) ⟶ I.cochainComplex.X (-1)) := by
    refine ⟨fun f g ↦ ?_⟩
    exact hneg.eq_of_tgt f g
  have hsub : Subsingleton (K.X (-1)) := by
    refine ⟨fun x y ↦ e.injective ?_⟩
    exact Subsingleton.elim _ _
  -- A subsingleton abelian-group object is zero.
  letI : Subsingleton (K.X (-1)) := hsub
  exact AddCommGrpCat.isZero_of_subsingleton (K.X (-1))

/-- Helper for 21.2.0.6: after identifying both degree-`0` cycle objects with kernels of the
same outgoing differential, restriction does not change degree-`0` cycles. -/
private noncomputable def restrictedHomComplexCyclesIsoNatZero
    (F : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution F) :
    ((CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
          (constantIntegerSheaf (J := J)))
        I.cochainComplex).restriction ComplexShape.embeddingUpNat).cycles 0 ≅
      (CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
          (constantIntegerSheaf (J := J)))
        I.cochainComplex).cycles (0 : ℤ) := by
  let K :=
    CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
        (constantIntegerSheaf (J := J)))
      I.cochainComplex
  let Kr := K.restriction ComplexShape.embeddingUpNat
  let Sr : ShortComplex AddCommGrpCat.{u} := Kr.sc' 0 0 1
  let Sf : ShortComplex AddCommGrpCat.{u} := K.sc' (-1) 0 1
  let e0 : Kr.X 0 ≅ K.X (0 : ℤ) :=
    K.restrictionXIso ComplexShape.embeddingUpNat rfl
  let e1 : Kr.X 1 ≅ K.X (1 : ℤ) :=
    K.restrictionXIso ComplexShape.embeddingUpNat rfl
  have hprevKr : (ComplexShape.up ℕ).prev 0 = 0 := by
    simp
  have hnextKr : (ComplexShape.up ℕ).next 0 = 1 := by
    simpa using (CochainComplex.next ℕ 0)
  have hprevK : (ComplexShape.up ℤ).prev (0 : ℤ) = (-1 : ℤ) := by
    simpa using (CochainComplex.prev ℤ (0 : ℤ))
  have hnextK : (ComplexShape.up ℤ).next (0 : ℤ) = (1 : ℤ) := by
    simpa using (CochainComplex.next ℤ (0 : ℤ))
  have hd :
      Kr.d 0 1 ≫ e1.hom = e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) := by
    -- Expand the restricted differential once so both cycle objects become kernels of the same
    -- outgoing differential.
    rw [HomologicalComplex.restriction_d_eq
      (K := K) (e := ComplexShape.embeddingUpNat) (i' := (0 : ℤ)) (j' := (1 : ℤ)) rfl rfl]
    calc
      ((e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) ≫ e1.inv) ≫ e1.hom) =
          e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) ≫ (e1.inv ≫ e1.hom) := by
            simp [Category.assoc]
      _ = e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) := by
            simp
  -- Compare both degree-`0` cycle objects through the common kernel description.
  exact
    (Kr.cyclesIsoSc' 0 0 1 hprevKr hnextKr) ≪≫
      Sr.cyclesIsoKernel ≪≫
      kernel.mapIso (Kr.d 0 1) (K.d (0 : ℤ) (1 : ℤ)) e0 e1 hd ≪≫
      Sf.cyclesIsoKernel.symm ≪≫
      (K.cyclesIsoSc' (-1) 0 1 hprevK hnextK).symm

/-- Helper for 21.2.0.6: in degree `0`, the restricted Hom complex and the full `ℤ`-indexed Hom
complex have the same homology. -/
private noncomputable def restrictedHomComplexHomologyIsoNatZero
    (F : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution F) :
    ((CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
          (constantIntegerSheaf (J := J)))
        I.cochainComplex).restriction ComplexShape.embeddingUpNat).homology 0 ≅
      (CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
          (constantIntegerSheaf (J := J)))
        I.cochainComplex).homology (0 : ℤ) := by
  let K :=
    CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
        (constantIntegerSheaf (J := J)))
      I.cochainComplex
  let Kr := K.restriction ComplexShape.embeddingUpNat
  let hCycles := restrictedHomComplexCyclesIsoNatZero (J := J) F I
  let eπr : Kr.homology 0 ≅ Kr.cycles 0 := (CochainComplex.isoHomologyπ₀ Kr).symm
  have hzeroPrev : K.d (-1) 0 = 0 := by
    -- The full predecessor differential vanishes because the degree `-1` term is zero.
    exact (fullHomComplexNegOneIsZero (J := J) F I).eq_of_src _ _
  let eπf : K.cycles (0 : ℤ) ≅ K.homology (0 : ℤ) :=
    K.isoHomologyπ (-1) 0 (by simp) hzeroPrev
  -- Move to cycles on both sides, compare cycles, then descend back to homology.
  exact eπr ≪≫ hCycles ≪≫ eπf

/-- Helper for 21.2.0.6: for a chosen injective resolution, the homology of the mapped
degree-zero Ext cocomplex identifies with the higher Ext group from the constant integer sheaf. -/
private noncomputable def homologyMappedExtZeroConstantSheafAddEquivExt
    (F : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution F) (i : ℕ) :
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) i).obj
      ((((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex))) ≃+
      Abelian.Ext (constantIntegerSheaf (J := J)) F i := by
  -- Route correction: once the mapped `Ext^0` cocomplex is compared with the restricted Hom
  -- complex, the remaining step is exactly the canonical `InjectiveResolution.extAddEquiv...`
  -- computation on the full Hom complex.
  cases i with
  | zero =>
      -- In degree `0`, insert the special restriction/full-Hom comparison before applying the
      -- standard Ext computation on the chosen injective resolution.
      exact
        (mappedExtZeroHomologyAddEquivRestrictedHom (J := J) F I 0).trans <|
          (restrictedHomComplexHomologyIsoNatZero (J := J) F I).addCommGroupIsoToAddEquiv.trans <|
            (I.extAddEquivCohomologyClass.trans
              (CochainComplex.HomComplex.homologyAddEquiv
                ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
                  (constantIntegerSheaf (J := J)))
                I.cochainComplex 0).symm).symm
  | succ n =>
      -- In successor degree, the ordinary restriction/homology comparison is enough.
      exact
        (mappedExtZeroHomologyAddEquivRestrictedHom (J := J) F I (n + 1)).trans <|
          (restrictedHomComplexHomologyIsoNatSucc (J := J) F I n).addCommGroupIsoToAddEquiv.trans <|
            (I.extAddEquivCohomologyClass.trans
              (CochainComplex.HomComplex.homologyAddEquiv
                ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj
                  (constantIntegerSheaf (J := J)))
                I.cochainComplex (n + 1)).symm).symm

omit [HasGlobalSectionsFunctor J AddCommGrpCat.{u}] in
/-- Helper for 21.2.0.6: the homology of the mapped `Ext^0(constantIntegerSheaf,-)` cocomplex on
the chosen injective resolution computes `Sheaf.cohomologyFunctor J i`. -/
private theorem homologyMappedExtZeroConstantSheaf_isomorphic_cohomologyFunctorObj
    (I : InjectiveResolution F) (i : ℕ) :
    IsIsomorphic
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) i).obj
        ((((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)))
      ((Sheaf.cohomologyFunctor J i).obj F) := by
  -- Convert the fixed-resolution Ext computation into the sheaf-cohomology owner by the
  -- definitional description of `Sheaf.cohomologyFunctor`.
  let eExt :
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) i).obj
        ((((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex))) ≅
        ((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) i).obj F) :=
    (homologyMappedExtZeroConstantSheafAddEquivExt (J := J) F I i).toAddCommGrpIso
  refine ⟨eExt ≪≫ ?_⟩
  exact eqToIso (by rw [cohomologyFunctor_eq_extFunctorObj_constantIntegerSheaf (J := J) i])

/-- 21.2.0.6, companion form on `Sheaf.cohomologyFunctor`: the source-facing comparison above
may be used propositionally via `IsIsomorphic`. Since `Sheaf.cohomologyFunctor J i` is the
Ext-owner from `SheafCohomology.Basic`, this remains theorem-valued and factors through the direct
underived comparison `Γ ≅ Ext^0(constantIntegerSheaf,-)` on the chosen injective resolution. -/
@[stacks 071H]
theorem cohomologyFunctor_obj_isomorphic_to_homology_globalSections_of_injectiveResolution
    (I : InjectiveResolution F) (i : ℕ) :
    IsIsomorphic ((Sheaf.cohomologyFunctor J i).obj F)
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) i).obj
        (((Γ J AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex)) :=
  by
    let eΓExtComplex :
        (((Γ J AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) ≅
          ((((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj I.cocomplex)) :=
      (NatIso.mapHomologicalComplex
        (globalSectionsIsoExtZeroConstantSheaf (J := J))
        (ComplexShape.up ℕ)).app I.cocomplex
    let eΓExtHomology :
        ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) i).obj
            (((Γ J AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
              I.cocomplex)) ≅
          ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) i).obj
            ((((Abelian.extFunctorObj (constantIntegerSheaf (J := J)) 0).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj I.cocomplex))) :=
      HomologicalComplex.homologyMapIso eΓExtComplex i
    rcases homologyMappedExtZeroConstantSheaf_isomorphic_cohomologyFunctorObj
      (J := J) (F := F) I i with ⟨eExtCoh⟩
    -- Compare the global-sections complex with the mapped `Ext^0` complex termwise, then use
    -- the fixed-resolution computation of sheaf cohomology by the mapped `Ext^0` cocomplex.
    exact ⟨eExtCoh.symm ≪≫ eΓExtHomology.symm⟩

/-- 21.2.0.6: `H^i(C, F)` is isomorphic to the homology of the global-sections complex of a
chosen injective resolution. -/
@[stacks 071H]
theorem globalCohomology_isomorphic_to_homology_globalSections_of_injectiveResolution
    (I : InjectiveResolution F) (i : ℕ) :
    IsIsomorphic (AddCommGrpCat.of (F.H i))
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) i).obj
        (((Γ J AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex)) :=
  by
    simpa using
      cohomologyFunctor_obj_isomorphic_to_homology_globalSections_of_injectiveResolution
        J I i

end

end
end Sheaf
end CategoryTheory
