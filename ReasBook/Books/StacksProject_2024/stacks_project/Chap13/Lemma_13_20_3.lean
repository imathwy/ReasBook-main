import Mathlib
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
import StacksProject_2024.Chap12.Definition_12_12_1
import StacksProject_2024.Chap13.Definition_13_8_1
import StacksProject_2024.Chap13.Definition_13_3_6
import StacksProject_2024.Chap13.Lemma_13_10_6
import StacksProject_2024.Chap13.Lemma_13_12_1
import StacksProject_2024.Chap13.Lemma_13_4_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Localization
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]

/-
Domain-style sampling for Lemma 13.20.3:
- primary domain: exact functors between bounded-below derived categories and the induced
  `δ`-functors on bounded-below complexes and on degree-zero objects;
- sampled owner declarations:
  `boundedBelowComplexToDerivedBelowDeltaFunctor`,
  `single0ToDplusDeltaFunctor`,
  `DeltaFunctor.postcomposeExactFunctor`,
  `Functor.totalRightDerived`,
  `mapBoundedBelowHomotopyToDerivedBelow_isLocalization`,
  `Functor.CommShift ℤ`,
  `Functor.IsTriangulated`;
- best owner abstraction: the public source-facing owners are the induced `DeltaFunctor`s attached
  to an exact functor `RF : D⁺(𝒜) ⥤ D⁺(ℬ)`, built by postcomposing the canonical bounded-below
  complex and degree-zero `δ`-functors; the canonical bounded-below right derived functor is only
  a specialization of this exact-functor owner;
- primitive data: the bounded-below complex owner
  `boundedBelowComplexToDerivedBelowDeltaFunctor`, the degree-zero owner
  `single0ToDplusDeltaFunctor`, and an exact functor `RF : D⁺(𝒜) ⥤ D⁺(ℬ)`;
- derived API: the induced `DeltaFunctor` structures on bounded-below complexes and on degree-zero
  objects, together with the later specialization to `Functor.totalRightDerived`.

Source/core/bridge triage:
- `source-facing`: the induced `δ`-functors of Lemma 13.20.3 for an exact
  `RF : D⁺(𝒜) ⥤ D⁺(ℬ)`;
- `core/canonical`: `boundedBelowComplexToDerivedBelowDeltaFunctor`,
  `single0ToDplusDeltaFunctor`, `DeltaFunctor.postcomposeExactFunctor`,
  `Functor.CommShift ℤ`, and `Functor.IsTriangulated`;
- `bridge/view`: the specialization from the generic exact-functor owners to
  `Functor.totalRightDerived`.
-/

/-- Helper for Lemma 13.20.3: the quotient bridge `Comp^+(\mathcal A) ⥤ K^+(\mathcal A)`. -/
private abbrev Qhplus : Comp⁺(𝒜) ⥤ K⁺(𝒜) :=
  HomotopyCategory.Plus.quotient 𝒜

/-- Helper for Lemma 13.20.3: the inclusion `Comp^+(\mathcal A) ⥤ Comp(\mathcal A)`. -/
private abbrev compPlusι : Comp⁺(𝒜) ⥤ Comp(𝒜) :=
  CochainComplex.Plus.ι 𝒜

/-- Helper for Lemma 13.20.3: the inclusion `D^+(\mathcal A) ⥤ D(\mathcal A)`. -/
private abbrev plusιA : D⁺(𝒜) ⥤ D(𝒜) :=
  ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))

/-- Helper for Lemma 13.20.3: the degree-zero homotopy object is bounded below. -/
private theorem single0_obj_mem_bounded_below (A : 𝒜) :
    HomotopyCategory.plus 𝒜 ((HomotopyCategory.singleFunctor 𝒜 0).obj A) := by
  simpa using
    (show CochainComplex.plus 𝒜 ((CochainComplex.singleFunctor 𝒜 0).obj A) from
      ⟨0, inferInstance⟩)

/-- Helper for Lemma 13.20.3: the degree-zero embedding `\mathcal A ⥤ K^+(\mathcal A)`. -/
private abbrev single0Plus : 𝒜 ⥤ K⁺(𝒜) :=
  ObjectProperty.lift
    (HomotopyCategory.plus 𝒜)
    (HomotopyCategory.singleFunctor 𝒜 0)
    single0_obj_mem_bounded_below

/-- Helper for Lemma 13.20.3: the unbounded derived-category functor induced by an additive
functor. -/
private abbrev mapHomotopyCategoryToDerived (F : 𝒜 ⥤ ℬ) [F.Additive] :
    HomotopyCategory 𝒜 (up ℤ) ⥤ DerivedCategory ℬ :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- Helper for Lemma 13.20.3: bounded-below objects of `K(\mathcal B)` map to bounded-below
objects of `D(\mathcal B)` under the quotient. -/
private theorem qh_obj_mem_t_plus
    (X : K⁺(ℬ)) :
    (t.plus : ObjectProperty (D(ℬ)))
      (DerivedCategory.Qh.obj X.obj) := by
  let K : CochainComplex ℬ ℤ := X.obj.as
  have hK : CochainComplex.plus ℬ K := by
    simpa [K, HomotopyCategory.plus] using X.property
  rcases hK with ⟨n, hn⟩
  let _ : K.IsStrictlyGE n := by simpa [K] using hn
  let _ : K.IsGE n := inferInstance
  let e : DerivedCategory.Qh.obj X.obj ≅ DerivedCategory.Q.obj K := by
    simpa [K, HomotopyCategory.quotient_obj_as] using
      (DerivedCategory.quotientCompQhIso ℬ).app K
  have hQ : (t.plus : ObjectProperty (D(ℬ))) (DerivedCategory.Q.obj K) := by
    refine ⟨n, ?_⟩
    change (DerivedCategory.Q.obj K).IsGE n
    exact (DerivedCategory.isGE_Q_obj_iff K n).2 inferInstance
  exact (t.plus : ObjectProperty (D(ℬ))).prop_of_iso e.symm hQ

/-- Helper for Lemma 13.20.3: the canonical functor `K^+(\mathcal A) ⟶ D^+(\mathcal A)`. -/
private abbrev mapBoundedBelowHomotopyToDerivedBelow :
    K⁺(𝒜) ⥤ D⁺(𝒜) :=
  (t.plus : ObjectProperty (D(𝒜))).lift
    ((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh)
    qh_obj_mem_t_plus

/-- Helper for Lemma 13.20.3: the canonical functor `K^+(\mathcal A) ⟶ D^+(\mathcal A)`. -/
private abbrev Qplus : K⁺(𝒜) ⥤ D⁺(𝒜) :=
  mapBoundedBelowHomotopyToDerivedBelow

/-- Helper for Lemma 13.20.3: the bounded-below homotopy-to-derived functor induced by an
additive functor. -/
private abbrev mapBoundedBelowHomotopyCategoryToDerivedBelow
    (F : 𝒜 ⥤ ℬ) [F.Additive] :
    K⁺(𝒜) ⥤ D⁺(ℬ) :=
  mapBoundedBelowHomotopyCategory F ⋙ mapBoundedBelowHomotopyToDerivedBelow

/-- Helper for Lemma 13.20.3: bounded-below objects of `K(\mathcal B)` map to bounded-below
objects of `D(\mathcal B)` under the quotient. -/
private theorem qh_obj_mem_t_plus_fullsubcat
    (X : (HomotopyCategory.plus ℬ).FullSubcategory) :
    (t.plus : ObjectProperty (D(ℬ)))
      (((ObjectProperty.ι (HomotopyCategory.plus ℬ)) ⋙ DerivedCategory.Qh).obj X) := by
  simpa using qh_obj_mem_t_plus (ℬ := ℬ) X

/-- Helper for Lemma 13.20.3: the canonical bounded-below comparison with the ambient functor
`K^+(\mathcal A) ⟶ D(\mathcal B)`. -/
private noncomputable def mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso
    (F : 𝒜 ⥤ ℬ) [F.Additive] :
    mapBoundedBelowHomotopyCategoryToDerivedBelow F ⋙
      ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ))) ≅
    ObjectProperty.ι (HomotopyCategory.plus 𝒜) ⋙ mapHomotopyCategoryToDerived (𝒜 := 𝒜) F :=
  (Functor.associator
      (mapBoundedBelowHomotopyCategory F)
      mapBoundedBelowHomotopyToDerivedBelow
      (ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ))))).symm ≪≫
    Functor.isoWhiskerLeft
      (mapBoundedBelowHomotopyCategory F)
      (ObjectProperty.liftCompιIso
        (t.plus : ObjectProperty (D(ℬ)))
        (ObjectProperty.ι (HomotopyCategory.plus ℬ) ⋙ DerivedCategory.Qh)
        (qh_obj_mem_t_plus_fullsubcat (ℬ := ℬ))) ≪≫
    Functor.associator
      (mapBoundedBelowHomotopyCategory F)
      (ObjectProperty.ι (HomotopyCategory.plus ℬ))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerRight
      ((HomotopyCategory.plus ℬ).liftCompιIso
        ((HomotopyCategory.plus 𝒜).ι ⋙ F.mapHomotopyCategory (up ℤ))
        (mapHomotopyCategory_obj_mem_boundedBelow F))
      DerivedCategory.Qh

/-- Helper for Lemma 13.20.3: the degree-zero bounded-below embedding followed by the inclusion
into the ambient homotopy category identifies with the usual degree-zero homotopy embedding. -/
private noncomputable def single0PlusCompιIso :
    single0Plus ⋙ ObjectProperty.ι (HomotopyCategory.plus 𝒜) ≅
      HomotopyCategory.singleFunctor 𝒜 0 :=
  (HomotopyCategory.plus 𝒜).liftCompιIso
    (HomotopyCategory.singleFunctor 𝒜 0)
    single0_obj_mem_bounded_below

/-- Helper for Lemma 13.20.3: the canonical bounded-below degree-zero embedding
`\mathcal A ⥤ D^+(\mathcal A)`. -/
private abbrev single0ToDplus : 𝒜 ⥤ D⁺(𝒜) :=
  single0Plus ⋙ mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)

/-- Helper for Lemma 13.20.3: sending `A[0]` through the bounded-below homotopy-to-derived
functor agrees with the usual single-object embedding in the derived category. -/
private noncomputable def single0PlusToSingleFunctorIso (F : 𝒜 ⥤ ℬ) [F.Additive] :
    single0Plus ⋙ mapBoundedBelowHomotopyCategoryToDerivedBelow F ⋙
      ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ))) ≅
    F ⋙ DerivedCategory.singleFunctor ℬ 0 :=
  Functor.isoWhiskerLeft single0Plus
      (mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso (𝒜 := 𝒜) F) ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (single0PlusCompιIso (𝒜 := 𝒜))
        (mapHomotopyCategoryToDerived (𝒜 := 𝒜) F) ≪≫
        Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerRight
            (HomotopyCategory.singleFunctorPostcompQuotientIso 𝒜 0)
            (F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh) ≪≫
          Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft
              (CochainComplex.singleFunctor 𝒜 0)
              (Functor.isoWhiskerRight
                (Functor.mapHomotopyCategoryFactors F (up ℤ))
                DerivedCategory.Qh) ≪≫
            (Functor.associator _ _ _).symm ≪≫
              Functor.isoWhiskerLeft
                (CochainComplex.singleFunctor 𝒜 0 ⋙
                  F.mapHomologicalComplex (up ℤ))
                (DerivedCategory.quotientCompQhIso ℬ) ≪≫
              Functor.associator _ _ _ ≪≫
                Functor.isoWhiskerRight
                  (HomologicalComplex.singleMapHomologicalComplex
                    F (ComplexShape.up ℤ) 0)
                  DerivedCategory.Q ≪≫
                Functor.associator _ _ _ ≪≫
                  Functor.isoWhiskerLeft F
                    (DerivedCategory.singleFunctorIsoCompQ ℬ 0).symm

local instance : Limits.PreservesFiniteLimits (CochainComplex.Plus.ι 𝒜) := by
  refine ⟨?_⟩
  intro J _ _
  let _ : CreatesLimitsOfShape J (CochainComplex.Plus.ι 𝒜) := by infer_instance
  infer_instance

local instance : Limits.PreservesFiniteColimits (CochainComplex.Plus.ι 𝒜) := by
  refine ⟨?_⟩
  intro J _ _
  let _ : CreatesColimitsOfShape J (CochainComplex.Plus.ι 𝒜) := by infer_instance
  infer_instance

/-- Helper for Lemma 13.20.3: the bounded-below complex-to-derived functor agrees with the
ambient complex-to-derived functor after forgetting bounded-below structure. -/
private theorem qhplus_comp_homotopy_inclusion_eq :
    ((Qhplus (𝒜 := 𝒜)) ⋙ ObjectProperty.ι (HomotopyCategory.plus 𝒜) : Comp⁺(𝒜) ⥤ K(𝒜)) =
      ((compPlusι (𝒜 := 𝒜)) ⋙
        (show Comp(𝒜) ⥤ K(𝒜) from HomotopyCategory.quotient 𝒜 (up ℤ))) := by
  rfl

/-- Helper for Lemma 13.20.3: the bounded-below complex-to-derived functor agrees with the
ambient complex-to-derived functor after forgetting bounded-below structure. -/
private noncomputable def boundedBelowComplexToDerivedBelowCompιIso :
    ((Qhplus (𝒜 := 𝒜)) ⋙ (Qplus (𝒜 := 𝒜)) ⋙ (plusιA (𝒜 := 𝒜)) :
      Comp⁺(𝒜) ⥤ D(𝒜)) ≅
    ((compPlusι (𝒜 := 𝒜)) ⋙ (DerivedCategory.Q : Comp(𝒜) ⥤ D(𝒜))) :=
  Functor.associator (Qhplus (𝒜 := 𝒜)) (Qplus (𝒜 := 𝒜)) (plusιA (𝒜 := 𝒜)) ≪≫
    Functor.isoWhiskerLeft (Qhplus (𝒜 := 𝒜))
      (ObjectProperty.liftCompιIso
        (t.plus : ObjectProperty (D(𝒜)))
        ((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh)
        (qh_obj_mem_t_plus_fullsubcat (ℬ := 𝒜))) ≪≫
    Functor.associator
      (Qhplus (𝒜 := 𝒜))
      (ObjectProperty.ι (HomotopyCategory.plus 𝒜))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerRight
      (eqToIso (qhplus_comp_homotopy_inclusion_eq (𝒜 := 𝒜)))
      DerivedCategory.Qh ≪≫
    Functor.associator
      (compPlusι (𝒜 := 𝒜))
      (HomotopyCategory.quotient 𝒜 (up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft (compPlusι (𝒜 := 𝒜)) (DerivedCategory.quotientCompQhIso 𝒜)

/-- Helper for Lemma 13.20.3: the transported bounded-below triangle attached to a short exact
sequence of bounded-below complexes. -/
private noncomputable def boundedBelowComplexToDerivedBelowTriangle
    {S : ShortComplex (Comp⁺(𝒜))} (hS : S.ShortExact) :
    Triangle (D⁺(𝒜)) :=
  Triangle.mk
    ((Qhplus ⋙ Qplus).map S.f)
    ((Qhplus ⋙ Qplus).map S.g)
    (ObjectProperty.homMk
      ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
        (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
          (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
            (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj S.X₁)))

/-- Helper for Lemma 13.20.3: the transported bounded-below triangle is distinguished. -/
private theorem boundedBelowComplexToDerivedBelow_triangle_distinguished
    {S : ShortComplex (Comp⁺(𝒜))} (hS : S.ShortExact) :
    boundedBelowComplexToDerivedBelowTriangle (𝒜 := 𝒜) hS ∈ distTriang (D⁺(𝒜)) := by
  rw [← plusιA.map_distinguished_iff]
  change
    Triangle.mk
        (plusιA.map ((Qhplus ⋙ Qplus).map S.f))
        (plusιA.map ((Qhplus ⋙ Qplus).map S.g))
        (plusιA.map
            (ObjectProperty.homMk
              ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
                (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
                  (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁)⟦
                    (1 : ℤ)⟧') ≫
                    (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj S.X₁))) ≫
          (plusιA.commShiftIso (1 : ℤ)).hom.app ((Qhplus ⋙ Qplus).obj S.X₁)) ∈
      distTriang (D(𝒜))
  refine
    isomorphic_distinguished _
      ((cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).triangle_distinguished
        (hS.map_of_exact compPlusι))
      _ ?_
  refine Triangle.isoMk _ _
    ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).app S.X₁)
    ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).app S.X₂)
    ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).app S.X₃)
    ?_ ?_ ?_
  · simpa using (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.naturality S.f
  · simpa using (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.naturality S.g
  · have hshift :
        (shiftFunctor (D(𝒜)) (1 : ℤ)).map
            ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁) ≫
            (shiftFunctor (D(𝒜)) (1 : ℤ)).map
              ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₁) =
          𝟙
            (((cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).obj
              (compPlusι.obj S.X₁))⟦(1 : ℤ)⟧) := by
      simpa using
        congrArg
          (fun k ↦ (shiftFunctor (D(𝒜)) (1 : ℤ)).map k)
          ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv_hom_id_app S.X₁)
    have hthird :
        (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
            (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
              (shiftFunctor (D(𝒜)) (1 : ℤ)).map
                  ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁) ≫
                (Functor.commShiftIso plusιA (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj S.X₁) ≫
                  (Functor.commShiftIso plusιA (1 : ℤ)).hom.app ((Qhplus ⋙ Qplus).obj S.X₁) ≫
                    (shiftFunctor (D(𝒜)) (1 : ℤ)).map
                      ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₁) =
          (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
            (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) := by
      calc
        (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
            (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
              (shiftFunctor (D(𝒜)) (1 : ℤ)).map
                  ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁) ≫
                (Functor.commShiftIso plusιA (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj S.X₁) ≫
                  (Functor.commShiftIso plusιA (1 : ℤ)).hom.app ((Qhplus ⋙ Qplus).obj S.X₁) ≫
                    (shiftFunctor (D(𝒜)) (1 : ℤ)).map
                      ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₁)
            =
          (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
            (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
              (shiftFunctor (D(𝒜)) (1 : ℤ)).map
                  ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁) ≫
                (shiftFunctor (D(𝒜)) (1 : ℤ)).map
                  ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₁) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
                (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
                  (shiftFunctor (D(𝒜)) (1 : ℤ)).map
                    ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁) ≫
                      k ≫
                        (shiftFunctor (D(𝒜)) (1 : ℤ)).map
                          ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₁))
              ((Functor.commShiftIso plusιA (1 : ℤ)).inv_hom_id_app ((Qhplus ⋙ Qplus).obj S.X₁))
        _ =
          (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
            (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) := by
          have hcancel :
              (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
                  (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
                    (shiftFunctor (D(𝒜)) (1 : ℤ)).map
                      ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁) ≫
                      (shiftFunctor (D(𝒜)) (1 : ℤ)).map
                        ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₁) =
                (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
                  (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) := by
            have hcancel' :
                (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
                    (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
                      (shiftFunctor (D(𝒜)) (1 : ℤ)).map
                        ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁) ≫
                        (shiftFunctor (D(𝒜)) (1 : ℤ)).map
                          ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₁) =
                  (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
                    (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
                      𝟙
                        (((cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).obj
                          (compPlusι.obj S.X₁))⟦(1 : ℤ)⟧) := by
              have hcancel'' :
                  (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
                      (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
                        ((shiftFunctor (D(𝒜)) (1 : ℤ)).map
                          ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁) ≫
                            (shiftFunctor (D(𝒜)) (1 : ℤ)).map
                              ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₁)) =
                    (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
                      (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
                        𝟙
                          (((cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).obj
                            (compPlusι.obj S.X₁))⟦(1 : ℤ)⟧) := by
                exact congrArg
                  (fun k ↦ (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
                    (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
                      k)
                  hshift
              simpa [Category.assoc] using hcancel''
            simpa [Category.assoc] using hcancel'
          exact hcancel
    simpa [boundedBelowComplexToDerivedBelowTriangle, DeltaFunctor.triangle, Category.assoc] using
      hthird

/-- Helper for Lemma 13.20.3: the transported bounded-below connecting morphisms are natural in
morphisms of short exact sequences. -/
private theorem boundedBelowComplexToDerivedBelow_delta_naturality
    {S T : ShortComplex (Comp⁺(𝒜))} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) :
    CommSq
      ((Qhplus ⋙ Qplus).map φ.τ₃)
      (ObjectProperty.homMk
        ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
          (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
            (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj S.X₁)))
      (ObjectProperty.homMk
        ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app T.X₃ ≫
          (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hT.map_of_exact compPlusι) ≫
            (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁)))
      (((Qhplus ⋙ Qplus).map φ.τ₁)⟦(1 : ℤ)⟧') := by
  apply CommSq.mk
  apply plusιA.map_injective
  simp only [Functor.map_comp]
  -- Transport the connecting morphism along the comparison isomorphism and then
  -- use the compatibility of the commutative shift isomorphism with morphisms.
  have hδ :
      (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).map
          ((compPlusι.mapShortComplex).map φ).τ₃ ≫
            (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hT.map_of_exact compPlusι) =
        (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
          ((cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).map
            ((compPlusι.mapShortComplex).map φ).τ₁)⟦(1 : ℤ)⟧' := by
    simpa using
      ((cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ_naturality
        (hS.map_of_exact compPlusι) (hT.map_of_exact compPlusι)
        ((compPlusι.mapShortComplex).map φ)).w
  have hinv :
      ((cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).map
          ((compPlusι.mapShortComplex).map φ).τ₁)⟦(1 : ℤ)⟧' ≫
            (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦
              (1 : ℤ)⟧') =
        (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
          (plusιA.map ((Qhplus ⋙ Qplus).map φ.τ₁))⟦(1 : ℤ)⟧' := by
    simpa using
      congrArg
        (fun k ↦ (shiftFunctor (D(𝒜)) (1 : ℤ)).map k)
        ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.naturality φ.τ₁)
  have hcomp_raw :=
    congrArg
      (fun k ↦ k ≫
        (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hT.map_of_exact compPlusι) ≫
          (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
            (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁))
      ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.naturality φ.τ₃)
  have hdelta_raw :=
    congrArg
      (fun k ↦ (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
        k ≫
          (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
            (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁))
      hδ
  have hinv_raw :=
    congrArg
      (fun k ↦ (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
        (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
          k ≫
            (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁))
      hinv
  have hshift_join :
      (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
          (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
            (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
              (plusιA.map ((Qhplus ⋙ Qplus).map φ.τ₁))⟦(1 : ℤ)⟧' ≫
                (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁) =
      (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
        (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
          (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
            (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj S.X₁) ≫
              plusιA.map ((((Qhplus ⋙ Qplus).map φ.τ₁)⟦(1 : ℤ)⟧')) := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
          (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
            (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁)⟦
              (1 : ℤ)⟧') ≫
              k)
        (plusιA.commShiftIso_inv_naturality ((Qhplus ⋙ Qplus).map φ.τ₁) (1 : ℤ))
  have hcomp_join :
      ((Qhplus ⋙ Qplus ⋙ plusιA).map φ.τ₃) ≫
          (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app T.X₃ ≫
            (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hT.map_of_exact compPlusι) ≫
              (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦
                (1 : ℤ)⟧') ≫
                (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁) =
      (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
        (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).map
          ((compPlusι.mapShortComplex).map φ).τ₃ ≫
            (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hT.map_of_exact compPlusι) ≫
              (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦
                (1 : ℤ)⟧') ≫
                (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁) := by
    calc
      ((Qhplus ⋙ Qplus ⋙ plusιA).map φ.τ₃) ≫
          (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app T.X₃ ≫
            (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hT.map_of_exact compPlusι) ≫
              (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦
                (1 : ℤ)⟧') ≫
                (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁)
          =
        (((Qhplus ⋙ Qplus ⋙ plusιA).map φ.τ₃) ≫
            (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app T.X₃) ≫
          (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hT.map_of_exact compPlusι) ≫
            (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦
              (1 : ℤ)⟧') ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁) := by
        simp [Category.assoc]
      _ =
        ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
            (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).map
              ((compPlusι.mapShortComplex).map φ).τ₃) ≫
          (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hT.map_of_exact compPlusι) ≫
            (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦
              (1 : ℤ)⟧') ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁) := by
        exact hcomp_raw
      _ =
        (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
          (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).map
            ((compPlusι.mapShortComplex).map φ).τ₃ ≫
            (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hT.map_of_exact compPlusι) ≫
              (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦
                (1 : ℤ)⟧') ≫
                (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁) := by
        simp [Category.assoc]
  have hdelta_join :
      (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
          (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).map
            ((compPlusι.mapShortComplex).map φ).τ₃ ≫
            (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hT.map_of_exact compPlusι) ≫
              (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦
                (1 : ℤ)⟧') ≫
                (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁) =
      (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
        (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
          ((cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).map
            ((compPlusι.mapShortComplex).map φ).τ₁)⟦(1 : ℤ)⟧' ≫
            (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦
              (1 : ℤ)⟧') ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁) := by
    calc
      (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
          (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).map
            ((compPlusι.mapShortComplex).map φ).τ₃ ≫
            (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hT.map_of_exact compPlusι) ≫
              (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦
                (1 : ℤ)⟧') ≫
                (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁)
          =
        (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
          ((cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).map
            ((compPlusι.mapShortComplex).map φ).τ₃ ≫
              (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hT.map_of_exact compPlusι)) ≫
            (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦
              (1 : ℤ)⟧') ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁) := by
        simp [Category.assoc]
      _ =
        (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
          ((cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
              ((cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).map
                ((compPlusι.mapShortComplex).map φ).τ₁)⟦(1 : ℤ)⟧') ≫
            (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦
              (1 : ℤ)⟧') ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁) := by
        exact hdelta_raw
      _ =
        (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
          (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
            ((cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).map
              ((compPlusι.mapShortComplex).map φ).τ₁)⟦(1 : ℤ)⟧' ≫
              (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦
                (1 : ℤ)⟧') ≫
                (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁) := by
        simp [Category.assoc]
  have hinv_join :
      (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
          (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
            ((cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).map
              ((compPlusι.mapShortComplex).map φ).τ₁)⟦(1 : ℤ)⟧' ≫
              (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
                (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁) =
      (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
        (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
          (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
            (plusιA.map ((Qhplus ⋙ Qplus).map φ.τ₁))⟦(1 : ℤ)⟧' ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁) := by
    calc
      (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
          (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
            ((cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).map
              ((compPlusι.mapShortComplex).map φ).τ₁)⟦(1 : ℤ)⟧' ≫
              (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦
                (1 : ℤ)⟧') ≫
                (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁)
          =
        (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
          (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
            (((cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).map
              ((compPlusι.mapShortComplex).map φ).τ₁)⟦(1 : ℤ)⟧' ≫
                (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app T.X₁)⟦
                  (1 : ℤ)⟧')) ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁) := by
        simp [Category.assoc]
      _ =
        (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
          (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
            (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁)⟦
              (1 : ℤ)⟧' ≫
              (plusιA.map ((Qhplus ⋙ Qplus).map φ.τ₁))⟦(1 : ℤ)⟧') ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁) := by
        exact hinv_raw
      _ =
        (boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
          (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
            (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁)⟦
              (1 : ℤ)⟧') ≫
              (plusιA.map ((Qhplus ⋙ Qplus).map φ.τ₁))⟦(1 : ℤ)⟧' ≫
                (plusιA.commShiftIso (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj T.X₁) := by
        simp [Category.assoc]
  have htail : _ := hinv_join.trans hshift_join
  simpa [Category.assoc] using hcomp_join.trans (hdelta_join.trans htail)

/-- Lemma 13.20.3 (1), source-facing owner: the canonical functor
`Comp^+(\mathcal A) ⥤ D^+(\mathcal A)` carries the connecting morphisms coming from short exact
sequences of bounded-below complexes, making it into a `δ`-functor. -/
noncomputable def boundedBelowComplexToDerivedBelowDeltaFunctor :
    DeltaFunctor (Comp⁺(𝒜)) D⁺(𝒜) where
  toFunctor := Qhplus ⋙ Qplus
  additive := inferInstance
  δ := fun {S} hS ↦
    ObjectProperty.homMk
      ((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).hom.app S.X₃ ≫
        (cochainComplexToDerivedDeltaFunctor (𝒜 := 𝒜)).δ (hS.map_of_exact compPlusι) ≫
          (((boundedBelowComplexToDerivedBelowCompιIso (𝒜 := 𝒜)).inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
            ((Functor.commShiftIso plusιA (1 : ℤ)).inv.app ((Qhplus ⋙ Qplus).obj S.X₁)))
  map_distinguished := fun {S} hS ↦ by
    simpa [boundedBelowComplexToDerivedBelowTriangle, DeltaFunctor.triangle] using
      boundedBelowComplexToDerivedBelow_triangle_distinguished (𝒜 := 𝒜) hS
  δ_naturality := fun {S T} hS hT φ ↦ by
    simpa using boundedBelowComplexToDerivedBelow_delta_naturality (𝒜 := 𝒜) hS hT φ

/-- The underlying functor of `boundedBelowComplexToDerivedBelowDeltaFunctor` is the canonical
bounded-below localization functor `K^+(\mathcal A) ⥤ D^+(\mathcal A)`. -/
@[simp] theorem boundedBelowComplexToDerivedBelowDeltaFunctor_toFunctor :
    (boundedBelowComplexToDerivedBelowDeltaFunctor : DeltaFunctor (Comp⁺(𝒜)) D⁺(𝒜)).toFunctor =
      Qhplus ⋙ Qplus := by
  rfl

/-- Helper for Lemma 13.20.3: the canonical degree-zero embedding into `D^+(\mathcal A)`,
followed by the inclusion into `D(\mathcal A)`, agrees with the usual single-object embedding. -/
private noncomputable def single0ToDerivedIso :
    single0ToDplus ⋙ plusιA ≅ DerivedCategory.singleFunctor 𝒜 0 :=
  single0PlusToSingleFunctorIso (𝒜 := 𝒜) (ℬ := 𝒜) (F := 𝟭 𝒜) ≪≫ Functor.leftUnitor _

/-- Helper for Lemma 13.20.3: the transported degree-zero triangle attached to a short exact
sequence in `\mathcal A`. -/
private noncomputable def single0ToDplusTriangle {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    Triangle (D⁺(𝒜)) :=
  Triangle.mk
    (single0ToDplus.map S.f)
    (single0ToDplus.map S.g)
    (ObjectProperty.homMk
      (single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ ≫
        ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
          (plusιA.commShiftIso (1 : ℤ)).inv.app (single0ToDplus.obj S.X₁)))

/-- Helper for Lemma 13.20.3: the transported degree-zero triangle is distinguished. -/
private theorem single0ToDplus_triangle_distinguished {S : ShortComplex 𝒜}
    (hS : S.ShortExact) :
    single0ToDplusTriangle hS ∈ distTriang (D⁺(𝒜)) := by
  rw [← plusιA.map_distinguished_iff]
  change
    Triangle.mk
        (plusιA.map (single0ToDplus.map S.f))
        (plusιA.map (single0ToDplus.map S.g))
        (plusιA.map
            (ObjectProperty.homMk
              (single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ ≫
                ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
                  (plusιA.commShiftIso (1 : ℤ)).inv.app (single0ToDplus.obj S.X₁))) ≫
          (plusιA.commShiftIso (1 : ℤ)).hom.app (single0ToDplus.obj S.X₁)) ∈
      distTriang (D(𝒜))
  refine isomorphic_distinguished _ hS.singleTriangle_distinguished _ ?_
  refine Triangle.isoMk _ _
    (single0ToDerivedIso.app S.X₁)
    (single0ToDerivedIso.app S.X₂)
    (single0ToDerivedIso.app S.X₃)
    ?_ ?_ ?_
  · simpa using single0ToDerivedIso.hom.naturality S.f
  · simpa using single0ToDerivedIso.hom.naturality S.g
  · have hshift :
        (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
            (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁) =
          𝟙 (((DerivedCategory.singleFunctor 𝒜 0).obj S.X₁)⟦(1 : ℤ)⟧) := by
      simpa using
        congrArg
          (fun k ↦ (shiftFunctor (D(𝒜)) (1 : ℤ)).map k)
          (single0ToDerivedIso.inv_hom_id_app S.X₁)
    have hthird :
        single0ToDerivedIso.hom.app S.X₃ ≫
            hS.singleδ ≫
              (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
                (Functor.commShiftIso plusιA (1 : ℤ)).inv.app (single0ToDplus.obj S.X₁) ≫
                  (Functor.commShiftIso plusιA (1 : ℤ)).hom.app (single0ToDplus.obj S.X₁) ≫
                    (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁) =
          single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ := by
      calc
        single0ToDerivedIso.hom.app S.X₃ ≫
            hS.singleδ ≫
              (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
                (Functor.commShiftIso plusιA (1 : ℤ)).inv.app (single0ToDplus.obj S.X₁) ≫
                  (Functor.commShiftIso plusιA (1 : ℤ)).hom.app (single0ToDplus.obj S.X₁) ≫
                    (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁)
            =
          single0ToDerivedIso.hom.app S.X₃ ≫
            hS.singleδ ≫
              (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
                (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ single0ToDerivedIso.hom.app S.X₃ ≫
                hS.singleδ ≫
                  (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
                    k ≫
                      (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁))
              ((Functor.commShiftIso plusιA (1 : ℤ)).inv_hom_id_app (single0ToDplus.obj S.X₁))
        _ = single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ := by
          calc
            single0ToDerivedIso.hom.app S.X₃ ≫
                hS.singleδ ≫
                  (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
                    (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁)
                =
              single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ ≫
                𝟙 (((DerivedCategory.singleFunctor 𝒜 0).obj S.X₁)⟦(1 : ℤ)⟧) := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ ≫ k)
                  hshift
            _ = single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ := by
              simp
    simpa [single0ToDplusTriangle, ShortComplex.ShortExact.singleTriangle, Category.assoc] using
      hthird

/-- Helper for Lemma 13.20.3: the transported degree-zero connecting morphisms are natural. -/
private theorem single0ToDplus_delta_naturality {S T : ShortComplex 𝒜}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) :
    CommSq
      ((single0ToDplus (𝒜 := 𝒜)).map φ.τ₃)
      (ObjectProperty.homMk
        (single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ ≫
          ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
            (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus (𝒜 := 𝒜)).obj S.X₁)))
      (ObjectProperty.homMk
        (single0ToDerivedIso.hom.app T.X₃ ≫ hT.singleδ ≫
          ((single0ToDerivedIso.inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
            (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus (𝒜 := 𝒜)).obj T.X₁)))
      (((single0ToDplus (𝒜 := 𝒜)).map φ.τ₁)⟦(1 : ℤ)⟧') := by
  apply CommSq.mk
  apply plusιA.map_injective
  simp only [Functor.map_comp]
  -- Transport the degree-zero connecting morphism along the comparison isomorphism
  -- and then commute the final shifted map across the commutative shift isomorphism.
  have hsingleδ :
      (DerivedCategory.singleFunctor 𝒜 0).map φ.τ₃ ≫ hT.singleδ =
        hS.singleδ ≫ ((DerivedCategory.singleFunctor 𝒜 0).map φ.τ₁)⟦(1 : ℤ)⟧' := by
    simpa using
      (ShortComplex.ShortExact.singleTriangle.map (h₁ := hS) (h₂ := hT) φ).comm₃.symm
  have hinv :
      ((DerivedCategory.singleFunctor 𝒜 0).map φ.τ₁)⟦(1 : ℤ)⟧' ≫
          ((single0ToDerivedIso.inv.app T.X₁)⟦(1 : ℤ)⟧') =
        ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
          (plusιA.map ((single0ToDplus (𝒜 := 𝒜)).map φ.τ₁))⟦(1 : ℤ)⟧' := by
    simpa using
      congrArg
        (fun k ↦ (shiftFunctor (D(𝒜)) (1 : ℤ)).map k)
        (single0ToDerivedIso.inv.naturality φ.τ₁)
  have hcomp_raw :=
    congrArg
      (fun k ↦ k ≫ hT.singleδ ≫
        ((single0ToDerivedIso.inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
          (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus (𝒜 := 𝒜)).obj T.X₁))
      (single0ToDerivedIso.hom.naturality φ.τ₃)
  have hdelta_raw :=
    congrArg
      (fun k ↦ single0ToDerivedIso.hom.app S.X₃ ≫
        k ≫
          ((single0ToDerivedIso.inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
            (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus (𝒜 := 𝒜)).obj T.X₁))
      hsingleδ
  have hinv_raw :=
    congrArg
      (fun k ↦ single0ToDerivedIso.hom.app S.X₃ ≫
        hS.singleδ ≫
          k ≫
            (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus (𝒜 := 𝒜)).obj T.X₁))
      hinv
  have hcomp_join :
      ((single0ToDplus (𝒜 := 𝒜) ⋙ plusιA).map φ.τ₃) ≫ single0ToDerivedIso.hom.app T.X₃ ≫
          hT.singleδ ≫
            ((single0ToDerivedIso.inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus (𝒜 := 𝒜)).obj T.X₁) =
      single0ToDerivedIso.hom.app S.X₃ ≫
        (DerivedCategory.singleFunctor 𝒜 0).map φ.τ₃ ≫
          hT.singleδ ≫
            ((single0ToDerivedIso.inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus (𝒜 := 𝒜)).obj T.X₁) := by
    simpa [Category.assoc] using hcomp_raw
  have hdelta_join :
      single0ToDerivedIso.hom.app S.X₃ ≫
          (DerivedCategory.singleFunctor 𝒜 0).map φ.τ₃ ≫
            hT.singleδ ≫
              ((single0ToDerivedIso.inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
                (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus (𝒜 := 𝒜)).obj T.X₁) =
      single0ToDerivedIso.hom.app S.X₃ ≫
        hS.singleδ ≫
          ((DerivedCategory.singleFunctor 𝒜 0).map φ.τ₁)⟦(1 : ℤ)⟧' ≫
            ((single0ToDerivedIso.inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus (𝒜 := 𝒜)).obj T.X₁) := by
    simpa [Category.assoc] using hdelta_raw
  have hshift_join :
      single0ToDerivedIso.hom.app S.X₃ ≫
          hS.singleδ ≫
            ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
              (plusιA.map ((single0ToDplus (𝒜 := 𝒜)).map φ.τ₁))⟦(1 : ℤ)⟧' ≫
                (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus (𝒜 := 𝒜)).obj T.X₁) =
      single0ToDerivedIso.hom.app S.X₃ ≫
        hS.singleδ ≫
          ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
            (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus (𝒜 := 𝒜)).obj S.X₁) ≫
              plusιA.map (((single0ToDplus (𝒜 := 𝒜)).map φ.τ₁)⟦(1 : ℤ)⟧') := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ single0ToDerivedIso.hom.app S.X₃ ≫
          hS.singleδ ≫
            ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
              k)
        (plusιA.commShiftIso_inv_naturality
          ((single0ToDplus (𝒜 := 𝒜)).map φ.τ₁) (1 : ℤ))
  have hinv_join :
      single0ToDerivedIso.hom.app S.X₃ ≫
          hS.singleδ ≫
            ((DerivedCategory.singleFunctor 𝒜 0).map φ.τ₁)⟦(1 : ℤ)⟧' ≫
              ((single0ToDerivedIso.inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
                (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus (𝒜 := 𝒜)).obj T.X₁) =
      single0ToDerivedIso.hom.app S.X₃ ≫
        hS.singleδ ≫
          ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
            (plusιA.map ((single0ToDplus (𝒜 := 𝒜)).map φ.τ₁))⟦(1 : ℤ)⟧' ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus (𝒜 := 𝒜)).obj T.X₁) := by
    calc
      single0ToDerivedIso.hom.app S.X₃ ≫
          hS.singleδ ≫
            ((DerivedCategory.singleFunctor 𝒜 0).map φ.τ₁)⟦(1 : ℤ)⟧' ≫
              ((single0ToDerivedIso.inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
                (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus (𝒜 := 𝒜)).obj T.X₁) =
        single0ToDerivedIso.hom.app S.X₃ ≫
          hS.singleδ ≫
            (((DerivedCategory.singleFunctor 𝒜 0).map φ.τ₁)⟦(1 : ℤ)⟧' ≫
              ((single0ToDerivedIso.inv.app T.X₁)⟦(1 : ℤ)⟧')) ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus (𝒜 := 𝒜)).obj T.X₁) := by
        simp [Category.assoc]
      _ =
        single0ToDerivedIso.hom.app S.X₃ ≫
          hS.singleδ ≫
            (((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
              (plusιA.map ((single0ToDplus (𝒜 := 𝒜)).map φ.τ₁))⟦(1 : ℤ)⟧') ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus (𝒜 := 𝒜)).obj T.X₁) := by
        simpa using
          congrArg
            (fun k ↦ single0ToDerivedIso.hom.app S.X₃ ≫
              hS.singleδ ≫
                k ≫
                  (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus (𝒜 := 𝒜)).obj T.X₁))
            hinv
      _ =
        single0ToDerivedIso.hom.app S.X₃ ≫
          hS.singleδ ≫
            ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
              (plusιA.map ((single0ToDplus (𝒜 := 𝒜)).map φ.τ₁))⟦(1 : ℤ)⟧' ≫
                (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus (𝒜 := 𝒜)).obj T.X₁) := by
        simp [Category.assoc]
  have htail : _ := hinv_join.trans hshift_join
  simpa [Category.assoc] using hcomp_join.trans (hdelta_join.trans htail)

/-- Helper for Lemma 13.20.3: the canonical degree-zero embedding into `D^+(\mathcal A)` carries
the connecting morphisms from short exact sequences, yielding a `δ`-functor. -/
private noncomputable def single0ToDplusDeltaFunctor :
    DeltaFunctor 𝒜 D⁺(𝒜) where
  toFunctor := single0ToDplus
  additive := inferInstance
  δ := fun {S} hS ↦
    ObjectProperty.homMk
      (single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ ≫
        ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
          ((Functor.commShiftIso plusιA (1 : ℤ)).inv.app (single0ToDplus.obj S.X₁)))
  map_distinguished := fun {S} hS ↦ by
    simpa [single0ToDplusTriangle, DeltaFunctor.triangle] using
      single0ToDplus_triangle_distinguished hS
  δ_naturality := fun {S T} hS hT φ ↦ by
    simpa using single0ToDplus_delta_naturality hS hT φ

variable (RF : D⁺(𝒜) ⥤ D⁺(ℬ))
variable [RF.CommShift ℤ] [RF.IsTriangulated]

-- Proof sketch: postcompose the canonical bounded-below complex `δ`-functor
-- `boundedBelowComplexToDerivedBelowDeltaFunctor` with the exact functor `RF`.
/- Lemma 13.20.3 (1), exact-functor form: any exact functor
`RF : D^+(\mathcal A) ⥤ D^+(\mathcal B)` induces a `\delta`-functor
`Comp^+(\mathcal A) ⥤ D^+(\mathcal B)`. The canonical bounded-below right derived functor is the
special case obtained by taking `RF` to be `Functor.totalRightDerived`. -/
#check (boundedBelowComplexToDerivedBelowDeltaFunctor.postcomposeExactFunctor RF :
  DeltaFunctor (Comp⁺(𝒜)) D⁺(ℬ))

-- Proof sketch: postcompose the canonical degree-zero bounded-below `δ`-functor
-- `single0ToDplusDeltaFunctor` with the exact functor `RF`.
/- Lemma 13.20.3 (2), exact-functor form: any exact functor
`RF : D^+(\mathcal A) ⥤ D^+(\mathcal B)` induces a `\delta`-functor
`\mathcal A ⥤ D^+(\mathcal B)` on degree-zero objects. The canonical bounded-below right derived
functor is again a specialization. -/
#check (single0ToDplusDeltaFunctor.postcomposeExactFunctor RF :
  DeltaFunctor 𝒜 D⁺(ℬ))

end

end CategoryTheory
