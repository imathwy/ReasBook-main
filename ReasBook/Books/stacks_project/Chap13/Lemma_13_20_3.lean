import Mathlib
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
import stacks_project.Chap13.Definition_13_8_1
import stacks_project.Chap13.Definition_13_3_6
import stacks_project.Chap13.Definition_13_15_3
import stacks_project.Chap13.Lemma_13_12_1
import stacks_project.Chap13.Lemma_13_11_6
import stacks_project.Chap13.Lemma_13_16_6
import stacks_project.Chap13.Lemma_13_20_2
import stacks_project.Chap13.Lemma_13_4_21
import stacks_project.Chap13.Lemma_13_5_8
import stacks_project.Chap13.Proposition_13_14_8
import stacks_project.Chap13.Situation_13_15_1

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

local notation "QisPlus" => boundedBelowHomotopyQuasiIso 𝒜
local notation "Qplus" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜))
local notation "Qhplus" => HomotopyCategory.Plus.quotient 𝒜
local notation "compPlusι" => CochainComplex.Plus.ι 𝒜
local notation "plusιA" => ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))

local instance :
    Functor.IsLocalization Qplus QisPlus :=
  mapBoundedBelowHomotopyToDerivedBelow_isLocalization

local instance : Limits.PreservesFiniteLimits compPlusι := by
  refine ⟨?_⟩
  intro J _ _
  let _ : CreatesLimitsOfShape J compPlusι := by infer_instance
  infer_instance

local instance : Limits.PreservesFiniteColimits compPlusι := by
  refine ⟨?_⟩
  intro J _ _
  let _ : CreatesColimitsOfShape J compPlusι := by infer_instance
  infer_instance

private noncomputable def boundedBelowComplexToDerivedIso :
    Qhplus ⋙ Qplus ⋙ plusιA ≅
      compPlusι ⋙ DerivedCategory.Q :=
  (Functor.associator Qhplus Qplus plusιA).symm ≪≫
    Functor.isoWhiskerLeft Qhplus
      ((t.plus : ObjectProperty (D(𝒜))).liftCompιIso
        (ObjectProperty.ι (HomotopyCategory.plus 𝒜) ⋙ DerivedCategory.Qh)
        qh_obj_mem_t_plus) ≪≫
    Functor.associator Qhplus
      (ObjectProperty.ι (HomotopyCategory.plus 𝒜))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerRight
      ((HomotopyCategory.plus 𝒜).liftCompιIso
        (compPlusι ⋙ HomotopyCategory.quotient 𝒜 (up ℤ))
        (fun K ↦ by
          simpa [HomotopyCategory.plus] using K.property))
      DerivedCategory.Qh ≪≫
    Functor.associator compPlusι
      (HomotopyCategory.quotient 𝒜 (up ℤ)) DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft compPlusι
      (DerivedCategory.quotientCompQhIso 𝒜)

/-- Lemma 13.20.3 (1), source-facing owner: the canonical functor
`Comp^+(\mathcal A) ⥤ D^+(\mathcal A)` carries the connecting morphisms coming from short exact
sequences of bounded-below complexes, making it into a `δ`-functor. -/
noncomputable def boundedBelowComplexToDerivedBelowDeltaFunctor :
    DeltaFunctor (Comp⁺(𝒜)) D⁺(𝒜) where
  toFunctor := Qhplus ⋙ Qplus
  additive := inferInstance
  δ := by
    intro S hS
    let hS' : (S.map compPlusι).ShortExact :=
      @ShortComplex.ShortExact.map_of_exact
        (Comp⁺(𝒜)) (CochainComplex 𝒜 ℤ) _ _
        (Preadditive.preadditiveHasZeroMorphisms)
        (Preadditive.preadditiveHasZeroMorphisms) S hS
        compPlusι (by infer_instance) (by infer_instance) (by infer_instance)
    exact ObjectProperty.homMk
      ((boundedBelowComplexToDerivedIso.hom.app S.X₃) ≫
        DerivedCategory.triangleOfSESδ hS' ≫
        ((boundedBelowComplexToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
          ((Functor.commShiftIso plusιA (1 : ℤ)).inv.app
            ((Qhplus ⋙ Qplus).obj S.X₁)))
  map_distinguished := by
    intro S hS
    sorry
  δ_naturality := by
    intro S T hS hT φ
    sorry

/-- The underlying functor of `boundedBelowComplexToDerivedBelowDeltaFunctor` is the canonical
bounded-below localization functor `K^+(\mathcal A) ⥤ D^+(\mathcal A)`. -/
@[simp] theorem boundedBelowComplexToDerivedBelowDeltaFunctor_toFunctor :
    (boundedBelowComplexToDerivedBelowDeltaFunctor : DeltaFunctor (Comp⁺(𝒜)) D⁺(𝒜)).toFunctor =
      Qhplus ⋙ Qplus :=
  rfl

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

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [EnoughInjectives 𝒜]
  (F : 𝒜 ⥤ ℬ) [F.Additive]
  [hKplusComm : (mapBoundedBelowHomotopyCategoryToDerivedBelow F).CommShift ℤ]
  [hKplusTriangulated : (mapBoundedBelowHomotopyCategoryToDerivedBelow F).IsTriangulated]

local notation "QisPlus" => boundedBelowHomotopyQuasiIso 𝒜
local notation "KplusToDplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow F
local notation "Qplus" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜))
local notation "RplusF" => Functor.totalRightDerived KplusToDplus Qplus QisPlus
local notation "αplus" => Functor.totalRightDerivedUnit KplusToDplus Qplus QisPlus

local instance :
    Functor.IsLocalization Qplus QisPlus :=
  mapBoundedBelowHomotopyToDerivedBelow_isLocalization

-- Proof sketch: Lemma 13.20.2 gives that the bounded-below right derived functor is everywhere
-- defined, so the canonical owner `Functor.totalRightDerived` applies to the bounded-below source
-- functor `KplusToDplus`.
/- The canonical bounded-below right derived functor of `F`, formalized as `RplusF`, comes with
its canonical right-derived witness `αplus`. The exactness assumptions used in the source-facing
statements of Lemma 13.20.3 are carried by the exact functor parameter `RF` in the preceding
section. -/
#check (inferInstance : Functor.IsRightDerivedFunctor RplusF αplus QisPlus)

/- The canonical bounded-below source functor `K^+(\mathcal A) ⥤ D^+(\mathcal B)` is already the
owner `mapBoundedBelowHomotopyCategoryToDerivedBelow F`, and its exactness data are exactly the
direct owner assumptions on that functor. -/
#check (inferInstance : (mapBoundedBelowHomotopyCategoryToDerivedBelow F).CommShift ℤ)
#check (inferInstance : (mapBoundedBelowHomotopyCategoryToDerivedBelow F).IsTriangulated)

end

end CategoryTheory
