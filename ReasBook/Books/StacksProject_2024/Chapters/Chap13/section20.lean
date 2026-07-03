import Mathlib
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_20_1 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {𝒟 : Type u₂}
  [Category.{v₁} 𝒜] [Abelian 𝒜]
  [Category.{v₂} 𝒟]

variable (F : K⁺(𝒜) ⥤ 𝒟)

/- Domain-style sampling for Lemma 13.20.1:
- primary domain: bounded-below injective cochain complexes and right-derived computation /
  acyclicity for additive functors on bounded-below and unbounded homotopy categories;
- sampled owner declarations:
  `CochainComplex.InjectivePlus`,
  `CochainComplex.PlusWithTermsIn.instIsKInjective`,
  `CochainComplex.IsKInjective.Qh_map_bijective`,
  `Functor.ComputesRightDerivedAt`,
  `computes_right_derived_functor_at_iff_bounded_below`;
- best owner abstraction: part `(1)` is source-facing at the chapter owner
  `CochainComplex.InjectivePlus 𝒜`, with computation exported through the canonical owner
  `Functor.ComputesRightDerivedAt`; part `(2)` is the degree-zero specialization to the Chapter 13
  owner `IsRightAcyclicForAdditiveFunctor`;
- primitive data: a bounded-below injective complex `I : CochainComplex.InjectivePlus 𝒜`, or an
  injective object `I : 𝒜`;
- derived API: the computation statement at `((HomotopyCategory.Plus.quotient 𝒜).obj I)` and the
  right-acyclicity statement
  for `I`.

Source/core/bridge triage:
- `source-facing`: the two textbook statements below;
- `core/canonical`: `CochainComplex.InjectivePlus 𝒜`,
  `Functor.ComputesRightDerivedAt`, and `IsRightAcyclicForAdditiveFunctor`;
- `bridge/view`: the canonical K-injective bridge
  `CochainComplex.PlusWithTermsIn.instIsKInjective`, the hom-bijection theorem
  `CochainComplex.IsKInjective.Qh_map_bijective`, and the bounded/unbounded comparison theorem
  `computes_right_derived_functor_at_iff_bounded_below`.
-/

-- Proof sketch: the owner `CochainComplex.InjectivePlus 𝒜` carries the canonical K-injective
-- structure from `CochainComplex.PlusWithTermsIn.instIsKInjective`. Hence the pointwise
-- costructured-arrow diagram over `((HomotopyCategory.Plus.quotient 𝒜).obj I)` is already
-- controlled by the hom-bijection theorem `CochainComplex.IsKInjective.Qh_map_bijective`, so the
-- identity denominator witnesses that `I` computes the right derived functor.
/-- Lemma 13.20.1 (1): a bounded-below cochain complex of injective objects in an abelian
category computes the right derived functor of any functor
`F : K^+(\mathcal A) ⥤ \mathcal D` with respect to quasi-isomorphisms. -/
theorem boundedBelowInjectiveComplex_computesRightDerivedFunctorAt
    (I : CochainComplex.InjectivePlus 𝒜) :
    F.ComputesRightDerivedAt (Qis⁺(𝒜)) ((HomotopyCategory.Plus.quotient 𝒜).obj I) := sorry

end

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F

-- Proof sketch: package the degree-zero complex `I[0]` as an object of
-- `CochainComplex.InjectivePlus 𝒜` using the injectivity of `I`, then apply part (1). Use
-- `computes_right_derived_functor_at_iff_bounded_below` to pass from the bounded-below
-- computation to the unbounded pointwise one, then conclude with the Chapter 13 source-facing owner
-- `IsRightAcyclicForAdditiveFunctor`.
/-- Lemma 13.20.1 (2): every injective object of an abelian category is right acyclic for any
additive functor to an abelian category. -/
theorem injective_isRightAcyclicForAdditiveFunctor
    (I : 𝒜) [Injective I] :
    IsRightAcyclicForAdditiveFunctor F I := sorry

end

end CategoryTheory

/-! ### Lemma_13_20_2 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open ComplexShape
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {𝒟 : Type u₂}
  [Category.{v₁} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
  [Category.{v₂} 𝒟]

variable (F : K⁺(𝒜) ⥤ 𝒟)

local notation "Qhplus" => HomotopyCategory.Plus.quotient 𝒜

-- Proof sketch: use Lemma 13.18.3 to replace every bounded-below complex by a quasi-isomorphic
-- bounded-below complex of injectives, so every object reaches the bounded-below injective
-- homotopy subcategory. Lemma 13.31.2, together with the canonical K-injective instance on the
-- chapter owner `CochainComplex.InjectivePlus 𝒜`, implies that a quasi-isomorphism between
-- bounded-below injective complexes
-- is already an isomorphism in `K^+(\mathcal A)`, hence any exact functor out of
-- `K^+(\mathcal A)` sends it to an isomorphism. Lemma 13.14.15 then yields pointwise existence of
-- the right derived functor.
/-- Lemma 13.20.2: if `𝒜` is an abelian category with enough injectives, then for every exact
functor `F : K^+(\mathcal A) ⥤ \mathcal D` into a triangulated category, the right derived
functor `RF : D^+(\mathcal A) ⥤ \mathcal D` is everywhere defined. -/
theorem boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives :
    F.HasPointwiseRightDerivedFunctor (Qis⁺(𝒜)) := by
  let _ : ObjectProperty.IsStableUnderRetracts (Ac⁺(𝒜)) := by
    dsimp [HomotopyCategory.subcategoryAcyclic]
    infer_instance
  let _ : IsSaturatedMultiplicativeSystem (Qis⁺(𝒜)) := by
    rw [← boundedBelowAcyclicHomotopyProperty_trW_eq_quasiIso 𝒜]
    infer_instance
  refine F.hasPointwiseRightDerivedFunctor_of_subset (Qis⁺(𝒜))
    (boundedBelowInjectiveHomotopyProperty 𝒜) ?_ ?_
  · intro X
    let K : Comp⁺(𝒜) := ⟨X.obj.as, X.property⟩
    obtain ⟨a, hX⟩ := (CochainComplex.plus_iff 𝒜 X.obj.as).1 X.property
    obtain ⟨I, -, -⟩ :=
      exists_injectiveResolution_strictlyGE_with_termwise_mono a hX
    let ι : K ⟶ I.complex.obj := ⟨I.ι⟩
    refine ⟨(Qhplus).obj I.complex.obj, (Qhplus).map ι, ?_, ?_⟩
    · intro n
      simpa using I.injective n
    ·
      simpa [K] using
        (show (Qis⁺(𝒜)) ((Qhplus).map ι) by
          change HomotopyCategory.quasiIso 𝒜 (up ℤ)
            ((HomotopyCategory.quotient 𝒜 (up ℤ)).map I.ι)
          rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
          exact I.quasiIso)
  · intro X X' s hX hX' hs
    change IsIso (F.map s)
    let _ : IsIso s := by
      let Xc : CochainComplex 𝒜 ℤ := X.obj.as
      let Xc' : CochainComplex 𝒜 ℤ := X'.obj.as
      let XI : CochainComplex.InjectivePlus 𝒜 := ⟨⟨Xc, X.property⟩, fun n ↦ by
        simpa [Xc] using hX n⟩
      let X'I : CochainComplex.InjectivePlus 𝒜 := ⟨⟨Xc', X'.property⟩, fun n ↦ by
        simpa [Xc'] using hX' n⟩
      have hs' : HomotopyCategory.quasiIso 𝒜 (up ℤ) s.hom := by
        simpa [boundedBelowHomotopyQuasiIso] using hs
      letI : Xc.IsKInjective :=
        by
          simpa [XI, Xc] using CochainComplex.PlusWithTermsIn.instIsKInjective XI
      letI : Xc'.IsKInjective :=
        by
          simpa [X'I, Xc'] using CochainComplex.PlusWithTermsIn.instIsKInjective X'I
      have hbij :
          ∀ ⦃M N : K(𝒜)⦄ (f : M ⟶ N), HomotopyCategory.quasiIso 𝒜 (up ℤ) f →
            Function.Bijective
              (fun g : N ⟶ (HomotopyCategory.quotient 𝒜 (up ℤ)).obj Xc ↦ f ≫ g) :=
        (CochainComplex.isKInjective_iff_precomp_bijective_of_quasiIso Xc).1
          (show Xc.IsKInjective from inferInstance)
      have hbij' :=
        (CochainComplex.isKInjective_iff_precomp_bijective_of_quasiIso Xc').1
          (show Xc'.IsKInjective from inferInstance)
      obtain ⟨t, ht⟩ := (hbij s.hom hs').surjective (𝟙 X.obj)
      have ht' : s.hom ≫ t = 𝟙 X.obj := by
        simpa using ht
      refine ⟨⟨⟨t⟩, ?_, ?_⟩⟩
      · ext
        exact ht'
      · ext
        apply (hbij' s.hom hs').injective
        calc
          s.hom ≫ t ≫ s.hom = (s.hom ≫ t) ≫ s.hom := by simp [Category.assoc]
          _ = 𝟙 X.obj ≫ s.hom := by rw [ht']; rfl
          _ = s.hom ≫ 𝟙 X'.obj := by simp
    infer_instance

end

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [EnoughInjectives 𝒜]
  [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

-- Proof sketch: specialize the previous theorem to the canonical bounded-below source functor
-- `K^+(\mathcal A) ⥤ D^+(\mathcal B)` attached to `F`.
/-- An additive functor from an abelian category with enough injectives has its bounded-below
right derived functor to `D^+(\mathcal B)` everywhere defined. -/
theorem additiveFunctor_boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives :
    (mapBoundedBelowHomotopyCategoryToDerivedBelow F).HasPointwiseRightDerivedFunctor
      (Qis⁺(𝒜)) := by
  simpa using
    (boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
      (mapBoundedBelowHomotopyCategoryToDerivedBelow F))

attribute [instance]
  additiveFunctor_boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives

end

end CategoryTheory

/-! ### Lemma_13_20_3 (from Chap13) -/
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

/-! ### Lemma_13_20_4 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/-
Domain-style sampling for Lemma 13.20.4:
- primary domain: right derived functors and the cohomological `δ`-functors they induce on
  abelian categories;
- sampled owner declarations:
  `Functor.homologySequenceComposableArrows₅_exact`,
  `Functor.rightDerivedZeroIsoSelf`,
  `Functor.isZero_rightDerived_obj_injective_succ`,
  `boundedBelowRightDerivedDeltaFunctor`,
  `boundedBelowRightDerivedDeltaFunctor_isUniversal_of_rightDerivedComparison`;
- best owner abstractions:
  the five-term exact-sequence owner for part `(1)`, the canonical right-derived owners from
  mathlib for parts `(3)` and `(4)`, and the chapter owner
  `boundedBelowRightDerivedDeltaFunctor RF` for part `(5)`;
- primitive data vs derived API:
  the primitive data are a short exact sequence for the five-term segment and a chosen
  bounded-below right-derived functor `RF` with its derivation witness; exactness, vanishing on
  injectives, and universality are derived API from those owners.

Source/core/bridge triage:
- `source-facing`: the five textbook consequences listed in Lemma 13.20.4.
- `core/canonical`: the mathlib owners `Functor.rightDerivedZeroIsoSelf`,
  `Functor.isZero_rightDerived_obj_injective_succ`, and the chapter owner
  `boundedBelowRightDerivedDeltaFunctor`.
- `bridge/view`: the specialization from enough injectives to the universality bridge
  `boundedBelowRightDerivedDeltaFunctor_isUniversal_of_rightDerivedComparison`.
-/

section FiveTerm

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} ℬ]
  [Abelian (Comp⁺(𝒜))]

/- Lemma 13.20.4 (1): the five-term exact cohomology segment for a short exact sequence of
bounded-below complexes is obtained by applying the canonical owner theorem
`Functor.homologySequenceComposableArrows₅_exact` to the distinguished triangle `G.triangle hS`
attached to that short exact sequence by the `δ`-functor `G`, and then truncating by `δlast`. -/
recall Functor.homologySequenceComposableArrows₅_exact

end FiveTerm

section BoundedBelowVanishing

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
  (boundedBelowHomotopyQuasiIso 𝒜)]
variable (RF : D⁺(𝒜) ⥤ D⁺(ℬ))
variable (α : mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶
  mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜) ⋙ RF)
variable [RF.IsRightDerivedFunctor α (boundedBelowHomotopyQuasiIso 𝒜)]

/- Lemma 13.20.4 (2): the negative cohomology functors of the bounded-below right derived
construction on degree-zero objects vanish. This is the canonical owner theorem from
Lemma `13.16.3`, recalled here rather than redeclared under a parallel name. -/
recall boundedBelowRightDerived_isZero_of_neg

end BoundedBelowVanishing

section RightDerived

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]
  [HasInjectiveResolutions 𝒜]

section

variable [PreservesFiniteLimits F]

/- Lemma 13.20.4 (3): under `[PreservesFiniteLimits F]`, mathlib packages the canonical
identification `R^0F ≅ F` as `Functor.rightDerivedZeroIsoSelf`; equivalently,
`F.toRightDerivedZero : F ⟶ R^0F` is an isomorphism. -/
recall Functor.rightDerivedZeroIsoSelf

end

/- Lemma 13.20.4 (4): injective objects are acyclic for the positive right derived functors of
`F`; this is the canonical mathlib owner theorem `Functor.isZero_rightDerived_obj_injective_succ`.
-/
recall Functor.isZero_rightDerived_obj_injective_succ

end RightDerived

section Universality

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]
  [PreservesFiniteLimits F] [EnoughInjectives 𝒜]

variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
  (boundedBelowHomotopyQuasiIso 𝒜)]
variable (RF : D⁺(𝒜) ⥤ D⁺(ℬ))
variable [RF.CommShift ℤ] [RF.IsTriangulated]

-- Proof sketch: apply the chapter owner theorem
-- `boundedBelowRightDerivedDeltaFunctor_isUniversal_of_rightDerivedComparison`; enough injectives
-- provide the required monomorphisms into right-acyclic objects via `EnoughInjectives.presentation`
-- and Lemma `13.20.1`.
/-- Lemma 13.20.4 (5): under enough injectives, if the bounded-below right derived functors
`A ↦ H^n((RF(A[0])) : D(\mathcal B))` agree degreewise with the canonical unbounded higher right
derived functors `R^nF`, then the canonical bounded-below right-derived cohomological
`δ`-functor is universal. -/
theorem boundedBelowRightDerivedDeltaFunctor_isUniversal_of_enoughInjectives
    (hcompare : ∀ n : ℕ, IsIsomorphic (RF.boundedBelowRightDerived n) (F.rightDerived n)) :
    CohomologicalDeltaFunctor.IsUniversal (boundedBelowRightDerivedDeltaFunctor RF) := by
  refine boundedBelowRightDerivedDeltaFunctor_isUniversal_of_rightDerivedComparison F RF hcompare ?_
  intro X
  let p := (EnoughInjectives.presentation X).some
  refine ⟨p.J, p.f, inferInstance, injective_isRightAcyclicForAdditiveFunctor F p.J⟩

end Universality

end CategoryTheory
