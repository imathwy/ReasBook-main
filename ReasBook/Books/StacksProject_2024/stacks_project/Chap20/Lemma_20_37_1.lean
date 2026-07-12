import Mathlib.Algebra.Category.ModuleCat.Limits
import StacksProject_2024.Chap15.Lemma_15_87_10
import StacksProject_2024.Chap19.Lemma_19_13_6
import StacksProject_2024.Chap20.Global_sections_module_owners_core
import StacksProject_2024.Chap20.Sections_on_open
import StacksProject_2024.Chap21.DerivedCategoryExact

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open CategoryTheory.Pretriangulated
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpaceDerivedSectionsAtOpenToAb

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u}) (U : Opens X.carrier)

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "QModX" => (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DModX)
local notation "QisModX" => HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)
local notation "H" p:max => DerivedCategory.homologyFunctor AddCommGrpCat p

local notation "RΓMod[" U "]" => moduleDerivedSectionsAtOpen X U
local notation:max "H^" p:max "(" U ", " K ")" =>
  moduleOpenHypercohomology X U K p

/-- Helper for Lemma 20.37.1: this names the ordinary module-valued sections functor on `U`
before passing to complexes or derived categories. -/
private abbrev moduleSectionsOnOpenFunctor :
    X.Modules ⥤ ModuleCat (sectionsRingOnOpen X U) :=
  SheafOfModules.evaluation X.ringCatSheaf (op U)

/-- Helper for Lemma 20.37.1: keep the additive structure on ordinary sections over `U`
available while elaborating owner-level helper signatures. -/
local instance moduleSectionsEvaluation_additive_local :
    (moduleSectionsOnOpenFunctor (X := X) (U := U)).Additive :=
  moduleSectionsEvaluation_additive X U

/-- Helper for Lemma 20.37.1: ordinary abelian-valued sections over `U` are additive already at
the section level, so owner-level comparison helpers can elaborate without theorem-body plumbing.
-/
local instance moduleSectionsAsAbelianFunctor_additive_local :
    (moduleSectionsAsAbelianFunctor X U).Additive :=
  moduleSectionsAsAbelianFunctor_additive X U

/-- Helper for Lemma 20.37.1: abelian-valued sections over `U` preserve countable products, so
the Milnor short exact sequence applies directly to the sections tower. -/
local instance moduleSectionsAsAbelianFunctor_preservesDiscreteNatLimits :
    PreservesLimitsOfShape (Discrete ℕ) (moduleSectionsAsAbelianFunctor X U) := by
  -- Proof comment: evaluation on `U` preserves countable products, and the forgetful functor to
  -- abelian groups preserves all limits, so their composite does as well.
  refine ⟨?_⟩
  intro K
  letI : PreservesLimit K (SheafOfModules.evaluation X.ringCatSheaf (op U)) := by
    letI :
        PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.evaluation X.ringCatSheaf (op U)) :=
      SheafOfModules.evaluationPreservesLimitsOfShape
        (D := Discrete ℕ) X.ringCatSheaf (op U)
    infer_instance
  letI :
      PreservesLimit
        (K ⋙ SheafOfModules.evaluation X.ringCatSheaf (op U))
        (forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}) :=
    ModuleCat.forget₂AddCommGroup_preservesLimit
      (F := K ⋙ SheafOfModules.evaluation X.ringCatSheaf (op U))
  simpa [moduleSectionsAsAbelianFunctor] using
    (CategoryTheory.Limits.comp_preservesLimit
      (K := K)
      (F := SheafOfModules.evaluation X.ringCatSheaf (op U))
      (G := forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}))

/- Domain-style sampling for Lemma 20.37.1:
- primary domain: sequential derived inverse limits in `D(𝒪_X)` and their behavior under open
  derived sections over a fixed open subset, together with the resulting Milnor short exact
  sequence on open hypercohomology groups;
- sampled owner declarations:
  `moduleDerivedSectionsAtOpen`,
  `moduleDerivedSectionsAtOpenToAb`,
  `CategoryTheory.additiveFunctor_totalRightDerived_preservesDerivedLimit`,
  `CategoryTheory.derivedLimit_cohomology_shortExact`;
- best owner abstraction:
  `source-facing`: the open-sections specialization of derived-limit preservation for
    `RΓ(U, -)` and the resulting Milnor short exact sequence on `H^m(U, K)`;
  `core/canonical`: the Chapter 20 owners `moduleDerivedSectionsAtOpen` for part `(1)` and
    the Chapter 15 owner theorem `derivedLimit_cohomology_shortExact`;
  `bridge/view`: the exact codomain-change bridge `moduleDerivedSectionsAtOpenToAb X U` from the
    canonical owner `moduleDerivedSectionsAtOpen X U` into `D(AddCommGrpCat)`, together with
    the Chapter 19 preservation theorem for additive total right derived functors used in part
    `(1)`.

Primitive data are only the ringed space `X`, the open subset `U`, the sequential inverse system
`Ksys`, the chosen derived-limit object `K`, and the cohomological degree `m`. The left
`R^1 lim` term is already canonically owned by
`SequentialInverseSystem.firstDerivedLimit` on the additive cohomology tower
`(Ksys ⋙ RΓ[U]) ⋙ H _`.
-/

/-- Helper for Lemma 20.37.1: ordinary module-valued sections over `U`, followed by passage to the
derived category, form the source functor whose right-derived owner is `RΓMod[U]`. -/
private abbrev moduleSectionsToDerived :
    CochainComplex X.Modules ℤ ⥤
      DerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  (moduleSectionsOnOpenFunctor (X := X) (U := U)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

/-- Helper for Lemma 20.37.1: the cochain-level sections functor on `U` admits the standard
Chapter 19 right-derived-functor structure. -/
private theorem moduleSectionsToDerived_hasRightDerivedFunctor :
    (moduleSectionsToDerived (X := X) (U := U)).HasRightDerivedFunctor QisModX := by
  -- Proof comment: ordinary sections on `U` are additive, so Chapter 19 provides the cochain-level
  -- right-derived-functor witness directly.
  simpa [moduleSectionsToDerived] using
    (CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor
      (moduleSectionsOnOpenFunctor (X := X) (U := U)))

attribute [local instance] moduleSectionsToDerived_hasRightDerivedFunctor

/-- Helper for Lemma 20.37.1: this is the source-to-owner unit exhibiting `RΓMod[U]` as the
chosen right derived functor of ordinary module-valued sections on `U`. -/
private abbrev moduleDerivedSectionsAtOpenUnit :
    moduleSectionsToDerived (X := X) (U := U) ⟶ QModX ⋙ RΓMod[U] :=
  let F : X.Modules ⥤ ModuleCat (sectionsRingOnOpen X U) :=
    SheafOfModules.evaluation X.ringCatSheaf (op U)
  let _ : F.Additive := moduleSectionsEvaluation_additive X U
  (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerivedUnit
    QModX
    QisModX

/-- Helper for Lemma 20.37.1: the Chapter 20 module-valued owner carries the expected
right-derived-functor structure. -/
private instance moduleDerivedSectionsAtOpen_isRightDerivedFunctor :
    Functor.IsRightDerivedFunctor
      (RΓMod[U])
      (moduleDerivedSectionsAtOpenUnit (X := X) (U := U))
      QisModX := by
  -- Proof comment: unfold the Chapter 20 owner once and reuse the canonical total-right-derived
  -- instance for the cochain-level sections functor.
  simpa [moduleSectionsToDerived, moduleDerivedSectionsAtOpen, moduleDerivedSectionsAtOpenUnit] using
    (inferInstance :
      Functor.IsRightDerivedFunctor
        ((moduleSectionsToDerived (X := X) (U := U)).totalRightDerived QModX QisModX)
        ((moduleSectionsToDerived (X := X) (U := U)).totalRightDerivedUnit QModX QisModX)
        QisModX)

/-- Helper for Lemma 20.37.1: the Chapter 19 canonical owner already carries its cochain-level
right-derived structure for ordinary module-valued sections over `U`. -/
private instance moduleSectionsOnOpen_totalRightDerived_isRightDerivedFunctor :
    Functor.IsRightDerivedFunctor
      (CategoryTheory.additiveFunctorTotalRightDerived
        (moduleSectionsOnOpenFunctor (X := X) (U := U)))
      (CategoryTheory.additiveFunctorTotalRightDerivedUnit
        (moduleSectionsOnOpenFunctor (X := X) (U := U)))
      QisModX := by
  -- TODO: normalize `additiveFunctorTotalRightDerivedUnit` to the abstract homotopy-side
  -- `Functor.totalRightDerivedUnit`, then reuse the canonical total-right-derived instance.
  sorry

/-- Helper for Lemma 20.37.1: the Chapter 20 owner `RΓMod[U]` is canonically the Chapter 19 total
right derived functor of ordinary module-valued sections over `U`. -/
private noncomputable def moduleDerivedSectionsAtOpen_totalRightDerivedIso :
    RΓMod[U] ≅
      CategoryTheory.additiveFunctorTotalRightDerived
        (moduleSectionsOnOpenFunctor (X := X) (U := U)) := by
  -- Route correction: the Chapter 19 canonical owner already exposes the needed cochain-level
  -- `IsRightDerivedFunctor` instance on `additiveFunctorTotalRightDerivedUnit`, so uniqueness of
  -- right derived functors compares it directly with the Chapter 20 owner `RΓMod[U]`.
  exact
    (RΓMod[U]).rightDerivedUnique
      (CategoryTheory.additiveFunctorTotalRightDerived
        (moduleSectionsOnOpenFunctor (X := X) (U := U)))
      (moduleDerivedSectionsAtOpenUnit (X := X) (U := U))
      (CategoryTheory.additiveFunctorTotalRightDerivedUnit
        (moduleSectionsOnOpenFunctor (X := X) (U := U)))
      QisModX

/-- Helper for Lemma 20.37.1: ordinary abelian-valued sections over `U`, followed by passage to
the derived category, form the source functor whose right-derived owners are the abelian-valued
Chapter 20 sections functors. -/
private abbrev moduleSectionsAsAbelianToDerived :
    CochainComplex X.Modules ℤ ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (moduleSectionsAsAbelianFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

/-- Helper for Lemma 20.37.1: the cochain-level abelian-valued sections functor on `U` admits the
standard Chapter 19 right-derived-functor structure. -/
private theorem moduleSectionsAsAbelianToDerived_hasRightDerivedFunctor :
    (moduleSectionsAsAbelianToDerived (X := X) (U := U)).HasRightDerivedFunctor QisModX := by
  -- Proof comment: Chapter 19 also derives the abelian-valued sections functor directly.
  simpa [moduleSectionsAsAbelianToDerived] using
    (CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor
      (moduleSectionsAsAbelianFunctor X U))

attribute [local instance] moduleSectionsAsAbelianToDerived_hasRightDerivedFunctor

/-- Helper for Lemma 20.37.1: the Chapter 20 abelian-valued owner carries the expected
right-derived-functor structure. -/
private instance moduleSectionsAsAbelianDerived_isRightDerivedFunctor :
    Functor.IsRightDerivedFunctor
      (moduleSectionsAsAbelianDerived X U)
      ((moduleSectionsAsAbelianToDerived (X := X) (U := U)).totalRightDerivedUnit QModX QisModX)
      QisModX := by
  -- Proof comment: unfold the abelian-valued owner once and use the canonical total-right-derived
  -- instance attached to the source functor.
  simpa [moduleSectionsAsAbelianDerived, moduleSectionsAsAbelianToDerived] using
    (inferInstance :
      Functor.IsRightDerivedFunctor
        ((moduleSectionsAsAbelianToDerived (X := X) (U := U)).totalRightDerived QModX QisModX)
        ((moduleSectionsAsAbelianToDerived (X := X) (U := U)).totalRightDerivedUnit QModX QisModX)
        QisModX)

/-- Helper for Lemma 20.37.1: the Chapter 19 canonical owner already carries its cochain-level
right-derived structure for ordinary abelian-valued sections over `U`. -/
private instance moduleSectionsAsAbelian_totalRightDerived_isRightDerivedFunctor :
    Functor.IsRightDerivedFunctor
      (CategoryTheory.additiveFunctorTotalRightDerived
        (moduleSectionsAsAbelianFunctor X U))
      (CategoryTheory.additiveFunctorTotalRightDerivedUnit
        (moduleSectionsAsAbelianFunctor X U))
      QisModX := by
  -- TODO: as above, bridge the explicit Chapter 19 cochain-level unit to the abstract
  -- homotopy-side total-right-derived unit before invoking the canonical instance.
  sorry

/-- Helper for Lemma 20.37.1: the Chapter 20 abelian-valued owner is canonically the Chapter 19
total right derived functor of ordinary abelian-valued sections over `U`. -/
private noncomputable def moduleSectionsAsAbelianDerived_totalRightDerivedIso :
    moduleSectionsAsAbelianDerived X U ≅
      CategoryTheory.additiveFunctorTotalRightDerived
        (moduleSectionsAsAbelianFunctor X U) := by
  -- Route correction: the same uniqueness comparison works for the abelian-valued open-sections
  -- owner, now with the Chapter 20 source unit for `moduleSectionsAsAbelianDerived X U`.
  exact
    (moduleSectionsAsAbelianDerived X U).rightDerivedUnique
      (CategoryTheory.additiveFunctorTotalRightDerived
        (moduleSectionsAsAbelianFunctor X U))
      ((moduleSectionsAsAbelianToDerived (X := X) (U := U)).totalRightDerivedUnit QModX QisModX)
      (CategoryTheory.additiveFunctorTotalRightDerivedUnit
        (moduleSectionsAsAbelianFunctor X U))
      QisModX

/-- Helper for Lemma 20.37.1: an isomorphism of sequential inverse systems induces the canonical
isomorphism between their product objects. -/
private noncomputable def towerProductIso
    {C : Type*} [Category C]
    {Ksys Lsys : SequentialInverseSystem C}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    (∏ᶜ inverseSystemFamily Ksys) ≅ ∏ᶜ inverseSystemFamily Lsys := by
  -- Proof comment: transport the discrete product diagram stagewise along the tower isomorphism.
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun n : Discrete ℕ ↦ e.app (Opposite.op n.as)
  exact HasLimit.isoOfNatIso eFamily

/-- Helper for Lemma 20.37.1: the product isomorphism induced by a tower isomorphism preserves
each stage projection. -/
private theorem towerProductIso_hom_comp_π
    {C : Type*} [Category C]
    {Ksys Lsys : SequentialInverseSystem C}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) (n : ℕ) :
    (towerProductIso e).hom ≫ Pi.π (inverseSystemFamily Lsys) n =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (Opposite.op n)).hom := by
  -- Proof comment: this is the defining projection formula for `HasLimit.isoOfNatIso`.
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun m : Discrete ℕ ↦ e.app (Opposite.op m.as)
  simpa [towerProductIso, eFamily] using limMap_π (α := eFamily.hom) (j := Discrete.mk n)

/-- Helper for Lemma 20.37.1: the product isomorphism induced by a tower isomorphism intertwines
the two Milnor difference maps. -/
private theorem towerProductIso_hom_comm_difference
    {C : Type*} [Category C] [Preadditive C]
    {Ksys Lsys : SequentialInverseSystem C}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    (towerProductIso e).hom ≫ derivedLimitDifferenceMap Lsys =
      derivedLimitDifferenceMap Ksys ≫ (towerProductIso e).hom := by
  -- Proof comment: compare the two Milnor endomorphisms after each projection to a stage.
  apply Pi.hom_ext
  intro n
  calc
    ((towerProductIso e).hom ≫ derivedLimitDifferenceMap Lsys) ≫
        Pi.π (inverseSystemFamily Lsys) n =
      (towerProductIso e).hom ≫
        (Pi.π (inverseSystemFamily Lsys) n -
          Pi.π (inverseSystemFamily Lsys) (n + 1) ≫
            Lsys.transitionMap (Nat.le_succ n)) := by
          rw [Category.assoc, derivedLimitDifferenceMap_comp_π]
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (Opposite.op n)).hom -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          (e.app (Opposite.op (n + 1))).hom ≫
            Lsys.transitionMap (Nat.le_succ n)) := by
          rw [Preadditive.comp_sub]
          rw [towerProductIso_hom_comp_π]
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ t ≫ Lsys.transitionMap (Nat.le_succ n))
              (towerProductIso_hom_comp_π e (n + 1))
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (Opposite.op n)).hom -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n) ≫
            (e.app (Opposite.op n)).hom) := by
          -- Proof comment: naturality identifies the successor-transition contribution.
          congr 1
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫ t)
              (e.hom.naturality ((homOfLE (Nat.le_succ n)).op)).symm
    _ =
      (Pi.π (inverseSystemFamily Ksys) n -
        Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n)) ≫
        (e.app (Opposite.op n)).hom := by
          rw [Preadditive.sub_comp]
          simp [Category.assoc]
    _ =
      derivedLimitDifferenceMap Ksys ≫ Pi.π (inverseSystemFamily Ksys) n ≫
        (e.app (Opposite.op n)).hom := by
          rw [← derivedLimitDifferenceMap_comp_π_assoc]
    _ =
      ((derivedLimitDifferenceMap Ksys ≫ (towerProductIso e).hom) ≫
        Pi.π (inverseSystemFamily Lsys) n) := by
          rw [Category.assoc, ← towerProductIso_hom_comp_π, ← Category.assoc]

/-- Helper for Lemma 20.37.1: a derived-limit witness transports across an isomorphism of towers
while keeping the limiting object fixed. -/
private theorem isDerivedLimitOfTowerIso
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    {Ksys Lsys : SequentialInverseSystem C} {K : C}
    (e : Ksys ≅ Lsys)
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit Lsys K := by
  rcases hK with ⟨hP, ι, δ, hδ⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun n : Discrete ℕ ↦ e.app (Opposite.op n.as)
  let hQ : HasProduct (inverseSystemFamily Lsys) := by
    exact hasLimit_of_iso eFamily
  letI : HasProduct (inverseSystemFamily Lsys) := hQ
  let p : (∏ᶜ inverseSystemFamily Ksys) ≅ ∏ᶜ inverseSystemFamily Lsys :=
    towerProductIso e
  let T : Triangle C :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let T' : Triangle C :=
    Triangle.mk (ι ≫ p.hom) (derivedLimitDifferenceMap Lsys) (p.inv ≫ δ)
  have hIso : T ≅ T' := by
    -- Proof comment: repackage the original Milnor triangle through the product comparison.
    refine Triangle.isoMk _ _ (Iso.refl _) p p ?_ ?_ ?_
    · simp [T, T']
    · simpa [T, T'] using (towerProductIso_hom_comm_difference e).symm
    · simp [T, T']
  have hT' : T' ∈ distTriang C := by
    -- Proof comment: distinguished triangles are stable under isomorphism.
    exact isomorphic_distinguished _ hδ _ hIso.symm
  exact ⟨hQ, ι ≫ p.hom, p.inv ≫ δ, hT'⟩

/-- Helper for Lemma 20.37.1: a derived-limit witness also transports across an isomorphism of
the limiting object while keeping the tower fixed. -/
private theorem isDerivedLimitOfObjectIso
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    {Ksys : SequentialInverseSystem C} {K L : C}
    (e : K ≅ L)
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit Ksys L := by
  rcases hK with ⟨hP, ι, δ, hδ⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  let T : Triangle C :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let T' : Triangle C :=
    Triangle.mk
      (e.inv ≫ ι)
      (derivedLimitDifferenceMap Ksys)
      (δ ≫ (shiftFunctor C (1 : ℤ)).map e.hom)
  have hIso : T ≅ T' := by
    -- Proof comment: only the first vertex and the shifted last leg change under the object
    -- isomorphism; the product vertices remain fixed.
    refine Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · simp [T, T']
    · simp [T, T']
    · simp [T, T']
  have hT' : T' ∈ distTriang C := by
    -- Proof comment: distinguished Milnor triangles are stable under isomorphism.
    exact isomorphic_distinguished _ hδ _ hIso.symm
  exact ⟨hP, e.inv ≫ ι, δ ≫ (shiftFunctor C (1 : ℤ)).map e.hom, hT'⟩

/-- Helper for Lemma 20.37.1: a derived-limit witness transports across postcomposition by a
natural isomorphism of target functors. -/
private theorem isDerivedLimitOfPostcompIso
    {C D : Type*} [Category C] [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    {A : SequentialInverseSystem C} {X : C} {F G : C ⥤ D}
    (e : F ≅ G)
    (h : IsDerivedLimit (A ⋙ F) (F.obj X)) :
    IsDerivedLimit (A ⋙ G) (G.obj X) := by
  -- Route correction: use the tower-level transport once on `Functor.isoWhiskerLeft A e`, rather
  -- than rebuilding the Milnor comparison separately in each derived-limit theorem below.
  let hTower :
      IsDerivedLimit (A ⋙ G) (F.obj X) :=
    isDerivedLimitOfTowerIso (Functor.isoWhiskerLeft A e) h
  exact isDerivedLimitOfObjectIso (e.app X) hTower

-- Proof sketch: apply Lemma `19.13.6` to the additive sections functor `Γ(U, -)` on
-- `𝒪_X`-modules with values in `Γ(U, 𝒪_X)`-modules, using the Chapter 20 owner
-- `moduleDerivedSectionsAtOpen X U`.
/-- Lemma 20.37.1 (1): for a ringed space `X` and an open subset `U ⊆ X`, the derived sections
functor `RΓ(U, -)` on `D(𝒪_X)`, valued in `D(ModuleCat (sectionsRingOnOpen X U))`, sends a
sequential derived inverse limit to the
derived inverse limit of the stagewise derived sections. -/
@[stacks 0D60]
theorem derivedSectionsOverOpen_preservesDerivedLimit
    {Ksys : SequentialInverseSystem DModX} {K : DModX}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit (Ksys ⋙ RΓMod[U]) ((RΓMod[U]).obj K) := by
  letI :
      PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.evaluation X.ringCatSheaf (op U)) :=
    SheafOfModules.evaluationPreservesLimitsOfShape (D := Discrete ℕ) X.ringCatSheaf (op U)
  let e :
      RΓMod[U] ≅ CategoryTheory.additiveFunctorTotalRightDerived
        (moduleSectionsOnOpenFunctor (X := X) (U := U)) :=
    moduleDerivedSectionsAtOpen_totalRightDerivedIso (X := X) (U := U)
  let hDerived :
      IsDerivedLimit
        (Ksys ⋙ CategoryTheory.additiveFunctorTotalRightDerived
          (moduleSectionsOnOpenFunctor (X := X) (U := U)))
        ((CategoryTheory.additiveFunctorTotalRightDerived
          (moduleSectionsOnOpenFunctor (X := X) (U := U))).obj K) :=
    CategoryTheory.additiveFunctor_totalRightDerived_preservesDerivedLimit
      (SheafOfModules.evaluation X.ringCatSheaf (op U)) hK
  -- Route correction: compare `RΓMod[U]` to the canonical Chapter 19 owner once by
  -- `rightDerivedUnique`, then transport the entire tower by `Functor.isoWhiskerLeft`.
  exact isDerivedLimitOfPostcompIso (A := Ksys) (X := K) e.symm hDerived

-- Proof sketch: compare the canonical abelian-valued owner `RΓ[U]` with the total right derived
-- functor of ordinary abelian-valued sections on `U`, then apply Lemma `19.13.6` in
-- `D(AddCommGrpCat)`.
/-- Bridge companion to Lemma 20.37.1 (1): after forgetting the
`Γ(U, 𝒪_X)`-module structure, the abelian-valued open derived sections functor `RΓ[U]` still
carries a derived limit of a sequential inverse system in `D(𝒪_X)` to the derived limit of the
stagewise derived sections over `U`, now viewed in `D(AddCommGrpCat)`. -/
theorem derivedSectionsOverOpen_underlyingAbelian_preservesDerivedLimit
    {Ksys : SequentialInverseSystem DModX} {K : DModX}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit (Ksys ⋙ RΓ[U]) ((RΓ[U]).obj K) := by
  let eAb :
      moduleSectionsAsAbelianDerived X U ≅
        CategoryTheory.additiveFunctorTotalRightDerived
          (moduleSectionsAsAbelianFunctor X U) :=
    moduleSectionsAsAbelianDerived_totalRightDerivedIso (X := X) (U := U)
  rcases moduleDerivedSectionsAtOpenToAb_isomorphic_moduleSectionsAsAbelianDerived X U with ⟨e⟩
  let hDerived :
      IsDerivedLimit
        (Ksys ⋙ CategoryTheory.additiveFunctorTotalRightDerived
          (moduleSectionsAsAbelianFunctor X U))
        ((CategoryTheory.additiveFunctorTotalRightDerived
          (moduleSectionsAsAbelianFunctor X U)).obj K) :=
    CategoryTheory.additiveFunctor_totalRightDerived_preservesDerivedLimit
      (moduleSectionsAsAbelianFunctor X U) hK
  let hAb :
      IsDerivedLimit
        (Ksys ⋙ moduleSectionsAsAbelianDerived X U)
        ((moduleSectionsAsAbelianDerived X U).obj K) :=
    isDerivedLimitOfPostcompIso (A := Ksys) (X := K) eAb.symm hDerived
  -- Route correction: do not forget the module-valued theorem from part `(1)`; transport directly
  -- from the Chapter 19 abelian owner to `RΓ[U]` through the canonical Chapter 20 bridge.
  exact isDerivedLimitOfPostcompIso (A := Ksys) (X := K) e.symm hAb

-- Proof sketch: move homology across the exact forgetful functor from
-- `Γ(U, 𝒪_X)`-modules to abelian groups, then unfold the Chapter 20 owner `RΓ[U]`.
/-- Helper for Lemma 20.37.1: forgetting the `Γ(U, 𝒪_X)`-module structure identifies
`H^q(U, K)` with the degree-`q` homology of the abelian-valued derived sections object
`(RΓ[U]).obj K`. -/
private noncomputable abbrev moduleOpenHypercohomologyIsoDerivedSectionsToAbHomology
    (K : DModX) (q : ℤ) :
    H^q(U, K) ≅
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).obj
        ((RΓ[U]).obj K) :=
  let F : ModuleCat (sectionsRingOnOpen X U) ⥤ AddCommGrpCat.{u} :=
    forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}
  CategoryTheory.exactFunctor_homology_iso_mapDerivedCategory
    F
    ((moduleDerivedSectionsAtOpen X U).obj K)
    q

-- Proof comment: the remaining proof only transports the Milnor short complex across the
-- canonical comparison isomorphism on its middle term.
/-- Helper for Lemma 20.37.1: conjugating the Milnor short-complex differential by the canonical
middle-term comparison `H^m(U, K) ≅ H_m((RΓ[U]).obj K)` preserves the zero composite. -/
private theorem derivedSectionsOverOpenMiddleTransportZero
    {A C : AddCommGrpCat.{u}} {K : DModX} {m : ℤ}
    (e : H^m(U, K) ≅ (H m).obj ((RΓ[U]).obj K))
    (ι₀ : A ⟶ (H m).obj ((RΓ[U]).obj K))
    (π₀ : (H m).obj ((RΓ[U]).obj K) ⟶ C)
    (h₀ : ι₀ ≫ π₀ = 0) :
    (ι₀ ≫ e.inv) ≫ (e.hom ≫ π₀) = 0 := by
  -- Proof comment: only associativity and the inverse-hom cancellation for `e` are needed.
  simpa [Category.assoc] using h₀

/-- Helper for Lemma 20.37.1: the transported left differential is compatible with the middle
comparison isomorphism used in the Milnor short-complex transport. -/
private theorem derivedSectionsOverOpenMiddleTransportLeft
    {A : AddCommGrpCat.{u}} {K : DModX} {m : ℤ}
    (e : H^m(U, K) ≅ (H m).obj ((RΓ[U]).obj K))
    (ι₀ : A ⟶ (H m).obj ((RΓ[U]).obj K)) :
    (Iso.refl A).hom ≫ (ι₀ ≫ e.inv) = ι₀ ≫ e.symm.hom := by
  -- Proof comment: the left endpoint is unchanged, so this square is just identity transport.
  simp

/-- Helper for Lemma 20.37.1: the transported right differential is compatible with the middle
comparison isomorphism used in the Milnor short-complex transport. -/
private theorem derivedSectionsOverOpenMiddleTransportRight
    {C : AddCommGrpCat.{u}} {K : DModX} {m : ℤ}
    (e : H^m(U, K) ≅ (H m).obj ((RΓ[U]).obj K))
    (π₀ : (H m).obj ((RΓ[U]).obj K) ⟶ C) :
    e.symm.hom ≫ (e.hom ≫ π₀) = π₀ ≫ (Iso.refl C).hom := by
  -- Proof comment: the right endpoint is unchanged, so the square reduces to `e.inv ≫ e.hom = 𝟙`.
  simp

/-- Helper for Lemma 20.37.1: the Milnor short complex for `((RΓ[U]).obj K)` is canonically
isomorphic to the source-facing short complex whose middle term is `H^m(U, K)`. -/
private noncomputable def derivedSectionsOverOpenMiddleTransportIso
    {A C : AddCommGrpCat.{u}} {K : DModX} {m : ℤ}
    (e : H^m(U, K) ≅ (H m).obj ((RΓ[U]).obj K))
    (ι₀ : A ⟶ (H m).obj ((RΓ[U]).obj K))
    (π₀ : (H m).obj ((RΓ[U]).obj K) ⟶ C)
    (h₀ : ι₀ ≫ π₀ = 0) :
    ShortComplex.mk ι₀ π₀ h₀ ≅
      ShortComplex.mk
        (ι₀ ≫ e.inv)
        (e.hom ≫ π₀)
        (derivedSectionsOverOpenMiddleTransportZero (X := X) (U := U) e ι₀ π₀ h₀) :=
  -- Proof comment: package the two transported differential compatibilities into one reusable
  -- short-complex isomorphism.
  ShortComplex.isoMk
    (Iso.refl _)
    e.symm
    (Iso.refl _)
    (derivedSectionsOverOpenMiddleTransportLeft (X := X) (U := U) e ι₀)
    (derivedSectionsOverOpenMiddleTransportRight (X := X) (U := U) e π₀)

-- Proof sketch: first apply part `(1)` to identify `RΓ[U](K)` as a derived limit of the
-- tower `n ↦ H^m(U, K_n)` computed by the canonical abelian-valued owner `RΓ[U]`, and then
-- apply the Chapter 15 Milnor short exact sequence directly on that tower.
/-- Lemma 20.37.1 (2): for a ringed space `X`, an open subset `U ⊆ X`, a sequential inverse
system `(K_n)` in `D(𝒪_X)`, a chosen derived limit `K = R lim K_n`, and
`m : ℤ`, the groups `H^m(U, K)` fit into the short exact sequence
`0 ⟶ R^1 lim H^{m-1}(U, K_n) ⟶ H^m(U, K) ⟶ lim H^m(U, K_n) ⟶ 0`.
Here the left and right towers are formed directly from the canonical Chapter 20 owner `RΓ[U]`. -/
@[stacks 0D60]
theorem derivedSectionsOverOpen_cohomology_shortExact
    (Ksys : SequentialInverseSystem DModX) (K : DModX)
    (hK : IsDerivedLimit Ksys K) (m : ℤ) :
    ∃ (ι :
        SequentialInverseSystem.firstDerivedLimit
            ((Ksys ⋙ RΓ[U]) ⋙ H (m - 1)) ⟶
          H^m(U, K))
      (π :
        H^m(U, K) ⟶
          limit ((Ksys ⋙ RΓ[U]) ⋙ H m))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  let e :
      H^m(U, K) ≅
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
          ((RΓ[U]).obj K) :=
    moduleOpenHypercohomologyIsoDerivedSectionsToAbHomology (X := X) (U := U) K m
  -- Proof comment: specialize the generic Milnor short exact sequence to the abelian-valued
  -- derived sections tower `Ksys ⋙ RΓ[U]`.
  rcases CategoryTheory.derivedLimit_cohomology_shortExact
      (Ksys ⋙ RΓ[U])
      ((RΓ[U]).obj K)
      (derivedSectionsOverOpen_underlyingAbelian_preservesDerivedLimit
        (X := X) (U := U) hK)
      m with
    ⟨ι₀, π₀, h₀, hShort₀⟩
  let transportedZero : (ι₀ ≫ e.inv) ≫ (e.hom ≫ π₀) = 0 :=
    derivedSectionsOverOpenMiddleTransportZero (X := X) (U := U) e ι₀ π₀ h₀
  let transportIso :
      ShortComplex.mk ι₀ π₀ h₀ ≅
        ShortComplex.mk (ι₀ ≫ e.inv) (e.hom ≫ π₀) transportedZero :=
    derivedSectionsOverOpenMiddleTransportIso (X := X) (U := U) e ι₀ π₀ h₀
  refine ⟨ι₀ ≫ e.inv, e.hom ≫ π₀, transportedZero, ?_⟩
  -- Route correction: move the middle-term conjugation into the helper `transportIso` so the
  -- final theorem only transports short exactness once.
  -- The Chapter 15 Milnor short exact sequence already has the required left and right terms.
  exact ShortComplex.shortExact_of_iso transportIso hShort₀

end

end AlgebraicGeometry.RingedSpace
