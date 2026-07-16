import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_14_10
import StacksProject_2024.stacks_project.Chap13.Lemma_13_11_5
import StacksProject_2024.stacks_project.Chap13.Situation_13_15_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open HomologicalComplex
open CochainComplex
open ComplexShape
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/- 
Domain-style sampling for Lemma 13.15.2:
- primary domain: comparison of pointwise derived-functor computation between the unbounded
  homotopy localization `K(\mathcal A) ⟶ D(\mathcal B)` and its bounded-below / bounded-above
  full-subcategory views;
- sampled owner declarations:
  `LocalizerMorphism.ofEq`,
  `LocalizerMorphism.hasPointwiseRightDerivedFunctorAt_iff_of_isRightDerivabilityStructure`,
  `LocalizerMorphism.isIso_iff_of_isRightDerivabilityStructure`,
  `Functor.ComputesRightDerivedAt`,
  `Functor.ComputesLeftDerivedAt`;
- best owner abstraction: the bounded inclusions are not second derived-functor owners; they are
  bridge/view localizer morphisms from `Qis⁺(𝒜)` and `Qis⁻(𝒜)` to the ambient quasi-isomorphism
  class `HomotopyCategory.quasiIso 𝒜 (up ℤ)`, and the six statements below are their
  source-facing consequences for pointwise derived functors;
- primitive data: the canonical functors from `Situation_13_15_1`, together with the bounded
  quasi-isomorphism owners `Qis⁺(𝒜)` and `Qis⁻(𝒜)` from `Lemma_13_11_6`;
- derived API: the equivalence of pointwise derived-definedness, the comparison of pointwise
  derived values, and the corresponding `ComputesRightDerivedAt` / `ComputesLeftDerivedAt`
  equivalences.

Source/core/bridge triage:
- `source-facing`: the six bounded-vs-unbounded comparison statements of Lemma `13.15.2`;
- `core/canonical`: the mathlib `LocalizerMorphism` derivability-structure comparison API and the
  Chapter `13` owners `Functor.ComputesRightDerivedAt` / `Functor.ComputesLeftDerivedAt`;
- `bridge/view`: the bounded inclusions `K⁺(𝒜) ⥤ K(\mathcal A)` and `K⁻(𝒜) ⥤ K(\mathcal A)`,
  which induce the comparison between the bounded and unbounded derived setups.
-/

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F
local notation "KplusToDplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow F
local notation "KminusToDminus" => mapBoundedAboveHomotopyCategoryToDerivedAbove F

/-- Helper for Lemma 13.15.2: the canonical inclusion `D^+(\mathcal B) ↪ D(\mathcal B)` reflects
isomorphisms because it is fully faithful. -/
lemma bounded_below_derived_inclusion_reflects_isomorphisms :
    (ObjectProperty.ι
      (DerivedCategory.TStructure.t.plus : ObjectProperty (D(ℬ)))).ReflectsIsomorphisms := by
  -- Proof comment: `ObjectProperty.ι` is fully faithful for any object property, so the bounded
  -- derived inclusion reflects isomorphisms formally.
  exact Functor.FullyFaithful.reflectsIsomorphisms
    (DerivedCategory.TStructure.t.plus : ObjectProperty (D(ℬ))).fullyFaithfulι

/-- Helper for Lemma 13.15.2: the canonical inclusion `D^-(\mathcal B) ↪ D(\mathcal B)` reflects
isomorphisms because it is fully faithful. -/
lemma bounded_above_derived_inclusion_reflects_isomorphisms :
    (ObjectProperty.ι
      (DerivedCategory.TStructure.t.minus : ObjectProperty (D(ℬ)))).ReflectsIsomorphisms := by
  -- Proof comment: this is the bounded-above analogue of the previous fully faithful reflection
  -- fact.
  exact Functor.FullyFaithful.reflectsIsomorphisms
    (DerivedCategory.TStructure.t.minus : ObjectProperty (D(ℬ))).fullyFaithfulι

-- Proof comment: this is the bounded-above analogue of the existing bounded-below comparison from
-- `Situation_13_15_1`.
/-- Helper for Lemma 13.15.2: the bounded-above derived functor agrees with the ambient derived
functor after composing with the canonical inclusions `K^-(\mathcal A) ↪ K(\mathcal A)` and
`D^-(\mathcal B) ↪ D(\mathcal B)`. -/
noncomputable abbrev mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso :
    mapBoundedAboveHomotopyCategoryToDerivedAbove F ⋙
      ObjectProperty.ι (DerivedCategory.TStructure.t.minus : ObjectProperty (D(ℬ))) ≅
    ObjectProperty.ι (HomotopyCategory.minus 𝒜) ⋙ mapHomotopyCategoryToDerived F :=
  (Functor.associator
      (mapBoundedAboveHomotopyCategory F)
      mapBoundedAboveHomotopyToDerivedAbove
      (ObjectProperty.ι (DerivedCategory.TStructure.t.minus : ObjectProperty (D(ℬ))))).symm ≪≫
    Functor.isoWhiskerLeft
      (mapBoundedAboveHomotopyCategory F)
      (ObjectProperty.liftCompιIso
        (DerivedCategory.TStructure.t.minus : ObjectProperty (D(ℬ)))
        (ObjectProperty.ι (HomotopyCategory.minus ℬ) ⋙ DerivedCategory.Qh)
        (qh_obj_mem_t_minus (𝒜 := ℬ))) ≪≫
    Functor.associator
      (mapBoundedAboveHomotopyCategory F)
      (ObjectProperty.ι (HomotopyCategory.minus ℬ))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerRight
      ((HomotopyCategory.minus ℬ).liftCompιIso
        ((HomotopyCategory.minus 𝒜).ι ⋙ F.mapHomotopyCategory (up ℤ))
        (mapHomotopyCategory_obj_mem_boundedAbove F))
      DerivedCategory.Qh

/-- Helper for Lemma 13.15.2: any quasi-isomorphism out of a bounded-below object of
`K(\mathcal A)` can be refined by a quasi-isomorphism whose target is still bounded below. -/
lemma exists_quasiIso_to_bounded_below_target
    (X : K⁺(𝒜)) {Y : K(𝒜)} (s : X.obj ⟶ Y) (hs : Qis s) :
    ∃ (Y' : K⁺(𝒜)) (t : Y ⟶ Y'.obj), Qis t := by
  -- Proof comment: use the lower support bound on `X` to force eventual vanishing of the
  -- homology of `Y`, then apply the truncation replacement of Lemma `13.11.5`.
  rw [HomotopyCategory.mem_quasiIso_iff] at hs
  obtain ⟨a, hXge⟩ :=
    (CochainComplex.plus_iff 𝒜 X.obj.as).1
      ((HomotopyCategory.plus_iff (𝒜 := 𝒜) X.obj).1 X.property)
  have hYeventual : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (Y.as.homology n) := by
    refine ⟨a, ?_⟩
    intro n hn
    let KX : CochainComplex 𝒜 ℤ := X.obj.as
    let _ : KX.IsStrictlyGE a := by
      simpa [KX] using hXge
    let _ : KX.HasHomology n := inferInstance
    have hXhomology : IsZero (KX.homology n) :=
      CochainComplex.isZero_of_isGE (K := KX) a n hn
    have hXhomotopy :
        IsZero (((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).obj X.obj)) := by
      simpa [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
        HomotopyCategory.quotient_obj_as] using
        (((HomotopyCategory.homologyFunctorFactors 𝒜 (up ℤ) n).app KX).isZero_iff).2
          hXhomology
    have hYhomotopy :
        IsZero (((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).obj Y)) := by
      exact IsZero.of_iso hXhomotopy
        ((asIso ((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).map s)).symm)
    let KY : CochainComplex 𝒜 ℤ := Y.as
    simpa [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
      HomotopyCategory.quotient_obj_as, KY] using
      (((HomotopyCategory.homologyFunctorFactors 𝒜 (up ℤ) n).app KY).isZero_iff).1
        hYhomotopy
  obtain ⟨a, hπ, htrunc⟩ :=
    exists_quasiIso_to_truncGE_of_eventually_isZero_homology (K := Y.as) hYeventual
  let Y' : K⁺(𝒜) :=
    ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj (CochainComplex.truncGE (K := Y.as) a), by
      -- Proof comment: the truncation bound gives the bounded-below structure on the refined
      -- target.
      rw [HomotopyCategory.plus_iff]
      exact (CochainComplex.plus_iff 𝒜 _).2 ⟨a, htrunc⟩⟩
  refine ⟨Y', ?_, ?_⟩
  · -- Proof comment: pass the truncation map to the homotopy category and then into `K⁺(𝒜)`.
    simpa [Y'] using
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map (CochainComplex.πTruncGE (K := Y.as) a)
  · -- Proof comment: the truncation map is a quasi-isomorphism by construction.
    simpa [Y'] using
      (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
          ((HomotopyCategory.quotient 𝒜 (up ℤ)).map
            (CochainComplex.πTruncGE (K := Y.as) a)) by
        rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
        exact hπ)

/-- Helper for Lemma 13.15.2: any quasi-isomorphism into a bounded-above object of
`K(\mathcal A)` can be refined by a quasi-isomorphism whose source is still bounded above. -/
lemma exists_quasiIso_from_bounded_above_source
    (X : K⁻(𝒜)) {Y : K(𝒜)} (s : Y ⟶ X.obj) (hs : Qis s) :
    ∃ (Y' : K⁻(𝒜)) (t : Y'.obj ⟶ Y), Qis t := by
  -- Proof comment: this is the dual truncation argument using the upper support bound on `X`.
  rw [HomotopyCategory.mem_quasiIso_iff] at hs
  obtain ⟨b, hXle⟩ :=
    (CochainComplex.minus_iff 𝒜 X.obj.as).1
      ((HomotopyCategory.minus_iff (𝒜 := 𝒜) X.obj).1 X.property)
  have hYeventual : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (Y.as.homology n) := by
    refine ⟨b, ?_⟩
    intro n hn
    let KX : CochainComplex 𝒜 ℤ := X.obj.as
    let _ : KX.IsStrictlyLE b := by
      simpa [KX] using hXle
    let _ : KX.HasHomology n := inferInstance
    have hXhomology : IsZero (KX.homology n) :=
      CochainComplex.isZero_of_isLE (K := KX) b n hn
    have hXhomotopy :
        IsZero (((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).obj X.obj)) := by
      simpa [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
        HomotopyCategory.quotient_obj_as] using
        (((HomotopyCategory.homologyFunctorFactors 𝒜 (up ℤ) n).app KX).isZero_iff).2
          hXhomology
    have hYhomotopy :
        IsZero (((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).obj Y)) := by
      exact IsZero.of_iso hXhomotopy
        (asIso (((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).map s)))
    let KY : CochainComplex 𝒜 ℤ := Y.as
    simpa [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
      HomotopyCategory.quotient_obj_as, KY] using
      (((HomotopyCategory.homologyFunctorFactors 𝒜 (up ℤ) n).app KY).isZero_iff).1
        hYhomotopy
  obtain ⟨b, hι, htrunc⟩ :=
    exists_quasiIso_from_truncLE_of_eventually_isZero_homology (K := Y.as) hYeventual
  let Y' : K⁻(𝒜) :=
    ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj (CochainComplex.truncLE (K := Y.as) b), by
      -- Proof comment: the truncation bound gives the bounded-above structure on the refined
      -- source.
      rw [HomotopyCategory.minus_iff]
      exact (CochainComplex.minus_iff 𝒜 _).2 ⟨b, htrunc⟩⟩
  refine ⟨Y', ?_, ?_⟩
  · -- Proof comment: pass the truncation inclusion to the homotopy category and then into
    -- `K⁻(𝒜)`.
    simpa [Y'] using
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map (CochainComplex.ιTruncLE (K := Y.as) b)
  · -- Proof comment: the truncation inclusion is a quasi-isomorphism by construction.
    simpa [Y'] using
      (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
          ((HomotopyCategory.quotient 𝒜 (up ℤ)).map
            (CochainComplex.ιTruncLE (K := Y.as) b)) by
        rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
        exact hι)

/-- Helper for Lemma 13.15.2: once the ambient and bounded-below right-derived values at `X`
are identified by an isomorphism which matches the canonical identity legs, the
`ComputesRightDerivedAt` predicate transports between the two settings. -/
lemma computes_right_derived_at_iff_of_value_iso
    (X : K⁺(𝒜))
    [HasPointwiseRightDerivedFunctorAt KtoD Qis X.obj]
    [HasPointwiseRightDerivedFunctorAt KplusToDplus (Qis⁺(𝒜)) X]
    (e : rightDerivedValue Qis KtoD X.obj ≅
      (rightDerivedValue (Qis⁺(𝒜)) KplusToDplus X).obj)
    (hleg :
      rightDerivedValueLeg Qis KtoD (𝟙 X.obj) (MorphismProperty.id_mem Qis X.obj) ≫ e.hom =
        ((mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso (F := F)).app X).inv ≫
          (ObjectProperty.ι
            (DerivedCategory.TStructure.t.plus : ObjectProperty (D(ℬ)))).map
            (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁺(𝒜)) X))) :
    ComputesRightDerivedAt KtoD Qis X.obj ↔
      ComputesRightDerivedAt KplusToDplus (Qis⁺(𝒜)) X := by
  let plusι : D⁺(ℬ) ⥤ D(ℬ) :=
    ObjectProperty.ι (DerivedCategory.TStructure.t.plus : ObjectProperty (D(ℬ)))
  constructor
  · intro h
    letI : ComputesRightDerivedAt KtoD Qis X.obj := h
    have hcomp :
        IsIso
          (((mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso (F := F)).app X).inv ≫
            plusι.map
              (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
                (MorphismProperty.id_mem (Qis⁺(𝒜)) X))) := by
      -- Proof comment: rewrite the bounded-below comparison to the ambient identity leg and use
      -- that the ambient computing hypothesis already makes that leg invertible.
      have hambient :
          IsIso
            (rightDerivedValueLeg Qis KtoD (𝟙 X.obj)
              (MorphismProperty.id_mem Qis X.obj) ≫ e.hom) := by
        exact
          (isIso_comp_right_iff
            (rightDerivedValueLeg Qis KtoD (𝟙 X.obj)
              (MorphismProperty.id_mem Qis X.obj))
            e.hom).2 inferInstance
      rw [← hleg]
      exact hambient
    have hplus :
        IsIso
          (plusι.map
            (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁺(𝒜)) X))) := by
      -- Proof comment: cancel the comparison isomorphism coming from
      -- `mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso`.
      exact
        (isIso_comp_left_iff
          (((mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso (F := F)).app X).inv)
          (plusι.map
            (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁺(𝒜)) X)))).1 hcomp
    have hbounded :
        IsIso
          (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
            (MorphismProperty.id_mem (Qis⁺(𝒜)) X)) := by
      -- Proof comment: the fully faithful inclusion `D⁺(ℬ) ↪ D(ℬ)` reflects invertibility of the
      -- bounded-below identity leg.
      letI : plusι.ReflectsIsomorphisms :=
        bounded_below_derived_inclusion_reflects_isomorphisms (ℬ := ℬ)
      exact
        Functor.ReflectsIsomorphisms.reflects plusι
          (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
            (MorphismProperty.id_mem (Qis⁺(𝒜)) X))
    exact ⟨hbounded⟩
  · intro h
    letI : ComputesRightDerivedAt KplusToDplus (Qis⁺(𝒜)) X := h
    have hplus :
        IsIso
          (plusι.map
            (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁺(𝒜)) X))) := by
      -- Proof comment: the bounded-below computing hypothesis gives invertibility before
      -- applying the fully faithful inclusion, so the image is invertible as well.
      infer_instance
    have hcomp :
        IsIso
          (((mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso (F := F)).app X).inv ≫
            plusι.map
              (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
                (MorphismProperty.id_mem (Qis⁺(𝒜)) X))) := by
      -- Proof comment: prepend the canonical comparison isomorphism from the bounded-below
      -- derived value to the ambient one.
      exact
        (isIso_comp_left_iff
          (((mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso (F := F)).app X).inv)
          (plusι.map
            (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁺(𝒜)) X)))).2 hplus
    have hambient :
        IsIso
          (rightDerivedValueLeg Qis KtoD (𝟙 X.obj)
            (MorphismProperty.id_mem Qis X.obj) ≫ e.hom) := by
      -- Proof comment: convert back to the ambient identity leg using the assumed comparison
      -- formula for `e`.
      rw [hleg]
      exact hcomp
    exact
      ⟨(isIso_comp_right_iff
          (rightDerivedValueLeg Qis KtoD (𝟙 X.obj)
            (MorphismProperty.id_mem Qis X.obj))
          e.hom).1 hambient⟩

/-- Helper for Lemma 13.15.2: once the ambient and bounded-above left-derived values at `X`
are identified by an isomorphism which matches the canonical identity projections, the
`ComputesLeftDerivedAt` predicate transports between the two settings. -/
lemma computes_left_derived_at_iff_of_value_iso
    (X : K⁻(𝒜))
    [HasPointwiseLeftDerivedFunctorAt KtoD Qis X.obj]
    [HasPointwiseLeftDerivedFunctorAt KminusToDminus (Qis⁻(𝒜)) X]
    (e : leftDerivedValue Qis KtoD X.obj ≅
      (leftDerivedValue (Qis⁻(𝒜)) KminusToDminus X).obj)
    (hprojection :
      e.hom ≫
          ((ObjectProperty.ι
            (DerivedCategory.TStructure.t.minus : ObjectProperty (D(ℬ)))).map
            (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁻(𝒜)) X))) ≫
          ((mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso (F := F)).app X).hom =
        leftDerivedValueProjection Qis KtoD (𝟙 X.obj) (MorphismProperty.id_mem Qis X.obj)) :
    ComputesLeftDerivedAt KtoD Qis X.obj ↔
      ComputesLeftDerivedAt KminusToDminus (Qis⁻(𝒜)) X := by
  let minusι : D⁻(ℬ) ⥤ D(ℬ) :=
    ObjectProperty.ι (DerivedCategory.TStructure.t.minus : ObjectProperty (D(ℬ)))
  constructor
  · intro h
    letI : ComputesLeftDerivedAt KtoD Qis X.obj := h
    have hcomp :
        IsIso
          (e.hom ≫
            minusι.map
              (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
                (MorphismProperty.id_mem (Qis⁻(𝒜)) X)) ≫
            ((mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso (F := F)).app X).hom) := by
      -- Proof comment: rewrite the bounded-above comparison to the ambient identity projection
      -- and use the ambient computing hypothesis.
      have hambient :
          IsIso
            (leftDerivedValueProjection Qis KtoD (𝟙 X.obj)
              (MorphismProperty.id_mem Qis X.obj)) := by
        infer_instance
      rw [hprojection]
      exact hambient
    have hmid :
        IsIso
          (e.hom ≫
            minusι.map
              (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
                (MorphismProperty.id_mem (Qis⁻(𝒜)) X))) := by
      -- Proof comment: cancel the rightmost comparison isomorphism
      -- `mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso.app X`.
      exact
        (isIso_comp_right_iff
          (e.hom ≫
            minusι.map
              (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
                (MorphismProperty.id_mem (Qis⁻(𝒜)) X)))
          ((mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso (F := F)).app X).hom).1
          (by simpa [Category.assoc] using hcomp)
    have hminus :
        IsIso
          (minusι.map
            (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁻(𝒜)) X))) := by
      -- Proof comment: cancel the value comparison isomorphism `e`.
      exact
        (isIso_comp_left_iff
          e.hom
          (minusι.map
            (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁻(𝒜)) X)))).1 hmid
    have hbounded :
        IsIso
          (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
            (MorphismProperty.id_mem (Qis⁻(𝒜)) X)) := by
      -- Proof comment: the fully faithful inclusion `D⁻(ℬ) ↪ D(ℬ)` reflects invertibility of the
      -- bounded-above identity projection.
      letI : minusι.ReflectsIsomorphisms :=
        bounded_above_derived_inclusion_reflects_isomorphisms (ℬ := ℬ)
      exact
        Functor.ReflectsIsomorphisms.reflects minusι
          (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
            (MorphismProperty.id_mem (Qis⁻(𝒜)) X))
    exact ⟨hbounded⟩
  · intro h
    letI : ComputesLeftDerivedAt KminusToDminus (Qis⁻(𝒜)) X := h
    have hminus :
        IsIso
          (minusι.map
            (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁻(𝒜)) X))) := by
      -- Proof comment: the bounded-above computing hypothesis gives invertibility before
      -- applying the inclusion, so its image is invertible as well.
      infer_instance
    have hmid :
        IsIso
          (e.hom ≫
            minusι.map
              (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
                (MorphismProperty.id_mem (Qis⁻(𝒜)) X))) := by
      -- Proof comment: prepend the comparison isomorphism between the ambient and bounded-above
      -- left-derived values.
      exact
        (isIso_comp_left_iff
          e.hom
          (minusι.map
            (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁻(𝒜)) X)))).2 hminus
    have hcomp :
        IsIso
          (e.hom ≫
            minusι.map
              (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
                (MorphismProperty.id_mem (Qis⁻(𝒜)) X)) ≫
            ((mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso (F := F)).app X).hom) := by
      -- Proof comment: append the canonical bounded-above comparison isomorphism landing in the
      -- ambient derived category.
      simpa [Category.assoc] using
        (isIso_comp_right_iff
          (e.hom ≫
            minusι.map
              (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
                (MorphismProperty.id_mem (Qis⁻(𝒜)) X)))
          ((mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso (F := F)).app X).hom).2
          hmid
    have hambient :
        IsIso
          (leftDerivedValueProjection Qis KtoD (𝟙 X.obj)
            (MorphismProperty.id_mem Qis X.obj)) := by
      -- Proof comment: rewrite the composite back to the ambient identity projection.
      rw [← hprojection]
      simpa [Category.assoc] using hcomp
    exact ⟨hambient⟩

-- Proof sketch: by Lemma 13.11.5, every quasi-isomorphism out of the bounded-below object `X`
-- can be refined to one whose target is still bounded below. This is exactly the
-- `LocalizerMorphism.ofEq rfl` bridge from `Qis⁺(𝒜)` to `Qis`, together with the canonical
-- right-derivability-structure comparison API, so the pointwise right-derived existence condition
-- is unchanged.
/-- Lemma 13.15.2 (1): for a bounded-below object `X` of `K^+(\mathcal A)`, the right derived
functor of `K(\mathcal A) ⥤ D(\mathcal B)` is defined at the underlying object of `X` if and only
if the right derived functor of `K^+(\mathcal A) ⥤ D^+(\mathcal B)` is defined at `X`. -/
theorem right_derived_defined_at_iff_bounded_below
    (X : K⁺(𝒜)) :
    HasPointwiseRightDerivedFunctorAt KtoD Qis X.obj ↔
      HasPointwiseRightDerivedFunctorAt KplusToDplus (Qis⁺(𝒜)) X := by
  -- TODO: package `exists_quasiIso_to_bounded_below_target` into finality of the bounded-below
  -- denominator functor and compare the two colimit diagrams via
  -- `mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso`.
  sorry

-- Proof sketch: once both pointwise right-derived values exist, the localizer-morphism bridge
-- `LocalizerMorphism.ofEq rfl` for `Qis⁺(𝒜) ⟶ Qis` and the canonical derivability-structure
-- comparison supply the comparison morphism; its invertibility is exactly the pointwise
-- comparison encoded by `LocalizerMorphism.rightDerivedFunctorComparison`. The bounded-below
-- value is viewed in `D(\mathcal B)` through the canonical full-subcategory inclusion
-- `D^+(\mathcal B) ↪ D(\mathcal B)`.
/-- Lemma 13.15.2 (2): when the right-derived values at a bounded-below object `X` are defined in
both settings, there is a canonical comparison isomorphism from the value computed in
`D(\mathcal B)` to the underlying object of the value computed in `D^+(\mathcal B)`. -/
noncomputable def right_derived_value_comparison_iso_bounded_below
    (X : K⁺(𝒜))
    [HasPointwiseRightDerivedFunctorAt KtoD Qis X.obj]
    [HasPointwiseRightDerivedFunctorAt KplusToDplus (Qis⁺(𝒜)) X] :
    rightDerivedValue Qis KtoD X.obj ≅
      (rightDerivedValue (Qis⁺(𝒜)) KplusToDplus X).obj := by
  -- TODO: once the bounded-below finality comparison is packaged, take the induced colimit
  -- comparison isomorphism and compose it with
  -- `mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso.app X`.
  sorry

-- Proof sketch: combine the equivalence of pointwise right-derived existence with the canonical
-- `isIso_iff_of_isRightDerivabilityStructure` comparison for the identity legs.
/-- Lemma 13.15.2 (3): a bounded-below object `X` computes the right derived functor of
`K(\mathcal A) ⥤ D(\mathcal B)` if and only if it computes the right derived functor of
`K^+(\mathcal A) ⥤ D^+(\mathcal B)`. -/
theorem computes_right_derived_functor_at_iff_bounded_below
    (X : K⁺(𝒜)) :
    ComputesRightDerivedAt KtoD Qis X.obj ↔
      ComputesRightDerivedAt KplusToDplus (Qis⁺(𝒜)) X := by
  -- Route correction: once the value comparison iso and the identity-leg compatibility are in
  -- place, the remaining transport is the formal `IsIso` argument packaged in
  -- `computes_right_derived_at_iff_of_value_iso`.
  sorry

-- Proof sketch: this is the dual argument to part (1). Lemma 13.11.5 furnishes bounded-above
-- refinements of quasi-isomorphisms into `X`; equivalently, `LocalizerMorphism.ofEq rfl` from
-- `Qis⁻(𝒜)` to `Qis` is the left-derivability-structure bridge, so pointwise left-derived
-- existence is unchanged.
/-- Lemma 13.15.2 (4): for a bounded-above object `X` of `K^-(\mathcal A)`, the left derived
functor of `K(\mathcal A) ⥤ D(\mathcal B)` is defined at the underlying object of `X` if and only
if the left derived functor of `K^-(\mathcal A) ⥤ D^-(\mathcal B)` is defined at `X`. -/
theorem left_derived_defined_at_iff_bounded_above
    (X : K⁻(𝒜)) :
    HasPointwiseLeftDerivedFunctorAt KtoD Qis X.obj ↔
      HasPointwiseLeftDerivedFunctorAt KminusToDminus (Qis⁻(𝒜)) X := by
  -- TODO: package `exists_quasiIso_from_bounded_above_source` into initiality of the
  -- bounded-above numerator functor and compare the two limit diagrams.
  sorry

-- Proof sketch: after both pointwise left-derived values are defined, the localizer-morphism
-- bridge `LocalizerMorphism.ofEq rfl` for `Qis⁻(𝒜) ⟶ Qis` identifies the bounded-above and
-- unbounded structured-arrow diagrams, and the resulting canonical comparison morphism is the one
-- whose invertibility is tracked by the left-derived derivability-structure API. The
-- bounded-above value is viewed in `D(\mathcal B)` through the canonical full-subcategory
-- inclusion `D^-(\mathcal B) ↪ D(\mathcal B)`.
/-- Lemma 13.15.2 (5): when the left-derived values at a bounded-above object `X` are defined in
both settings, there is a canonical comparison isomorphism from the value computed in
`D(\mathcal B)` to the underlying object of the value computed in `D^-(\mathcal B)`. -/
noncomputable def left_derived_value_comparison_iso_bounded_above
    (X : K⁻(𝒜))
    [HasPointwiseLeftDerivedFunctorAt KtoD Qis X.obj]
    [HasPointwiseLeftDerivedFunctorAt KminusToDminus (Qis⁻(𝒜)) X] :
    leftDerivedValue Qis KtoD X.obj ≅
      (leftDerivedValue (Qis⁻(𝒜)) KminusToDminus X).obj := by
  -- TODO: once the bounded-above initiality comparison is packaged, take the induced limit
  -- comparison isomorphism and compose it with the canonical inclusion `D⁻(ℬ) ↪ D(ℬ)`.
  sorry

-- Proof sketch: combine the equivalence of pointwise left-derived existence with the comparison
-- of the canonical pointwise counit morphisms under the derived-structure bridge.
/-- Lemma 13.15.2 (6): a bounded-above object `X` computes the left derived functor of
`K(\mathcal A) ⥤ D(\mathcal B)` if and only if it computes the left derived functor of
`K^-(\mathcal A) ⥤ D^-(\mathcal B)`. -/
theorem computes_left_derived_functor_at_iff_bounded_above
    (X : K⁻(𝒜)) :
    ComputesLeftDerivedAt KtoD Qis X.obj ↔
      ComputesLeftDerivedAt KminusToDminus (Qis⁻(𝒜)) X := by
  -- Route correction: once the value comparison iso and the identity-projection compatibility are
  -- in place, the remaining transport is the formal `IsIso` argument packaged in
  -- `computes_left_derived_at_iff_of_value_iso`.
  sorry

end

end CategoryTheory
