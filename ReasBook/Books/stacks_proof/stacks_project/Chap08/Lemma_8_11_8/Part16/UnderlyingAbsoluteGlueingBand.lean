import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part16.GerbeBandComparisonData

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Helper for Chap08 Lemma 8 11 8/Part16: an isomorphism of absolute-glueing data has
componentwise inverse laws on each localized sheaf. -/
theorem absoluteGlueingIsoApp_hom_inv_id
    {F G : GrothendieckTopology.AbsoluteGlueing J} (η : F ≅ G) (U : C) :
    η.hom.app U ≫ η.inv.app U = 𝟙 (F.obj U) := by
  -- Evaluate the inverse law of the absolute-glueing isomorphism at the chosen base object.
  calc
    η.hom.app U ≫ η.inv.app U =
        ((η.hom ≫ η.inv : F ⟶ F) :
          GrothendieckTopology.AbsoluteGlueing.Hom J F F).app U := rfl
    _ = ((𝟙 F : F ⟶ F) :
          GrothendieckTopology.AbsoluteGlueing.Hom J F F).app U := by
        exact
          congrArg
            (fun α : F ⟶ F ↦
              (α : GrothendieckTopology.AbsoluteGlueing.Hom J F F).app U)
            η.hom_inv_id
    _ = 𝟙 (F.obj U) := rfl

/-- Helper for Chap08 Lemma 8 11 8/Part16: an isomorphism of absolute-glueing data has the
reverse componentwise inverse law on each localized sheaf. -/
theorem absoluteGlueingIsoApp_inv_hom_id
    {F G : GrothendieckTopology.AbsoluteGlueing J} (η : F ≅ G) (U : C) :
    η.inv.app U ≫ η.hom.app U = 𝟙 (G.obj U) := by
  -- Evaluate the reverse inverse law of the absolute-glueing isomorphism at the same component.
  calc
    η.inv.app U ≫ η.hom.app U =
        ((η.inv ≫ η.hom : G ⟶ G) :
          GrothendieckTopology.AbsoluteGlueing.Hom J G G).app U := rfl
    _ = ((𝟙 G : G ⟶ G) :
          GrothendieckTopology.AbsoluteGlueing.Hom J G G).app U := by
        exact
          congrArg
            (fun α : G ⟶ G ↦
              (α : GrothendieckTopology.AbsoluteGlueing.Hom J G G).app U)
            η.inv_hom_id
    _ = 𝟙 (G.obj U) := rfl

/-- Helper for Chap08 Lemma 8 11 8/Part16: an isomorphism of absolute-glueing data induces an
isomorphism on each localized sheaf. -/
noncomputable def absoluteGlueingIsoApp
    {F G : GrothendieckTopology.AbsoluteGlueing J} (η : F ≅ G) (U : C) :
    F.obj U ≅ G.obj U where
  hom := η.hom.app U
  inv := η.inv.app U
  hom_inv_id := absoluteGlueingIsoApp_hom_inv_id (J := J) η U
  inv_hom_id := absoluteGlueingIsoApp_inv_hom_id (J := J) η U

/-- Helper for Chap08 Lemma 8 11 8/Part16: the Chapter 7 absolute-glueing equivalence
reconstructs a global `Type`-valued sheaf from an absolute-glueing datum. -/
noncomputable def absoluteGlueingReconstruction
    (F : GrothendieckTopology.AbsoluteGlueing J) :
    Sheaf J (Type (max u v)) :=
  ((GrothendieckTopology.sheafToAbsoluteGlueingFunctor (J := J)).asEquivalence).inverse.obj F

/-- Helper for Chap08 Lemma 8 11 8/Part16: the reconstructed sheaf restricts back to the
localized sheaf stored in the absolute-glueing datum. -/
noncomputable def absoluteGlueingReconstructionOverIso
    (F : GrothendieckTopology.AbsoluteGlueing J) (U : C) :
    (absoluteGlueingReconstruction (J := J) F).over U ≅ F.obj U :=
  let E : Sheaf J (Type (max u v)) ≌ GrothendieckTopology.AbsoluteGlueing J :=
    (GrothendieckTopology.sheafToAbsoluteGlueingFunctor (J := J)).asEquivalence
  absoluteGlueingIsoApp (J := J) (η := E.counitIso.app F) U

/-- Helper for Chap08 Lemma 8 11 8/Part16: absolute-glueing comparison data reconstructs a
global `Type`-valued sheaf with the same local automorphism-sheaf comparisons. -/
theorem underlyingBandDataOfAbsoluteGlueing
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibility : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparison y) :
    ∃ R : Sheaf J (Type (max u v)),
      ∃ comparisonR : ∀ {U : C} (x : 𝒮.p.Fiber U),
        R.over U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparisonR x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparisonR y := by
  -- Reconstruct the global sheaf by the public Chapter 7 equivalence, then prepend the counit
  -- comparison to every local automorphism-sheaf comparison.
  refine ⟨absoluteGlueingReconstruction (J := J) F, ?_⟩
  refine ⟨fun {U} x ↦ absoluteGlueingReconstructionOverIso (J := J) F U ≪≫ comparison x, ?_⟩
  intro U x y φ
  -- The conjugation law is unchanged after precomposing with the reconstruction-over isomorphism.
  simpa using
    congrArg
      (fun i ↦ absoluteGlueingReconstructionOverIso (J := J) F U ≪≫ i)
      (compatibility (U := U) (x := x) (y := y) φ)

/-- Helper for Chap08 Lemma 8 11 8/Part16: the source-facing absolute-glueing datum whose
localized sheaves are the underlying automorphism sheaves with conjugation-compatible
comparisons. -/
abbrev underlyingAbsoluteGlueingBandData
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) : Prop :=
  ∃ F : GrothendieckTopology.AbsoluteGlueing J,
    ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
      ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
        comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
          comparison y

/-- Helper for Chap08 Lemma 8 11 8/Part16: a source absolute-glueing package reconstructs the
global `Type`-valued comparison datum needed before adding the abelian-group structure. -/
theorem underlyingBandDataOfSource
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (hsource : underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian) :
    ∃ R : Sheaf J (Type (max u v)),
      ∃ comparisonR : ∀ {U : C} (x : 𝒮.p.Fiber U),
        R.over U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparisonR x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparisonR y := by
  -- The source datum already contains the absolute-glueing object and its local comparisons;
  -- reconstruct the global sheaf through the Chapter 7 absolute-glueing equivalence.
  obtain ⟨F, comparisonF, compatibilityF⟩ := hsource
  exact underlyingBandDataOfAbsoluteGlueing (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF

/-- Helper for Chap08 Lemma 8 11 8/Part16: any global `Type`-valued automorphism band can be
lifted to a global `AddCommGrpCat`-valued band with the same conjugation compatibility. -/
abbrev addCommBandLiftFromUnderlyingData
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) : Prop :=
  ∀ (R : Sheaf J (Type (max u v)))
    (comparisonR : ∀ {U : C} (x : 𝒮.p.Fiber U),
      R.over U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x),
    (∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonR x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonR y) →
      ∃ G : Sheaf J AddCommGrpCat.{max u v},
        ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
          G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
          ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
            comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
              comparison y

/-- Helper for Chap08 Lemma 8 11 8/Part16: source absolute-glueing data plus the conditional
AddComm lift prove the reconstructed additive comparison package. -/
theorem existsReconstructedAddCommBandComparisonDataOfSourceAndLift
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (hsource : underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian)
    (hlift : addCommBandLiftFromUnderlyingData (𝒮 := 𝒮) hAbelian) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v},
      ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison y := by
  -- Reconstruct the global Type-valued band from the source absolute-glueing datum.
  obtain ⟨R, comparisonR, compatibilityR⟩ :=
    underlyingBandDataOfSource (𝒮 := 𝒮) hAbelian hsource
  -- Apply the isolated additive lift to the reconstructed Type-valued band.
  exact hlift R comparisonR compatibilityR

/-- Helper for Chap08 Lemma 8 11 8/Part16: a source absolute-glueing datum and an additive lift
for every reconstructed `Type`-valued band already imply the final gerbe-band existential. -/
theorem existsGerbeBandOfSourceAndLift
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (hsource : underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian)
    (hlift : addCommBandLiftFromUnderlyingData (𝒮 := 𝒮) hAbelian) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v}, IsGerbeBand hAbelian G := by
  -- First use the source datum and additive lift to obtain the explicit comparison-data package.
  have hcomparison :
      ∃ G : Sheaf J AddCommGrpCat.{max u v},
        ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
          G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
          ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
            comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
              comparison y :=
    existsReconstructedAddCommBandComparisonDataOfSourceAndLift
      (𝒮 := 𝒮) hAbelian hsource hlift
  -- The predicate-level packaging lemma converts the comparison data to the stated band.
  exact exists_gerbe_band_of_reconstructed_comparison_data (𝒮 := 𝒮) hAbelian hcomparison

/-- Helper for Chap08 Lemma 8 11 8/Part16: a fixed absolute-glueing source datum closes the
specialized additive comparison package as soon as the reconstructed Type-valued band has an
AddComm lift. -/
theorem existsAddCommBandComparisonDataOfAbsoluteGlueingOfLift
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hlift : addCommBandLiftFromUnderlyingData (𝒮 := 𝒮) hAbelian) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v},
      ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison y := by
  -- First reconstruct the global Type-valued band from the fixed absolute-glueing datum.
  obtain ⟨R, comparisonR, compatibilityR⟩ :=
    underlyingBandDataOfAbsoluteGlueing (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF
  -- The remaining additive input is now exactly the isolated lift predicate for that band.
  exact hlift R comparisonR compatibilityR

end CategoryTheory
