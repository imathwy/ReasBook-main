import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part16.FixedAbsoluteGlueingAddCommData
import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part15

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Helper for Chap08 Lemma 8 11 8/Part16: an externally constructed absolute-glueing package
with the automorphism-sheaf comparisons is exactly the source datum consumed by this part. -/
theorem sourceUnderlyingAbsoluteGlueingBandDataOfPackage
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (data :
      ∃ F : GrothendieckTopology.AbsoluteGlueing J,
        ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
            F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
          ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
            comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
              comparison y) :
    underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian := by
  -- The Part16 source predicate is this package; the adapter fixes the owner interface for the
  -- missing chosen-cover construction without unfolding it at each call site.
  exact data

/-- Helper for Chap08 Lemma 8 11 8/Part16: the source absolute-glueing datum supplied by the
earlier chosen-cover construction, isolated from the broken Part04-to-Part15 aggregate import. -/
theorem sourceUnderlyingAbsoluteGlueingBandDataOfGerbe
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian := by
  exact
    sourceUnderlyingAbsoluteGlueingBandDataOfPackage (𝒮 := 𝒮) hAbelian
      (exists_underlying_automorphism_absolute_glueing (𝒮 := 𝒮) hGerbe hAbelian)

/-- Helper for Chap08 Lemma 8 11 8/Part16: a source absolute-glueing datum together with the
terminal-section transport law needed to make the reconstructed terminal operations restrict
additively.  This is the source-proof datum expressed by
`γ^V_{T,x} ∘ ρ_f|_T = γ^U_{T,x}`. -/
abbrev underlyingAbsoluteGlueingBandDataWithTransport
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) : Prop :=
  ∃ F : GrothendieckTopology.AbsoluteGlueing J,
    ∃ comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
        F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
      ∃ compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparisonF y,
        fixedReconstructedTerminalSectionRestrictionTransportCompatible
          (𝒮 := 𝒮) hAbelian F comparisonF

/-- Helper for Chap08 Lemma 8 11 8/Part16: the source-level terminal transition square from
Part15 is exactly the terminal-section transport package consumed by the fixed reconstructed
operations.  The only extra input is Chapter 7 counit naturality, already isolated in Part15. -/
theorem fixedReconstructedTerminalSectionRestrictionTransportCompatible_of_sourceTerminalTransport
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (hterminal :
      sourceAbsoluteGlueingTerminalRestrictionTransportCompatible
        (𝒮 := 𝒮) hAbelian F comparisonF) :
      fixedReconstructedTerminalSectionRestrictionTransportCompatible
        (𝒮 := 𝒮) hAbelian F comparisonF := by
  intro U V f x
  obtain ⟨g, hg⟩ := hterminal f x
  refine ⟨g, ?_⟩
  intro a
  let xV := ((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x
  let TU : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  let TV : (Over V)ᵒᵖ := op (Over.mk (𝟙 V))
  let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
  have hlocal :
      ((comparisonF xV).hom.1.app TV)
        (((absoluteGlueingReconstructionOverIso (J := J) F V).hom.1.app TV)
          (R.1.map f.op a)) =
      ((comparisonF xV).hom.1.app TV)
        (GrothendieckTopology.absoluteGlueingToPresheafMap J F f
          (((absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app TU) a)) := by
    simpa [R, TU, TV, xV, absoluteGlueingReconstruction,
      absoluteGlueingReconstructionOverIso, Category.assoc] using
      congrFun
        (absolute_glueing_reconstruction_restriction_map_after_local_comparison
          (𝒮 := 𝒮) (J := J) hAbelian F comparisonF (f := f) xV)
        a
  have hstart :
      fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF
        xV (R.1.map f.op a) =
      ((comparisonF xV).hom.1.app TV)
        (((absoluteGlueingReconstructionOverIso (J := J) F V).hom.1.app TV)
          (R.1.map f.op a)) := by
    simp [fixedReconstructedTerminalSectionEquiv, R, TV, xV]
  have htransport :
      ((comparisonF xV).hom.1.app TV)
        (((absoluteGlueingReconstructionOverIso (J := J) F V).hom.1.app TV)
          (R.1.map f.op a)) =
      ((comparisonF xV).hom.1.app TV)
        (GrothendieckTopology.absoluteGlueingToPresheafMap J F f
          (((absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app TU) a)) := hlocal
  have hadd :
      ((comparisonF xV).hom.1.app TV)
        (GrothendieckTopology.absoluteGlueingToPresheafMap J F f
          (((absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app TU) a)) =
      g.hom
        (((comparisonF x).hom.1.app TU)
          (((absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app TU) a)) := by
    exact hg (((absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app TU) a)
  have hend :
      g.hom
        (((comparisonF x).hom.1.app TU)
          (((absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app TU) a)) =
      g.hom
        (fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF x a) := by
    simp [fixedReconstructedTerminalSectionEquiv, TU]
  exact hstart.trans (htransport.trans (hadd.trans hend))

/-- Helper for Chap08 Lemma 8 11 8/Part16: the transport-strengthened source package forgets
to the underlying absolute-glueing source datum. -/
theorem underlyingAbsoluteGlueingBandDataOfTransportSource
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (data :
      underlyingAbsoluteGlueingBandDataWithTransport
        (𝒮 := 𝒮) hAbelian) :
    underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian := by
  obtain ⟨F, comparisonF, compatibilityF, _htransport⟩ := data
  exact ⟨F, comparisonF, compatibilityF⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: strengthened source package that includes the two
non-terminal additivity inputs needed to upgrade the local underlying comparison to an
`AddCommGrpCat`-valued comparison.  This records the next source-side target after terminal
transport gives `hops`. -/
abbrev underlyingAbsoluteGlueingBandDataWithTransportAndLocalAdditivity
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) : Prop :=
  ∃ F : GrothendieckTopology.AbsoluteGlueing J,
    ∃ comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
        F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
      ∃ compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparisonF y,
        ∃ htransport :
          fixedReconstructedTerminalSectionRestrictionTransportCompatible
            (𝒮 := 𝒮) hAbelian F comparisonF,
          let hops :=
            fixedReconstructedTerminalSectionOperationRestrictionCompatible_of_transport
              (𝒮 := 𝒮) hAbelian F comparisonF htransport
          fixedReconstructedAddCommSheafLocalUnderlyingComparisonPreservesAdd
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops ∧
            fixedReconstructedAddCommSheafLocalUnderlyingComparisonInvPreservesAdd
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops

/-- Helper for Chap08 Lemma 8 11 8/Part16: the source package with non-terminal local additivity
forgets to the terminal-transport source package. -/
theorem underlyingAbsoluteGlueingBandDataWithTransportOfLocalAdditivitySource
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (data :
      underlyingAbsoluteGlueingBandDataWithTransportAndLocalAdditivity
        (𝒮 := 𝒮) hGerbe hAbelian) :
    underlyingAbsoluteGlueingBandDataWithTransport (𝒮 := 𝒮) hAbelian := by
  obtain ⟨F, comparisonF, compatibilityF, htransport, _hadd⟩ := data
  exact ⟨F, comparisonF, compatibilityF, htransport⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: the chosen-cover source absolute-glueing datum
comes with the terminal-section transport characterization needed by the fixed additive
reconstruction.  The terminal `γ/ρ` calculation is isolated in Part15 as the public
`exists_underlying_automorphism_absolute_glueing_with_terminal_transport` package, and this
theorem only adapts it to the Part16 consumer shape. -/
theorem sourceUnderlyingAbsoluteGlueingBandDataWithTransportOfGerbe
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    underlyingAbsoluteGlueingBandDataWithTransport (𝒮 := 𝒮) hAbelian := by
  obtain ⟨F, comparisonF, compatibilityF, hterminal⟩ :=
    exists_underlying_automorphism_absolute_glueing_with_terminal_transport
      (𝒮 := 𝒮) hGerbe hAbelian
  exact
    ⟨F, comparisonF, compatibilityF,
      fixedReconstructedTerminalSectionRestrictionTransportCompatible_of_sourceTerminalTransport
        (𝒮 := 𝒮) hAbelian F comparisonF hterminal⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: over a base object whose gerbe fiber has an object,
the terminal sections of the reconstructed `Type`-valued sheaf inherit the abelian-group
structure transported from the corresponding local automorphism sheaf. -/
theorem reconstructedTerminalSections_addCommGroup_of_fiber
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C} (x : 𝒮.p.Fiber U) :
    Nonempty (AddCommGroup
      ((absoluteGlueingReconstruction (J := J) F).1.obj (op U))) := by
  -- First lift the fixed localized `Type` sheaf `F.obj U` to an additive sheaf by transporting
  -- across the comparison with the automorphism sheaf of the chosen object `x`.
  obtain ⟨A, forgetIso, _liftedComparison, _liftedCompatibility⟩ :=
    slice_addcomm_sheaf_of_underlying_comparison
      (𝒮 := 𝒮) hAbelian (F.obj U) x (comparisonF x)
  let T : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  let overIso := absoluteGlueingReconstructionOverIso (J := J) F U
  -- At the terminal slice object, compose the reconstruction-over comparison with the inverse
  -- of the forgetful comparison to get an equivalence of section types.
  let sectionEquiv :
      (absoluteGlueingReconstruction (J := J) F).1.obj (op U) ≃
        A.1.obj T :=
    { toFun := fun a ↦ (forgetIso.inv.app T) ((overIso.hom.1.app T) a)
      invFun := fun b ↦ (overIso.inv.1.app T) ((forgetIso.hom.app T) b)
      left_inv := by
        intro a
        calc
          (overIso.inv.1.app T)
              ((forgetIso.hom.app T)
                ((forgetIso.inv.app T) ((overIso.hom.1.app T) a))) =
            (overIso.inv.1.app T) ((overIso.hom.1.app T) a) := by
              have hforget :
                  (forgetIso.hom.app T)
                      ((forgetIso.inv.app T) ((overIso.hom.1.app T) a)) =
                    (overIso.hom.1.app T) a :=
                congrFun
                  (congrArg (fun η ↦ η.app T) forgetIso.inv_hom_id)
                  ((overIso.hom.1.app T) a)
              exact congrArg (fun z ↦ (overIso.inv.1.app T) z) hforget
          _ = a := by
              exact
                congrFun
                  (congrArg (fun η ↦ η.1.app T) overIso.hom_inv_id)
                  a
      right_inv := by
        intro b
        calc
          (forgetIso.inv.app T)
              ((overIso.hom.1.app T)
                ((overIso.inv.1.app T) ((forgetIso.hom.app T) b))) =
            (forgetIso.inv.app T) ((forgetIso.hom.app T) b) := by
              have hover :
                  (overIso.hom.1.app T)
                      ((overIso.inv.1.app T) ((forgetIso.hom.app T) b)) =
                    (forgetIso.hom.app T) b :=
                congrFun
                  (congrArg (fun η ↦ η.1.app T) overIso.inv_hom_id)
                  ((forgetIso.hom.app T) b)
              exact congrArg (fun z ↦ (forgetIso.inv.app T) z) hover
          _ = b := by
              exact
                congrFun
                  (congrArg (fun η ↦ η.app T) forgetIso.hom_inv_id)
                  b }
  -- Transport the existing abelian-group structure on the lifted additive sheaf's terminal
  -- sections back along this equivalence.
  exact ⟨Equiv.addCommGroup sectionEquiv⟩

end CategoryTheory
