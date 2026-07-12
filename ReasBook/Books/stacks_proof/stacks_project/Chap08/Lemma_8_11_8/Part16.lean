import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Lemma_7_26_6
import StacksProject_2024.Chap08.Lemma_8_3_7
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Definition_8_11_1
import StacksProject_2024.Chap08.Lemma_8_11_8.Part01
import StacksProject_2024.Chap08.Lemma_8_11_8.Part16.Index

universe u v w z

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Helper for Chap08 Lemma 8 11 8/Part16: the source-local additivity package is exactly the
remaining input needed to assemble the operations-level source datum.  Terminal transport gives
the fixed reconstructed operations; the two non-terminal additivity inputs upgrade the underlying
local comparisons to `AddCommGrpCat`-valued comparisons, and conjugation compatibility is then
formal from the underlying source comparisons. -/
theorem underlyingAbsoluteGlueingBandDataWithOperationsOfTransportAndLocalAdditivity
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (data :
      underlyingAbsoluteGlueingBandDataWithTransportAndLocalAdditivity
        (𝒮 := 𝒮) hGerbe hAbelian) :
    underlyingAbsoluteGlueingBandDataWithOperations
      (𝒮 := 𝒮) hGerbe hAbelian := by
  obtain ⟨F, comparisonF, compatibilityF, htransport, hadd, hinvadd⟩ := data
  let comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      (fixedReconstructedAddCommSheafOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF
        (fixedReconstructedTerminalSectionOperationRestrictionCompatible_of_transport
          (𝒮 := 𝒮) hAbelian F comparisonF htransport)).over U ≅
          𝒮.automorphismAddCommSheaf hAbelian x :=
    fun {U} x ↦
      fixedReconstructedAddCommSheafLocalComparisonOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF
        (fixedReconstructedTerminalSectionOperationRestrictionCompatible_of_transport
          (𝒮 := 𝒮) hAbelian F comparisonF htransport)
        hadd hinvadd x
  have hcomparison :
      ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
        comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
          comparison y := by
    intro U x y φ
    dsimp [comparison]
    exact
      fixedReconstructedAddCommSheafLocalComparisonOfOperations_conj
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF
        (fixedReconstructedTerminalSectionOperationRestrictionCompatible_of_transport
          (𝒮 := 𝒮) hAbelian F comparisonF htransport)
        hadd hinvadd φ
  exact
    underlyingAbsoluteGlueingBandDataWithOperationsOfTransportAndComparisons
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF
      htransport comparison hcomparison

/-- Helper for Chap08 Lemma 8 11 8/Part16: the source transport package's fixed absolute-glueing
object.  This keeps the non-terminal additivity frontier tied to the concrete chosen-cover source
data, rather than to an arbitrary terminal-transport package. -/
noncomputable abbrev sourceTransportAbsoluteGlueingOfGerbe
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    GrothendieckTopology.AbsoluteGlueing J :=
  fixed_cover_underlying_automorphism_absolute_glueing (𝒮 := 𝒮) hGerbe hAbelian

/-- Helper for Chap08 Lemma 8 11 8/Part16: the source transport package's underlying local
comparison family. -/
noncomputable abbrev sourceTransportComparisonOfGerbe
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x : 𝒮.p.Fiber U) :
    (sourceTransportAbsoluteGlueingOfGerbe (𝒮 := 𝒮) hGerbe hAbelian).obj U ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x :=
  fixed_cover_absolute_glueing_comparison_map (𝒮 := 𝒮) hGerbe hAbelian x

/-- Helper for Chap08 Lemma 8 11 8/Part16: the source transport package's local comparisons are
compatible with conjugation. -/
theorem sourceTransportCompatibilityOfGerbe
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      sourceTransportComparisonOfGerbe (𝒮 := 𝒮) hGerbe hAbelian x ≪≫
          automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        sourceTransportComparisonOfGerbe (𝒮 := 𝒮) hGerbe hAbelian y := by
  intro U x y φ
  simpa [sourceTransportComparisonOfGerbe] using
    fixed_cover_absolute_glueing_comparison_map_conj
      (𝒮 := 𝒮) hGerbe hAbelian φ

/-- Helper for Chap08 Lemma 8 11 8/Part16: the source transport package's terminal restriction
compatibility. -/
theorem sourceTransportRestrictionCompatibleOfGerbe
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    fixedReconstructedTerminalSectionRestrictionTransportCompatible
      (𝒮 := 𝒮) hAbelian
      (sourceTransportAbsoluteGlueingOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      (sourceTransportComparisonOfGerbe (𝒮 := 𝒮) hGerbe hAbelian) := by
  exact
    fixedReconstructedTerminalSectionRestrictionTransportCompatible_of_sourceTerminalTransport
      (𝒮 := 𝒮) hAbelian
      (sourceTransportAbsoluteGlueingOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      (sourceTransportComparisonOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      (fixed_cover_absolute_glueing_terminal_transport_compatible
        (𝒮 := 𝒮) hGerbe hAbelian)

/-- Helper for Chap08 Lemma 8 11 8/Part16: the source transport package also carries the
sheafwise non-terminal `γ/ρ` compatibility isolated in Part15. -/
theorem sourceTransportSheafwiseRestrictionCompatibleOfGerbe
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    sourceAbsoluteGlueingSheafwiseRestrictionTransportCompatible
      (𝒮 := 𝒮) hAbelian
      (sourceTransportAbsoluteGlueingOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      (sourceTransportComparisonOfGerbe (𝒮 := 𝒮) hGerbe hAbelian) := by
  intro U V f x T
  simpa [sourceTransportAbsoluteGlueingOfGerbe, sourceTransportComparisonOfGerbe,
    fixed_cover_underlying_automorphism_absolute_glueing] using
    fixed_cover_absolute_glueing_sheafwise_transport_compatible
      (𝒮 := 𝒮) hGerbe hAbelian f x T

/-- Helper for Chap08 Lemma 8 11 8/Part16: the object obtained by mapping the terminal object
of `Over V` along `f : V ⟶ U` is the concrete slice object `Over.mk f`. -/
private theorem overMap_obj_overMk_id_eq {U V : C} (f : V ⟶ U) :
    (Over.map f).obj (Over.mk (𝟙 V)) = Over.mk f := by
  apply CostructuredArrow.obj_ext
  · rfl
  · simp

/-- Helper for Chap08 Lemma 8 11 8/Part16: a Type-valued natural transformation commutes with
dependent transport along an equality of source objects. -/
private theorem typeNatTrans_app_cast_eq
    {D : Type*} [Category D] {P Q : D ⥤ Type w} (α : P ⟶ Q)
    {X Y : D} (p : X = Y) (x : P.obj X) :
    α.app Y (Eq.mp (congrArg P.obj p) x) =
      Eq.mp (congrArg Q.obj p) (α.app X x) := by
  cases p
  rfl

/-- Helper for Chap08 Lemma 8 11 8/Part16: dependent casts coming from equality of
`AddCommGrpCat` objects preserve addition. -/
private theorem addCommGrpCat_cast_add
    {A B : AddCommGrpCat.{z}} (p : A = B) (a b : A) :
    Eq.mp (congrArg (fun X : AddCommGrpCat.{z} ↦ (X : Type z)) p) (a + b) =
      Eq.mp (congrArg (fun X : AddCommGrpCat.{z} ↦ (X : Type z)) p) a +
        Eq.mp (congrArg (fun X : AddCommGrpCat.{z} ↦ (X : Type z)) p) b := by
  cases p
  rfl

/-- Helper for Chap08 Lemma 8 11 8/Part16: the reconstruction counit, evaluated at a concrete
slice object `Over.mk f`, identifies the absolute-glueing transition with the restriction from
the reconstructed sheaf. -/
private theorem reconstructionOverIso_transition_app_overMk
    (F : GrothendieckTopology.AbsoluteGlueing J) {U V : C} (f : V ⟶ U) :
    ∀ a : (absoluteGlueingReconstruction (J := J) F).1.obj (op V),
      (F.transition f).hom.1.app (op (Over.mk (𝟙 V)))
        ((absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app
          (op ((Over.map f).obj (Over.mk (𝟙 V)))) a) =
      (absoluteGlueingReconstructionOverIso (J := J) F V).hom.1.app
        (op (Over.mk (𝟙 V))) a := by
  intro a
  have h :=
    congrFun
      (congrArg
        (fun τ ↦ τ.hom.app (op (Over.mk (𝟙 V))))
        (fixedAbsoluteGlueingReconstructionOverIso_hom_naturality_assoc
          (J := J) F (f := f)))
      a
  simpa [GrothendieckTopology.sheafToAbsoluteGlueingFunctor, Sheaf.over,
    Over.mapForget, Over.mapForget_eq, FunctorToTypes.map_comp_apply] using h

/-- Helper for Chap08 Lemma 8 11 8/Part16: the generic operations-level consumer for the
non-terminal source `γ/ρ` square.  The remaining point is no longer source-specific: after
`hsheafwise` identifies the fixed transition at `T : (C / V)ᵒᵖ` with the canonical additive
base-change map, one must normalize the Chapter 7 reconstruction counit at the dependent object
`op ((Over.map f).obj (Over.mk (𝟙 V))) = op (Over.mk f)` and transfer the resulting additivity
statement back to the actual slice object of the goal. -/
private theorem fixedReconstructedLocalUnderlyingComparisonPreservesAdd_of_sheafwiseTransport
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (htransport :
      fixedReconstructedTerminalSectionRestrictionTransportCompatible
        (𝒮 := 𝒮) hAbelian F comparisonF)
    (hsheafwise :
      sourceAbsoluteGlueingSheafwiseRestrictionTransportCompatible
        (𝒮 := 𝒮) hAbelian F comparisonF) :
    fixedReconstructedAddCommSheafLocalUnderlyingComparisonPreservesAdd
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF
      (fixedReconstructedTerminalSectionOperationRestrictionCompatible_of_transport
        (𝒮 := 𝒮) hAbelian F comparisonF htransport) := by
  let hops :=
    fixedReconstructedTerminalSectionOperationRestrictionCompatible_of_transport
      (𝒮 := 𝒮) hAbelian F comparisonF htransport
  have hoverMk :
      ∀ {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
        (s t : (((fixedReconstructedAddCommSheafOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U).1.obj
            (op (Over.mk f)))),
          (show ((𝒮.automorphismAddCommSheaf hAbelian x).1.obj (op (Over.mk f))) from
            (fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops x).hom.1.app
                (op (Over.mk f)) (s + t)) =
            (show ((𝒮.automorphismAddCommSheaf hAbelian x).1.obj (op (Over.mk f))) from
              (fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations
                (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops x).hom.1.app
                  (op (Over.mk f)) s) +
            (show ((𝒮.automorphismAddCommSheaf hAbelian x).1.obj (op (Over.mk f))) from
              (fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations
                (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops x).hom.1.app
                  (op (Over.mk f)) t) := by
    -- Remaining normalized algebraic step: combine `hsheafwise` at `op (Over.mk (𝟙 V))`
    -- with the reconstructed terminal-section additivity over `V`, then cancel the induced
    -- base-change homomorphism using the sheaf isomorphisms in the source square.
    intro U V f x s t
    let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
    let TV : (Over V)ᵒᵖ := op (Over.mk (𝟙 V))
    let TU : (Over U)ᵒᵖ := op ((Over.map f).obj (Over.mk (𝟙 V)))
    let Tmk : (Over U)ᵒᵖ := op (Over.mk f)
    let xV : 𝒮.p.Fiber V := ((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x
    obtain ⟨g, hg⟩ := hsheafwise f x TV
    let A : AddCommGrpCat.{max u v} :=
      (𝒮.automorphismAddCommSheaf hAbelian x).1.obj Tmk
    let A₀ : AddCommGrpCat.{max u v} :=
      (𝒮.automorphismAddCommSheaf hAbelian x).1.obj TU
    let B : AddCommGrpCat.{max u v} :=
      (𝒮.automorphismAddCommSheaf hAbelian xV).1.obj TV
    have hObj : Tmk = TU := by
      simp [Tmk, TU, overMap_obj_overMk_id_eq]
    have hA : A = A₀ :=
      congrArg (fun T ↦ (𝒮.automorphismAddCommSheaf hAbelian x).1.obj T) hObj
    have hAType : (A : Type (max u v)) = (A₀ : Type (max u v)) :=
      congrArg (fun X : AddCommGrpCat.{max u v} ↦ (X : Type (max u v))) hA
    let gFun : A → B := fun z ↦ g.hom (Eq.mp hAType z)
    have hsource (a : R.1.obj (op V)) :
        (show B from
          (comparisonF xV).hom.1.app TV
            ((absoluteGlueingReconstructionOverIso (J := J) F V).hom.1.app TV a)) =
          gFun
            (show A from
              (comparisonF x).hom.1.app Tmk
                ((absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app Tmk a)) := by
      have hrecon :
          (F.transition f).hom.1.app (op (Over.mk (𝟙 V)))
            ((absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app
              (op ((Over.map f).obj (Over.mk (𝟙 V)))) a) =
          (absoluteGlueingReconstructionOverIso (J := J) F V).hom.1.app
            (op (Over.mk (𝟙 V))) a :=
        reconstructionOverIso_transition_app_overMk (J := J) F f a
      calc
        (show B from
          (comparisonF xV).hom.1.app TV
            ((absoluteGlueingReconstructionOverIso (J := J) F V).hom.1.app TV a)) =
            (show B from
              (comparisonF xV).hom.1.app TV
                ((F.transition f).hom.1.app (op (Over.mk (𝟙 V)))
                  ((absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app
                    (op ((Over.map f).obj (Over.mk (𝟙 V)))) a))) := by
              simpa [TV, B, xV] using
                congrArg (fun z ↦ (comparisonF xV).hom.1.app TV z) hrecon.symm
        _ = gFun
            (show A from
              (comparisonF x).hom.1.app Tmk
                ((absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app Tmk a)) := by
              have hcast :
                  Eq.mp hAType
                    (show A from
                      (comparisonF x).hom.1.app Tmk
                        ((absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app Tmk a)) =
                  (show A₀ from
                    (comparisonF x).hom.1.app TU
                      ((absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app TU a)) := by
                let α :
                    ((absoluteGlueingReconstruction (J := J) F).over U).1 ⟶
                      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1 :=
                  (absoluteGlueingReconstructionOverIso (J := J) F U).hom.1 ≫
                    (comparisonF x).hom.1
                have hdomain :
                    Eq.mp
                      (congrArg
                        (fun T ↦ ((absoluteGlueingReconstruction (J := J) F).over U).1.obj T)
                        hObj) a = a := by
                  simp [R, Tmk, TU, Sheaf.over]
                have hα :
                    Eq.mp
                      (congrArg
                        (fun T ↦ (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1.obj T)
                        hObj)
                      (α.app Tmk a) =
                    α.app TU a := by
                  have hnat := typeNatTrans_app_cast_eq α hObj a
                  rw [← hnat, hdomain]
                simpa [hAType, α, A, A₀, Tmk, TU, automorphismUnderlyingSheaf] using hα
              calc
                (show B from
                  (comparisonF xV).hom.1.app TV
                    ((F.transition f).hom.1.app (op (Over.mk (𝟙 V)))
                      ((absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app
                        (op ((Over.map f).obj (Over.mk (𝟙 V)))) a))) =
                    (AddCommGrpCat.Hom.hom g)
                      (show A₀ from
                        (comparisonF x).hom.1.app TU
                          ((absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app TU a)) := by
                      simpa [A₀, B, TV, TU, xV] using
                        hg ((absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app
                          (op ((Over.map f).obj (Over.mk (𝟙 V)))) a)
                _ = gFun
                    (show A from
                      (comparisonF x).hom.1.app Tmk
                        ((absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app Tmk a)) := by
                      dsimp [gFun]
                      simpa using congrArg (fun z ↦ (AddCommGrpCat.Hom.hom g) z) hcast.symm
    let eU :=
      fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops x
    let eV := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF xV
    have hsource_eU (a : R.1.obj (op V)) :
        eV a =
          gFun
            (show A from eU.hom.1.app Tmk
              (show (((fixedReconstructedAddCommSheafOfOperations
                (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U).1.obj
                  Tmk) from a)) := by
      simpa [eU, eV, fixedReconstructedTerminalSectionEquiv, R, TV, Tmk] using hsource a
    have hEV_add :
        eV (show R.1.obj (op V) from s + t) =
          eV (show R.1.obj (op V) from s) + eV (show R.1.obj (op V) from t) := by
      have hsum :
          (show R.1.obj (op V) from s + t) =
            fixedReconstructedTerminalSectionSumOfFiber
              (𝒮 := 𝒮) hAbelian F comparisonF xV
              (show R.1.obj (op V) from s) (show R.1.obj (op V) from t) := by
        change
          fixedReconstructedGlobalSumOfOperations
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
              (show R.1.obj (op V) from s) (show R.1.obj (op V) from t) =
            fixedReconstructedTerminalSectionSumOfFiber
              (𝒮 := 𝒮) hAbelian F comparisonF xV
              (show R.1.obj (op V) from s) (show R.1.obj (op V) from t)
        exact
          fixedReconstructedGlobalSumOfOperations_eq_sumOfFiber
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops xV
            (show R.1.obj (op V) from s) (show R.1.obj (op V) from t)
      rw [hsum]
      simpa [eV, fixedReconstructedTerminalSectionEquiv, R, TV] using
        fixedReconstructedTerminalSectionEquiv_map_add
          (𝒮 := 𝒮) hAbelian F comparisonF xV
          (show R.1.obj (op V) from s) (show R.1.obj (op V) from t)
    have hgFun_map_add (a b : A) : gFun (a + b) = gFun a + gFun b := by
      have hcast_add :
          Eq.mp hAType (a + b) = Eq.mp hAType a + Eq.mp hAType b := by
        simpa [hAType] using addCommGrpCat_cast_add (A := A) (B := A₀) hA a b
      dsimp [gFun]
      simpa using
        (congrArg (fun z ↦ (AddCommGrpCat.Hom.hom g) z) hcast_add).trans
          (map_add g.hom (Eq.mp hAType a) (Eq.mp hAType b))
    have heU_right (a : A) :
        (show A from eU.hom.1.app Tmk
          (eU.inv.1.app Tmk
            (show ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1.obj Tmk) from a))) = a := by
      exact
        congrFun (congrArg (fun η ↦ η.1.app Tmk) eU.inv_hom_id)
          (show ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1.obj Tmk) from a)
    have hgFun_injective : Function.Injective gFun := by
      intro a b hab
      let ra : R.1.obj (op V) :=
        eU.inv.1.app Tmk
          (show ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1.obj Tmk) from a)
      let rb : R.1.obj (op V) :=
        eU.inv.1.app Tmk
          (show ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1.obj Tmk) from b)
      have hga : eV ra = gFun a := by
        simpa [ra, heU_right a] using hsource_eU ra
      have hgb : eV rb = gFun b := by
        simpa [rb, heU_right b] using hsource_eU rb
      have hev : eV ra = eV rb := hga.trans (hab.trans hgb.symm)
      have hpre : ra = rb := eV.injective hev
      calc
        a = (show A from eU.hom.1.app Tmk
              (eU.inv.1.app Tmk
                (show ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1.obj Tmk) from a))) := by
              exact (heU_right a).symm
        _ = (show A from eU.hom.1.app Tmk
              (eU.inv.1.app Tmk
                (show ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1.obj Tmk) from b))) := by
              simpa [ra, rb] using congrArg (fun z ↦ (show A from eU.hom.1.app Tmk z)) hpre
        _ = b := heU_right b
    apply hgFun_injective
    calc
      gFun
          (show A from eU.hom.1.app Tmk
            (show (((fixedReconstructedAddCommSheafOfOperations
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U).1.obj
                Tmk) from s + t)) =
          eV (show R.1.obj (op V) from s + t) := by
            exact (hsource_eU (show R.1.obj (op V) from s + t)).symm
      _ = eV (show R.1.obj (op V) from s) + eV (show R.1.obj (op V) from t) := hEV_add
      _ =
          gFun
            (show A from eU.hom.1.app Tmk
              (show (((fixedReconstructedAddCommSheafOfOperations
                (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U).1.obj
                  Tmk) from s)) +
          gFun
            (show A from eU.hom.1.app Tmk
              (show (((fixedReconstructedAddCommSheafOfOperations
                (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U).1.obj
                  Tmk) from t)) := by
            rw [hsource_eU (show R.1.obj (op V) from s),
              hsource_eU (show R.1.obj (op V) from t)]
      _ =
          gFun
            ((show A from eU.hom.1.app Tmk
              (show (((fixedReconstructedAddCommSheafOfOperations
                (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U).1.obj
                  Tmk) from s)) +
            (show A from eU.hom.1.app Tmk
              (show (((fixedReconstructedAddCommSheafOfOperations
                (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U).1.obj
                  Tmk) from t))) := by
            exact (hgFun_map_add _ _).symm
  intro U x T s t
  cases T with
  | op T0 =>
    exact hoverMk T0.hom x s t

/-- Helper for Chap08 Lemma 8 11 8/Part16: the missing source-specific non-terminal `γ/ρ`
calculation says the chosen source local underlying comparison preserves addition on every object of
each slice site. -/
theorem sourceTransportLocalUnderlyingComparisonPreservesAddOfGerbe
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    fixedReconstructedAddCommSheafLocalUnderlyingComparisonPreservesAdd
      (𝒮 := 𝒮) hGerbe hAbelian
      (sourceTransportAbsoluteGlueingOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      (sourceTransportComparisonOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      (sourceTransportCompatibilityOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      (fixedReconstructedTerminalSectionOperationRestrictionCompatible_of_transport
        (𝒮 := 𝒮) hAbelian
        (sourceTransportAbsoluteGlueingOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
        (sourceTransportComparisonOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
        (sourceTransportRestrictionCompatibleOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)) := by
  exact
    fixedReconstructedLocalUnderlyingComparisonPreservesAdd_of_sheafwiseTransport
      (𝒮 := 𝒮) hGerbe hAbelian
      (sourceTransportAbsoluteGlueingOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      (sourceTransportComparisonOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      (sourceTransportCompatibilityOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      (sourceTransportRestrictionCompatibleOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      (sourceTransportSheafwiseRestrictionCompatibleOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)

/-- Helper for Chap08 Lemma 8 11 8/Part16: the inverse of the chosen source local underlying
comparison also preserves addition on every object of each slice site. -/
theorem sourceTransportLocalUnderlyingComparisonInvPreservesAddOfGerbe
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    fixedReconstructedAddCommSheafLocalUnderlyingComparisonInvPreservesAdd
      (𝒮 := 𝒮) hGerbe hAbelian
      (sourceTransportAbsoluteGlueingOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      (sourceTransportComparisonOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      (sourceTransportCompatibilityOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      (fixedReconstructedTerminalSectionOperationRestrictionCompatible_of_transport
        (𝒮 := 𝒮) hAbelian
        (sourceTransportAbsoluteGlueingOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
        (sourceTransportComparisonOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
        (sourceTransportRestrictionCompatibleOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)) := by
  intro U x T s t
  let F := sourceTransportAbsoluteGlueingOfGerbe (𝒮 := 𝒮) hGerbe hAbelian
  let comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x :=
    fun {U} x ↦ sourceTransportComparisonOfGerbe (𝒮 := 𝒮) hGerbe hAbelian x
  let compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y :=
    fun {U} {x} {y} φ ↦
      sourceTransportCompatibilityOfGerbe (𝒮 := 𝒮) hGerbe hAbelian φ
  let htransport :
      fixedReconstructedTerminalSectionRestrictionTransportCompatible
        (𝒮 := 𝒮) hAbelian F comparisonF :=
    sourceTransportRestrictionCompatibleOfGerbe (𝒮 := 𝒮) hGerbe hAbelian
  let hops :=
    fixedReconstructedTerminalSectionOperationRestrictionCompatible_of_transport
      (𝒮 := 𝒮) hAbelian F comparisonF htransport
  let e :=
    fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops x
  let A : AddCommGrpCat.{max u v} :=
    ((fixedReconstructedAddCommSheafOfOperations
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U).1.obj T
  let B : AddCommGrpCat.{max u v} :=
    (𝒮.automorphismAddCommSheaf hAbelian x).1.obj T
  have hforward :
      ∀ a b : A,
        (show B from e.hom.1.app T (a + b)) =
          (show B from e.hom.1.app T a) + (show B from e.hom.1.app T b) :=
    sourceTransportLocalUnderlyingComparisonPreservesAddOfGerbe
      (𝒮 := 𝒮) hGerbe hAbelian x T
  have hleft :
      ∀ a : A,
        (show A from e.inv.1.app T (show B from e.hom.1.app T a)) = a := by
    intro a
    exact congrFun (congrArg (fun η ↦ η.1.app T) e.hom_inv_id) a
  have hright :
      ∀ b : B,
        (show B from e.hom.1.app T (show A from e.inv.1.app T b)) = b := by
    intro b
    exact congrFun (congrArg (fun η ↦ η.1.app T) e.inv_hom_id) b
  -- The inverse direction is formal from the forward additivity and the two pointwise inverse
  -- laws of the underlying sheaf isomorphism.
  exact
    inverse_map_add_of_map_add
      (A := A)
      (B := B)
      (fun a : A ↦ (show B from e.hom.1.app T a))
      (fun b : B ↦ (show A from e.inv.1.app T b))
      hforward hleft hright s t

/-- Helper for Chap08 Lemma 8 11 8/Part16: the precise source-side frontier for the operations
package.  `sourceUnderlyingAbsoluteGlueingBandDataWithTransportOfGerbe` supplies the terminal
transport form of the source equality
`γ^V_{T,x} ∘ ρ_f|_T = γ^U_{T,x}`.  The remaining obligation is its non-terminal, sheafwise
additivity form: the underlying local comparison and its inverse preserve addition on every
object of the slice site. -/
theorem sourceUnderlyingAbsoluteGlueingBandDataWithTransportAndLocalAdditivityOfGerbe
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    underlyingAbsoluteGlueingBandDataWithTransportAndLocalAdditivity
      (𝒮 := 𝒮) hGerbe hAbelian := by
  refine
    ⟨sourceTransportAbsoluteGlueingOfGerbe (𝒮 := 𝒮) hGerbe hAbelian,
      sourceTransportComparisonOfGerbe (𝒮 := 𝒮) hGerbe hAbelian,
      sourceTransportCompatibilityOfGerbe (𝒮 := 𝒮) hGerbe hAbelian,
      sourceTransportRestrictionCompatibleOfGerbe (𝒮 := 𝒮) hGerbe hAbelian, ?_⟩
  constructor
  · exact sourceTransportLocalUnderlyingComparisonPreservesAddOfGerbe
      (𝒮 := 𝒮) hGerbe hAbelian
  · exact sourceTransportLocalUnderlyingComparisonInvPreservesAddOfGerbe
      (𝒮 := 𝒮) hGerbe hAbelian

/-- Helper for Chap08 Lemma 8 11 8/Part16: the chosen-cover source absolute-glueing datum
comes with the operation compatibility needed by the fixed additive reconstruction.  This is the
precise Lean target for the source proof's characterization
`γ^V_{T,x} ∘ ρ_f|_T = γ^U_{T,x}`. -/
theorem sourceUnderlyingAbsoluteGlueingBandDataWithOperationsOfGerbe
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    underlyingAbsoluteGlueingBandDataWithOperations
      (𝒮 := 𝒮) hGerbe hAbelian := by
  exact
    underlyingAbsoluteGlueingBandDataWithOperationsOfTransportAndLocalAdditivity
      (𝒮 := 𝒮) hGerbe hAbelian
      (sourceUnderlyingAbsoluteGlueingBandDataWithTransportAndLocalAdditivityOfGerbe
        (𝒮 := 𝒮) hGerbe hAbelian)

/-- Helper for Chap08 Lemma 8 11 8/Part16: a gerbe with abelian automorphism sheaves provides
one source absolute-glueing datum together with a fixed additive reconstruction for that same
datum. -/
theorem existsSourceAbsoluteGlueingWithFixedAddCommSheafData
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    underlyingAbsoluteGlueingBandDataWithFixedAddCommSheafData
      (𝒮 := 𝒮) hAbelian := by
  -- Consume the strengthened canonical source directly; the source proof never needs an
  -- additive lift for an arbitrary compatible `Type`-valued band.
  exact
    fixedAddCommSourceOfOperationsSource
      (𝒮 := 𝒮) hGerbe hAbelian
      (sourceUnderlyingAbsoluteGlueingBandDataWithOperationsOfGerbe
        (𝒮 := 𝒮) hGerbe hAbelian)

/-- Helper for Chap08 Lemma 8 11 8/Part16: a gerbe with abelian automorphism sheaves supplies
the source absolute-glueing datum whose localized sheaves are the underlying automorphism
sheaves. -/
theorem sourceAbsoluteGlueingBandDataOfGerbe
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian := by
  -- Project the underlying source datum from the combined source-and-fixed reconstruction
  -- frontier, leaving the additive reconstruction component for the fixed-source theorem below.
  exact
    underlyingAbsoluteGlueingBandDataOfFixedAddCommSource
      (𝒮 := 𝒮) hAbelian
      (existsSourceAbsoluteGlueingWithFixedAddCommSheafData
        (𝒮 := 𝒮) hGerbe hAbelian)

/-- Helper for Chap08 Lemma 8 11 8/Part16: the chosen source absolute-glueing datum attached
to a gerbe with abelian automorphism sheaves. -/
noncomputable abbrev sourceAbsoluteGlueingOfGerbe
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    GrothendieckTopology.AbsoluteGlueing J :=
  Classical.choose
    (existsSourceAbsoluteGlueingWithFixedAddCommSheafData (𝒮 := 𝒮) hGerbe hAbelian)

/-- Helper for Chap08 Lemma 8 11 8/Part16: the chosen source absolute-glueing datum carries
its local comparison family and conjugation compatibility as one normalized package. -/
theorem sourceAbsoluteGlueingComparisonPackageOfGerbe
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        (sourceAbsoluteGlueingOfGerbe (𝒮 := 𝒮) hGerbe hAbelian).obj U ≅
          automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
      ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
        comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
          comparison y := by
  -- Read the local comparison family from the same combined frontier that defines the chosen
  -- source absolute-glueing object.
  obtain ⟨comparisonF, compatibilityF, _hfixed⟩ :=
    Classical.choose_spec
      (existsSourceAbsoluteGlueingWithFixedAddCommSheafData (𝒮 := 𝒮) hGerbe hAbelian)
  exact ⟨comparisonF, compatibilityF⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: the local comparisons from the chosen source
absolute-glueing datum to the underlying automorphism sheaves. -/
noncomputable abbrev sourceAbsoluteGlueingComparisonOfGerbe
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∀ {U : C} (x : 𝒮.p.Fiber U),
      (sourceAbsoluteGlueingOfGerbe (𝒮 := 𝒮) hGerbe hAbelian).obj U ≅
        automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x :=
  fun {U} x ↦
    Classical.choose
      (sourceAbsoluteGlueingComparisonPackageOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      (U := U) x

/-- Helper for Chap08 Lemma 8 11 8/Part16: the chosen source comparisons are compatible with
conjugation in each fiber. -/
theorem sourceAbsoluteGlueingCompatibilityOfGerbe
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      sourceAbsoluteGlueingComparisonOfGerbe (𝒮 := 𝒮) hGerbe hAbelian x ≪≫
          automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        sourceAbsoluteGlueingComparisonOfGerbe (𝒮 := 𝒮) hGerbe hAbelian y := by
  -- Project the whole dependent compatibility law from the source package, keeping the same
  -- chosen comparison family as the public projection above.
  intro U x y φ
  exact
    Classical.choose_spec
      (sourceAbsoluteGlueingComparisonPackageOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      (U := U) (x := x) (y := y) φ

/-- Helper for Chap08 Lemma 8 11 8/Part16: the chosen source absolute-glueing datum admits
the fixed additive reconstruction package needed for the gerbe band. -/
theorem fixedAbsoluteGlueingAddCommSheafDataOfSource
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian
      (sourceAbsoluteGlueingOfGerbe (𝒮 := 𝒮) hGerbe hAbelian) := by
  -- Use the projection helper so the fixed-data owner stays definitionally the chosen source
  -- absolute-glueing object.
  exact
    fixedAbsoluteGlueingAddCommSheafDataOfFixedAddCommSource
      (𝒮 := 𝒮) hAbelian
      (existsSourceAbsoluteGlueingWithFixedAddCommSheafData
        (𝒮 := 𝒮) hGerbe hAbelian)

/-- Helper for Chap08 Lemma 8 11 8/Part16: fixed additive data for the chosen source
absolute-glueing object assemble the exact source-and-fixed package used by the final theorem. -/
theorem sourceAndFixedAdditiveReconstructionDataOfChosenSource
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (hfixed :
      fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian
        (sourceAbsoluteGlueingOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)) :
    ∃ F : GrothendieckTopology.AbsoluteGlueing J,
      ∃ comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
          F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
        ∃ _compatibilityF :
          ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
            comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
              comparisonF y,
          fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F := by
  -- Reuse the source-data packager so this source-specific adapter only supplies the chosen
  -- source object, its comparison package, and the matching fixed additive reconstruction.
  exact
    sourceAndFixedAdditiveReconstructionDataOfFixedDatum (𝒮 := 𝒮) hAbelian
      (sourceAbsoluteGlueingOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      (sourceAbsoluteGlueingComparisonOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      (sourceAbsoluteGlueingCompatibilityOfGerbe (𝒮 := 𝒮) hGerbe hAbelian)
      hfixed

/-- Helper for Chap08 Lemma 8 11 8/Part16: a gerbe with abelian automorphism sheaves supplies
one source absolute-glueing datum together with the additive reconstruction frontier for that
same datum. -/
theorem sourceAndFixedAdditiveReconstructionDataOfGerbe
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∃ F : GrothendieckTopology.AbsoluteGlueing J,
      ∃ comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
          F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
        ∃ _compatibilityF :
          ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
            comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
              comparisonF y,
          fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F := by
  -- Route correction: the previous statement asked for additive reconstruction for every
  -- compatible absolute-glueing datum.  The source proof only needs the concrete datum produced
  -- from the chosen-cover automorphism sheaves, plus additive reconstruction for that datum.
  -- With the source datum and its fixed additive reconstruction separated, final packaging is
  -- only the existential assembly required by the theorem statement.
  exact existsSourceAbsoluteGlueingWithFixedAddCommSheafData (𝒮 := 𝒮) hGerbe hAbelian

/-- Helper for Chap08 Lemma 8 11 8/Part16: the source-and-fixed reconstruction package
forgets to the underlying absolute-glueing datum. -/
theorem underlyingAbsoluteGlueingBandDataOfSourceAndFixedData
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (data :
      ∃ F : GrothendieckTopology.AbsoluteGlueing J,
        ∃ comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
            F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
          ∃ _compatibilityF :
            ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
              comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
                comparisonF y,
            fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F) :
    underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian := by
  -- Reuse the support-level projection so the target file does not duplicate the fixed-data
  -- forgetting step.
  exact
    underlyingAbsoluteGlueingBandDataOfSourceAndFixedPackage
      (𝒮 := 𝒮) hAbelian data

/-- Helper for Chap08 Lemma 8 11 8/Part16: the combined source-and-fixed reconstruction
package projects back to the underlying absolute-glueing datum. -/
theorem underlyingAbsoluteGlueingBandDataOfSourceAndFixed
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian := by
  -- Use the generic projection helper so this source-specific wrapper has only one responsibility:
  -- supplying the combined package attached to the gerbe.
  exact
    underlyingAbsoluteGlueingBandDataOfSourceAndFixedData
      (𝒮 := 𝒮) hAbelian
      (sourceAndFixedAdditiveReconstructionDataOfGerbe
        (𝒮 := 𝒮) hGerbe hAbelian)

/-- Helper for Chap08 Lemma 8 11 8/Part16: a gerbe with abelian automorphism sheaves supplies
the source absolute-glueing datum whose local objects are the underlying automorphism sheaves. -/
theorem underlyingAbsoluteGlueingBandDataOfGerbe
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian := by
  -- Project the source datum from the stabilized source-and-fixed frontier, so downstream proofs
  -- consume one normalized source package rather than duplicating the projection shape.
  exact underlyingAbsoluteGlueingBandDataOfSourceAndFixed (𝒮 := 𝒮) hGerbe hAbelian

/-- Helper for Chap08 Lemma 8 11 8/Part16: a fixed absolute-glueing datum whose local sheaves
are identified with the underlying automorphism sheaves reconstructs a global additive sheaf with
the same conjugation-compatible local comparisons. -/
theorem reconstructedAbsoluteGlueingAddCommSheaf
    (_hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (_compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hfixed : fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v},
      ∃ _forgetIso :
        (G.1 ⋙ forget AddCommGrpCat.{max u v}) ≅
          (absoluteGlueingReconstruction (J := J) F).1,
        ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
          G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
          ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
            comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
              comparison y := by
  -- The arbitrary-`F` theorem is now only a projection from an explicit fixed additive package;
  -- the construction of that package is handled by the source-specific frontier above.
  exact hfixed

/-- Helper for Chap08 Lemma 8 11 8/Part16: the fixed reconstructed additive sheaf package
forgets down to the comparison-data interface used by the final band assembly. -/
theorem existsAddCommBandComparisonDataOfReconstructedSheaf
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (data :
      ∃ G : Sheaf J AddCommGrpCat.{max u v},
        ∃ _forgetIso :
          (G.1 ⋙ forget AddCommGrpCat.{max u v}) ≅
            (absoluteGlueingReconstruction (J := J) F).1,
          ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
            G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
            ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
              comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
                comparison y) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v},
      ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison y := by
  -- Reuse the fixed-data projection so all later band assembly consumes the same normalized
  -- comparison-data interface.
  exact fixedAbsoluteGlueingAddCommSheafDataComparisonData (𝒮 := 𝒮) hAbelian data

/-- Helper for Chap08 Lemma 8 11 8/Part16: a source-and-fixed absolute-glueing package
projects to the explicit reconstructed additive comparison-data interface. -/
theorem existsReconstructedComparisonDataOfSourceAndFixedData
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (data :
      ∃ F : GrothendieckTopology.AbsoluteGlueing J,
        ∃ comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
            F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
          ∃ _compatibilityF :
            ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
              comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
                comparisonF y,
            fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v},
      ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison y := by
  -- The source comparisons identify the absolute-glueing object; the fixed additive package
  -- already contains the global additive sheaf and the compatible local comparisons.
  obtain ⟨F, _comparisonF, _compatibilityF, hfixed⟩ := data
  exact existsAddCommBandComparisonDataOfReconstructedSheaf
    (𝒮 := 𝒮) hAbelian F hfixed

/-- Helper for Chap08 Lemma 8 11 8/Part16: a source-and-fixed absolute-glueing package
directly gives the final gerbe-band existential. -/
theorem existsGerbeBandOfSourceAndFixedData
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (data :
      ∃ F : GrothendieckTopology.AbsoluteGlueing J,
        ∃ comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
            F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
          ∃ _compatibilityF :
            ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
              comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
                comparisonF y,
            fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v}, IsGerbeBand hAbelian G := by
  -- First project the combined source-and-fixed package to comparison data, then reuse the
  -- stable predicate-level gerbe-band packaging lemma.
  exact exists_gerbe_band_of_reconstructed_comparison_data
    (𝒮 := 𝒮) hAbelian
    (existsReconstructedComparisonDataOfSourceAndFixedData
      (𝒮 := 𝒮) hAbelian data)

/-- Helper for Chap08 Lemma 8 11 8/Part16: the operations-level source package is already
enough to close the final gerbe-band existential.  This is the intended consumer of the source
proof's `ρ/γ` transition characterization. -/
theorem existsGerbeBandOfOperationsSource
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (data :
      underlyingAbsoluteGlueingBandDataWithOperations
        (𝒮 := 𝒮) hGerbe hAbelian) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v}, IsGerbeBand hAbelian G := by
  exact
    existsGerbeBandOfSourceAndFixedData
      (𝒮 := 𝒮) hAbelian
      (fixedAddCommSourceOfOperationsSource
        (𝒮 := 𝒮) hGerbe hAbelian data)

/-- Helper for Chap08 Lemma 8 11 8/Part16: fixed reconstructed additive sheaf data already
packages as the gerbe-band existential once the local comparisons are conjugation-compatible. -/
theorem existsGerbeBandOfReconstructedSheafData
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (data :
      ∃ G : Sheaf J AddCommGrpCat.{max u v},
        ∃ _forgetIso :
          (G.1 ⋙ forget AddCommGrpCat.{max u v}) ≅
            (absoluteGlueingReconstruction (J := J) F).1,
          ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
            G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
            ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
              comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
                comparison y) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v}, IsGerbeBand hAbelian G := by
  -- First forget the auxiliary comparison with the reconstructed Type-valued sheaf.
  have hcomparison :
      ∃ G : Sheaf J AddCommGrpCat.{max u v},
        ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
          G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
          ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
            comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
              comparison y :=
    existsAddCommBandComparisonDataOfReconstructedSheaf (𝒮 := 𝒮) hAbelian F data
  -- Then use the already stabilized predicate-level packaging helper.
  exact exists_gerbe_band_of_reconstructed_comparison_data (𝒮 := 𝒮) hAbelian hcomparison

/-- Helper for Chap08 Lemma 8 11 8/Part16: the fixed additive reconstruction package for one
absolute-glueing datum is already enough to produce the final gerbe-band existential. -/
theorem existsGerbeBandOfFixedAbsoluteGlueingAddCommSheafData
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {F : GrothendieckTopology.AbsoluteGlueing J}
    (hfixed : fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v}, IsGerbeBand hAbelian G := by
  -- Consume the fixed package at the reconstructed-sheaf interface and discard the auxiliary
  -- forgetful comparison in the already-proved closing helper.
  exact existsGerbeBandOfReconstructedSheafData (𝒮 := 𝒮) hAbelian F hfixed

/-- Helper for Chap08 Lemma 8 11 8/Part16: the source-specific absolute-glueing package,
including fixed additive reconstruction for that same source datum, closes the band theorem. -/
theorem existsGerbeBandOfSourceAddCommSheafData
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v}, IsGerbeBand hAbelian G := by
  -- The remaining frontier already produces the combined source-and-fixed package; the adapter
  -- above performs the final predicate-level packaging in one place.
  exact
    existsGerbeBandOfSourceAndFixedData
      (𝒮 := 𝒮) hAbelian
      (sourceAndFixedAdditiveReconstructionDataOfGerbe
        (𝒮 := 𝒮) hGerbe hAbelian)

/-- Helper for Chap08 Lemma 8 11 8/Part16: source absolute-glueing data and a fixed-datum
additive reconstruction theorem are exactly the two inputs needed for the reconstructed
comparison-data package. -/
theorem existsReconstructedAddCommBandComparisonDataOfSourceAndReconstruction
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (hsource : underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian)
    (hreconstructed :
      ∀ (F : GrothendieckTopology.AbsoluteGlueing J)
        (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
          F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x),
        (∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparisonF y) →
          ∃ G : Sheaf J AddCommGrpCat.{max u v},
            ∃ _ :
              (G.1 ⋙ forget AddCommGrpCat.{max u v}) ≅
                (absoluteGlueingReconstruction (J := J) F).1,
              ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
                G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
                ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
                  comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
                    comparison y) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v},
      ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison y := by
  -- Split the source package into its absolute-glueing object and underlying comparisons.
  obtain ⟨F, comparisonF, compatibilityF⟩ := hsource
  -- Apply the fixed-datum additive reconstruction and forget the auxiliary Type-sheaf
  -- comparison, leaving exactly the band comparison-data existential.
  exact
    existsAddCommBandComparisonDataOfReconstructedSheaf
      (𝒮 := 𝒮) hAbelian F
      (hreconstructed F comparisonF compatibilityF)

/-- Helper for Chap08 Lemma 8 11 8/Part16: source absolute-glueing data together with the
fixed-datum additive reconstruction directly give the final gerbe-band existential. -/
theorem existsGerbeBandOfSourceAndReconstruction
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (hsource : underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian)
    (hreconstructed :
      ∀ (F : GrothendieckTopology.AbsoluteGlueing J)
        (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
          F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x),
        (∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparisonF y) →
          ∃ G : Sheaf J AddCommGrpCat.{max u v},
            ∃ _ :
              (G.1 ⋙ forget AddCommGrpCat.{max u v}) ≅
                (absoluteGlueingReconstruction (J := J) F).1,
              ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
                G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
                ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison y) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v}, IsGerbeBand hAbelian G := by
  -- The source package chooses the absolute-glueing object; the fixed reconstruction theorem
  -- supplies the additive sheaf data for that object, and the new adapter packages it directly.
  obtain ⟨F, comparisonF, compatibilityF⟩ := hsource
  exact
    existsGerbeBandOfReconstructedSheafData
      (𝒮 := 𝒮) hAbelian F
      (hreconstructed F comparisonF compatibilityF)

/-- Helper for Chap08 Lemma 8 11 8/Part16: a fixed source absolute-glueing datum admits the
specialized global additive reconstruction needed for the gerbe band. -/
theorem existsAddCommBandComparisonDataOfAbsoluteGlueing
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hfixed : fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v},
      ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
            comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
              comparison y := by
  -- Use the fixed absolute-glueing reconstruction frontier, then project it to the comparison
  -- data consumed by the final band predicate.
  exact existsAddCommBandComparisonDataOfReconstructedSheaf
    (𝒮 := 𝒮) hAbelian F <|
    reconstructedAbsoluteGlueingAddCommSheaf
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hfixed

/-- Helper for Chap08 Lemma 8 11 8/Part16: a fixed absolute-glueing datum and its reconstructed
additive sheaf package directly give the final gerbe-band existential. -/
theorem existsGerbeBandOfAbsoluteGlueingDatum
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hfixed : fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v}, IsGerbeBand hAbelian G := by
  -- First use the fixed-`F` reconstruction frontier to obtain the additive sheaf, its forgetful
  -- comparison with the reconstructed Type sheaf, and its compatible local comparisons.
  have hdata :
      ∃ G : Sheaf J AddCommGrpCat.{max u v},
        ∃ _ :
          (G.1 ⋙ forget AddCommGrpCat.{max u v}) ≅
            (absoluteGlueingReconstruction (J := J) F).1,
          ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
            G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
            ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
              comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
                comparison y :=
    reconstructedAbsoluteGlueingAddCommSheaf
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hfixed
  -- The final band predicate only consumes the additive sheaf and conjugation-compatible
  -- comparison family, so the auxiliary forgetful isomorphism can be discarded here.
  exact existsGerbeBandOfReconstructedSheafData (𝒮 := 𝒮) hAbelian F hdata

/-- Helper for Chap08 Lemma 8 11 8/Part16: source absolute-glueing data reduce the main
gerbe-band theorem to the fixed-datum additive reconstruction. -/
theorem existsGerbeBandOfUnderlyingAbsoluteGlueingData
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (hsource : underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian)
    (hreconstructed :
      ∀ (F : GrothendieckTopology.AbsoluteGlueing J)
        (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
          F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x),
        (∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparisonF y) →
          fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v}, IsGerbeBand hAbelian G := by
  -- Split the source datum into the fixed absolute-glueing object, its underlying comparisons,
  -- and the conjugation law needed by the fixed reconstruction helper.
  obtain ⟨F, comparisonF, compatibilityF⟩ := hsource
  exact
    existsGerbeBandOfAbsoluteGlueingDatum
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF
      (hreconstructed F comparisonF compatibilityF)

/-- Helper for Chap08 Lemma 8 11 8/Part16: source absolute-glueing data reduce the final
reconstruction frontier to the fixed absolute-glueing additive reconstruction. -/
theorem existsReconstructedAddCommBandComparisonDataOfSource
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (hsource : underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian)
    (hreconstructed :
      ∀ (F : GrothendieckTopology.AbsoluteGlueing J)
        (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
          F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x),
        (∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparisonF y) →
          fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v},
      ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison y := by
  -- Use the explicit two-input bridge: source data choose `F`, and the remaining frontier is the
  -- fixed-`F` additive reconstruction theorem.
  exact
    existsReconstructedAddCommBandComparisonDataOfSourceAndReconstruction
      (𝒮 := 𝒮) hAbelian hsource
      (fun F comparisonF compatibilityF ↦
        reconstructedAbsoluteGlueingAddCommSheaf
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF
          (hreconstructed F comparisonF compatibilityF))


/-- Helper for Chap08 Lemma 8 11 8/Part16: the remaining reconstruction frontier is a global
additive sheaf together with local comparisons to every automorphism sheaf and the conjugation
compatibility of those comparisons. -/
theorem exists_reconstructed_addcomm_band_comparison_data
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v},
      ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison y := by
  -- Route correction: the old final proof asked for an arbitrary global Type-band additive lift.
  -- The stable route first obtains the source absolute-glueing datum, then reconstructs the
  -- additive sheaf only for that fixed datum.
  exact
    existsReconstructedComparisonDataOfSourceAndFixedData
      (𝒮 := 𝒮) hAbelian
      (sourceAndFixedAdditiveReconstructionDataOfGerbe
        (𝒮 := 𝒮) hGerbe hAbelian)

-- Proof sketch: first use that in a gerbe any two local objects become locally isomorphic; since
-- the automorphism sheaves are abelian, conjugation is independent of the chosen local
-- isomorphism, so these local automorphism sheaves glue canonically on overlaps. Then use the
-- gluing lemmas for sheaves on the site and on its localizations to descend the resulting local
-- systems to a single global sheaf of abelian groups whose restriction to each `C/U` identifies
-- with the corresponding automorphism sheaf.
/-- Lemma 8.11.8: if `𝒮` is a gerbe over the site `(C, J)` and every automorphism sheaf
`Aut[𝒮](x)` is canonically abelian for its native composition law, then there exists a sheaf `𝒢`
of abelian groups on `C` whose restriction to each localized site `C/U` is identified with
the canonical abelian-group automorphism sheaf attached to `x`, compatibly with conjugation by
morphisms in the fiber over `U`. -/
@[stacks 0CJY]
theorem exists_gerbe_band_of_abelian_automorphism_sheaves
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v}, IsGerbeBand hAbelian G := by
  -- Route correction: the direct final assembly route must pass through the absolute-glueing
  -- reconstruction API from the earlier parts.  The source datum chooses the fixed
  -- absolute-glueing object; the source-package assembly helper packages the reconstructed
  -- additive sheaf as the band.
  exact existsGerbeBandOfSourceAddCommSheafData (𝒮 := 𝒮) hGerbe hAbelian

end CategoryTheory
