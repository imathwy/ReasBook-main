import StacksProject_2024.Chap22.Lemma_22_20_1
import StacksProject_2024.Chap22.AdmissibleShortExact
import StacksProject_2024.Chap22.Definition_22_7_1
import StacksProject_2024.Chap22.PropertyPDGModule

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w x

/- The source-facing item in Section 22.28 uses the Chapter 22 property `(P)` filtration owner for
differential graded modules, while the telescope construction itself is already formalized
generically in Lemma `22.20.1`. The canonical refine therefore keeps the generic admissibility
lemmas as support API and adds a thin Chapter 22 bridge to that generic telescope filtration. -/

namespace PropertyPFiltration

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCountableCoproducts C]
variable {Graded : Type w} [Category.{x} Graded]
variable (forgetToGraded : C ⥤ Graded) {P : C} (F : _root_.PropertyPFiltration P)

/-- Support lemma for Lemma 22.28.5 (2), split-mono part: if the filtration maps are admissible
after forgetting the differential, this bridge exposes the telescope map admissibility already
present in the local context. -/
instance instTelescopeIsAdmissibleMono
    [hTelescope : IsAdmissibleMono forgetToGraded F.telescopeShortComplex.f] :
    IsAdmissibleMono forgetToGraded F.telescopeShortComplex.f :=
  hTelescope

/-- Support lemma for Lemma 22.28.5 (2), split-mono part: if the filtration maps are admissible
after forgetting the differential, this bridge repackages an explicit admissibility witness for the
telescope map. -/
theorem telescope_isAdmissibleMono
    (hTelescope : IsAdmissibleMono forgetToGraded F.telescopeShortComplex.f) :
    IsAdmissibleMono forgetToGraded F.telescopeShortComplex.f := by
  -- Proof comment: this theorem is only the explicit-value version of the preceding bridge
  -- instance.
  exact hTelescope

/-- Support lemma for Lemma 22.28.5 (2), split-epi part: if the filtration maps are admissible
after forgetting the differential, this bridge exposes the telescope augmentation admissibility
already present in the local context. -/
instance instTelescopeIsAdmissibleEpi
    [hTelescope : IsAdmissibleEpi forgetToGraded F.telescopeShortComplex.g] :
    IsAdmissibleEpi forgetToGraded F.telescopeShortComplex.g :=
  hTelescope

/-- Support lemma for Lemma 22.28.5 (2), split-epi part: if the filtration maps are admissible
after forgetting the differential, this bridge repackages an explicit admissibility witness for the
telescope augmentation. -/
theorem telescope_isAdmissibleEpi
    (hTelescope : IsAdmissibleEpi forgetToGraded F.telescopeShortComplex.g) :
    IsAdmissibleEpi forgetToGraded F.telescopeShortComplex.g := by
  -- Proof comment: this theorem is only the explicit-value version of the preceding bridge
  -- instance.
  exact hTelescope

end

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
variable {Graded : Type w} [Category.{x} Graded]
variable (forgetToGraded : C ⥤ Graded) {P : C} (F : _root_.PropertyPFiltration P)

/-- Generic support API for Lemma 22.28.5 (2): if the transition maps of a chosen filtration are
already known to yield admissible telescope maps after forgetting the differential, then the
telescope short exact sequence is admissible. -/
instance instTelescopeIsAdmissibleShortExact
    [hMono : IsAdmissibleMono forgetToGraded F.telescopeShortComplex.f]
    [hEpi : IsAdmissibleEpi forgetToGraded F.telescopeShortComplex.g] :
    IsAdmissibleShortExact forgetToGraded F.telescopeShortComplex :=
by
  -- Proof comment: package the already available admissible mono/epi witnesses together with the
  -- canonical short exactness from Lemma 22.20.1.
  exact ⟨F.telescopeShortExact, hMono, hEpi⟩

/-- Generic support API for Lemma 22.28.5 (2): if the transition maps of a chosen filtration are
already known to yield admissible telescope maps after forgetting the differential, then the
telescope short exact sequence is admissible. -/
theorem telescope_gradedSplitting
    (hMono : IsAdmissibleMono forgetToGraded F.telescopeShortComplex.f)
    (hEpi : IsAdmissibleEpi forgetToGraded F.telescopeShortComplex.g) :
    IsAdmissibleShortExact forgetToGraded F.telescopeShortComplex := by
  -- Proof comment: delegate to the bridge instance after installing the explicit admissibility
  -- witnesses.
  letI : IsAdmissibleMono forgetToGraded F.telescopeShortComplex.f := hMono
  letI : IsAdmissibleEpi forgetToGraded F.telescopeShortComplex.g := hEpi
  infer_instance

end

end PropertyPFiltration

namespace CochainComplex.PropertyPFiltration

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ
local notation "forgetGraded" =>
  (dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A))

/-- The transition maps in a Chapter 22 property `(P)` filtration are admissible after forgetting
the differential. -/
instance instStepIsAdmissibleMono {P : DGMod} (F : PropertyPFiltration P) (n : ℕ) :
    IsAdmissibleMono forgetGraded (F.toFiltration.step n) :=
  F.admissible n

/-- The admissibility of all transition maps is available to typeclass search as a single family. -/
instance instStepsAreAdmissibleMono {P : DGMod} (F : PropertyPFiltration P) :
    ∀ n, IsAdmissibleMono forgetGraded (F.toFiltration.step n) :=
  F.admissible

/-- Helper for Lemma 22.28.5: each filtration step is termwise split monic in every degree. -/
theorem stepTermwiseSplitMono {P : DGMod} (F : PropertyPFiltration P) (k : ℕ) (n : ℤ) :
    IsSplitMono ((F.inclusion k).f n) := by
  -- Proof comment: Chapter 22 admissibility of the filtration step is exactly termwise split
  -- monomorphy after forgetting the differential.
  let gradedMap :=
    (dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A)).map (F.inclusion k)
  letI : IsSplitMono gradedMap := F.admissible k
  refine IsSplitMono.mk' ⟨retraction gradedMap n, ?_⟩
  simpa [gradedMap, dgModuleUnderlyingGradedHomSystem] using
    congr_fun (IsSplitMono.id gradedMap) n

/-- Helper for Lemma 22.28.5: the chosen retraction of the degree-`n` filtration step
`(F.inclusion k).f n`. -/
noncomputable def stepTermwiseRetraction {P : DGMod} (F : PropertyPFiltration P) (k : ℕ) (n : ℤ) :
    (F.stage (k + 1)).X n ⟶ (F.stage k).X n :=
  @retraction (ModuleCat A) _ _ _ ((F.inclusion k).f n) (stepTermwiseSplitMono F k n)

/-- Helper for Lemma 22.28.5: the chosen retraction of a degreewise filtration step is a left
inverse. -/
theorem stepTermwiseInclusion_retraction {P : DGMod} (F : PropertyPFiltration P) (k : ℕ) (n : ℤ) :
    (F.inclusion k).f n ≫ stepTermwiseRetraction F k n = 𝟙 ((F.stage k).X n) := by
  -- Proof comment: this is the defining identity of the split-mono retraction chosen above.
  simpa [stepTermwiseRetraction] using
    @IsSplitMono.id (ModuleCat A) _ _ _ ((F.inclusion k).f n) (stepTermwiseSplitMono F k n)

/-- Helper for Lemma 22.28.5: the `k`-th stage admits a finite-support lift into the degree-`n`
telescope coproduct. -/
noncomputable def telescopeDegreewiseStageLift {P : DGMod} (F : PropertyPFiltration P) (n : ℤ) :
    ∀ k : ℕ, (F.stage k).X n ⟶ (F.toFiltration.telescopeShortComplex.X₂).X n
  | 0 => 0
  | k + 1 =>
      let previous :
          (F.stage (k + 1)).X n ⟶ (F.toFiltration.telescopeShortComplex.X₂).X n :=
        stepTermwiseRetraction F k n ≫ telescopeDegreewiseStageLift F n k
      let correction :
          (F.stage (k + 1)).X n ⟶ (F.toFiltration.telescopeShortComplex.X₂).X n :=
        (𝟙 _ - stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
          ((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n)
      previous + correction

/-- Helper for Lemma 22.28.5: the complement projector associated to a split filtration step is
killed after precomposition by that step. -/
theorem stepTermwiseProjectorCancellation {P : DGMod} (F : PropertyPFiltration P) (k : ℕ)
    (n : ℤ) :
    (F.inclusion k).f n ≫
        (𝟙 ((F.stage (k + 1)).X n) - stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) =
      0 := by
  -- Proof comment: expand the subtraction after composition and then replace the middle composite
  -- by the chosen left inverse identity.
  have hmiddle :
      (F.inclusion k).f n ≫ stepTermwiseRetraction F k n ≫ (F.inclusion k).f n =
        𝟙 ((F.stage k).X n) ≫ (F.inclusion k).f n := by
    -- Proof comment: reassociate once so the chosen retraction identity can be applied directly.
    calc
      (F.inclusion k).f n ≫ stepTermwiseRetraction F k n ≫ (F.inclusion k).f n =
        ((F.inclusion k).f n ≫ stepTermwiseRetraction F k n) ≫ (F.inclusion k).f n := by
          simp only [Category.assoc]
      _ = 𝟙 ((F.stage k).X n) ≫ (F.inclusion k).f n := by
          rw [stepTermwiseInclusion_retraction]
  calc
    (F.inclusion k).f n ≫
        (𝟙 ((F.stage (k + 1)).X n) - stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) =
      (F.inclusion k).f n ≫ 𝟙 ((F.stage (k + 1)).X n) -
        ((F.inclusion k).f n ≫ stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) := by
          simp only [Preadditive.comp_sub]
    _ =
      (F.inclusion k).f n ≫ 𝟙 ((F.stage (k + 1)).X n) -
        (𝟙 ((F.stage k).X n) ≫ (F.inclusion k).f n) := by
          rw [hmiddle]
    _ = 0 := by
      simp

/-- Helper for Lemma 22.28.5: the recursive stage lifts are compatible with the successor maps of
the filtration. -/
theorem telescopeDegreewiseStageLift_compat {P : DGMod} (F : PropertyPFiltration P) (n : ℤ)
    (k : ℕ) :
    (F.inclusion k).f n ≫ telescopeDegreewiseStageLift F n (k + 1) =
      telescopeDegreewiseStageLift F n k := by
  -- Route correction: the recursive section construction was already correct; the missing step was
  -- the exact projector-cancellation normal form needed to make the correction summand vanish.
  -- Proof comment: expand the successor-stage lift once; the previous summand collapses through the
  -- chosen retraction, while the correction summand is killed by the complement projector lemma.
  have hprevious :
      ((F.inclusion k).f n ≫ stepTermwiseRetraction F k n) ≫ telescopeDegreewiseStageLift F n k =
        (𝟙 ((F.stage k).X n)) ≫ telescopeDegreewiseStageLift F n k := by
    -- Proof comment: this is the lift-level version of the chosen retraction identity.
    exact congrArg (fun t ↦ t ≫ telescopeDegreewiseStageLift F n k)
      (stepTermwiseInclusion_retraction F k n)
  have hcorrection :
      ((F.inclusion k).f n ≫
          (𝟙 ((F.stage (k + 1)).X n) -
            stepTermwiseRetraction F k n ≫ (F.inclusion k).f n)) ≫
        ((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n) =
      0 ≫ ((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n) := by
    -- Proof comment: after precomposition by the filtration step, the correction projector is zero.
    exact congrArg (fun t ↦ t ≫ ((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n))
      (stepTermwiseProjectorCancellation F k n)
  have hzeroSigma :
      (0 : (F.stage k).X n ⟶ (F.stage (k + 1)).X n) ≫
          ((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n) =
        0 := by
    -- Proof comment: the correction term is annihilated before it reaches the coproduct summand.
    simpa using
      (zero_comp ((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n) :
        (0 : (F.stage k).X n ⟶ (F.stage (k + 1)).X n) ≫
            ((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n) =
          0)
  calc
    (F.inclusion k).f n ≫ telescopeDegreewiseStageLift F n (k + 1) =
      (F.inclusion k).f n ≫
          (stepTermwiseRetraction F k n ≫ telescopeDegreewiseStageLift F n k +
            (𝟙 ((F.stage (k + 1)).X n) -
                stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
              ((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n)) := by
            rfl
    _ =
      ((F.inclusion k).f n ≫ stepTermwiseRetraction F k n) ≫
          telescopeDegreewiseStageLift F n k +
        ((F.inclusion k).f n ≫
            (𝟙 ((F.stage (k + 1)).X n) -
              stepTermwiseRetraction F k n ≫ (F.inclusion k).f n)) ≫
          ((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n) := by
            simp only [Preadditive.comp_add, Category.assoc]
    _ =
      ((F.inclusion k).f n ≫ stepTermwiseRetraction F k n) ≫ telescopeDegreewiseStageLift F n k +
        0 ≫ ((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n) := by
          rw [hcorrection]
    _ =
      (𝟙 ((F.stage k).X n)) ≫ telescopeDegreewiseStageLift F n k +
        0 ≫ ((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n) := by
          rw [hprevious]
    _ = telescopeDegreewiseStageLift F n k + 0 := by
      calc
        (𝟙 ((F.stage k).X n)) ≫ telescopeDegreewiseStageLift F n k +
            0 ≫ ((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n) =
          telescopeDegreewiseStageLift F n k +
            0 ≫ ((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n) := by
              simp
        _ = telescopeDegreewiseStageLift F n k + 0 := by
              exact congrArg (fun t ↦ telescopeDegreewiseStageLift F n k + t) hzeroSigma
    _ = telescopeDegreewiseStageLift F n k := by
      simp

/-- Helper for Lemma 22.28.5: the stage lifts form a cocone on the evaluated filtration diagram. -/
theorem telescopeDegreewiseStageLift_naturality {P : DGMod} (F : PropertyPFiltration P) (n : ℤ) :
    ∀ k : ℕ,
      (F.toFiltration.diagram ⋙ HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n).map
          (homOfLE (Nat.le_succ k)) ≫
        telescopeDegreewiseStageLift F n (k + 1) =
          telescopeDegreewiseStageLift F n k := by
  intro k
  -- Proof comment: evaluating the successor map in the sequence diagram recovers the filtration
  -- inclusion in degree `n`.
  simpa [_root_.PropertyPFiltration.diagram, Functor.ofSequence_map_homOfLE_succ] using
    telescopeDegreewiseStageLift_compat F n k

/-- Helper for Lemma 22.28.5: the `(k + 1)`-st coproduct summand maps to the ambient module under
the telescope augmentation by the expected cocone map. -/
theorem sigmaLeg_comp_telescopeAugmentation {P : DGMod} (F : PropertyPFiltration P) (n : ℤ)
    (k : ℕ) :
    ((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n) ≫
        ((F.toFiltration.telescopeShortComplex.g).f n) =
      (F.coconeApp (k + 1)).f n := by
  -- Proof comment: first use the universal coproduct computation for `Sigma.desc` in the
  -- cochain-complex category, then evaluate the resulting morphism equality in degree `n`.
  have hSigma :
      Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1) ≫ F.toFiltration.telescopeShortComplex.g =
        F.coconeApp (k + 1) := by
    simpa [_root_.PropertyPFiltration.telescopeShortComplex,
      CochainComplex.PropertyPFiltration.coconeApp] using
      (Limits.Sigma.ι_desc (p := F.toFiltration.toCocone.app) (k + 1))
  exact congrArg (fun f ↦ f.f n) hSigma

/-- Helper for Lemma 22.28.5: each stage lift still lands in the ambient module after applying the
telescope augmentation in degree `n`. -/
theorem telescopeDegreewiseStageLift_compAugmentation {P : DGMod} (F : PropertyPFiltration P)
    (n : ℤ) :
    ∀ k : ℕ,
      telescopeDegreewiseStageLift F n k ≫ ((F.toFiltration.telescopeShortComplex.g).f n) =
        (F.coconeApp k).f n := by
  intro k
  induction k with
  | zero =>
      -- Proof comment: the initial stage is zero, so both maps out of it vanish.
      have hzero : IsZero ((F.stage 0).X n) := by
        exact (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n).map_isZero F.stageZero
      exact hzero.eq_of_src _ _
  | succ k ih =>
      -- Route correction: use explicit congruence steps for the previous and correction summands,
      -- rather than asking `rw` to normalize both summands under addition and reassociation.
      have hcocone :
          (F.inclusion k).f n ≫ (F.coconeApp (k + 1)).f n = (F.coconeApp k).f n := by
        -- Proof comment: the filtration cocone is natural with respect to the successor map.
        simpa [CochainComplex.PropertyPFiltration.coconeApp, _root_.PropertyPFiltration.diagram,
          Functor.ofSequence_map_homOfLE_succ] using
          congrArg (fun f ↦ f.f n)
            (F.toFiltration.toCocone.naturality (homOfLE (Nat.le_succ k)))
      have hpreviousAug :
          stepTermwiseRetraction F k n ≫
              (telescopeDegreewiseStageLift F n k ≫
                ((F.toFiltration.telescopeShortComplex.g).f n)) =
            stepTermwiseRetraction F k n ≫ (F.coconeApp k).f n := by
        -- Proof comment: the induction hypothesis identifies the previous summand after
        -- augmentation.
        exact congrArg (fun t ↦ stepTermwiseRetraction F k n ≫ t) ih
      have hcorrectionAug :
          (𝟙 ((F.stage (k + 1)).X n) -
              stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
              (((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n) ≫
                ((F.toFiltration.telescopeShortComplex.g).f n)) =
            (𝟙 ((F.stage (k + 1)).X n) -
                stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
              (F.coconeApp (k + 1)).f n := by
        -- Proof comment: the correction summand uses the evaluated coproduct-leg formula for the
        -- telescope augmentation.
        exact congrArg
          (fun t ↦
            (𝟙 ((F.stage (k + 1)).X n) -
                stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫ t)
          (sigmaLeg_comp_telescopeAugmentation F n k)
      have hretCocone :
          stepTermwiseRetraction F k n ≫ (F.coconeApp k).f n =
            stepTermwiseRetraction F k n ≫
              ((F.inclusion k).f n ≫ (F.coconeApp (k + 1)).f n) := by
        -- Proof comment: rewrite the predecessor cocone map through the successor cocone map.
        exact congrArg (fun t ↦ stepTermwiseRetraction F k n ≫ t) hcocone.symm
      have hsplit :
          stepTermwiseRetraction F k n ≫ (F.inclusion k).f n +
              (𝟙 ((F.stage (k + 1)).X n) -
                stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) =
            𝟙 ((F.stage (k + 1)).X n) := by
        -- Proof comment: the retraction projector and its complement add up to the identity.
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      -- Proof comment: expand the recursive lift once, identify both summands after augmentation,
      -- rewrite the predecessor cocone map through cocone naturality, and then recombine the
      -- projector with its complement.
      calc
        telescopeDegreewiseStageLift F n (k + 1) ≫ ((F.toFiltration.telescopeShortComplex.g).f n) =
          (stepTermwiseRetraction F k n ≫ telescopeDegreewiseStageLift F n k +
              (𝟙 ((F.stage (k + 1)).X n) -
                  stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
                ((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n)) ≫
              ((F.toFiltration.telescopeShortComplex.g).f n) := by
                rfl
        _ =
          stepTermwiseRetraction F k n ≫
              (telescopeDegreewiseStageLift F n k ≫
                ((F.toFiltration.telescopeShortComplex.g).f n)) +
            (𝟙 ((F.stage (k + 1)).X n) -
                stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
              (((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n) ≫
                ((F.toFiltration.telescopeShortComplex.g).f n)) := by
                  simp only [Preadditive.add_comp, Category.assoc]
        _ =
          stepTermwiseRetraction F k n ≫ (F.coconeApp k).f n +
            (𝟙 ((F.stage (k + 1)).X n) -
                stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
              (F.coconeApp (k + 1)).f n := by
                calc
                  stepTermwiseRetraction F k n ≫
                      (telescopeDegreewiseStageLift F n k ≫
                        ((F.toFiltration.telescopeShortComplex.g).f n)) +
                    (𝟙 ((F.stage (k + 1)).X n) -
                        stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
                      (((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n) ≫
                        ((F.toFiltration.telescopeShortComplex.g).f n)) =
                    stepTermwiseRetraction F k n ≫ (F.coconeApp k).f n +
                      (𝟙 ((F.stage (k + 1)).X n) -
                          stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
                        (((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n) ≫
                          ((F.toFiltration.telescopeShortComplex.g).f n)) := by
                            exact congrArg
                              (fun t ↦
                                t +
                                  (𝟙 ((F.stage (k + 1)).X n) -
                                      stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
                                    (((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n) ≫
                                      ((F.toFiltration.telescopeShortComplex.g).f n)))
                              hpreviousAug
                  _ =
                    stepTermwiseRetraction F k n ≫ (F.coconeApp k).f n +
                      (𝟙 ((F.stage (k + 1)).X n) -
                          stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
                        (F.coconeApp (k + 1)).f n := by
                          exact congrArg
                            (fun t ↦ stepTermwiseRetraction F k n ≫ (F.coconeApp k).f n + t)
                            hcorrectionAug
        _ =
          stepTermwiseRetraction F k n ≫
              ((F.inclusion k).f n ≫ (F.coconeApp (k + 1)).f n) +
            (𝟙 ((F.stage (k + 1)).X n) -
                stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
              (F.coconeApp (k + 1)).f n := by
                exact congrArg
                  (fun t ↦
                    t +
                      (𝟙 ((F.stage (k + 1)).X n) -
                          stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
                        (F.coconeApp (k + 1)).f n)
                  hretCocone
        _ =
          ((stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) +
              (𝟙 ((F.stage (k + 1)).X n) -
                stepTermwiseRetraction F k n ≫ (F.inclusion k).f n)) ≫
            (F.coconeApp (k + 1)).f n := by
              calc
                stepTermwiseRetraction F k n ≫
                    ((F.inclusion k).f n ≫ (F.coconeApp (k + 1)).f n) +
                  (𝟙 ((F.stage (k + 1)).X n) -
                      stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
                    (F.coconeApp (k + 1)).f n =
                  ((stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
                      (F.coconeApp (k + 1)).f n) +
                    (𝟙 ((F.stage (k + 1)).X n) -
                        stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
                      (F.coconeApp (k + 1)).f n := by
                        simp only [Category.assoc]
                _ =
                  ((stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) +
                      (𝟙 ((F.stage (k + 1)).X n) -
                        stepTermwiseRetraction F k n ≫ (F.inclusion k).f n)) ≫
                    (F.coconeApp (k + 1)).f n := by
                      rw [← Preadditive.add_comp]
        _ = (𝟙 ((F.stage (k + 1)).X n)) ≫ (F.coconeApp (k + 1)).f n := by
              rw [hsplit]
        _ = (F.coconeApp (k + 1)).f n := by
              simp

/-- Helper for Lemma 22.28.5: the stage lifts define a cocone on the degree-`n` filtration
diagram with values in the telescope coproduct. -/
noncomputable def telescopeDegreewiseLiftCocone {P : DGMod} (F : PropertyPFiltration P) (n : ℤ) :
    Cocone (F.toFiltration.diagram ⋙ HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n) :=
  Cocone.mk _ <|
    NatTrans.ofSequence
      (fun k ↦ telescopeDegreewiseStageLift F n k)
      (telescopeDegreewiseStageLift_naturality F n)

/-- Helper for Lemma 22.28.5: descending the stage lifts along the evaluated colimit cocone gives
a section of the telescope augmentation in degree `n`. -/
noncomputable def telescopeDegreewiseSection {P : DGMod} (F : PropertyPFiltration P) (n : ℤ) :
    P.X n ⟶ (F.toFiltration.telescopeShortComplex.X₂).X n :=
  (isColimitOfPreserves
      (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n)
      F.toFiltration.isColimit).desc
    (telescopeDegreewiseLiftCocone F n)

/-- Helper for Lemma 22.28.5: on each filtration stage, the descended degreewise section agrees
with the recursive stage lift. -/
theorem telescopeDegreewiseSection_fac {P : DGMod} (F : PropertyPFiltration P) (n : ℤ) (k : ℕ) :
    (F.coconeApp k).f n ≫ telescopeDegreewiseSection F n =
      telescopeDegreewiseStageLift F n k := by
  -- Proof comment: this is exactly the universal property of the colimit cocone after evaluation.
  simpa [telescopeDegreewiseSection, telescopeDegreewiseLiftCocone,
    CochainComplex.PropertyPFiltration.coconeApp, _root_.PropertyPFiltration.cocone] using
    (isColimitOfPreserves
      (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n)
      F.toFiltration.isColimit).fac
        (telescopeDegreewiseLiftCocone F n) k

/-- Helper for Lemma 22.28.5: the descended degreewise section is a right inverse to the telescope
augmentation. -/
theorem telescopeDegreewiseSection_rightInv {P : DGMod} (F : PropertyPFiltration P) (n : ℤ) :
    telescopeDegreewiseSection F n ≫ ((F.toFiltration.telescopeShortComplex.g).f n) =
      𝟙 (P.X n) := by
  let hcolim :=
    isColimitOfPreserves
      (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n)
      F.toFiltration.isColimit
  -- Proof comment: compare both endomorphisms of `P.X n` after precomposing with every stage map
  -- of the evaluated colimit cocone.
  apply hcolim.hom_ext
  intro k
  calc
    (F.coconeApp k).f n ≫ telescopeDegreewiseSection F n ≫
        ((F.toFiltration.telescopeShortComplex.g).f n) =
      telescopeDegreewiseStageLift F n k ≫
        ((F.toFiltration.telescopeShortComplex.g).f n) := by
          simpa [Category.assoc] using
            congrArg
              (fun t =>
                t ≫ ((F.toFiltration.telescopeShortComplex.g).f n))
              (telescopeDegreewiseSection_fac F n k)
    _ = (F.coconeApp k).f n := telescopeDegreewiseStageLift_compAugmentation F n k
    _ = (F.coconeApp k).f n ≫ 𝟙 (P.X n) := by simp

/-- Helper for Lemma 22.28.5: evaluating the telescope short exact sequence in degree `n`
produces a short exact sequence of `A`-modules. -/
theorem telescopeDegreewiseShortExact [HasColimitsOfShape ℕ DGMod]
    [HasExactColimitsOfShape ℕ DGMod]
    {P : DGMod} (F : PropertyPFiltration P) (n : ℤ) :
    (F.toFiltration.telescopeShortComplex.map
      (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n)).ShortExact := by
  -- Proof comment: exactness is preserved by the evaluation functor.
  simpa [CategoryTheory.CochainComplex.degreewiseShortComplex] using
    F.toFiltration.telescopeShortExact.map_of_exact
      (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n)

/-- Helper for Lemma 22.28.5: every evaluated telescope short complex is split by the descended
degreewise section. -/
noncomputable def telescopeDegreewiseSplitting [HasColimitsOfShape ℕ DGMod]
    [HasExactColimitsOfShape ℕ DGMod]
    {P : DGMod} (F : PropertyPFiltration P) (n : ℤ) :
    (CategoryTheory.CochainComplex.degreewiseShortComplex F.toFiltration.telescopeShortComplex n).Splitting :=
  ShortComplex.Splitting.ofExactOfSection
      (F.toFiltration.telescopeShortComplex.map
        (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n))
      (telescopeDegreewiseShortExact F n).exact
      (telescopeDegreewiseSection F n)
      (telescopeDegreewiseSection_rightInv F n)
      (telescopeDegreewiseShortExact F n).mono_f

/-- Canonical typeclass form of the telescope admissibility assertion for Chapter 22 property
`(P)` filtrations. -/
instance instTelescopeIsAdmissibleShortExact [HasColimitsOfShape ℕ DGMod]
    [HasExactColimitsOfShape ℕ DGMod]
    [PreservesColimitsOfShape (Discrete ℕ) forgetGraded]
    [PreservesColimitsOfShape ℕ forgetGraded]
    {P : DGMod} (F : PropertyPFiltration P) :
    IsAdmissibleShortExact forgetGraded F.toFiltration.telescopeShortComplex :=
by
  -- Route correction: rather than proving a stronger unused generic admissibility API, build the
  -- Stacks-project DG statement directly from the degreewise splitting criterion.
  refine (CochainComplex.isAdmissibleShortExact_iff_nonempty_degreewiseSplitting
    F.toFiltration.telescopeShortComplex).2 ?_
  refine ⟨fun n ↦ ?_⟩
  exact telescopeDegreewiseSplitting F n

/-- Lemma 22.28.5 (2): a Chapter 22 property `(P)` filtration on a differential graded `A`-module
induces an admissible telescope short exact sequence after forgetting the differential, provided
sequential colimits are exact in `DGMod` and the graded-forgetful functor preserves the relevant
colimits. -/
@[stacks 0FQL]
theorem telescope_gradedSplitting [HasColimitsOfShape ℕ DGMod]
    [HasExactColimitsOfShape ℕ DGMod]
    [PreservesColimitsOfShape (Discrete ℕ) forgetGraded]
    [PreservesColimitsOfShape ℕ forgetGraded]
    {P : DGMod} (F : PropertyPFiltration P) :
    IsAdmissibleShortExact forgetGraded F.toFiltration.telescopeShortComplex := by
  infer_instance

end

end CochainComplex.PropertyPFiltration
