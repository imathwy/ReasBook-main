import stacks_project.Chap12.«12_24_5_1»

-- Declarations for this item will be appended below by the statement pipeline.

universe uR uPrev uMid uNext

open CategoryTheory
open CategoryTheory.Limits
open ModuleCat

namespace FilteredCohomology

section

variable {R : Type uR} [Ring R]
variable {KPrev : Type uPrev} [AddCommGroup KPrev] [Module R KPrev]
variable {Kn : Type uMid} [AddCommGroup Kn] [Module R Kn]
variable {KNext : Type uNext} [AddCommGroup KNext] [Module R KNext]

variable (dPrev : KPrev →ₗ[R] Kn) (dNext : Kn →ₗ[R] KNext)
variable (F : ℤ → Submodule R Kn) (p : ℤ)

/- Domain-style sampling for `12.24.5.2`:
- primary domain: the graded piece of the filtration induced on cohomology by a filtered module,
  together with the second and third isomorphism theorems for submodules;
- sampled owner declarations in this domain:
  `CategoryTheory.DecreasingFiltration.gradedPiece`,
  `FilteredCohomology.step`,
  `Submodule.quotientQuotientEquivQuotient`,
  `LinearMap.quotKerEquivRange`;
- best owner abstraction: the decreasing filtration on the ambient cohomology module, with
  `FilteredCohomology.step` retained only as the source-facing quotient-step presentation and
  `CategoryTheory.DecreasingFiltration.gradedPiece` as the canonical owner of the graded piece;
- primitive data: the ambient cohomology quotient `ker dNext / im dPrev`, hence the zero-composite
  hypothesis `dNext ∘ dPrev = 0`, together with the representative submodules
  `FilteredCohomology.representative dPrev dNext F p`;
- derived API: the filtration stages inside cohomology, the bridge
  `stepEquivFiltrationStage`, and the textbook quotient description of the graded piece;
- source/core/bridge triage:
  `source-facing`: the induced cohomology filtration and its `p`-th graded piece;
  `core/canonical`: `CategoryTheory.DecreasingFiltration.gradedPiece`,
    `FilteredCohomology.step`, `Submodule.quotientQuotientEquivQuotient`, and
    `LinearMap.quotKerEquivRange`;
  `bridge/view`: `stepEquivFiltrationStage` and `inducedCohomologyGradedPieceEquiv`.

This file therefore promotes the induced cohomology filtration itself to the public owner, while
the quotient-of-submodules presentation remains a bridge theorem. -/

local notation "Cycles" => dNext.ker
local notation "Boundaries" => dPrev.range
local notation "Cohomology" => ↥Cycles ⧸ Submodule.submoduleOf Boundaries Cycles
local notation "Representative" => representative dPrev dNext F p
local notation "NextRepresentative" => representative dPrev dNext F (p + 1)
local notation "P" => Cycles ⊓ F p
local notation "TextbookDenominator" =>
  Submodule.submoduleOf (Cycles ⊓ F (p + 1)) P ⊔
    Submodule.submoduleOf (Boundaries ⊓ F p) P
local notation "StepDenominator" =>
  Submodule.map
    (Submodule.mkQ (Submodule.submoduleOf Boundaries Representative))
    (Submodule.submoduleOf NextRepresentative Representative)

private theorem filtration_succ_le
    (G : ℤ → Submodule R Kn) (q : ℤ) (hG : Antitone G) : G (q + 1) ≤ G q :=
  hG (by omega)

private noncomputable abbrev stepEquivStage
    (hcomp : dNext.comp dPrev = 0) (q : ℤ) (hF : Antitone F) :
    step dPrev dNext F q ≃ₗ[R] stageSubmodule dPrev dNext F hcomp q :=
  (stepEquivFiltrationStage dPrev dNext F hcomp q hF).trans <|
    LinearEquiv.ofEq _ _ <| by
      simpa using
        congrArg (ModuleCat.subobjectModule (ModuleCat.of R Cohomology))
          (inducedCohomologyFiltration_obj dPrev dNext F hcomp hF q)

private theorem stepMap_hypothesis (hF : F (p + 1) ≤ F p) :
    Submodule.submoduleOf Boundaries NextRepresentative ≤
      LinearMap.ker
        ((Submodule.submoduleOf Boundaries Representative).mkQ.comp
          (Submodule.inclusion
            (representative_mono dPrev dNext F hF))) := by
  intro x hx
  change
    (Submodule.submoduleOf Boundaries Representative).mkQ
        ((Submodule.inclusion
            (representative_mono dPrev dNext F hF)) x) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr <| by
    simpa [LinearMap.mem_range, Submodule.submoduleOf] using hx

private noncomputable def stepMap (hF : F (p + 1) ≤ F p) :
    step dPrev dNext F (p + 1) →ₗ[R] step dPrev dNext F p :=
  (Submodule.submoduleOf Boundaries NextRepresentative).liftQ
    ((Submodule.submoduleOf Boundaries Representative).mkQ.comp
      (Submodule.inclusion
        (representative_mono dPrev dNext F hF)))
    (stepMap_hypothesis dPrev dNext F p hF)

private theorem stepMap_range_eq_denominator (hF : F (p + 1) ≤ F p) :
    LinearMap.range (stepMap dPrev dNext F p hF) = StepDenominator := by
  rw [stepMap, Submodule.range_liftQ]
  let hrepr : NextRepresentative ≤ Representative :=
    representative_mono dPrev dNext F hF
  calc
    LinearMap.range
        ((Submodule.submoduleOf Boundaries Representative).mkQ.comp
          (Submodule.inclusion
            hrepr)) =
      Submodule.map
        (Submodule.mkQ (Submodule.submoduleOf Boundaries Representative))
        (LinearMap.range
          (Submodule.inclusion hrepr)) := by
      rw [LinearMap.range_comp]
    _ = StepDenominator := by
      simpa [Submodule.submoduleOf] using
        congrArg
          (Submodule.map (Submodule.mkQ (Submodule.submoduleOf Boundaries Representative)))
          (Submodule.range_inclusion NextRepresentative Representative hrepr)

private theorem stageSubmodule_succ_le
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) :
    stageSubmodule dPrev dNext F hcomp (p + 1) ≤
      stageSubmodule dPrev dNext F hcomp p :=
  stageSubmodule_antitone dPrev dNext F hcomp hF (by omega)

private theorem stepRange_map_eq_stageSubmoduleSucc
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) :
    let hFp : F (p + 1) ≤ F p := filtration_succ_le F p hF
    let f := stepMap dPrev dNext F p hFp
    let e : step dPrev dNext F p ≃ₗ[R] stageSubmodule dPrev dNext F hcomp p :=
      stepEquivStage dPrev dNext F hcomp p hF
    Submodule.map (e : _ →ₗ[R] _) (LinearMap.range f) =
      Submodule.submoduleOf
        (stageSubmodule dPrev dNext F hcomp (p + 1))
        (stageSubmodule dPrev dNext F hcomp p) := by
  sorry

private theorem cycles_sup_nextRepresentative_eq_representative
    (hF : F (p + 1) ≤ F p) :
    P ⊔ NextRepresentative = Representative := by
  have hstage : Cycles ⊓ F (p + 1) ≤ P := inf_le_inf le_rfl hF
  calc
    P ⊔ NextRepresentative = (P ⊔ (Cycles ⊓ F (p + 1))) ⊔ Boundaries := by
      rw [sup_assoc]
    _ = Representative := by
      rw [sup_eq_left.2 hstage]

private theorem cycles_inf_nextRepresentative_eq_intermediateDenominator
    (hcomp : dNext.comp dPrev = 0) (hF : F (p + 1) ≤ F p) :
    P ⊓ NextRepresentative = (Cycles ⊓ F (p + 1)) ⊔ (Boundaries ⊓ F p) := by
  have hstage : Cycles ⊓ F (p + 1) ≤ P := inf_le_inf le_rfl hF
  have hbound : Boundaries ≤ Cycles := LinearMap.range_le_ker_iff.mpr hcomp
  have hPB : P ⊓ Boundaries = Boundaries ⊓ F p := by
    calc
      P ⊓ Boundaries = Cycles ⊓ (F p ⊓ Boundaries) := by
        simp [inf_left_comm, inf_comm]
      _ = F p ⊓ Boundaries := by
        rw [inf_eq_right.2 (le_trans inf_le_right hbound)]
      _ = Boundaries ⊓ F p := by rw [inf_comm]
  calc
    P ⊓ NextRepresentative = P ⊓ (Boundaries ⊔ (Cycles ⊓ F (p + 1))) := by
      rw [sup_comm]
    _ = (P ⊓ Boundaries) ⊔ (Cycles ⊓ F (p + 1)) := by
      rw [inf_sup_assoc_of_le Boundaries hstage]
    _ = (Cycles ⊓ F (p + 1)) ⊔ (Boundaries ⊓ F p) := by
      rw [hPB, sup_comm]

private theorem quotientInfDenominator_eq_textbookDenominator
    (hcomp : dNext.comp dPrev = 0) (hF : F (p + 1) ≤ F p) :
    Submodule.comap (Submodule.subtype P) P ⊓
        Submodule.comap (Submodule.subtype P) NextRepresentative =
      TextbookDenominator := by
  have hstage : Cycles ⊓ F (p + 1) ≤ P := inf_le_inf le_rfl hF
  have hbound : Boundaries ⊓ F p ≤ P := by
    refine le_inf ?_ inf_le_right
    exact le_trans inf_le_left (LinearMap.range_le_ker_iff.mpr hcomp)
  rw [← Submodule.comap_inf, cycles_inf_nextRepresentative_eq_intermediateDenominator
    dPrev dNext F p hcomp hF]
  exact
    (Submodule.submoduleOf_sup_of_le hstage hbound :
      Submodule.submoduleOf ((Cycles ⊓ F (p + 1)) ⊔ (Boundaries ⊓ F p)) P =
        TextbookDenominator)

private noncomputable def stepQuotientEquiv
    (hcomp : dNext.comp dPrev = 0) (hF : F (p + 1) ≤ F p) :
    (step dPrev dNext F p ⧸ StepDenominator) ≃ₗ[R]
      (↥P ⧸ TextbookDenominator) := by
  have hP :
      (↥P ⧸ TextbookDenominator) ≃ₗ[R]
        (↥Representative ⧸ Submodule.submoduleOf NextRepresentative Representative) :=
    by
      rw [← quotientInfDenominator_eq_textbookDenominator dPrev dNext F p hcomp hF,
        ← cycles_sup_nextRepresentative_eq_representative dPrev dNext F p hF]
      simpa [Submodule.submoduleOf] using
        LinearMap.quotientInfEquivSupQuotient P NextRepresentative
  exact
    (Submodule.quotientQuotientEquivQuotient
        (Submodule.submoduleOf Boundaries Representative)
        (Submodule.submoduleOf NextRepresentative Representative)
        (by
          change
            Submodule.comap (Submodule.subtype Representative) Boundaries ≤
              Submodule.comap (Submodule.subtype Representative) NextRepresentative
          exact Submodule.comap_mono (show Boundaries ≤ NextRepresentative from le_sup_right))).trans
      hP.symm

private noncomputable def gradedPieceQuotientEquiv
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) :
    ((inducedCohomologyFiltration dPrev dNext F hcomp hF).gradedPiece p) ≃ₗ[R]
      (↥(stageSubmodule dPrev dNext F hcomp p) ⧸
        Submodule.submoduleOf
          (stageSubmodule dPrev dNext F hcomp (p + 1))
          (stageSubmodule dPrev dNext F hcomp p)) := by
  let H := inducedCohomologyFiltration dPrev dNext F hcomp hF
  let Stage := stageSubmodule dPrev dNext F hcomp
  let hstage :
      Stage (p + 1) ≤ Stage p :=
    stageSubmodule_antitone dPrev dNext F hcomp hF (by omega)
  let jSucc : ModuleCat.of R ↥(Stage (p + 1)) ⟶
      ModuleCat.of R Cohomology :=
    ModuleCat.ofHom (Stage (p + 1)).subtype
  let jCurr : ModuleCat.of R ↥(Stage p) ⟶
      ModuleCat.of R Cohomology :=
    ModuleCat.ofHom (Stage p).subtype
  let ι : ModuleCat.of R ↥(Stage (p + 1)) ⟶ ModuleCat.of R ↥(Stage p) :=
    ModuleCat.ofHom (Submodule.inclusion hstage)
  haveI : Mono jSucc :=
    (ModuleCat.mono_iff_injective _).mpr fun x y h ↦ Subtype.ext h
  let eSucc :
      (H.obj (p + 1) : ModuleCat R) ≅
        ModuleCat.of R ↥(Stage (p + 1)) := by
    simpa [H, inducedCohomologyFiltration] using
      (Subobject.underlyingIso jSucc)
  haveI : Mono jCurr :=
    (ModuleCat.mono_iff_injective _).mpr fun x y h ↦ Subtype.ext h
  let eCurr :
      (H.obj p : ModuleCat R) ≅ ModuleCat.of R ↥(Stage p) := by
    simpa [H, inducedCohomologyFiltration] using
      (Subobject.underlyingIso jCurr)
  have hstageInclusion :
      H.stageInclusion p = eSucc.hom ≫ ι ≫ eCurr.inv := by
    have hmk :
        Subobject.ofLE _ _ (Subobject.mk_le_mk_of_comm ι (by rfl)) =
          (Subobject.underlyingIso jSucc).hom ≫ ι ≫ (Subobject.underlyingIso jCurr).inv :=
      Subobject.ofLE_mk_le_mk_of_comm ι (by rfl)
    simpa [H, ι, eSucc, eCurr, DecreasingFiltration.stageInclusion, inducedCohomologyFiltration]
      using hmk
  have hcomm : H.stageInclusion p ≫ eCurr.hom = eSucc.hom ≫ ι := by
    rw [hstageInclusion]
    simp
  let ePiece : H.gradedPiece p ≅ cokernel ι := by
    simpa [H, DecreasingFiltration.gradedPiece] using
      (cokernel.mapIso (H.stageInclusion p) ι eSucc eCurr hcomm)
  exact ePiece.toLinearEquiv.trans <|
    (ModuleCat.cokernelIsoRangeQuotient ι).toLinearEquiv.trans <|
      (by
        refine Submodule.quotEquivOfEq _ _ ?_
        simpa [ι, Submodule.submoduleOf] using
          (Submodule.range_inclusion (Stage (p + 1)) (Stage p) hstage))

/- 12.24.5.2: assume `dNext ∘ dPrev = 0` and that `F` is a decreasing filtration. The `p`-th
graded piece of the induced cohomology filtration is canonically the quotient of consecutive
filtration stages inside cohomology, and the second and third isomorphism theorems identify that
graded piece with the textbook quotient
`(\ker dNext ∩ F p) / ((\ker dNext ∩ F (p + 1)) + (range dPrev ∩ F p))`. -/
noncomputable def inducedCohomologyGradedPieceEquiv
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) :
    ((inducedCohomologyFiltration dPrev dNext F hcomp hF).gradedPiece p) ≃ₗ[R]
      (↥P ⧸ TextbookDenominator) := by
  let hFp : F (p + 1) ≤ F p := filtration_succ_le F p hF
  let e : step dPrev dNext F p ≃ₗ[R] stageSubmodule dPrev dNext F hcomp p :=
    stepEquivStage dPrev dNext F hcomp p hF
  exact
    (gradedPieceQuotientEquiv dPrev dNext F p hcomp hF).trans <|
      (Submodule.Quotient.equiv
        (LinearMap.range (stepMap dPrev dNext F p hFp))
        (Submodule.submoduleOf
          (stageSubmodule dPrev dNext F hcomp (p + 1))
          (stageSubmodule dPrev dNext F hcomp p))
        e
        (by
          simpa [hFp, e] using
            stepRange_map_eq_stageSubmoduleSucc dPrev dNext F p hcomp hF)).symm.trans <|
        (Submodule.quotEquivOfEq
          (LinearMap.range (stepMap dPrev dNext F p hFp))
          StepDenominator
          (stepMap_range_eq_denominator dPrev dNext F p hFp)).trans <|
        stepQuotientEquiv dPrev dNext F p hcomp hFp

end

end FilteredCohomology
