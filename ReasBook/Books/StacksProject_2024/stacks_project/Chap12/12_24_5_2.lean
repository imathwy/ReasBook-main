import Mathlib.LinearAlgebra.Isomorphisms
import StacksProject_2024.stacks_project.Chap12.Definition_12_19_1

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

/-- Helper for 12.24.5.2: every boundary class is a cycle when `dNext ∘ dPrev = 0`. -/
private theorem dPrev_mem_cycles
    (hcomp : dNext.comp dPrev = 0) (x : KPrev) :
    dPrev x ∈ Cycles := by
  -- Evaluate the vanishing composite on a representative to place boundaries in cycles.
  change dNext (dPrev x) = 0
  simpa [LinearMap.comp_apply] using
    congrArg (fun f : KPrev →ₗ[R] KNext => f x) hcomp

/-- Helper for 12.24.5.2: the boundary submodule viewed inside `ker dNext`. -/
private noncomputable abbrev boundariesInCycles
    (hcomp : dNext.comp dPrev = 0) :
    Submodule R Cycles :=
  LinearMap.range <|
    LinearMap.codRestrict Cycles dPrev (dPrev_mem_cycles dPrev dNext hcomp)

/-- Helper for 12.24.5.2: the ambient cohomology quotient used by `stageSubmodule`. -/
private abbrev ambientCohomology
    (hcomp : dNext.comp dPrev = 0) :=
  Cycles ⧸ boundariesInCycles dPrev dNext hcomp

/-- The representative submodule
`(\ker dNext ∩ F p) + \operatorname{im} dPrev ⊆ K^n` for the `p`-th step of the filtration
induced on cohomology. -/
abbrev representative : Submodule R Kn :=
  Cycles ⊓ F p ⊔ Boundaries

/-- 12.24.5.1: the `p`-th step of the filtration induced on cohomology is represented, in module
language, by the quotient
`((\ker dNext ∩ F p) + \operatorname{im} dPrev) / \operatorname{im} dPrev`. -/
abbrev step :=
  ↥(representative dPrev dNext F p) ⧸ (Boundaries).submoduleOf (representative dPrev dNext F p)

/-- The representative submodules are antitone in the filtration index. -/
theorem representative_mono {q q' : ℤ} (hqq' : F q' ≤ F q) :
    representative dPrev dNext F q' ≤ representative dPrev dNext F q :=
  sup_le_sup (inf_le_inf le_rfl hqq') le_rfl

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

/-- Helper for 12.24.5.2: the concrete map from `Cycles ∩ F q` to cohomology whose range is the
`q`-th induced stage. -/
private noncomputable abbrev stageMap
    (hcomp : dNext.comp dPrev = 0) (q : ℤ) :
    ↥(Cycles ⊓ F q) →ₗ[R] ambientCohomology dPrev dNext hcomp :=
  (boundariesInCycles dPrev dNext hcomp).mkQ.comp
    (Submodule.inclusion (show Cycles ⊓ F q ≤ Cycles from inf_le_left))

/-- Helper for 12.24.5.2: a cycle class lies in the embedded boundaries exactly when its
underlying element lies in `dPrev.range`. -/
private theorem mem_boundariesInCycles_iff
    (hcomp : dNext.comp dPrev = 0) (x : Cycles) :
    x ∈ boundariesInCycles dPrev dNext hcomp ↔ (x : Kn) ∈ Boundaries := by
  -- Unpack membership in the codomain-restricted range to the underlying boundary condition.
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by simp [LinearMap.codRestrict_apply]⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, Subtype.ext ?_⟩
    simpa [LinearMap.codRestrict_apply] using hy

/-- Helper for 12.24.5.2: the kernel of the concrete stage map is the boundary part inside
`Cycles ∩ F q`. -/
private theorem ker_stageMap
    (hcomp : dNext.comp dPrev = 0) (q : ℤ) :
    LinearMap.ker (stageMap dPrev dNext F hcomp q) =
      (Boundaries ⊓ F q).submoduleOf (Cycles ⊓ F q) := by
  -- Identify vanishing in cohomology with lying in the boundary range.
  refine le_antisymm ?_ ?_
  · intro x hx
    change
      (boundariesInCycles dPrev dNext hcomp).mkQ
          ((Submodule.inclusion (show Cycles ⊓ F q ≤ Cycles from inf_le_left)) x) = 0 at hx
    have hxB :
        (x : Kn) ∈ Boundaries := by
      exact
        (mem_boundariesInCycles_iff dPrev dNext hcomp
          ((Submodule.inclusion (show Cycles ⊓ F q ≤ Cycles from inf_le_left)) x)).mp
          ((Submodule.Quotient.mk_eq_zero _).mp hx)
    exact ⟨hxB, x.2.2⟩
  · intro x hx
    change ((x : Kn) ∈ Boundaries ∧ (x : Kn) ∈ F q) at hx
    change
      (boundariesInCycles dPrev dNext hcomp).mkQ
          ((Submodule.inclusion (show Cycles ⊓ F q ≤ Cycles from inf_le_left)) x) = 0
    exact
      (Submodule.Quotient.mk_eq_zero _).mpr <|
        (mem_boundariesInCycles_iff dPrev dNext hcomp
          ((Submodule.inclusion (show Cycles ⊓ F q ≤ Cycles from inf_le_left)) x)).mpr hx.1

private theorem cyclesDenominatorEq (q : ℤ) :
    Submodule.comap (Submodule.subtype (Cycles ⊓ F q)) (Cycles ⊓ F q) ⊓
        Submodule.comap (Submodule.subtype (Cycles ⊓ F q)) Boundaries =
      (Boundaries ⊓ F q).submoduleOf (Cycles ⊓ F q) := by
  ext x
  change ((x : Kn) ∈ Cycles ⊓ F q ∧ (x : Kn) ∈ Boundaries) ↔
      ((x : Kn) ∈ Boundaries ∧ (x : Kn) ∈ F q)
  constructor
  · intro hx
    exact ⟨hx.2, hx.1.2⟩
  · intro hx
    exact ⟨x.2, hx.1⟩

/-- Companion bridge: the second isomorphism law identifies the quotient
`(\ker dNext ∩ F p) / (\operatorname{im} dPrev ∩ F p)` with the source-facing filtration step
`((\ker dNext ∩ F p) + \operatorname{im} dPrev) / \operatorname{im} dPrev`. -/
noncomputable def cyclesQuotientEquivStep (q : ℤ) :
    (↥(Cycles ⊓ F q) ⧸ (Boundaries ⊓ F q).submoduleOf (Cycles ⊓ F q)) ≃ₗ[R]
      step dPrev dNext F q :=
  (Submodule.quotEquivOfEq
      ((Boundaries ⊓ F q).submoduleOf (Cycles ⊓ F q))
      (Submodule.comap (Submodule.subtype (Cycles ⊓ F q)) (Cycles ⊓ F q) ⊓
        Submodule.comap (Submodule.subtype (Cycles ⊓ F q)) Boundaries)
      (cyclesDenominatorEq dPrev dNext F q).symm).trans <|
    by
      simpa [step, representative, Submodule.submoduleOf, sup_comm] using
        (LinearMap.quotientInfEquivSupQuotient (Cycles ⊓ F q) Boundaries)

/-- The `q`-th induced filtration stage, viewed as a submodule of the ambient cohomology module
`ker dNext / im dPrev`. -/
noncomputable def stageSubmodule (hcomp : dNext.comp dPrev = 0) (q : ℤ) :
    Submodule R (ambientCohomology dPrev dNext hcomp) :=
  LinearMap.range (stageMap dPrev dNext F hcomp q)

/-- Monotonicity of the induced cohomology stage submodules. -/
theorem stageSubmodule_mono (hcomp : dNext.comp dPrev = 0) {q q' : ℤ} (hqq' : F q' ≤ F q) :
    stageSubmodule dPrev dNext F hcomp q' ≤ stageSubmodule dPrev dNext F hcomp q := by
  let hstage : Cycles ⊓ F q' ≤ Cycles ⊓ F q := inf_le_inf le_rfl hqq'
  have hmap :
      (stageMap dPrev dNext F hcomp q).comp (Submodule.inclusion hstage) =
        stageMap dPrev dNext F hcomp q' := by
    ext x
    rfl
  simpa [stageSubmodule, hmap] using
    LinearMap.range_comp_le_range
      (Submodule.inclusion hstage)
      (stageMap dPrev dNext F hcomp q)

/-- The induced cohomology stage submodules form a decreasing filtration. -/
theorem stageSubmodule_antitone (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) :
    Antitone (stageSubmodule dPrev dNext F hcomp) := by
  intro q q' hqq'
  exact stageSubmodule_mono dPrev dNext F hcomp (hF hqq')

/-- The induced filtration on the cohomology quotient `ker dNext / im dPrev`, specialized to the
module-valued situation underlying Definition `12.24.5`. -/
noncomputable def inducedCohomologyFiltration
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) :
    CategoryTheory.DecreasingFiltration (ModuleCat.of R (ambientCohomology dPrev dNext hcomp)) where
  toFun q :=
    (ModuleCat.subobjectModule (ModuleCat.of R (ambientCohomology dPrev dNext hcomp))).symm
      (stageSubmodule dPrev dNext F hcomp (OrderDual.ofDual q))
  monotone' := by
    intro q q' hqq'
    exact
      (ModuleCat.subobjectModule _).symm.monotone <|
        (show
          stageSubmodule dPrev dNext F hcomp (OrderDual.ofDual q) ≤
            stageSubmodule dPrev dNext F hcomp (OrderDual.ofDual q') from
          stageSubmodule_antitone dPrev dNext F hcomp hF
            (show OrderDual.ofDual q' ≤ OrderDual.ofDual q from hqq'))

/-- The `q`-th stage of the induced cohomology filtration is the image of the representative map
from `\ker dNext ∩ F q` into `ker dNext / im dPrev`. -/
theorem inducedCohomologyFiltration_obj
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) (q : ℤ) :
    (inducedCohomologyFiltration dPrev dNext F hcomp hF).obj q =
      (ModuleCat.subobjectModule (ModuleCat.of R (ambientCohomology dPrev dNext hcomp))).symm
        (stageSubmodule dPrev dNext F hcomp q) := by
  rfl

/-- Equation `(12.24.5.1)`: the source-facing quotient
`((\ker dNext ∩ F q) + \operatorname{im} dPrev) / \operatorname{im} dPrev`
is canonically the underlying module of the `q`-th stage of the induced cohomology filtration. -/
noncomputable def stepEquivFiltrationStage
    (hcomp : dNext.comp dPrev = 0) (q : ℤ) (hF : Antitone F) :
    step dPrev dNext F q ≃ₗ[R]
      ModuleCat.subobjectModule (ModuleCat.of R (ambientCohomology dPrev dNext hcomp))
        ((inducedCohomologyFiltration dPrev dNext F hcomp hF).obj q) := by
  let e₁ :
      step dPrev dNext F q ≃ₗ[R]
        (↥(Cycles ⊓ F q) ⧸ (Boundaries ⊓ F q).submoduleOf (Cycles ⊓ F q)) :=
    (cyclesQuotientEquivStep dPrev dNext F q).symm
  let e₂ :
      (↥(Cycles ⊓ F q) ⧸ (Boundaries ⊓ F q).submoduleOf (Cycles ⊓ F q)) ≃ₗ[R]
      stageSubmodule dPrev dNext F hcomp q :=
    (Submodule.quotEquivOfEq
        ((Boundaries ⊓ F q).submoduleOf (Cycles ⊓ F q))
        (stageMap dPrev dNext F hcomp q).ker
        (ker_stageMap dPrev dNext F hcomp q).symm).trans
      ((stageMap dPrev dNext F hcomp q).quotKerEquivRange)
  let e₃ :
      stageSubmodule dPrev dNext F hcomp q ≃ₗ[R]
        ModuleCat.subobjectModule (ModuleCat.of R (ambientCohomology dPrev dNext hcomp))
          ((inducedCohomologyFiltration dPrev dNext F hcomp hF).obj q) :=
    LinearEquiv.ofEq _ _ <| by
      simpa using
        congrArg
          (ModuleCat.subobjectModule (ModuleCat.of R (ambientCohomology dPrev dNext hcomp)))
          (inducedCohomologyFiltration_obj dPrev dNext F hcomp hF q).symm
  exact e₁.trans (e₂.trans e₃)

private theorem filtration_succ_le
    (G : ℤ → Submodule R Kn) (q : ℤ) (hG : Antitone G) : G (q + 1) ≤ G q :=
  hG (by omega)

private noncomputable abbrev stepEquivStage
    (hcomp : dNext.comp dPrev = 0) (q : ℤ) (hF : Antitone F) :
    step dPrev dNext F q ≃ₗ[R] stageSubmodule dPrev dNext F hcomp q :=
  (stepEquivFiltrationStage dPrev dNext F hcomp q hF).trans <|
    LinearEquiv.ofEq _ _ <| by
      -- Reindex the owner filtration stage onto the explicit stage submodule used in this file.
      simpa using
        congrArg
          (ModuleCat.subobjectModule
            (ModuleCat.of R (ambientCohomology dPrev dNext hcomp)))
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

/-- Helper for 12.24.5.2: the inclusion of the next stage has the expected image inside the
current stage. -/
private theorem next_stage_submodule_eq_range_inclusion
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) :
    LinearMap.range (Submodule.inclusion (stageSubmodule_succ_le dPrev dNext F p hcomp hF)) =
      Submodule.submoduleOf
        (stageSubmodule dPrev dNext F hcomp (p + 1))
        (stageSubmodule dPrev dNext F hcomp p) := by
  -- Rewrite the inclusion range in the standard `submoduleOf` form.
  simpa [Submodule.submoduleOf] using
    (Submodule.range_inclusion
      (stageSubmodule dPrev dNext F hcomp (p + 1))
      (stageSubmodule dPrev dNext F hcomp p)
      (stageSubmodule_succ_le dPrev dNext F p hcomp hF))

/-- Helper for 12.24.5.2: the cycle-side denominator is the intersection with boundaries inside
`Cycles ⊓ F q`. -/
private theorem cycles_denominator_eq
    (q : ℤ) :
    Submodule.comap (Submodule.subtype (Cycles ⊓ F q)) (Cycles ⊓ F q) ⊓
        Submodule.comap (Submodule.subtype (Cycles ⊓ F q)) Boundaries =
      (Boundaries ⊓ F q).submoduleOf (Cycles ⊓ F q) := by
  ext x
  change ((x : Kn) ∈ Cycles ⊓ F q ∧ (x : Kn) ∈ Boundaries) ↔
      ((x : Kn) ∈ Boundaries ∧ (x : Kn) ∈ F q)
  constructor
  · intro hx
    exact ⟨hx.2, hx.1.2⟩
  · intro hx
    exact ⟨x.2, hx.1⟩

/-- Helper for 12.24.5.2: `cyclesQuotientEquivStep` sends a cycle generator to the corresponding
step generator. -/
private theorem cycles_quotient_equiv_step_apply_mk_cycle
    (q : ℤ) (x : ↥(Cycles ⊓ F q)) :
    cyclesQuotientEquivStep dPrev dNext F q (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        ((Submodule.inclusion
          (show Cycles ⊓ F q ≤ representative dPrev dNext F q from le_sup_left)) x) := by
  -- Collapse the denominator transport first so the owner quotient computation applies verbatim.
  unfold cyclesQuotientEquivStep
  rw [LinearEquiv.trans_apply]
  rw [Submodule.quotEquivOfEq_mk]
  simpa [step, representative, Submodule.submoduleOf, sup_comm] using
    (LinearMap.quotientInfEquivSupQuotient_apply_mk
      (p := Cycles ⊓ F q) (p' := Boundaries) x)

/-- Helper for 12.24.5.2: on a cycle representative, `stepEquivStage` is the ambient cohomology
class of that cycle. -/
private theorem cycles_quotient_equiv_step_symm_apply_mk_cycle
    (q : ℤ) (x : ↥(Cycles ⊓ F q)) :
    (cyclesQuotientEquivStep dPrev dNext F q).symm
        (Submodule.Quotient.mk
          ((Submodule.inclusion
            (show Cycles ⊓ F q ≤ representative dPrev dNext F q from le_sup_left)) x)) =
      Submodule.Quotient.mk x := by
  -- Invert the forward generator formula through the step-side linear equivalence.
  exact
    (LinearEquiv.symm_apply_eq (cyclesQuotientEquivStep dPrev dNext F q)).2 <|
      (cycles_quotient_equiv_step_apply_mk_cycle dPrev dNext F q x).symm

/-- Helper for 12.24.5.2: on a cycle representative, `stepEquivStage` is the ambient cohomology
class of that cycle. -/
private theorem step_ker_transport_apply_mk
    (q : ℤ) (hcomp : dNext.comp dPrev = 0) (x : ↥(Cycles ⊓ F q)) :
    (Submodule.quotEquivOfEq
      ((Boundaries ⊓ F q).submoduleOf (Cycles ⊓ F q))
      (stageMap dPrev dNext F hcomp q).ker
      (ker_stageMap dPrev dNext F hcomp q).symm)
      (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
  -- Rewrite the quotient transport on generators by the owner computation rule.
  simpa using
    (Submodule.quotEquivOfEq_mk
      ((Boundaries ⊓ F q).submoduleOf (Cycles ⊓ F q))
      (stageMap dPrev dNext F hcomp q).ker
      (ker_stageMap dPrev dNext F hcomp q).symm x)

/-- Helper for 12.24.5.2: the middle factor of `stepEquivFiltrationStage` sends a cycle
generator to its ambient cohomology class. -/
private theorem step_equiv_filtration_stage_e₂_apply_mk_cycle
    (q : ℤ) (hcomp : dNext.comp dPrev = 0) (x : ↥(Cycles ⊓ F q)) :
    ((((Submodule.quotEquivOfEq
        ((Boundaries ⊓ F q).submoduleOf (Cycles ⊓ F q))
        (stageMap dPrev dNext F hcomp q).ker
        (ker_stageMap dPrev dNext F hcomp q).symm).trans
          ((stageMap dPrev dNext F hcomp q).quotKerEquivRange))
        (Submodule.Quotient.mk x) : stageSubmodule dPrev dNext F hcomp q) :
      ambientCohomology dPrev dNext hcomp) =
      (boundariesInCycles dPrev dNext hcomp).mkQ
        ((Submodule.inclusion (show Cycles ⊓ F q ≤ Cycles from inf_le_left)) x) := by
  -- Compute the composite equivalence on the canonical quotient generator.
  rw [LinearEquiv.trans_apply]
  rw [step_ker_transport_apply_mk dPrev dNext F q hcomp x]
  rw [LinearMap.quotKerEquivRange_apply_mk]
  rfl

/-- Helper for 12.24.5.2: on a cycle representative, `stepEquivStage` is the ambient cohomology
class of that cycle. -/
private theorem step_equiv_stage_mk_cycle
    (q : ℤ) (hcomp : dNext.comp dPrev = 0) (hF : Antitone F)
    (x : ↥(Cycles ⊓ F q)) :
    ((((stepEquivStage dPrev dNext F hcomp q hF)
        (Submodule.Quotient.mk
          ((Submodule.inclusion
            (show Cycles ⊓ F q ≤ representative dPrev dNext F q from le_sup_left)) x))) :
        stageSubmodule dPrev dNext F hcomp q) :
      ambientCohomology dPrev dNext hcomp) =
      (boundariesInCycles dPrev dNext hcomp).mkQ
        ((Submodule.inclusion (show Cycles ⊓ F q ≤ Cycles from inf_le_left)) x) := by
  -- Route correction: compute the `e₁` inverse-generator step first, then evaluate the middle
  -- `e₂` quotient-to-range bridge; the remaining `ofEq` transports collapse definitionally.
  unfold stepEquivStage
  unfold stepEquivFiltrationStage
  simp only [LinearEquiv.trans_apply]
  rw [cycles_quotient_equiv_step_symm_apply_mk_cycle dPrev dNext F q x]
  -- Change to the concrete range representative, where `quotKerEquivRange_apply_mk` is exact.
  change
    ↑((stageMap dPrev dNext F hcomp q).quotKerEquivRange (Submodule.Quotient.mk x)) =
      (boundariesInCycles dPrev dNext hcomp).mkQ
        ((Submodule.inclusion (show Cycles ⊓ F q ≤ Cycles from inf_le_left)) x)
  rw [LinearMap.quotKerEquivRange_apply_mk]
  rfl

/-- Helper for 12.24.5.2: every representative class is equal to a cycle representative modulo
boundaries. -/
private theorem step_mk_eq_mk_cycle
    (q : ℤ) (x : representative dPrev dNext F q) :
    ∃ c : ↥(Cycles ⊓ F q),
      (Submodule.Quotient.mk x : step dPrev dNext F q) =
        Submodule.Quotient.mk
          ((Submodule.inclusion
            (show Cycles ⊓ F q ≤ representative dPrev dNext F q from le_sup_left)) c) := by
  rcases Submodule.mem_sup.1 x.2 with ⟨c, hc, b, hb, hxb⟩
  refine ⟨⟨c, hc⟩, ?_⟩
  -- The boundary summand dies in the quotient presentation of the step.
  apply (Submodule.Quotient.eq
    (p := Submodule.submoduleOf Boundaries (representative dPrev dNext F q))
    (x := x)
    (y := (Submodule.inclusion
      (show Cycles ⊓ F q ≤ representative dPrev dNext F q from le_sup_left)) ⟨c, hc⟩)).2
  change ((x : Kn) - c) ∈ Boundaries
  have hx : (x : Kn) = c + b := by simpa using hxb.symm
  simpa [hx, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hb

/-- Helper for 12.24.5.2: `stepMap` sends a cycle generator to the same cycle viewed at the
previous stage. -/
private theorem stepMap_mk_cycle
    (hFp : F (p + 1) ≤ F p) (x : ↥(Cycles ⊓ F (p + 1))) :
    stepMap dPrev dNext F p hFp
        (Submodule.Quotient.mk
          ((Submodule.inclusion
            (show Cycles ⊓ F (p + 1) ≤ representative dPrev dNext F (p + 1) from le_sup_left))
            x)) =
      Submodule.Quotient.mk
        ((Submodule.inclusion
          (show Cycles ⊓ F p ≤ representative dPrev dNext F p from le_sup_left))
          ((Submodule.inclusion
            (show Cycles ⊓ F (p + 1) ≤ Cycles ⊓ F p from inf_le_inf le_rfl hFp)) x)) := by
  -- Unfold the quotient lift only on the canonical cycle generator.
  rw [stepMap, Submodule.liftQ_apply]
  rfl

/-- Helper for 12.24.5.2: after coercing to ambient cohomology, `stepMap` followed by the current
stage equivalence agrees on quotient generators with the next-stage equivalence. -/
private theorem step_equiv_stage_naturality_on_mk
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F)
    (hFp : F (p + 1) ≤ F p) (x : representative dPrev dNext F (p + 1)) :
    ((((stepEquivStage dPrev dNext F hcomp p hF)
        (stepMap dPrev dNext F p hFp (Submodule.Quotient.mk x))) :
        stageSubmodule dPrev dNext F hcomp p) :
      ambientCohomology dPrev dNext hcomp) =
      ((((stepEquivStage dPrev dNext F hcomp (p + 1) hF)
        (Submodule.Quotient.mk x)) :
        stageSubmodule dPrev dNext F hcomp (p + 1)) :
      ambientCohomology dPrev dNext hcomp) := by
  rcases step_mk_eq_mk_cycle dPrev dNext F (p + 1) x with ⟨c, hc⟩
  -- Replace the source representative by its cycle component before comparing stages.
  rw [hc]
  rw [stepMap_mk_cycle dPrev dNext F p hFp]
  -- Both sides now reduce to the same ambient cohomology class of the same cycle.
  rw [step_equiv_stage_mk_cycle dPrev dNext F p hcomp hF]
  rw [step_equiv_stage_mk_cycle dPrev dNext F (p + 1) hcomp hF]
  rfl

/-- Helper for 12.24.5.2: transporting `stepMap` across `stepEquivStage` is the canonical
inclusion of the next stage into the current one. -/
private theorem step_equiv_stage_naturality
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) :
    let hFp : F (p + 1) ≤ F p := filtration_succ_le F p hF
    let eSucc : step dPrev dNext F (p + 1) ≃ₗ[R]
        stageSubmodule dPrev dNext F hcomp (p + 1) :=
      stepEquivStage dPrev dNext F hcomp (p + 1) hF
    let eCurr : step dPrev dNext F p ≃ₗ[R]
        stageSubmodule dPrev dNext F hcomp p :=
      stepEquivStage dPrev dNext F hcomp p hF
    (eCurr : _ →ₗ[R] _).comp (stepMap dPrev dNext F p hFp) =
      (Submodule.inclusion (stageSubmodule_succ_le dPrev dNext F p hcomp hF)).comp
        (eSucc : _ →ₗ[R] _) := by
  dsimp
  ext z
  -- The quotient generator comparison already computes both compositions in ambient cohomology.
  simpa [LinearMap.comp_apply] using
    step_equiv_stage_naturality_on_mk dPrev dNext F p hcomp hF
      (filtration_succ_le F p hF) z

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
  dsimp
  let hFp : F (p + 1) ≤ F p := filtration_succ_le F p hF
  let f := stepMap dPrev dNext F p hFp
  let eCurr : step dPrev dNext F p ≃ₗ[R] stageSubmodule dPrev dNext F hcomp p :=
    stepEquivStage dPrev dNext F hcomp p hF
  let eSucc : step dPrev dNext F (p + 1) ≃ₗ[R]
      stageSubmodule dPrev dNext F hcomp (p + 1) :=
    stepEquivStage dPrev dNext F hcomp (p + 1) hF
  -- Route correction: identify the transported step map with the canonical stage inclusion first,
  -- then compute the image by `range_comp` and surjectivity of the next-stage equivalence.
  calc
    Submodule.map (eCurr : _ →ₗ[R] _) (LinearMap.range f) =
        LinearMap.range ((eCurr : _ →ₗ[R] _).comp f) := by
      rw [← LinearMap.range_comp]
    _ =
        LinearMap.range
          ((Submodule.inclusion (stageSubmodule_succ_le dPrev dNext F p hcomp hF)).comp
            (eSucc : _ →ₗ[R] _)) := by
      rw [step_equiv_stage_naturality dPrev dNext F p hcomp hF]
    _ =
        Submodule.map
          (Submodule.inclusion (stageSubmodule_succ_le dPrev dNext F p hcomp hF))
          (LinearMap.range (eSucc : _ →ₗ[R] _)) := by
      rw [LinearMap.range_comp]
    _ =
        Submodule.map
          (Submodule.inclusion (stageSubmodule_succ_le dPrev dNext F p hcomp hF))
          ⊤ := by
      rw [LinearMap.range_eq_top.2 eSucc.surjective]
    _ =
        LinearMap.range (Submodule.inclusion (stageSubmodule_succ_le dPrev dNext F p hcomp hF)) := by
      rw [Submodule.map_top]
    _ =
        Submodule.submoduleOf
          (stageSubmodule dPrev dNext F hcomp (p + 1))
          (stageSubmodule dPrev dNext F hcomp p) := by
      exact next_stage_submodule_eq_range_inclusion dPrev dNext F p hcomp hF

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
      ModuleCat.of R (ambientCohomology dPrev dNext hcomp) :=
    ModuleCat.ofHom (Stage (p + 1)).subtype
  let jCurr : ModuleCat.of R ↥(Stage p) ⟶
      ModuleCat.of R (ambientCohomology dPrev dNext hcomp) :=
    ModuleCat.ofHom (Stage p).subtype
  let ι : ModuleCat.of R ↥(Stage (p + 1)) ⟶ ModuleCat.of R ↥(Stage p) :=
    ModuleCat.ofHom (Submodule.inclusion hstage)
  haveI : Mono jSucc :=
    (ModuleCat.mono_iff_injective _).mpr fun x y h ↦ Subtype.ext h
  let eSucc :
      (H.obj (p + 1) : ModuleCat R) ≅
        ModuleCat.of R ↥(Stage (p + 1)) := by
    -- Identify the owner-side stage object with the concrete submodule carrier.
    simpa [H, inducedCohomologyFiltration] using
      (Subobject.underlyingIso jSucc)
  haveI : Mono jCurr :=
    (ModuleCat.mono_iff_injective _).mpr fun x y h ↦ Subtype.ext h
  let eCurr :
      (H.obj p : ModuleCat R) ≅ ModuleCat.of R ↥(Stage p) := by
    -- The same identification for the current filtration stage.
    simpa [H, inducedCohomologyFiltration] using
      (Subobject.underlyingIso jCurr)
  have hι : ι ≫ jCurr = jSucc := by
    -- Both composites are the inclusion of the smaller stage into ambient cohomology.
    ext x
    rfl
  have hstageInclusion :
      H.stageInclusion p = eSucc.hom ≫ ι ≫ eCurr.inv := by
    have hmk :
        Subobject.ofLE _ _ (Subobject.mk_le_mk_of_comm ι hι) =
          (Subobject.underlyingIso jSucc).hom ≫ ι ≫ (Subobject.underlyingIso jCurr).inv :=
      Subobject.ofLE_mk_le_mk_of_comm ι hι
    simpa [H, ι, eSucc, eCurr, DecreasingFiltration.stageInclusion, inducedCohomologyFiltration]
      using hmk
  have hcomm : H.stageInclusion p ≫ eCurr.hom = eSucc.hom ≫ ι := by
    -- Rewrite the abstract stage inclusion through the concrete submodule identifications.
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

/-- 12.24.5.2: assume `dNext ∘ dPrev = 0` and that `F` is a decreasing filtration. The `p`-th
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
