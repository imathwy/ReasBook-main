import Mathlib.LinearAlgebra.Isomorphisms
import stacks_proof.stacks_project.Chap12.Definition_12_24_5
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe uR uPrev uMid uNext

open CategoryTheory
open ModuleCat

namespace FilteredCohomology

section

variable {R : Type uR} [Ring R]
variable {KPrev : Type uPrev} [AddCommGroup KPrev] [Module R KPrev]
variable {Kn : Type uMid} [AddCommGroup Kn] [Module R Kn]
variable {KNext : Type uNext} [AddCommGroup KNext] [Module R KNext]
variable (dPrev : KPrev →ₗ[R] Kn) (dNext : Kn →ₗ[R] KNext)
variable (F : ℤ → Submodule R Kn) (p : ℤ)

local notation "Cycles" => dNext.ker
local notation "Boundaries" => dPrev.range

private noncomputable abbrev boundariesInCycles (hcomp : dNext.comp dPrev = 0) :
    Submodule R Cycles :=
  LinearMap.range <|
    LinearMap.codRestrict Cycles dPrev fun c ↦
      (LinearMap.range_le_ker_iff.mpr hcomp) (LinearMap.mem_range_self dPrev c)

private abbrev Cohomology (hcomp : dNext.comp dPrev = 0) :=
  Cycles ⧸ boundariesInCycles dPrev dNext hcomp

/- Domain-style sampling for `12.24.5.1`:
- primary domain: the induced decreasing filtration on the cohomology quotient
  `ker dNext / im dPrev` of a filtered cochain fragment of `R`-modules;
- sampled declarations in the owner ecosystem:
  `CategoryTheory.DecreasingFiltration`,
  `CategoryTheory.FilteredComplex.inducedCohomologyFiltration`,
  `CategoryTheory.FilteredComplex.inducedCohomologyFiltration_obj`,
  `LinearMap.quotientInfEquivSupQuotient`,
  `LinearMap.quotKerEquivRange`;
- best owner abstraction: the module-level induced filtration
  `FilteredCohomology.inducedCohomologyFiltration` on `ker dNext / im dPrev`, with the quotient
  `FilteredCohomology.step` kept only as the source-facing presentation of its `p`-th stage;
- primitive data: the incoming and outgoing differentials at degree `n`, the middle filtration
  `F`, together with the zero-composite hypothesis `dNext ∘ dPrev = 0` needed for the ambient
  cohomology quotient `ker dNext / im dPrev`, and the antitonicity of `F` needed for the
  filtration structure;
- derived API: the representative submodule `representative`, the source-facing quotient `step`,
  the intrinsic stage image `stageSubmodule`, the second-isomorphism-law bridge
  `cyclesQuotientEquivStep`, and the comparison
  `stepEquivFiltrationStage` from the source quotient to the canonical filtration stage;
- source/core/bridge triage:
  `source-facing`: Equation `(12.24.5.1)`, i.e. the quotient
    `((\ker dNext ∩ F p) + \operatorname{im} dPrev) / \operatorname{im} dPrev`;
  `core/canonical`: the induced decreasing filtration on `ker dNext / im dPrev`;
  `bridge/view`: `cyclesQuotientEquivStep` and `stepEquivFiltrationStage`.

This file should therefore own the induced filtration and expose the textbook quotient only as the
source-facing bridge for its stages, rather than forcing downstream files to rebuild the owner. -/

/-- The representative submodule
`(\ker dNext ∩ F p) + \operatorname{im} dPrev ⊆ K^n` for the `p`-th step of the filtration
induced on cohomology. -/
abbrev representative : Submodule R Kn :=
  Cycles ⊓ F p ⊔ Boundaries

/-- 12.24.5.1: the `p`-th step of the filtration induced on cohomology is represented, in module
language, by the quotient
`((\ker dNext ∩ F p) + \operatorname{im} dPrev) / \operatorname{im} dPrev`. -/
@[stacks 012R]
abbrev step :=
  ↥(representative dPrev dNext F p) ⧸ (Boundaries).submoduleOf (representative dPrev dNext F p)

/-- The representative submodules are antitone in the filtration index. -/
theorem representative_mono {q q' : ℤ} (hqq' : F q' ≤ F q) :
    representative dPrev dNext F q' ≤ representative dPrev dNext F q :=
  sup_le_sup (inf_le_inf le_rfl hqq') le_rfl

private theorem cyclesDenominatorEq :
    Submodule.comap (Submodule.subtype (Cycles ⊓ F p)) (Cycles ⊓ F p) ⊓
        Submodule.comap (Submodule.subtype (Cycles ⊓ F p)) Boundaries =
      (Boundaries ⊓ F p).submoduleOf (Cycles ⊓ F p) := by
  ext x
  change ((x : Kn) ∈ Cycles ⊓ F p ∧ (x : Kn) ∈ Boundaries) ↔
      ((x : Kn) ∈ Boundaries ∧ (x : Kn) ∈ F p)
  constructor
  · intro hx
    exact ⟨hx.2, hx.1.2⟩
  · intro hx
    exact ⟨x.2, hx.1⟩

/-- Companion bridge: the second isomorphism law identifies the quotient
`(\ker dNext ∩ F p) / (\operatorname{im} dPrev ∩ F p)` with the source-facing filtration step
`((\ker dNext ∩ F p) + \operatorname{im} dPrev) / \operatorname{im} dPrev`. -/
noncomputable def cyclesQuotientEquivStep :
    (↥(Cycles ⊓ F p) ⧸ (Boundaries ⊓ F p).submoduleOf (Cycles ⊓ F p)) ≃ₗ[R]
      step dPrev dNext F p := by
  rw [← cyclesDenominatorEq dPrev dNext F p]
  simpa [step, representative, Submodule.submoduleOf, sup_comm] using
    LinearMap.quotientInfEquivSupQuotient (Cycles ⊓ F p) Boundaries

private noncomputable abbrev stageMap (hcomp : dNext.comp dPrev = 0) (q : ℤ) :
    ↥(Cycles ⊓ F q) →ₗ[R] Cohomology dPrev dNext hcomp :=
  (boundariesInCycles dPrev dNext hcomp).mkQ.comp
    (Submodule.inclusion (show Cycles ⊓ F q ≤ Cycles from inf_le_left))

/-- The `q`-th induced filtration stage, viewed as a submodule of the ambient cohomology module
`ker dNext / im dPrev`. -/
noncomputable def stageSubmodule (hcomp : dNext.comp dPrev = 0) (q : ℤ) :
    Submodule R (Cohomology dPrev dNext hcomp) :=
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
    CategoryTheory.DecreasingFiltration (ModuleCat.of R (Cohomology dPrev dNext hcomp)) where
  toFun q :=
    (ModuleCat.subobjectModule (ModuleCat.of R (Cohomology dPrev dNext hcomp))).symm
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
      (ModuleCat.subobjectModule (ModuleCat.of R (Cohomology dPrev dNext hcomp))).symm
        (stageSubmodule dPrev dNext F hcomp q) := by
  rfl

private theorem mem_boundariesInCycles_iff (hcomp : dNext.comp dPrev = 0) (x : Cycles) :
    x ∈ boundariesInCycles dPrev dNext hcomp ↔ (x : Kn) ∈ Boundaries := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by simp [LinearMap.codRestrict_apply]⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, Subtype.ext ?_⟩
    simpa [LinearMap.codRestrict_apply] using hy

private theorem ker_stageMap (hcomp : dNext.comp dPrev = 0) (q : ℤ) :
    LinearMap.ker (stageMap dPrev dNext F hcomp q) =
      (Boundaries ⊓ F q).submoduleOf (Cycles ⊓ F q) := by
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

/-- Equation `(12.24.5.1)`: the source-facing quotient
`((\ker dNext ∩ F q) + \operatorname{im} dPrev) / \operatorname{im} dPrev`
is canonically the underlying module of the `q`-th stage of the induced cohomology filtration. -/
@[stacks 012R]
noncomputable def stepEquivFiltrationStage
    (hcomp : dNext.comp dPrev = 0) (q : ℤ) (hF : Antitone F) :
    step dPrev dNext F q ≃ₗ[R]
      ModuleCat.subobjectModule (ModuleCat.of R (Cohomology dPrev dNext hcomp))
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
        ModuleCat.subobjectModule (ModuleCat.of R (Cohomology dPrev dNext hcomp))
          ((inducedCohomologyFiltration dPrev dNext F hcomp hF).obj q) :=
    LinearEquiv.ofEq _ _ <| by
      simpa using
        congrArg
          (ModuleCat.subobjectModule (ModuleCat.of R (Cohomology dPrev dNext hcomp)))
          (inducedCohomologyFiltration_obj dPrev dNext F hcomp hF q).symm
  exact e₁.trans (e₂.trans e₃)

end

end FilteredCohomology
