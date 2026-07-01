import Mathlib
import stacks_project.Chap12.Definition_12_23_6
import stacks_project.Chap12.«12_24_5_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ModuleCat
open HomologicalComplex.Filtered
open scoped CategoryTheory

noncomputable section

universe uR uM

section

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/- Domain-style sampling for Lemma `12.23.7`:
- primary domain: filtered differential modules and the owner predicates on the associated
  one-object filtered differential object;
- sampled owner declarations in this domain:
  `CategoryTheory.DecreasingFiltration`,
  `CategoryTheory.FilteredObject`,
  `HomologicalComplex.Filtered.weaklyConvergesToHomology`,
  `HomologicalComplex.Filtered.abutsToHomology`,
  `FilteredCohomology.representative`;
- best owner abstraction: the packaged one-object complex in `Fil(ModuleCat R)`, with the Stacks
  Project submodule equalities kept as source-facing criteria;
- primitive data: the differential `d`, the antitone filtration `F`, and the stage-preservation
  proof `hdF`;
- derived API: the weak-convergence and abutment criteria below, obtained by specializing the
  owner predicates to the packaged filtered module, together with the canonical cohomology-step
  representative reused from `FilteredCohomology`;
- source/core/bridge triage:
  `source-facing`: `weakConvergenceCriterion` and `cohomologyFiltrationCriterion`;
  `core/canonical`: `HomologicalComplex.Filtered.{weaklyConvergesToHomology,abutsToHomology}`;
  `bridge/view`: the packaging of a filtered module as a one-object filtered differential object.

The owner predicates already exist upstream, so this file should only keep the source-facing
submodule criteria and the minimal bridge needed to specialize those owners. -/

/-- The pagewise equalities in equations `(12.23.5.2)` and `(12.23.5.1)` that characterize weak
convergence of the spectral sequence associated to a filtered differential module. -/
def weakConvergenceCriterion
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) : Prop :=
  ∀ p : ℤ,
    (⨆ r : ℕ, (F p ⊓ Submodule.map d (F (p - r + 1))) ⊔ F (p + 1)) =
        (LinearMap.range d ⊓ F p) ⊔ F (p + 1) ∧
      ((LinearMap.ker d ⊓ F p) ⊔ F (p + 1)) =
        ⨅ r : ℕ, (F p ⊓ Submodule.comap d (F (p + r))) ⊔ F (p + 1)

/-- The intersection/union equalities of Lemma `12.23.7 (2)` for the filtration induced on
cohomology, expressed on the canonical representatives
`FilteredCohomology.representative d d F p` inside `M`. -/
def cohomologyFiltrationCriterion
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) : Prop :=
  (⨅ p : ℤ, FilteredCohomology.representative d d F p) =
      LinearMap.range d ∧
    (⨆ p : ℤ, FilteredCohomology.representative d d F p) =
      LinearMap.ker d

private noncomputable abbrev toSubobject (S : Submodule R M) :
    Subobject (ModuleCat.of R M) :=
  (ModuleCat.subobjectModule (ModuleCat.of R M)).symm S

private def toFilteredObject (F : ℤ → Submodule R M) (hF : Antitone F) :
    Fil(ModuleCat R) where
  obj := ModuleCat.of R M
  filtration :=
    { toFun := fun p ↦ toSubobject (F (OrderDual.ofDual p))
      monotone' := by
        intro p q hpq
        exact
          (ModuleCat.subobjectModule (ModuleCat.of R M)).symm.monotone
            (show F (OrderDual.ofDual p) ≤ F (OrderDual.ofDual q) from hF hpq) }

variable [LocallySmall (ModuleCat R)] [WellPowered (ModuleCat R)]
  [HasWidePullbacks (ModuleCat R)] [HasCoproducts (ModuleCat R)]
  [InitialMonoClass (ModuleCat R)]

private theorem toSubobject_factors
    (d : M →ₗ[R] M) {S : Submodule R M} (hS : Submodule.map d S ≤ S) :
    (toSubobject S).Factors
      ((toSubobject S).arrow ≫ ModuleCat.ofHom d) := sorry

private def toFilteredEndomorphism
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) :
    toFilteredObject F hF ⟶ toFilteredObject F hF where
  hom := ModuleCat.ofHom d
  preserves := by
    intro p
    simpa [toFilteredObject] using toSubobject_factors d (hdF p)

private def toFilteredDifferentialObject
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) (hd : d.comp d = 0) :
    HomologicalComplex (Fil(ModuleCat R)) (ComplexShape.refl PUnit.{1}) where
  X := fun _ ↦ toFilteredObject F hF
  d := fun _ _ ↦ toFilteredEndomorphism d F hF hdF
  shape := by
    intro i j hij
    cases i
    cases j
    exact False.elim <| hij <| by simp
  d_comp_d' := by
    intro i j k _ _
    change toFilteredEndomorphism d F hF hdF ≫ toFilteredEndomorphism d F hF hdF = 0
    apply FilteredObject.Hom.ext
    ext x
    simpa [toFilteredEndomorphism] using LinearMap.congr_fun hd x

-- Proof sketch: package `(M, d, F)` as the corresponding one-object filtered differential object
-- in `FilteredObject (ModuleCat R)`, then specialize the owner criterion
-- `weaklyConvergesToHomology_iff` from Definition `12.23.6`.
/-- Lemma 12.23.7 (1): for a filtered differential module, weak convergence of the associated
spectral sequence to cohomology is exactly the pair of pagewise equalities `(12.23.5.2)` and
`(12.23.5.1)`. The canonical owner predicate is
`HomologicalComplex.Filtered.weaklyConvergesToHomology`; the right-hand side records its module
theoretic criterion. -/
theorem weaklyConvergesToCohomology_iff
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) (hd : d.comp d = 0) :
    weaklyConvergesToHomology (toFilteredDifferentialObject d F hF hdF hd) ↔
      weakConvergenceCriterion d F := sorry

/-- The induced filtration on `H(M, d)` is separated and exhaustive exactly when the textbook
intersection/union criterion holds for the representatives `Ker(d) ∩ F^p M + Im(d)`. -/
theorem cohomologyFiltrationCriterion_iff_separatedExhaustive
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) (hd : d.comp d = 0) :
    cohomologyFiltrationCriterion d F ↔
      inducedHomologyFiltrationSeparatedExhaustive
        (toFilteredDifferentialObject d F hF hdF hd) := sorry

-- Proof sketch: combine the owner characterization of abutment with the owner description of the
-- induced homology filtration as a decreasing filtration on `H(M, d)`, then identify its stages
-- in `ModuleCat R` with the representatives `Ker(d) ∩ F^p M + Im(d)`.
/-- Lemma 12.23.7 (2): for a filtered differential module, the associated spectral sequence abuts
to cohomology exactly when it weakly converges and the induced cohomology filtration satisfies the
textbook intersection/union criterion on the representatives `Ker(d) ∩ F^p M + Im(d)`. -/
theorem abutsToCohomology_iff
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) (hd : d.comp d = 0) :
    abutsToHomology (toFilteredDifferentialObject d F hF hdF hd) ↔
      weaklyConvergesToHomology (toFilteredDifferentialObject d F hF hdF hd) ∧
        cohomologyFiltrationCriterion d F := by
  rw [abutsToHomology_iff, ← cohomologyFiltrationCriterion_iff_separatedExhaustive d F hF hdF hd]

end
