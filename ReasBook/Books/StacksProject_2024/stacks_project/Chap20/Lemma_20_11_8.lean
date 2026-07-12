import StacksProject_2024.Chap20.«20_11_0_2»
import StacksProject_2024.Chap21.Lemma_21_10_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.11.8:
- primary domain: Čech-to-sheaf cohomology vanishing for `𝒪_X`-modules on the opens site
  of a ringed space;
- sampled owner declarations:
  `moduleUnderlyingPresheaf`,
  `moduleCechCohomology`,
  `higherCohomology_isZero_of_vanishingHigherCech_on_cofinal_coverings`;
- best owner abstraction: the core owner for higher-Čech vanishing is the site-level theorem
  `higherCohomology_isZero_of_vanishingHigherCech_on_cofinal_coverings` with its
  source-facing cofinal-covering hypotheses on a basis `B` and covering system `Cov`; this file
  keeps the stronger source-facing ringed-space hypothesis “vanishing on every open covering” only
  as a thin bridge to those site-level hypotheses with `B = Set.univ`;
- primitive data: a ringed space `X`, a module `ℱ : RingedSpace.Modules X`, an indexed family of
  opens `𝒰`,
  and an open `U`;
- derived API: coverwise Čech-vanishing, the bridge to the site-level owner, and the resulting
  higher-sheaf-cohomology vanishing theorem.

Source/core/bridge triage:
- `source-facing`: `HasVanishingHigherCechOnOpenCoverings`;
- `core/canonical`: `higherCohomology_isZero_of_vanishingHigherCech_on_cofinal_coverings`;
- `bridge/view`: `moduleUnderlyingPresheaf`, `moduleCechCohomology`, and the comparison from an
  indexed open family to a covering in `(Opens X.carrier) / U`.
-/

/-- An `𝒪_X`-module has vanishing higher Čech cohomology on every indexed family of opens,
equivalently on every open covering of its union, when the positive-degree Čech cohomology of its
underlying additive presheaf always vanishes. -/
def HasVanishingHigherCechOnOpenCoverings
    (ℱ : RingedSpace.Modules X) : Prop :=
  ∀ {ι : Type u} (𝒰 : ι → Opens X.carrier) (p : ℕ),
    0 < p → IsZero (moduleCechCohomology 𝒰 ℱ p)

namespace HasVanishingHigherCechOnOpenCoverings

/-- If `ℱ` has vanishing higher Čech cohomology on every open covering, then the underlying
additive presheaf has vanishing higher slice-site Čech cohomology for every family in `Over U`. -/
theorem isZero_cechCohomology
    {ℱ : RingedSpace.Modules X}
    {U : Opens X.carrier} {ι : Type u}
    (hℱ : HasVanishingHigherCechOnOpenCoverings ℱ)
    (V : ι → Over U) (p : ℕ) (hp : 0 < p) :
    IsZero
      (cechCohomology U V ((moduleUnderlyingPresheaf X).obj ℱ) p) := by
  have h : IsZero (moduleCechCohomology (fun i ↦ (V i).left) ℱ p) := hℱ _ _ hp
  sorry

end HasVanishingHigherCechOnOpenCoverings

private def openCoveringsCov (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Set (FormalCoproduct (Over U)) :=
  {cover : FormalCoproduct (Over U) |
    ((Opens.grothendieckTopology X.carrier).over U).CoversTop cover.obj}

private theorem openCoveringsCov_cover
    {U : Opens X.carrier} {cover : FormalCoproduct (Over U)}
    (hcover : cover ∈ openCoveringsCov X U) :
    ((Opens.grothendieckTopology X.carrier).over U).CoversTop cover.obj := by
  simpa [openCoveringsCov] using hcover

private theorem openCoveringsCov_intersections
    {U : Opens X.carrier} {cover : FormalCoproduct (Over U)}
    (_hcover : cover ∈ openCoveringsCov X U) (n : ℕ)
    (i : cechCoverIntersectionIndex cover n) :
    cechCoverIntersectionObject cover n i ∈ (Set.univ : Set (Opens X.carrier)) := by
  simp

private theorem openCoveringsCov_cofinal
    {U : Opens X.carrier} {ι : Type _} (family : ι → Over U)
    (hfamily : ((Opens.grothendieckTopology X.carrier).over U).CoversTop family) :
    ∃ cover : FormalCoproduct (Over U),
      cover ∈ openCoveringsCov X U ∧
        Nonempty (cover ⟶ FormalCoproduct.mk ι family) := by
  let cover : FormalCoproduct (Over U) := FormalCoproduct.mk ι family
  refine ⟨cover, ?_, ?_⟩
  · simpa [openCoveringsCov, cover] using hfamily
  · change Nonempty (FormalCoproduct.mk ι family ⟶ FormalCoproduct.mk ι family)
    exact ⟨𝟙 _⟩

-- Proof sketch: embed `ℱ` into an injective `𝒪_X`-module `ℐ`, let `ℚ := ℐ/ℱ`, and use
-- Lemmas `20.11.1`, `20.11.7`, `20.10.2`, and `13.20.4` to propagate the higher Čech-vanishing
-- hypothesis from `ℱ` to `ℚ`. The long exact cohomology sequence of
-- `0 ⟶ ℱ ⟶ ℐ ⟶ ℚ ⟶ 0` then gives the vanishing of `H^p(U, ℱ)` for every `p > 0` by induction.
/-- Lemma 20.11.8: if an `𝒪_X`-module has vanishing higher Čech cohomology for every
open covering of every open subset of `X`, then every higher sheaf cohomology group
`H^p(U, ℱ)` with `p > 0` is zero. -/
@[stacks 01EV]
theorem higherCohomology_isZero_of_vanishingHigherCech_on_openCoverings
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (ℱ : RingedSpace.Modules X) (hℱ : HasVanishingHigherCechOnOpenCoverings ℱ)
    (U : Opens X.carrier) (p : ℕ) (hp : 0 < p) :
    IsZero (((moduleUnderlyingSheaf X).obj ℱ).H' p U) := by
  letI : HasProducts AddCommGrpCat.{u} := inferInstance
  have hCoverings :
      Sheaf.HasCofinalCoveringsWithVanishingHigherCech
        ((moduleUnderlyingSheaf X).obj ℱ) Set.univ (openCoveringsCov X) := by
    refine
      { coversTop := ?_
        intersections_mem := ?_
        cofinal := ?_
        higherCech_isZero := ?_ }
    · intro U hU cover hcover
      exact openCoveringsCov_cover hcover
    · intro U hU cover hcover n i
      exact openCoveringsCov_intersections hcover n i
    · intro U hU ι family hfamily
      exact openCoveringsCov_cofinal family hfamily
    · intro U hU cover hcover p hp
      exact hℱ.isZero_cechCohomology cover.obj p hp
  exact
    higherCohomology_isZero_of_vanishingHigherCech_on_cofinal_coverings
      Set.univ
      (openCoveringsCov X)
      ((moduleUnderlyingSheaf X).obj ℱ)
      hCoverings
      (by simp)
      p hp

end AlgebraicGeometry.RingedSpace
