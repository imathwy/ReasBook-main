import StacksProject_2024.stacks_project.Chap20.Lemma_20_9_3
import StacksProject_2024.stacks_project.Chap20.«20_9_0_2»
import StacksProject_2024.stacks_project.Chap20.«20_11_0_2»
import StacksProject_2024.stacks_project.Chap20.Lemma_20_11_2
import StacksProject_2024.stacks_project.Chap20.Lemma_20_11_7
import StacksProject_2024.stacks_project.Chap21.Lemma_21_10_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.11.9:
- primary domain: Čech cohomology of `𝒪_X`-modules on a ringed space, with cofinal
  refinement hypotheses on indexed open covers of basis opens;
- sampled owner declarations:
  `moduleCechCohomology`,
  `IsRefinement`,
  `module_sections_surjective_of_shortExact_of_cofinal_cechH1_zero`;
- best owner abstraction: the source-facing owner here is still the basiswise cofinal-acyclicity
  predicate, but its Čech-vanishing payload should be stated with the chapter owner
  `moduleCechCohomology`, while the cover comparison data should reuse the chapter refinement
  owner `IsRefinement` instead of duplicating its pointwise inequality fields;
- primitive data: a basis open `U ∈ B`, an indexed cover `𝒱` of `U`, a refining family `𝒰`,
  a refinement map `refine` together with `IsRefinement 𝒱 𝒰 refine`, and the basis-membership
  conditions on the members and their finite intersections;
- derived API: vanishing of `moduleCechCohomology 𝒰 ℱ p` in positive degree and the sheaf
  cohomology vanishing conclusion.

Source/core/bridge triage:
- `source-facing`: `HasCofinalBasisCechAcyclicCoverings` and the resulting higher-cohomology
  vanishing theorem;
- `core/canonical`: `moduleCechCohomology`, `IsRefinement`, and
  `((moduleUnderlyingSheaf X).obj ℱ).H' p U`;
- `bridge/view`: the basiswise cofinality hypothesis built from that refinement owner.

The refinement therefore keeps the source-facing basiswise hypothesis, but removes the gratuitous
parallel refinement payload and reuses the chapter-level Čech-cohomology/refinement owners
directly.
-/

/-- An `𝒪_X`-module has a cofinal system of basis-stable coverings on which all positive Čech
cohomology groups vanish. -/
def HasCofinalBasisCechAcyclicCoverings
    (B : Set (Opens X.carrier)) (ℱ : X.Modules) : Prop :=
  ∀ ⦃U : Opens X.carrier⦄, U ∈ B →
    ∀ {κ : Type u} (𝒱 : κ → Opens X.carrier), iSup 𝒱 = U →
      ∃ (ι : Type u) (𝒰 : ι → Opens X.carrier) (refine : ι → κ),
        iSup 𝒰 = U ∧
          IsRefinement 𝒱 𝒰 refine ∧
          (∀ i, 𝒰 i ∈ B) ∧
          (∀ p : ℕ, ∀ σ : Fin (p + 1) → ι, iInf (𝒰 ∘ σ) ∈ B) ∧
          ∀ p : ℕ, 0 < p → IsZero (moduleCechCohomology 𝒰 ℱ p)

-- Proof sketch: this is exactly the defining content of
-- `HasCofinalBasisCechAcyclicCoverings`, evaluated at the basis open `U` and the cover `𝒱`.
/-- Unfolding the cofinal basis-cover hypothesis produces a refining basis-stable cover with
vanishing positive Čech cohomology. -/
theorem hasCofinalBasisCechAcyclicCoverings_apply
    {B : Set (Opens X.carrier)} (ℱ : X.Modules)
    (hℱ : HasCofinalBasisCechAcyclicCoverings B ℱ)
    {U : Opens X.carrier} (hU : U ∈ B)
    {κ : Type u} (𝒱 : κ → Opens X.carrier) (h𝒱 : iSup 𝒱 = U) :
    ∃ (ι : Type u) (𝒰 : ι → Opens X.carrier) (refine : ι → κ),
      iSup 𝒰 = U ∧
        IsRefinement 𝒱 𝒰 refine ∧
        (∀ i, 𝒰 i ∈ B) ∧
        (∀ p : ℕ, ∀ σ : Fin (p + 1) → ι, iInf (𝒰 ∘ σ) ∈ B) ∧
        ∀ p : ℕ, 0 < p → IsZero (moduleCechCohomology 𝒰 ℱ p) :=
  hℱ hU 𝒱 h𝒱

private def openCoverOverHom
    {U : Opens X.carrier} {ι κ : Type u}
    (V : κ → Over U) (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U)
    (refine : ι → κ) (hrefine : IsRefinement (fun j ↦ (V j).left) 𝒰 refine) :
    FormalCoproduct.mk ι (openCoverOver U 𝒰 h𝒰) ⟶ FormalCoproduct.mk κ V where
  f := refine
  φ i := Over.homMk (homOfLE (hrefine i)) (Subsingleton.elim _ _)

private theorem openCoverOver_mem_basis
    {B : Set (Opens X.carrier)} {U : Opens X.carrier} {ι : Type u}
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (hB : ∀ i, 𝒰 i ∈ B) :
    ∀ i, (openCoverOver U 𝒰 h𝒰 i).left ∈ B := by
  intro i
  simpa [openCoverOver] using hB i

private theorem openCoverOver_intersections_mem_basis
    {B : Set (Opens X.carrier)} {U : Opens X.carrier} {ι : Type u}
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U)
    (hB : ∀ p : ℕ, ∀ σ : Fin (p + 1) → ι, iInf (𝒰 ∘ σ) ∈ B)
    (n : ℕ) (i : cechCoverIntersectionIndex (FormalCoproduct.mk ι (openCoverOver U 𝒰 h𝒰)) n) :
    cechCoverIntersectionObject (FormalCoproduct.mk ι (openCoverOver U 𝒰 h𝒰)) n i ∈ B := by
  sorry

private theorem isZero_cechCohomology_openCoverOver
    {U : Opens X.carrier} {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U)
    (ℱ : X.Modules) (p : ℕ) (hzero : IsZero (moduleCechCohomology 𝒰 ℱ p)) :
    IsZero (cechCohomology U (openCoverOver U 𝒰 h𝒰) ((moduleUnderlyingPresheaf X).obj ℱ) p) := by
  sorry

private def basisCechAcyclicCov
    (B : Set (Opens X.carrier)) (ℱ : X.Modules) (U : Opens X.carrier) :
    Set (FormalCoproduct (Over U)) :=
  {cover : FormalCoproduct (Over U) |
    ((Opens.grothendieckTopology X.carrier).over U).CoversTop cover.obj ∧
      (∀ i, (cover.obj i).left ∈ B) ∧
      (∀ n : ℕ, ∀ i : cechCoverIntersectionIndex cover n,
        cechCoverIntersectionObject cover n i ∈ B) ∧
      ∀ p : ℕ, 0 < p →
        IsZero (cechCohomology U cover.obj ((moduleUnderlyingPresheaf X).obj ℱ) p)}

-- Proof sketch: embed `ℱ` into an injective `𝒪_X`-module, use Lemmas `20.11.1` and
-- `20.11.7` together with the basis-stable cover hypothesis to propagate vanishing to the
-- quotient, and then induct on the cohomological degree via the long exact sequence attached to
-- `0 ⟶ ℱ ⟶ ℐ ⟶ ℚ ⟶ 0`. The basis-stable cover hypothesis ensures the Čech complexes for covers
-- in the cofinal system are built from sections on opens still lying in `B`.
/-- Lemma 20.11.9: if an `𝒪_X`-module `ℱ` has vanishing positive Čech cohomology on a cofinal
system of basis-stable coverings of each open `U ∈ B`, then every higher cohomology group
`H^p(U, ℱ)` vanishes for `p > 0` and every `U ∈ B`. -/
@[stacks 01EW]
theorem higherCohomology_isZero_of_vanishingHigherCech_on_basisCoverings
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (B : Set (Opens X.carrier)) (ℱ : X.Modules)
    (hℱ : HasCofinalBasisCechAcyclicCoverings B ℱ)
    (U : Opens X.carrier) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    IsZero (((moduleUnderlyingSheaf X).obj ℱ).H' p U) := by
  letI : HasProducts AddCommGrpCat.{u} := inferInstance
  have hUnderlying :
      Sheaf.HasCofinalCoveringsWithVanishingHigherCech
        ((moduleUnderlyingSheaf X).obj ℱ)
        B
        (basisCechAcyclicCov B ℱ) := by
    refine
      { coversTop := ?_
        intersections_mem := ?_
        cofinal := ?_
        higherCech_isZero := ?_ }
    · intro U hU cover hcover
      exact hcover.1
    · intro U hU cover hcover n i
      exact hcover.2.2.1 n i
    · intro U hU ι V hV
      have hV' : iSup (fun i ↦ (V i).left) = U :=
        iSup_left_eq_of_coversTop_over V hV
      obtain ⟨κ, 𝒰, refine, h𝒰, hrefine, hB, hBinter, hacyclic⟩ :=
        hasCofinalBasisCechAcyclicCoverings_apply ℱ hℱ hU
          (fun i ↦ (V i).left) hV'
      refine ⟨FormalCoproduct.mk κ (openCoverOver U 𝒰 h𝒰), ?_, ?_⟩
      · refine ⟨openCoverOver_coversTop U 𝒰 h𝒰, openCoverOver_mem_basis 𝒰 h𝒰 hB, ?_, ?_⟩
        · intro n i
          exact openCoverOver_intersections_mem_basis 𝒰 h𝒰 hBinter n i
        · intro q hq
          exact isZero_cechCohomology_openCoverOver 𝒰 h𝒰 ℱ q (hacyclic q hq)
      · exact ⟨openCoverOverHom V 𝒰 h𝒰 refine hrefine⟩
    · intro U hU cover hcover q hq
      exact hcover.2.2.2 q hq
  exact
    higherCohomology_isZero_of_vanishingHigherCech_on_cofinal_coverings
      B
      (basisCechAcyclicCov B ℱ)
      ((moduleUnderlyingSheaf X).obj ℱ)
      hUnderlying
      hU p hp

end AlgebraicGeometry.RingedSpace
