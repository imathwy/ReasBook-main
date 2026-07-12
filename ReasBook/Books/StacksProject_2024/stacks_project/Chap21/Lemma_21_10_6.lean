import StacksProject_2024.Chap13.Lemma_13_22_2_Grothendieck_spectral_sequence
import StacksProject_2024.Chap21.Definition_21_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat]
variable [HasExt (Sheaf J AddCommGrpCat)]
variable [HasProducts AddCommGrpCat]

variable (U : C) [HasFiniteProducts (Over U)]
variable {ι : Type (max u v)} (family : ι → Over U)

/-
Domain-style sampling for Lemma 21.10.6:
- primary domain: Grothendieck spectral sequences for the composite of the degree-zero Čech
  cohomology functor of a covering family with the inclusion of abelian sheaves into abelian
  presheaves;
- sampled canonical declarations:
  `exists_grothendieckSpectralSequence`,
  `cechCohomologyDegree`,
  `sheafToPresheaf`,
  `Sheaf.cohomologyPresheaf`,
  `FilteredComplex.convergesToCohomology`;
- best owner abstraction: the Chapter `13` Grothendieck spectral-sequence owner specialized to
  the Čech degree-zero functor, with abutment data expressed through the Chapter `12/13` owners
  `FilteredComplex`, `IsAssociatedToFilteredComplex`,
  `CohomologicalSpectralSequence AddCommGrpCat 0`, and
  `FilteredComplex.convergesToCohomology`;
- primitive data: the object `U`, the family `family : ι → Over U`, the covering proof
  `hfamily : (J.over U).CoversTop family`, and the canonical inclusion
  `sheafToPresheaf J AddCommGrpCat`;
- derived API: the existential spectral-sequence package for a fixed coefficient sheaf, its
  page-two identification, and the canonical filtered-complex convergence package together with
  the comparison between its abutment cohomology and sheaf cohomology.

Source/core/bridge triage:
- `source-facing`: the existence of the Čech-to-sheaf-cohomology spectral sequence for a fixed
  cover and coefficient sheaf;
- `core/canonical`: `exists_grothendieckSpectralSequence`, `cechCohomologyDegree`,
  `sheafToPresheaf`, `Sheaf.cohomologyPresheaf`, and
  `FilteredComplex`, `IsAssociatedToFilteredComplex`,
  `CohomologicalSpectralSequence AddCommGrpCat 0`, and
  `FilteredComplex.convergesToCohomology`;
- `bridge/view`: the page-two and abutment isomorphisms expressing those owners in the textbook
  forms `Čech H^p(family, \underline H^q(F))` and `H^n(U, F)`.

The previous wrapper owner duplicated the Chapter `13` existential spectral-sequence API and hid
the source theorem behind `Nonempty`. The refined file keeps the source-facing existence theorem as
a direct specialization of the Chapter `13`
Grothendieck spectral-sequence existence theorem to the composite
`cechCohomologyOnSheaves J family 0 = sheafToPresheaf J AddCommGrpCat ⋙
  (cechCohomologyDegree U family 0).obj`.
-/

-- Proof sketch: apply the Grothendieck spectral sequence to the composite of the left exact
-- inclusion `sheafToPresheaf J AddCommGrpCat` with degree-zero Čech cohomology for `family`.
-- Lemma `21.8.2` identifies degree-zero Čech cohomology with sections over `U`, Lemma `21.10.2`
-- shows that injective abelian sheaves are Čech-acyclic for the cover, Lemma `21.9.6`
-- identifies higher Čech cohomology with the right derived functors of degree zero, and Lemma
-- `21.10.5` identifies the right derived functors of the inclusion with the cohomology
-- presheaves. Specializing Lemma `13.22.2` at a fixed coefficient sheaf `F` gives the displayed
-- `E₂`-page and abutment, together with the boundedness, finite-filtration, and Chapter `12`
-- convergence owners for the resulting spectral sequence.
/-- Lemma 21.10.6: for a covering family `family : ι → Over U` on the slice site `(C / U, J.over
U)`, and an abelian sheaf `F`, there is a cohomological spectral sequence with
`E₂^{p,q} = Čech H^p(family, \underline H^q(F))` converging to `H^{p+q}(U, F)`. -/
@[stacks 03AZ]
theorem exists_cechToSheafCohomologySpectralSequence
    (hfamily : (J.over U).CoversTop family) (F : Sheaf J AddCommGrpCat) :
    ∃ (filteredComplex : FilteredComplex AddCommGrpCat)
      (spectralSequence : CohomologicalSpectralSequence AddCommGrpCat 0)
      (_ : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (pageTwoIso : ∀ p q : ℕ,
        (spectralSequence.page 2).X (Int.ofNat p, Int.ofNat q) ≅
          cechCohomology U family (F.cohomologyPresheaf q) p)
      (targetIso : ∀ n : ℕ,
        filteredComplex.underlying.homology (Int.ofNat n) ≅ F.H' n U),
      CohomologicalSpectralSequence.IsBounded spectralSequence ∧
        filteredComplex.cohomologyFiltrationIsFinite ∧
        filteredComplex.convergesToCohomology spectralSequence := by
  sorry

end

end CategoryTheory
