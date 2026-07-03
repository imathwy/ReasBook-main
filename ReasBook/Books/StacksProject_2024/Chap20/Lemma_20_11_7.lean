import Mathlib
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap20.«20_25_0_2»
import StacksProject_2024.Chap20.Lemma_20_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

/- Domain-style sampling for Lemma 20.11.7:
- primary domain: Čech cohomology of sheaves of modules on a ringed space, and evaluation of a
  short exact sequence on an open subset;
- inspected owner declarations:
  `CategoryTheory.cechComplexFunctor`,
  `AlgebraicGeometry.RingedSpace.moduleCechCohomology`,
  `IsRefinement`,
  `(RingedSpace.Modules AlgebraicGeometry.RingedSpace)`,
  `SheafOfModules.evaluation`;
- best owner abstraction: the degree-one vanishing hypothesis should be expressed directly using
  the chapter owner `moduleCechCohomology`, while the map on sections should be the canonical
  evaluation map of `S.g`; the only refinement data should be the primitive witness
  `IsRefinement 𝒱 cover refine`, not a parallel wrapper structure;
- primitive data: a short complex `S : ShortComplex (RingedSpace.Modules X)`, an open subset `U`, an
  indexed cover `𝒱`, and a refining cover together with a map `refine : κ → ι` witnessing
  `IsRefinement 𝒱 cover refine`;
- derived API: the vanishing of `moduleCechCohomology cover S.X₁ 1` and the surjectivity of
  `((SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)).map S.g)`.

Source/core/bridge triage:
- `source-facing`: the cofinal refinement hypothesis and the surjectivity conclusion of
  Lemma 20.11.7;
- `core/canonical`: `moduleCechCohomology`, `(RingedSpace.Modules X)`, `(RingedSpace.ringCatSheaf X)`, and
  `SheafOfModules.evaluation`;
- `bridge/view`: the refinement witness `IsRefinement`, and the underlying additive presheaf
  functor already absorbed inside `moduleCechCohomology`.

The previous file packaged the refinement witness as a separate public `structure`. That witness is
not a new mathematical owner, only existential source data, so the refined file keeps it directly
inside the source-facing hypothesis and reuses the chapter owners for the actual cohomology and
evaluation constructions.
-/

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- Every covering of `U` admits a refinement with vanishing first Čech cohomology in `S.X₁`. -/
abbrev HasCofinalCechH1VanishingRefinement
    (S : ShortComplex (RingedSpace.Modules X)) (U : Opens X.carrier) : Prop :=
  ∀ {ι : Type u} (𝒱 : ι → Opens X.carrier), iSup 𝒱 = U →
    ∃ (κ : Type u) (cover : κ → Opens X.carrier) (refine : κ → ι),
      iSup cover = U ∧
        IsRefinement 𝒱 cover refine ∧
        IsZero (moduleCechCohomology cover S.X₁ 1)

-- Proof sketch: start with a section of `S.X₃(U)` and choose an open cover on which it lifts
-- locally through `S.g`. Refine this cover to one with vanishing first Čech cohomology for
-- `S.X₁`; the differences of the local lifts form a Čech `1`-cocycle in `S.X₁`, hence a
-- coboundary. Correct the local lifts by the corresponding `0`-cochain and glue the adjusted
-- sections to obtain a global lift in `S.X₂(U)`.
/-- Lemma 20.11.7: for a short exact sequence of `\mathcal O_X`-modules on a ringed space, if
every open covering of `U` admits a refinement whose first Čech cohomology with coefficients in
the left term vanishes, then every section of the quotient over `U` lifts to the middle term. -/
theorem module_sections_surjective_of_shortExact_of_cofinal_cechH1_zero
    (S : ShortComplex (RingedSpace.Modules X)) (hS : S.ShortExact) (U : Opens X.carrier)
    (hcech : HasCofinalCechH1VanishingRefinement S U) :
    Function.Surjective ((SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)).map S.g) := sorry

end AlgebraicGeometry.RingedSpace
