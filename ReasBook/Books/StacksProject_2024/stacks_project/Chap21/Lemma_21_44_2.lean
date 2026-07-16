import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap20.Lemma_20_46_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace SheafOfModules.RingedSite

open AlgebraicGeometry.RingedSpace.CochainComplex

/- Domain-style sampling for Lemma 21.44.2:
- primary domain: strictly perfect cochain complexes of `𝒪`-modules on a ringed site and
  stability under the canonical mapping-cone construction;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `CochainComplex.IsStrictlyPerfect`,
  `CochainComplex.mappingCone`,
  `isStrictlyPerfect_mappingCone`;
- best owner abstraction: the Chapter 20 owner theorem
  `isStrictlyPerfect_mappingCone` on complexes of modules over an arbitrary sheaf of rings;
- primitive data: a morphism `f : K ⟶ L` together with strict-perfectness hypotheses on `K` and
  `L`;
- derived API: none; the Chapter 21 ringed-site statement is exactly this owner theorem with
  `R := ringSheaf J 𝒪`.

Source/core/bridge triage:
- `source-facing`: Lemma 21.44.2 for complexes of `𝒪`-modules on a ringed site;
- `core/canonical`: `isStrictlyPerfect_mappingCone`;
- `bridge/view`: the ringed-site specialization via `ringSheaf J 𝒪`.

This file is therefore recall-only: `ringedSiteModuleCategory J 𝒪` is definitionally
`SheafOfModules (ringSheaf J 𝒪)`, and Definition `21.44.1` already identifies the
site-presented strict-perfectness predicate with the Chapter 20 owner. Keeping a second theorem
here would only duplicate that canonical API. -/

/- Lemma 21.44.2: the cone of a morphism between strictly perfect complexes of `𝒪`-modules on a
ringed site is strictly perfect. In the project API this is exactly the Chapter 20 owner theorem on
complexes of modules over the sheaf of rings `ringSheaf J 𝒪`. -/
recall isStrictlyPerfect_mappingCone

end SheafOfModules.RingedSite
