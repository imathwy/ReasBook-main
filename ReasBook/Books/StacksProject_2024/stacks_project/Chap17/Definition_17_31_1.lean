import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap18.Definition_18_35_1

/- Domain-style sampling for Definition 17.31.1:
- primary domain: naive cotangent complexes of sheaves of commutative rings on the opens site of
  a topological space;
- sampled owner declarations:
  `SheafOfModules.RingedSite.presentationNaiveCotangent`,
  `SheafOfModules.RingedSite.naiveCotangent`,
  `SheafOfModules.RingedSite.naiveCotangent_X_negOne`,
  `SheafOfModules.RingedSite.naiveCotangent_X_zero`;
- best owner abstraction: the canonical ringed-site owner
  `SheafOfModules.RingedSite.naiveCotangent`, specialized to the opens site
  `Opens.grothendieckTopology X`;
- primitive data: a sheaf of commutative rings `\mathcal A` on the opens site and a sheaf of
  `\mathcal A`-algebras `\mathcal B`;
- derived API: the degree `-1` and `0` identification theorems already owned upstream by Chapter
  18.

Source/core/bridge triage:
- `source-facing`: the naive cotangent complex `NL_{\mathcal B/\mathcal A}` on a topological
  space;
- `core/canonical`: `SheafOfModules.RingedSite.naiveCotangent`;
- `bridge/view`: specialization from an arbitrary ringed site to the opens site of a topological
  space.
-/

/- Definition 17.31.1: on the opens site of a topological space, the naive cotangent complex
`NL_{\mathcal B/\mathcal A}` is exactly the canonical ringed-site owner
`SheafOfModules.RingedSite.naiveCotangent`. -/
recall SheafOfModules.RingedSite.naiveCotangent
