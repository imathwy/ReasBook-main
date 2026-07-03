import Mathlib.Tactic.Recall
import StacksProject_2024.Chap18.Lemma_18_28_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

/- Domain-style sampling for Lemma 17.17.8:
- primary domain: tensor products of sheaves of modules on a ringed space and preservation of
  short exact sequences under tensoring on the right;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `sheafModuleTensorRightFunctor`,
  `SheafOfModules.IsFlat`,
  `SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient`;
- best owner abstraction: the canonical owner is the site-level theorem
  `SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient`, whose ringed-space case is
  obtained by specializing to the opens-site of `X`;
- primitive data: a short exact sequence in `RingedSpace.Modules X`, a right tensor factor, and a
  flat quotient term;
- derived API: the ringed-space wording of the same tensor-preservation result.

Source/core/bridge triage:
- `source-facing`: the Stacks-project ringed-space formulation of preservation of short exactness
  under tensoring by a fixed sheaf;
- `core/canonical`: `SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient`;
- `bridge/view`: the specialization from a ringed site `(Opens X, Opens.grothendieckTopology X,
  ringCatSheaf X)` to the ambient category `RingedSpace.Modules X`.

Primitive-vs-derived check:
- the deleted local theorem `CategoryTheory.ShortComplex.ShortExact.moduleTensorRight_of_isFlat`
  was only a ringed-space wrapper around the Chapter 18 owner theorem, differing by namespace and
  by passing flatness explicitly instead of through the owner instance;
- this file should therefore be a recall/use file rather than maintain a parallel theorem name.
-/

/- Lemma 17.17.8: for a ringed space `(X, 𝒪_X)`, tensoring a short exact sequence of
`𝒪_X`-modules on the right by any `𝒪_X`-module preserves short exactness when the quotient term is
flat. This is exactly the ringed-space specialization of the canonical site-level owner theorem
`SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient`. -/
recall SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient
