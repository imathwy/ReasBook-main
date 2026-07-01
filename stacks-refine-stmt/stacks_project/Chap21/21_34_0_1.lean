import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import stacks_project.Chap18.Definition_18_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open CochainComplex.HomComplex.CohomologyClass

universe u v

section

variable {X : RingedSite.{u, v}} {U : X}

local notation "ModU" => SheafOfModules (RingedSite.structureSheaf (X.localization U))

/- Domain-style sampling for 21.34.0.1:
- primary domain: cohomology of Hom complexes and morphisms in the homotopy category of cochain
  complexes of `\mathcal O_U`-modules on the localized ringed site `X.localization U`;
- sampled owner declarations:
  `RingedSite.localization`,
  `RingedSite.localization_structureSheaf`,
  `CochainComplex.HomComplex.homologyAddEquiv`,
  `CochainComplex.HomComplex.CohomologyClass.homAddEquiv`,
  `stacks_project/Items/Chap20/20_41_0_1.lean`;
- best owner abstraction: the source-facing ambient owner is the localized ringed site
  `X.localization U`, while the canonical core equivalences are
  `CochainComplex.HomComplex.homologyAddEquiv` and `homAddEquiv`;
- primitive data vs derived API:
  the primitive inputs are the ambient module category `ModU`, the complexes `L`, `M`, and the
  degree `n`; the displayed identification is already the upstream composite
  `(CochainComplex.HomComplex.homologyAddEquiv L M n).trans homAddEquiv`;
- source/core/bridge triage:
  `source-facing`: the textbook identification
  `H^n(\Gamma(U, \mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal M^\bullet))) ≃
  \operatorname{Hom}_{K(\mathcal O_U)}(\mathcal L^\bullet|_U, \mathcal M^\bullet[n]|_U)`;
  `core/canonical`: `X.localization U`,
  `CochainComplex.HomComplex.homologyAddEquiv`, and `homAddEquiv`;
  `bridge/view`: the direct composite equivalence below.

This file therefore targets the `bridge/view` layer. Keeping only `homologyAddEquiv` would stop at
cohomology classes and miss the final owner-level identification with morphisms in the homotopy
category, while introducing a local wrapper for the composite would duplicate existing upstream API.
-/

/- 21.34.0.1: on the localized ringed site `X.localization U`, the displayed equality
`H^n(\Gamma(U, \mathcal{H}\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal M^\bullet))) =
\operatorname{Hom}_{K(\mathcal O_U)}(\mathcal L^\bullet|_U, \mathcal M^\bullet[n]|_U)`
is the direct upstream composite from the degree-`n` homology of the Hom complex to morphisms
into the `n`-fold shift in the cochain homotopy category. -/
variable (L M : CochainComplex ModU ℤ) (n : ℤ)

#check (CochainComplex.HomComplex.homologyAddEquiv L M n).trans homAddEquiv

end
