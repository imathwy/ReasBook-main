import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import stacks_project.Chap17.Definition_17_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open CochainComplex.HomComplex.CohomologyClass
open TopologicalSpace

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {U : Opens X}

local notation "ModU" => SheafOfModules ((RingedSpace.ringCatSheaf X).over U)

/- Domain-style sampling for 20.41.0.1:
- primary domain: cohomology of Hom complexes and morphisms in the homotopy category of cochain
  complexes of `\mathcal O_U`-modules;
- sampled owner declarations:
  `RingedSpace.ringCatSheaf`,
  `Sheaf.over`,
  `SheafOfModules`,
  `CochainComplex.HomComplex.homologyAddEquiv`,
  `CochainComplex.HomComplex.CohomologyClass.homAddEquiv`,
  `stacks_project/Items/Chap15/15_72_0_1.lean`;
- best owner abstraction: the canonical owner layer is the Hom-complex cohomology-class API,
  instantiated in the ambient open-subspace module category
  `ModU`;
- primitive data vs derived API:
  the primitive inputs are the ambient category `ModU`, the complexes `L`, `M`, and the degree
  `n`; the displayed equivalence is already the derived upstream composite
  `(CochainComplex.HomComplex.homologyAddEquiv L M n).trans homAddEquiv`;
- source/core/bridge triage:
  `source-facing`: the textbook identification
  `H^n(\Gamma(U, \mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal M^\bullet))) ≃
  \operatorname{Hom}_{K(\mathcal O_U)}(\mathcal L^\bullet, \mathcal M^\bullet[n])`;
  `core/canonical`: `ModU`,
  `CochainComplex.HomComplex.homologyAddEquiv`, and `homAddEquiv`;
  `bridge/view`: the direct composite equivalence below.

This file therefore targets the `bridge/view` layer. A local named wrapper with the same
interface is duplicate derived API and should be deleted in favor of direct canonical reuse.
Since mathlib names the two canonical owner equivalences but not their composite, the correct
surface here is the direct composite expression itself rather than a new alias introduced only for
this file.
-/

/- 20.41.0.1: after identifying the sections of the internal-Hom complex on `U` with the Hom
complex in `SheafOfModules ((RingedSpace.ringCatSheaf X).over U)`, the desired equivalence is the standard
upstream composite from Hom-complex homology to morphisms in the homotopy category. -/
variable (L M : CochainComplex ModU ℤ) (n : ℤ)

#check (CochainComplex.HomComplex.homologyAddEquiv L M n).trans homAddEquiv

end

end AlgebraicGeometry.RingedSpace
