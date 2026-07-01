import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import stacks_project.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CochainComplex.HomComplex.CohomologyClass

universe u v

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

local notation "Mod" => SheafOfModules (ringSheaf J 𝒪)

/- Domain-style sampling for 21.34.0.2:
- primary domain: cohomology of Hom complexes and morphisms in the homotopy category of cochain
  complexes of `\mathcal O`-modules on a ringed site;
- sampled owner declarations:
  `ringSheaf`,
  `CochainComplex.HomComplex.homologyAddEquiv`,
  `CochainComplex.HomComplex.CohomologyClass.homAddEquiv`,
  `stacks_project/Items/Chap15/15_72_0_1.lean`,
  `stacks_project/Items/Chap20/20_41_0_1.lean`;
- best owner abstraction: the ambient owner is the ringed-site structure sheaf `ringSheaf J 𝒪`,
  and the canonical bridge layer is the Hom-complex cohomology-class API; the source statement
  itself is the upstream composite
  `(CochainComplex.HomComplex.homologyAddEquiv L M n).trans homAddEquiv`;
- primitive data vs derived API:
  the primitive inputs are the ambient module category `Mod`, the complexes `L`, `M`, and the
  degree `n`; the intermediate cohomology-class quotient and both equivalences are already
  canonical upstream;
- source/core/bridge triage:
  `source-facing`: the textbook identification
  `H^n(\Gamma(\mathcal C, \mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet,
  \mathcal M^\bullet))) ≃ \operatorname{Hom}_{K(\mathcal O)}
  (\mathcal L^\bullet, \mathcal M^\bullet[n])`;
  `core/canonical`: `ringSheaf J 𝒪`,
  `CochainComplex.HomComplex.homologyAddEquiv`, and `homAddEquiv`;
  `bridge/view`: the direct composite equivalence below.

This file therefore targets the `bridge/view` layer. A local wrapper with the same interface would
duplicate existing derived API, so the correct surface is direct canonical reuse of the composite.
-/

/- 21.34.0.2: for complexes of `\mathcal O`-modules on the ringed site `(\mathcal C, \mathcal O)`,
the displayed equality
`H^n(\Gamma(\mathcal C, \mathcal{H}\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal M^\bullet)))
= \operatorname{Hom}_{K(\mathcal O)}(\mathcal L^\bullet, \mathcal M^\bullet[n])`
is the direct upstream composite from the degree-`n` homology of the Hom complex to morphisms
into the `n`-fold shift in the cochain homotopy category. -/
variable (L M : CochainComplex Mod ℤ) (n : ℤ)

#check (CochainComplex.HomComplex.homologyAddEquiv L M n).trans homAddEquiv

end
