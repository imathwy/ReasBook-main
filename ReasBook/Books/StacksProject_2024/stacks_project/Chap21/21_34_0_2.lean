import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import StacksProject_2024.Chap18.RingedSiteModuleCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CochainComplex.HomComplex
open CochainComplex.HomComplex.CohomologyClass

universe u v

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

local notation "Mod" => ringedSiteModuleCategory J 𝒪

/- Domain-style sampling for 21.34.0.2:
- primary domain: cohomology of Hom complexes and morphisms in the homotopy category of cochain
  complexes of `𝒪`-modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `CochainComplex.HomComplex.homologyAddEquiv`,
  `CochainComplex.HomComplex.CohomologyClass.homAddEquiv`,
  `stacks_project/Chap15/15_72_0_1.lean`,
  `stacks_project/Chap20/20_41_0_1.lean`;
- best owner abstraction: the ambient owner is the chapter-level module category
  `ringedSiteModuleCategory J 𝒪`, and the canonical bridge layer is the Hom-complex
  cohomology-class API; the source statement itself is the upstream composite
  `(CochainComplex.HomComplex.homologyAddEquiv L M n).trans homAddEquiv`;
- primitive data vs derived API:
  the primitive inputs are the ambient module category `Mod`, the complexes `L`, `M`, and the
  degree `n`; the intermediate cohomology-class quotient and both equivalences are already
  canonical upstream;
- source/core/bridge triage:
  `source-facing`: the textbook identification
  `H^n(Γ(𝒞, Hom^•(L^•, M^•))) ≃ Hom_{K(𝒪)}(L^•, M^•[n])`;
  `core/canonical`: `ringedSiteModuleCategory J 𝒪`,
  `CochainComplex.HomComplex.homologyAddEquiv`, and `homAddEquiv`;
  `bridge/view`: the direct composite equivalence below.

This file therefore targets the `bridge/view` layer. A local wrapper with the same interface would
duplicate existing derived API, so the correct surface is direct canonical reuse of the composite.
-/

/- 21.34.0.2: for complexes of `𝒪`-modules on the ringed site `(𝒞, 𝒪)`, the displayed
identification
`H^n(Γ(𝒞, Hom^•(L^•, M^•))) ≃ Hom_{K(𝒪)}(L^•, M^•[n])`
is the direct upstream composite from the degree-`n` homology of the Hom complex to morphisms
into the `n`-fold shift in the cochain homotopy category. -/
variable (L M : CochainComplex Mod ℤ) (n : ℤ)

/- 21.34.0.2: the degree-`n` homology of the Hom complex computes morphisms from `L` to the
`n`-shift of `M` in the cochain homotopy category. This numbered item is the direct canonical
composite `(homologyAddEquiv L M n).trans homAddEquiv`, so the refined surface stays
alias-free instead of introducing a duplicate local alias for that bridge. -/
noncomputable example :
    (CochainComplex.HomComplex L M).homology n ≃+
      ((HomotopyCategory.quotient Mod _).obj L ⟶
        (HomotopyCategory.quotient Mod _).obj (M⟦n⟧)) :=
  (homologyAddEquiv L M n).trans homAddEquiv

end
