import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategoryBasic
import StacksProject_2024.stacks_project.Chap21.Lemma_21_19_1_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex
open CochainComplex.HomComplex.CohomologyClass
open RingedSite.Hom

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {X : RingedSite.{u, v}} {U : X}
variable [HasBinaryProducts X.carrier]

local notation "ModX" => ModuleCat X
local notation "ModU" => ModuleCat (X.localization U)

/- Domain-style sampling for 21.34.0.1:
- primary domain: cohomology of Hom complexes and morphisms in the homotopy category of cochain
  complexes of `𝒪_X`-modules restricted to the localized ringed site `X.localization U`;
- sampled owner declarations:
  `ModuleCat`,
  `localizedRestrictionComplex`,
  `homologyAddEquiv`,
  `homAddEquiv`,
  `stacks_project/Chap20/20_41_0_1.lean`;
- best owner abstraction: the source-facing ambient owner is the localized ringed site
  `X.localization U`, reached from the ambient ringed site `X` by the canonical restriction
  functor `localizedRestrictionComplex X U`; the canonical localized module category is `ModU`,
  and the canonical core equivalences are
  `homologyAddEquiv` and `homAddEquiv`;
- primitive data vs derived API:
  the primitive inputs are the ambient ringed site `X`, the object `U : X`, the complexes
  `L`, `M` of `𝒪_X`-modules, and the degree `n`; the displayed identification is the upstream
  composite applied to the restricted complexes
  `((localizedRestrictionComplex X U).obj L)` and `((localizedRestrictionComplex X U).obj M)`;
- source/core/bridge triage:
  `source-facing`: the textbook identification
  `H^n(Γ(U, Hom^•(L^•, M^•))) ≃ Hom_{K(𝒪_U)}(L^•|_U, M^•[n]|_U)`;
  `core/canonical`: `X.localization U`, `localizedRestrictionComplex X U`,
  `homologyAddEquiv`, and `homAddEquiv`;
  `bridge/view`: the direct composite equivalence below.

This file therefore targets the `bridge/view` layer. Keeping only `homologyAddEquiv` would stop at
cohomology classes and miss the final owner-level identification with morphisms in the homotopy
category, while omitting restriction from `X` to `X/U` would change the source statement's
objects.
-/

/- 21.34.0.1: after restricting complexes of `𝒪_X`-modules to the localized ringed site
`X.localization U`, the displayed equivalence
`H^n(Γ(U, Hom^•(L^•, M^•))) ≃ Hom_{K(𝒪_U)}(L^•|_U, M^•[n]|_U)`
is the direct upstream composite from the degree-`n` homology of the localized Hom complex to
morphisms into the `n`-fold shift in the cochain homotopy category. -/
variable (L M : CochainComplex ModX ℤ) (n : ℤ)

/-- 21.34.0.1: the degree-`n` homology of the localized Hom complex computing
`Γ(U, \mathcal{H}om^\bullet(L^\bullet, M^\bullet))` identifies with morphisms from the restricted
complex `L|_U` to the shifted restricted complex `M|_U⟦n⟧` in the cochain homotopy category. -/
@[stacks 0A8Y]
abbrev localizedHomComplexHomologyToHomotopyHomAddEquiv :
    (CochainComplex.HomComplex
      ((localizedRestrictionComplex X U).obj L)
      ((localizedRestrictionComplex X U).obj M)).homology n ≃+
      ((HomotopyCategory.quotient ModU _).obj ((localizedRestrictionComplex X U).obj L) ⟶
        (HomotopyCategory.quotient ModU _).obj
          (((localizedRestrictionComplex X U).obj M)⟦n⟧)) :=
  (homologyAddEquiv
      ((localizedRestrictionComplex X U).obj L)
      ((localizedRestrictionComplex X U).obj M)
      n).trans
    homAddEquiv

end

end SheafOfModules.RingedSite
