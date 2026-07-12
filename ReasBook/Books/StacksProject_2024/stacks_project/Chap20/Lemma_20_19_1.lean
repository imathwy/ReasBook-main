import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import StacksProject_2024.Chap06.RingedSpaceModuleCore
import StacksProject_2024.Chap21.Lemma_21_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.19.1:
- primary domain: filtered colimits of `𝒪_X`-modules and their compatibility with sheaf
  cohomology on a quasi-compact open subset of a ringed space;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.cohomologyAtObjectFunctor`,
  `SheafOfModules.cohomologyAtObject_isomorphic`,
  `CompactOpens`,
  `CategoryTheory.Limits.colimit.post`;
- best owner abstraction: the ambient module category `RingedSpace.Modules X`, together with the
  canonical fixed-open cohomology owner
  `SheafOfModules.cohomologyAtObjectFunctor X.ringCatSheaf q U.toOpens`; the quasi-compact open
  input should use the canonical owner `CompactOpens X.carrier`, while the intersection hypothesis
  is canonically carried by `[QuasiSeparatedSpace X.carrier]`;
- primitive data: a ringed space `X`, a compact open `U : CompactOpens X.carrier`, a degree `q`,
  and a filtered diagram `ℱ : I ⥤ X.Modules`;
- derived API: the canonical colimit comparison map for the functor `ℱ ↦ H^q(U, ℱ)`.

Source/core/bridge triage:
- `source-facing`: the canonical comparison morphism
  `colim_i H^q(U, 𝓕_i) ⟶ H^q(U, colim_i 𝓕_i)` and the
  isomorphism statement under the quasi-compact hypotheses;
- `core/canonical`: `RingedSpace.Modules`, `CompactOpens`,
  `SheafOfModules.cohomologyAtObjectFunctor`, and `colimit.post`;
- `bridge/view`: the Chapter 21 comparison
  `SheafOfModules.cohomologyAtObject_isomorphic X.ringCatSheaf ℱ q U.toOpens`, which identifies
  the canonical owner with the additive sheaf cohomology object
  `((moduleUnderlyingSheaf X).obj ℱ).H' q U.toOpens`.
-/

section

variable {X : RingedSpace.{u}}
variable [PrespectralSpace X.carrier]
variable [QuasiSeparatedSpace X.carrier]
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable (U : CompactOpens X.carrier) (q : ℕ)

-- Proof sketch: first prove the degree-zero statement for every compact open simultaneously, using
-- that filtered colimits commute with sections on compact opens in a prespectral space whose
-- compact opens are stable under binary intersections. Then choose functorial injective embeddings
-- of the diagram, use exactness of filtered colimits of abelian groups and the vanishing of higher
-- Čech cohomology for injectives on finite covers by compact opens, and conclude by induction on
-- `q`.
/-- Lemma 20.19.1: if the underlying topological space of a ringed space `X` has a basis of
quasi-compact opens and the intersection of any two quasi-compact opens is quasi-compact, then for
every filtered diagram `(𝓕_i)` of `𝒪_X`-modules, every quasi-compact open subset
`U`, and every `q ≥ 0`, the canonical map
`colim_i H^q(U, 𝓕_i) ⟶ H^q(U, colim_i 𝓕_i)` is an
isomorphism. The topological hypotheses are expressed canonically by
`[PrespectralSpace X.carrier] [QuasiSeparatedSpace X.carrier]`, and the quasi-compact open input by
`U : CompactOpens X.carrier`. The comparison is stated on the canonical owner
`SheafOfModules.cohomologyAtObjectFunctor X.ringCatSheaf q U.toOpens`; the existing bridge
`SheafOfModules.cohomologyAtObject_isomorphic` identifies its values with the additive sheaf
cohomology objects `((moduleUnderlyingSheaf X).obj 𝓕).H' q U.toOpens`. -/
@[stacks 01FF]
instance ringedSpaceModuleCohomologyColimitComparison_isIso_of_isCompact
    {I : Type v} [Category I] [Small.{u} I] [IsFiltered I]
    (ℱ : I ⥤ X.Modules) :
    IsIso
      (colimit.post ℱ (SheafOfModules.cohomologyAtObjectFunctor X.ringCatSheaf q U.toOpens)) :=
  sorry

end

end AlgebraicGeometry.RingedSpace
