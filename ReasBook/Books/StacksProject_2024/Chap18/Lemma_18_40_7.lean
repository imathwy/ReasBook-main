import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap18.Definition_18_32_1
import StacksProject_2024.Chap18.Definition_18_40_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, ∀ X : Over U, HasWeakSheafify ((J.over U).over X) AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]

local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

/- Domain-style sampling for Lemma 18.40.7:
- primary domain: rank-one finite locally free modules and invertible modules on a ringed site;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsFiniteLocallyFreeOfRank`,
  `SheafOfModules.RingedSite.IsInvertible`,
  `CategoryTheory.HasLocalUnitDichotomy`,
  `CategoryTheory.IsLocallyRingedSite`;
- best owner abstractions:
  the source-facing clauses should be expressed directly in terms of the Chapter 18 owners
  `IsFiniteLocallyFreeOfRank`, `IsInvertible`, and the local-dichotomy owner
  `HasLocalUnitDichotomy`, rather than by repeating the latter as an ad hoc quantified hypothesis;
- primitive data:
  the module `ℒ` and the ambient local unit dichotomy on the structure sheaf;
- derived API:
  the invertibility instance for rank-one locally free modules and the converse rank-one local
  freeness statement under the local unit dichotomy.

Source/core/bridge triage:
- `source-facing`: the two clauses of Stacks Lemma 18.40.7;
- `core/canonical`: `IsFiniteLocallyFreeOfRank`, `IsInvertible`,
  `CategoryTheory.HasLocalUnitDichotomy`;
- `bridge/view`: the local unit dichotomy is reused through its chapter owner, not restated as a
  parallel quantified parameter.
-/

-- Proof sketch: for a rank-one local trivialization, the evaluation map
-- `\mathcal L \otimes_{\mathcal O} \mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)
-- \to \mathcal O` is locally identified with the standard evaluation map for
-- `\mathcal O_U`, hence is an isomorphism on a cover; Lemma `18.32.2` then gives invertibility.
/-- Lemma 18.40.7 (1): on a ringed site, a locally free `\mathcal O`-module of rank `1` is
invertible. -/
instance isInvertible_of_isFiniteLocallyFreeOfRank_one
    (ℒ : Mod)
    [IsFiniteLocallyFreeOfRank 1 ℒ] :
    IsInvertible ℒ := sorry

-- Proof sketch: by Lemma `18.32.2`, an invertible module is locally a direct summand of a finite
-- free module. Over a cover satisfying the local unit-dichotomy for the structure sheaf, the
-- corresponding idempotent matrices split as finite locally free modules of constant rank, and
-- invertibility forces that local rank to be `1`.
/-- Lemma 18.40.7 (2): if every section of the structure sheaf is locally either invertible or has
invertible complement, then every invertible `\mathcal O`-module is locally free of rank `1`. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible_of_local_unit_dichotomy
    (ℒ : Mod)
    [IsInvertible ℒ]
    [HasLocalUnitDichotomy J 𝒪] :
    IsFiniteLocallyFreeOfRank 1 ℒ := sorry

end SheafOfModules.RingedSite
