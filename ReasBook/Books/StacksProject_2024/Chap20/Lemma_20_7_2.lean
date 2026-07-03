import Mathlib
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap21.Lemma_21_7_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 20.7.2:
- primary domain: sheaf cohomology of `\mathcal O_X`-modules on the opens site of a ringed space;
- sampled owner declarations:
  `GrothendieckTopology.Cover`,
  `GrothendieckTopology.Cover.Arrow`,
  `SheafOfModules.toSheaf`,
  `_root_.exists_cover_restrict_eq_zero_of_positive_cohomology_class`;
- best owner abstraction: the core owner is the general ringed-site theorem
  `_root_.exists_cover_restrict_eq_zero_of_positive_cohomology_class`, specialized here to the
  opens-site ringed space `(RingedSpace.ringCatSheaf X)`;
- primitive-vs-derived split:
  primitive data are the ringed space `X`, the module `ℱ : (RingedSpace.Modules X)`, the open
  `U : Opens X.carrier`, and the cohomology class `ξ`;
  the underlying additive sheaf and the restriction maps on cohomology are derived canonically by
  `SheafOfModules.toSheaf`;
- source/core/bridge triage:
  `source-facing`: local vanishing of a positive-degree cohomology class after refining by a
  cover of `U`;
  `core/canonical`: `_root_.exists_cover_restrict_eq_zero_of_positive_cohomology_class`;
  `bridge/view`: this ringed-space specialization along `(RingedSpace.ringCatSheaf X)`.
-/

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

local notation "JX" => Opens.grothendieckTopology X.carrier

-- Proof sketch: represent `ξ` by a cocycle in an injective resolution of `ℱ`. In positive degree
-- exactness identifies this cocycle locally with a coboundary, so after refining to a suitable
-- cover of `U` in the opens site its restrictions vanish in cohomology on every cover arrow.
/-- Lemma 20.7.2: every positive-degree cohomology class of a sheaf of `\mathcal O_X`-modules on
an open subspace `U` becomes zero after restricting to a suitable open covering of `U`. -/
lemma exists_cover_restrict_eq_zero_of_positive_cohomology_class
    (ℱ : (RingedSpace.Modules X)) {U : Opens X.carrier} {n : ℕ} (hn : 0 < n)
    (ξ : ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ).H' n U) :
    ∃ T : JX.Cover U, ∀ I : T.Arrow,
      ((((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ).cohomologyPresheaf n).map I.f.op) ξ = 0 :=
    by
  simpa [JX] using
    (_root_.exists_cover_restrict_eq_zero_of_positive_cohomology_class
      (𝒪 := (RingedSpace.ringCatSheaf X)) ℱ hn ξ)

end AlgebraicGeometry
