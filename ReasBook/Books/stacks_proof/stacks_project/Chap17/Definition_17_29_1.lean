import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap17.Definition_17_28_3
import stacks_proof.stacks_project.Chap18.Definition_18_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat

noncomputable section

universe u

/- Domain-style sampling for Definition 17.29.1:
- primary domain: differential operators between sheaves of modules on a ringed site, specialized
  to the opens site of a topological space;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`,
  `SheafOfModules.RingedSite.isDifferentialOperatorOfOrder_app`,
  `SheafOfModules.RingedSite.restrictionAlong`,
  `LinearMap.IsDifferentialOperatorOfOrder`;
- best owner abstraction: the canonical ringed-site owner
  `SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`, specialized to the opens site;
- primitive data: a morphism after same-site restriction of scalars along a morphism of sheaves of
  commutative rings;
- derived API: the objectwise evaluation theorem
  `SheafOfModules.RingedSite.isDifferentialOperatorOfOrder_app`.

Source/core/bridge triage:
- `source-facing`: Definition 17.29.1 on the opens site of a topological space;
- `core/canonical`: `SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`;
- `bridge/view`: specialization from an arbitrary ringed site to the opens site.
-/

/- Definition 17.29.1: on the opens site of a topological space, relative differential operators
of order `k` are exactly the canonical ringed-site owner
`SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`. -/
recall SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder

namespace TopCat.Sheaf

/-- Opens-site bridge for Definition 17.29.1: the ringed-site owner specialized to the Chapter 17
restriction-of-scalars surface. -/
abbrev IsDifferentialOperatorOfOrder
    {X : TopCat.{u}} {O₁ O₂ : TopCat.Sheaf CommRingCat.{u} X}
    (φ : O₁ ⟶ O₂)
    {F G : SheafOfModules (ringSheaf O₂)}
    (D : (SheafOfModules.restrictScalars (ringSheafMap φ)).obj F ⟶
      (SheafOfModules.restrictScalars (ringSheafMap φ)).obj G)
    (k : ℕ) : Prop :=
  SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder φ D k

end TopCat.Sheaf
