import StacksProject_2024.stacks_project.Chap20.«20_15_0_1»
import StacksProject_2024.stacks_project.Chap21.SiteAbelianDerived

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace TopCat
open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization
attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u + 1}}
variable [CompactSpace X] [T2Space X]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (X.Sheaf AddCommGrpCat.{u + 1})]

/-
Domain-style sampling for Lemma 20.16.2:
- primary domain: global Čech cohomology on compact Hausdorff spaces and its comparison with the
  canonical sheaf-cohomology owner;
- sampled owner declarations:
  `globalCechCohomology`,
  `CategoryTheory.Sheaf.H`,
  `CategoryTheory.Sheaf.cohomologyFunctor`,
  `CohomologicalDeltaFunctor.IsUniversal`,
  `CohomologicalDeltaFunctor.universal_delta_functor_unique_up_to_unique_iso`;
- best owner abstraction: this file's main source-facing object is the canonical colimit owner
  `globalCechCohomology`; the global sheaf-cohomology target is canonically owned by
  `AddCommGrpCat.of (ℱ.H n)`, with `Sheaf.cohomologyFunctor (Opens.grothendieckTopology X) n`
  serving only as the Ext-owner bridge behind that global value. The proof mechanism passes
  through the chapter owners for universal cohomological `δ`-functors, but there is no upstream
  theorem already packaging this exact global compact-Hausdorff comparison, so the public entry
  should remain this source-facing `IsIsomorphic` theorem rather than a new wrapper or a fake
  recall.

Source/core/bridge triage:
- `source-facing`: the compact-Hausdorff comparison
  `Čech H^n(X, ℱ) ≅ H^n(X, ℱ)`;
- `core/canonical`: `globalCechCohomology`, `Sheaf.H`,
  `CohomologicalDeltaFunctor.IsUniversal`, and
  `CohomologicalDeltaFunctor.universal_delta_functor_unique_up_to_unique_iso`;
- `bridge/view`: `Sheaf.cohomologyFunctor`, the objectwise-on-opens owner `Sheaf.H'`, and the
  degree-zero and degree-one comparison inputs from the previous files, upgraded through
  universality to all degrees.

Primitive data versus derived API:
- primitive data: a compact Hausdorff space `X`, an abelian sheaf `ℱ` on `X`, and a degree `n`;
- derived API: the theorem-level compact-Hausdorff comparison
  `IsIsomorphic (globalCechCohomology ℱ n) (AddCommGrpCat.of (ℱ.H n))`.
-/

-- Proof sketch: Lemma `20.16.1` gives the comparison isomorphism in degrees `0` and `1`. Usual
-- sheaf cohomology is a universal `δ`-functor, while on compact Hausdorff spaces the Čech
-- cohomology groups admit compatible connecting morphisms and vanish in positive degree on
-- injective sheaves, so they also form a universal `δ`-functor. Uniqueness of universal
-- `δ`-functors then upgrades the comparison to an isomorphism in every degree.
/-- Lemma 20.16.2: if `X` is Hausdorff and quasi-compact and `ℱ` is an abelian sheaf on `X`, then
for every `n` the global Čech cohomology object `Čech H^n(X, ℱ)` is canonically isomorphic to the
sheaf cohomology group `H^n(X, ℱ)`. -/
@[stacks 09V2]
theorem globalCechCohomology_isomorphic_sheafCohomology_of_compact_t2
    (ℱ : X.Sheaf AddCommGrpCat.{u + 1}) (n : ℕ) :
    IsIsomorphic (globalCechCohomology ℱ n) (AddCommGrpCat.of (ℱ.H n)) := sorry

end Sheaf
end CategoryTheory
