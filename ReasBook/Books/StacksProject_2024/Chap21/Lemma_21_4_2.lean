import Mathlib
import StacksProject_2024.Chap21.Definition_21_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory
namespace Sheaf
namespace Torsor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{w}}

/- Domain-style sampling for Lemma 21.4.2:
- primary domain: torsors under a sheaf of groups on a site;
- sampled owner declarations:
  `CategoryTheory.Sheaf.PseudoTorsor`,
  `CategoryTheory.Sheaf.Torsor`,
  `CategoryTheory.Sheaf.Torsor.Hom`,
  `CategoryTheory.Sheaf.Torsor.trivial`,
  `TopCat.SheafOfGroups.Torsor.toSiteTorsor`;
- best owner abstraction: `CategoryTheory.Sheaf.Torsor` is the source-facing site-level owner;
  the primitive comparison object is an equivariant isomorphism of torsors, and triviality should
  be expressed as existence of such an isomorphism to `Torsor.trivial` rather than through a
  special-purpose wrapper dedicated only to the trivial target;
- primitive data: torsors `P Q : CategoryTheory.Sheaf.Torsor G` together with morphisms
  `P.Hom Q` and `Q.Hom P`;
- derived API: `Torsor.Iso`, `Torsor.IsTrivial`, and the global-sections characterization below.

Source/core/bridge triage:
- `source-facing`: `CategoryTheory.Sheaf.Torsor G`;
- `core/canonical`: `CategoryTheory.Sheaf.Torsor.Hom`, `CategoryTheory.Sheaf.Torsor.Iso`,
  `CategoryTheory.Sheaf.Torsor.trivial`, and `CategoryTheory.Sheaf.Torsor.IsTrivial`;
- `bridge/view`: the Chapter 20 specialization through `TopCat.SheafOfGroups.Torsor.toSiteTorsor`.
-/

variable [HasWeakSheafify J (Type w)]
variable [HasGlobalSectionsFunctor J (Type w)]

-- Proof sketch: a trivialization sends a global section of the torsor to a global section of the
-- trivial torsor, and the identity section of `G` pulls back along the inverse trivialization to a
-- global section of `P`. Conversely, a chosen global section of `P` identifies each local section
-- with the unique group element carrying the chosen section to it; the torsor axioms make this
-- assignment natural in the site variable and hence produce an equivariant isomorphism with the
-- trivial torsor.
/-- Lemma 21.4.2: a `G`-torsor on a site is trivial if and only if its sheaf of sections has a
nonempty set of global sections. -/
lemma isTrivial_iff_nonempty_globalSections (P : Torsor G) :
    P.IsTrivial ↔ Nonempty ((Sheaf.Γ J (Type w)).obj P.carrier) := sorry

end Torsor
end Sheaf
end CategoryTheory
