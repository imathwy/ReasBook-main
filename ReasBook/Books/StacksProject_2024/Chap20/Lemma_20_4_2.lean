import Mathlib
import StacksProject_2024.Chap20.Definition_20_4_1
import StacksProject_2024.Chap21.Lemma_21_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite
open TopCat
open TopologicalSpace.Opens

noncomputable section

universe u

namespace TopCat.SheafOfGroups
namespace Torsor

variable {X : TopCat.{u}} {G : X.Sheaf GrpCat.{u}}

/- Domain-style sampling for Lemma 20.4.2:
- primary domain: torsors under a sheaf of groups and their global sections;
- sampled owner declarations:
  `TopCat.SheafOfGroups.Torsor`,
  `CategoryTheory.Sheaf.Torsor`,
  `CategoryTheory.Sheaf.Torsor.isTrivial_iff_nonempty_globalSections`,
  `Sheaf.ΓNatIsoSheafSections`;
- best owner abstraction: the site-level theorem
  `CategoryTheory.Sheaf.Torsor.isTrivial_iff_nonempty_globalSections`, specialized to
  `Opens.grothendieckTopology X`;
- primitive data: the source-facing topological torsor `P : Torsor G`;
- derived API: the canonical bridge `P.toSiteTorsor` and direct reuse of
  `Sheaf.ΓNatIsoSheafSections` for sections over `⊤`.

Source/core/bridge triage:
- `source-facing`: `TopCat.SheafOfGroups.Torsor` and the Chapter 20 theorem below;
- `core/canonical`: `CategoryTheory.Sheaf.Torsor.isTrivial_iff_nonempty_globalSections`;
- `bridge/view`: the public bridge `Torsor.toSiteTorsor`.
-/

/-- Lemma 20.4.2: a `G`-torsor on `X` is trivial if and only if it has a global section. -/
theorem isTrivial_iff_nonempty_global_sections (P : Torsor G) :
    P.IsTrivial ↔ Nonempty (P.Sections ⊤) := by
  let _ : HasTerminal (TopologicalSpace.Opens ↑X) := ⟨⟨⊤, Preorder.isTerminalTop⟩⟩
  let e :
      (Sheaf.Γ (Opens.grothendieckTopology X) (Type u)).obj P.carrier ≃ P.Sections ⊤ :=
    by
      simpa [Torsor.Sections] using
        ((Sheaf.ΓNatIsoSheafSections (J := Opens.grothendieckTopology X) (A := Type u)
          (T := (⊤ : TopologicalSpace.Opens ↑X)) Preorder.isTerminalTop).app P.carrier).toEquiv
  have h := CategoryTheory.Sheaf.Torsor.isTrivial_iff_nonempty_globalSections P.toSiteTorsor
  constructor
  · intro hP
    change P.toSiteTorsor.IsTrivial at hP
    rcases h.mp hP with ⟨s⟩
    exact ⟨e s⟩
  · rintro ⟨s⟩
    change P.toSiteTorsor.IsTrivial
    exact h.mpr ⟨e.symm s⟩

end Torsor
end TopCat.SheafOfGroups
