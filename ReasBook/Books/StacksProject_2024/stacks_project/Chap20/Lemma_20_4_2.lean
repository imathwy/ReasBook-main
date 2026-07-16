import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.Topology.Category.TopCat.Opens
import StacksProject_2024.stacks_project.Chap20.Definition_20_4_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_4_2
import StacksProject_2024.stacks_project.Chap20.OpensInstances

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace CategoryTheory.Sheaf.Torsor

variable {X : TopCat.{u}} {G : X.Sheaf GrpCat.{u}}

/- Domain-style sampling for Lemma 20.4.2:
- primary domain: torsors under a sheaf of groups and their global sections;
- sampled owner declarations:
  `CategoryTheory.Sheaf.Torsor`,
  `CategoryTheory.Sheaf.Torsor.isTrivial_iff_nonempty_globalSections`,
  `CategoryTheory.Sheaf.Torsor.Sections`,
  `Preorder.isTerminalTop`,
  `Sheaf.ΓNatIsoSheafSections`;
- best owner abstraction: the site-level theorem
  `CategoryTheory.Sheaf.Torsor.isTrivial_iff_nonempty_globalSections`, specialized to
  `Opens.grothendieckTopology X`;
- primitive data: the source-facing topological torsor `P : CategoryTheory.Sheaf.Torsor G`;
- derived API: the direct site-level theorem and the terminal-open comparison
  `Sheaf.ΓNatIsoSheafSections`, using the canonical top open `⊤ : Opens X`.

Source/core/bridge triage:
- `source-facing`: `CategoryTheory.Sheaf.Torsor G` specialized to the opens site of `X`;
- `core/canonical`: `CategoryTheory.Sheaf.Torsor.isTrivial_iff_nonempty_globalSections`;
- `bridge/view`: the specialization from site global sections to sections over `⊤ : Opens X`.
-/

/-- Site-theoretic global sections of a torsor are nonempty exactly when its sections over `⊤`
are nonempty. -/
@[simp] theorem nonempty_globalSections_iff_nonempty_sections_top (P : Torsor G) :
    Nonempty ((Sheaf.Γ (Opens.grothendieckTopology X) (Type u)).obj P.carrier) ↔
      Nonempty (P.Sections (⊤ : Opens X)) := by
  let _ : ∀ U : Opens X, Nonempty (U ⟶ (⊤ : Opens X)) := fun _ ↦ ⟨homOfLE le_top⟩
  let e :
      (Sheaf.Γ (Opens.grothendieckTopology X) (Type u)).obj P.carrier ≃
        P.Sections (⊤ : Opens X) :=
    ((Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) (Type u)
      (Preorder.isTerminalTop (Opens X))).app P.carrier).toEquiv
  constructor
  · rintro ⟨s⟩
    exact ⟨e s⟩
  · rintro ⟨s⟩
    exact ⟨e.symm s⟩

/-- Lemma 20.4.2: a `G`-torsor on `X` is trivial if and only if it has a global section. -/
@[stacks 02FP]
theorem isTrivial_iff_nonempty_global_sections (P : Torsor G) :
    P.IsTrivial ↔ Nonempty (P.Sections (⊤ : Opens X)) :=
  (isTrivial_iff_nonempty_globalSections P).trans
    (P.nonempty_globalSections_iff_nonempty_sections_top)

end CategoryTheory.Sheaf.Torsor
