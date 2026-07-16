import StacksProject_2024.stacks_project.Chap20.Lemma_20_19_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace TopCat
open TopCat.Sheaf

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X Z : TopCat.{u}}

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})]

/- Domain-style sampling for Lemma 20.20.1:
- primary domain: sheaf cohomology and pushforward along a continuous map of topological spaces;
- sampled owner declarations:
  `Sheaf.H'`,
  `(i _*)`,
  `Sheaf.pushforward_cohomologyOnOpen_isomorphic_preimage`;
- best owner abstraction: the Chapter 20 owner
  `pushforward_cohomologyOnOpen_isomorphic_preimage`, which compares cohomology of `f_* ℱ` on an
  open `U` with cohomology of `ℱ` on `f⁻¹(U)`;
- primitive data: a map `i : Z ⟶ X`, an abelian sheaf `F` on `Z`, the open `⊤ : Opens X`, and a
  degree `p`;
- derived API: the owner-oriented global specialization to `⊤ : Opens X` and the source-facing
  symmetric global-cohomology comparison below.

Source/core/bridge triage:
- `source-facing`: the global cohomology comparison for the map `i`;
- `core/canonical`: `pushforward_cohomologyOnOpen_isomorphic_preimage`;
- `bridge/view`: specializing the owner theorem to the top open.

The closed-embedding hypothesis from the textbook statement is redundant for this canonical
specialization, so it is not kept in the refined public API. -/
-- Proof sketch: this is the specialization of
-- `pushforward_cohomologyOnOpen_isomorphic_preimage` to the top open `⊤ : Opens X`.
/-- Owner-oriented companion for Lemma 20.20.1: the global degree-`p` cohomology of `i_* F` on
`X` is canonically isomorphic to the global degree-`p` cohomology of `F` on `Z`. -/
theorem pushforward_global_cohomology_isomorphic
    (i : Z ⟶ X) (F : Z.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    IsIsomorphic (((pushforward AddCommGrpCat.{u} i).obj F).H' p (⊤ : Opens X))
      (F.H' p (⊤ : Opens Z)) := by
  simpa using pushforward_cohomologyOnOpen_isomorphic_preimage i F (⊤ : Opens X) p

/-- Lemma 20.20.1: the source closed-embedding hypothesis is redundant, so for any map
`i : Z ⟶ X` and abelian sheaf `F` on `Z`, the global degree-`p` cohomology of `F` on `Z` is
canonically isomorphic to the global degree-`p` cohomology of `i_* F` on `X`. -/
@[stacks 02UV]
theorem global_cohomology_iso_pushforward
    (i : Z ⟶ X) (F : Z.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    IsIsomorphic (F.H' p (⊤ : Opens Z))
      (((pushforward AddCommGrpCat.{u} i).obj F).H' p (⊤ : Opens X)) := by
  rcases pushforward_global_cohomology_isomorphic i F p with ⟨e⟩
  exact ⟨by simpa using e.symm⟩

end Sheaf
end CategoryTheory
