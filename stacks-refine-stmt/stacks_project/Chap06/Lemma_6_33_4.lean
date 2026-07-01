import stacks_project.Chap06.Glueing_data_for_sheaves_on_an_open_cover
import stacks_project.Chap06.Lemma_6_33_1
import stacks_project.Chap06.Lemma_6_33_2

open CategoryTheory TopologicalSpace TopCat
open TopologicalSpace.Opens

noncomputable section

universe u v

section

variable {X : TopCat.{u}} {ι : Type v}

/- Domain-style sampling for Lemma 6.33.4:
- primary domain: sheaf descent along an open cover, expressed through gluing data;
- sampled owner declarations:
  `SheafOpenCoverGlueing`,
  `SheafOpenCoverGlueing.ofSheafFunctor`,
  `exists_unique_hom_of_open_cover`,
  `exists_sheaf_realizing_open_cover_glueing`;
- owner abstraction: the canonical project owner is `SheafOpenCoverGlueing U`, and the bridge from
  global sheaves to that owner is `SheafOpenCoverGlueing.ofSheafFunctor U hU`;
- primitive data: an open cover `U : ι → Opens X` with `TopologicalSpace.IsOpenCover U`;
- derived API: unique gluing of local morphisms and existence of a realizing sheaf.

Source/core/bridge triage:
- `source-facing`: the textbook equivalence between sheaves on `X` and gluing data on the open
  cover `U`;
- `core/canonical`: the owner `SheafOpenCoverGlueing U`;
- `bridge/view`: the restriction functor `SheafOpenCoverGlueing.ofSheafFunctor U hU`. -/

-- Proof sketch: use `exists_unique_hom_of_open_cover` to identify the restriction functor as full
-- and faithful, and `exists_sheaf_realizing_open_cover_glueing` to show essential surjectivity.
/-- Lemma 6.33.4: for an open cover `X = ⋃ i, U i`, restricting a sheaf of sets on `X` to the
members of the cover and their pairwise identifications yields an equivalence between sheaves on
`X` and the category of open-cover gluing data for `U`. -/
theorem sheafRestrictionToOpenCover_isEquivalence
    (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U) :
    Functor.IsEquivalence (SheafOpenCoverGlueing.ofSheafFunctor U hU) := by
  sorry

end
