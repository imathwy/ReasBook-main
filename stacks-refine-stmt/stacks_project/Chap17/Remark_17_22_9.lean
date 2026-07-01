import Mathlib
import Mathlib.CategoryTheory.Sites.Limits
import stacks_project.Chap06.Example_6_29_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

local notation "JX" => Opens.grothendieckTopology twoClosedPointsSpace

/- Domain-style sampling for Remark 17.22.9:
- primary domain: filtered-colimit comparison morphisms for global sections of abelian sheaves on a
  topological space;
- sampled owner abstractions:
  `twoClosedPointsSpace`,
  `tailPushforwardIntegerSheafFunctor`,
  `sheafSections`,
  `colimit.post`,
  `preservesColimit_of_isIso_post`,
  `tailPushforwardIntegerSheaf_exists_global_sections_colimit`,
  `tailPushforwardColimit_global_sections_comparison_isIso`;
- best owner abstraction: the explicit comparison morphism
  `colimit.post tailPushforwardIntegerSheafFunctor
    ((sheafSections JX AddCommGrpCat).obj (op ⊤))`;
- primitive data: the imported witness space `twoClosedPointsSpace` and filtered diagram
  `tailPushforwardIntegerSheafFunctor`;
- derived API: the class-level statement
  `PreservesColimit tailPushforwardIntegerSheafFunctor
    ((sheafSections JX AddCommGrpCat).obj (op ⊤))`
  and its negation, which are bridge consequences of the comparison-map failure;
- layer triage:
  `source-facing`: the explicit map
    `colim Γ(X, j_{n,*}\underline{Z}) → Γ(X, colim j_{n,*}\underline{Z})`;
  `core/canonical`: `colimit.post`;
  `bridge/view`: the explicit Chapter 6 witness
    `twoClosedPointsSpace`, `tailPushforwardIntegerSheafFunctor`, together with the derived
    `PreservesColimit` reformulation.
-/

-- Proof sketch: Example `6.29.2` identifies the colimit of the global sections of the system
-- `j_{n,*}\underline{\mathbf Z}` on a quasi-compact space with an object of sections `M`, while
-- the global sections of the colimit sheaf are `M ⊞ M`; hence global sections need not preserve a
-- filtered colimit on a quasi-compact space.
/-- The two-closed-points space from Example 6.29.2 is quasi-compact. -/
theorem isCompact_univ_twoClosedPointsSpace :
    IsCompact (Set.univ : Set twoClosedPointsSpace) := by
  sorry

/-- Remark 17.22.9: on the Chapter 6 two-closed-points space, the canonical comparison map
`colim Γ(X, j_{n,*}\underline{Z}) → Γ(X, colim j_{n,*}\underline{Z})` is not an isomorphism. -/
theorem twoClosedPoints_globalSections_colimitComparison_not_isIso :
    ¬ IsIso
      (colimit.post tailPushforwardIntegerSheafFunctor
        ((sheafSections JX AddCommGrpCat).obj (op ⊤))) := by
  sorry

/-- Remark 17.22.9: equivalently, the same comparison map of global sections is not bijective. -/
theorem twoClosedPoints_globalSections_colimitComparison_not_bijective :
    ¬ Function.Bijective
      (colimit.post tailPushforwardIntegerSheafFunctor
        ((sheafSections JX AddCommGrpCat).obj (op ⊤))) := by
  intro hbij
  exact twoClosedPoints_globalSections_colimitComparison_not_isIso
    ((ConcreteCategory.isIso_iff_bijective _).2 hbij)

/-- Remark 17.22.9: the failure of the canonical comparison map implies that the global-sections
functor does not preserve this filtered colimit. -/
theorem twoClosedPoints_globalSections_not_preserves_filteredColimit :
    ¬ PreservesColimit tailPushforwardIntegerSheafFunctor
      ((sheafSections JX AddCommGrpCat).obj (op ⊤)) := by
  intro hpres
  let _ : PreservesColimit tailPushforwardIntegerSheafFunctor
      ((sheafSections JX AddCommGrpCat).obj (op ⊤)) := hpres
  exact twoClosedPoints_globalSections_colimitComparison_not_isIso inferInstance

/-- Remark 17.22.9: Example 6.29.2 gives a quasi-compact space for which the canonical comparison
map from the colimit of global sections of a filtered system of sheaves of abelian groups to the
global sections of the colimit sheaf is not an isomorphism. Thus some hypothesis beyond
quasi-compactness of `X` is necessary in Lemma 17.22.8. -/
theorem quasiCompact_does_not_force_globalSections_colimitComparison_isIso :
    ∃ X : TopCat.{0}, IsCompact (Set.univ : Set X) ∧
      ∃ 𝓕 : ℕ ⥤ X.Sheaf AddCommGrpCat.{0},
        ¬ IsIso
          (colimit.post 𝓕
            ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op ⊤))) := by
  refine ⟨twoClosedPointsSpace, isCompact_univ_twoClosedPointsSpace, tailPushforwardIntegerSheafFunctor,
    ?_⟩
  simpa using twoClosedPoints_globalSections_colimitComparison_not_isIso

/-- Remark 17.22.9: in particular, quasi-compactness does not force the global-sections functor to
preserve filtered colimits. -/
theorem quasiCompact_does_not_force_globalSections_preserve_filteredColimits :
    ∃ X : TopCat.{0}, IsCompact (Set.univ : Set X) ∧
      ∃ 𝓕 : ℕ ⥤ X.Sheaf AddCommGrpCat.{0},
        ¬ PreservesColimit 𝓕
          ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op ⊤)) := by
  refine ⟨twoClosedPointsSpace, isCompact_univ_twoClosedPointsSpace, tailPushforwardIntegerSheafFunctor,
    ?_⟩
  simpa using twoClosedPoints_globalSections_not_preserves_filteredColimit
