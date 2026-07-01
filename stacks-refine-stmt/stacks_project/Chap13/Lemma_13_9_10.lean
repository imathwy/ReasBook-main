import Mathlib
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import stacks_project.Chap12.Lemma_12_14_12

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Pretriangulated ComplexShape HomologicalComplex
open CategoryTheory.CochainComplex

universe u v

namespace CochainComplex

section

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable (S : ShortComplex (CochainComplex V ℤ))
variable (σ σ' : ∀ n : ℤ, (degreewiseShortComplex S n).Splitting)

local notation "Q" => HomotopyCategory.quotient V (up ℤ)

/- Domain-style sampling for Lemma 13.9.10:
- primary domain: degreewise split short complexes of cochain complexes and the induced triangles
  in the homotopy category;
- inspected owner declarations:
  `CochainComplex.trianglehOfDegreewiseSplit`,
  `CochainComplex.homOfDegreewiseSplit`,
  `CochainComplex.sectionDifference`,
  `CochainComplex.homOfDegreewiseSplit_homotopy_of_splitting_difference`,
  `Triangle.isoMk`;
- best owner abstraction: the bridge/view owner is
  `CochainComplex.trianglehOfDegreewiseSplit S σ`, so the comparison for two splittings of the
  same short complex should be a thin triangle isomorphism built from identities on objects and
  the Chapter 12 owner homotopy theorem for the connecting morphisms;
- primitive data: the short complex `S` and the two degreewise splitting families `σ`, `σ'`;
- derived API: the induced identity-on-objects triangle isomorphism. The three commutativity
  equalities are proof data for that isomorphism, not standalone public API.

Source/core/bridge triage:
- `source-facing`: the comparison between the triangles attached to the same termwise split short
  complex with two splitting choices;
- `core/canonical`: `trianglehOfDegreewiseSplit`, `homOfDegreewiseSplit`,
  `sectionDifference`, `homOfDegreewiseSplit_homotopy_of_splitting_difference`, and
  `Triangle.isoMk`;
- `bridge/view`: the resulting identity-on-objects triangle isomorphism.
-/

-- Proof sketch: the first two arrows in `trianglehOfDegreewiseSplit S σ` depend only on `S.f` and
-- `S.g`, so the corresponding squares commute by `simp`. For the third arrow, the canonical
-- section-difference family `hⁿ = s'ⁿ ≫ rⁿ` satisfies
-- `(σ' n).s = (σ n).s + hⁿ ≫ fⁿ`; Lemma 12.14.12 then shows that the two connecting morphisms are
-- homotopic, hence equal in the homotopy category.
/-- Lemma 13.9.10: for two choices of degreewise splittings of the same termwise split exact
sequence of cochain complexes, the associated triangles in the homotopy category are isomorphic by
the identity on all three terms. -/
noncomputable def trianglehOfDegreewiseSplit_iso_of_splittings :
    trianglehOfDegreewiseSplit S σ ≅ trianglehOfDegreewiseSplit S σ' :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [triangleOfDegreewiseSplit])
    (by simp [triangleOfDegreewiseSplit])
    (by
      let h :
          ∀ n : ℤ, (degreewiseShortComplex S n).X₃ ⟶ (degreewiseShortComplex S n).X₁ :=
        fun n ↦ (σ' n).s ≫ (σ n).r
      have hs : sectionDifference S σ σ' h := by
        intro n
        change (σ' n).s = (σ n).s + ((σ' n).s ≫ (σ n).r) ≫
          (degreewiseShortComplex S n).f
        rw [Category.assoc, (σ n).r_f, Preadditive.comp_sub, Category.comp_id,
          (σ' n).s_g_assoc]
        abel
      simpa [triangleOfDegreewiseSplit] using
        congrArg
          (fun k ↦ k ≫ (Functor.commShiftIso Q 1).hom.app S.X₁)
          (HomotopyCategory.eq_of_homotopy _ _
            (homOfDegreewiseSplit_homotopy_of_splitting_difference S σ σ' h hs)).symm)

end

end CochainComplex
