import Mathlib
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import StacksProject_2024.Chap12.Lemma_12_14_12

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
/-- Helper for Lemma 13.9.10: the canonical correction family comparing the two degreewise
splittings. -/
private abbrev splittingDifferenceCorrection :
    ∀ n : ℤ, (degreewiseShortComplex S n).X₃ ⟶ (degreewiseShortComplex S n).X₁ :=
  fun n ↦ (σ' n).s ≫ (σ n).r

/-- Helper for Lemma 13.9.10: the canonical correction family satisfies the section-difference
identity required by Lemma 12.14.12. -/
private theorem splitting_difference_witness :
    sectionDifference S σ σ' (splittingDifferenceCorrection (S := S) σ σ') := by
  -- Expand the correction term and cancel the common summands additively.
  intro n
  change (σ' n).s = (σ n).s + ((σ' n).s ≫ (σ n).r) ≫ (degreewiseShortComplex S n).f
  rw [Category.assoc, (σ n).r_f, Preadditive.comp_sub, Category.comp_id, (σ' n).s_g_assoc]
  abel

/-- Helper for Lemma 13.9.10: the two connecting morphisms become equal in the homotopy
category because Lemma 12.14.12 gives a homotopy between them. -/
private theorem homOfDegreewiseSplit_eq_in_homotopy_category_of_splittings :
    (HomotopyCategory.quotient V (up ℤ)).map (homOfDegreewiseSplit S σ') =
      (HomotopyCategory.quotient V (up ℤ)).map (homOfDegreewiseSplit S σ) := by
  -- Pass from the source-level homotopy to equality in the quotient category.
  exact HomotopyCategory.eq_of_homotopy _ _
    (homOfDegreewiseSplit_homotopy_of_splitting_difference
      (S := S) (spl := σ) (spl' := σ')
      (h := splittingDifferenceCorrection (S := S) σ σ')
      (splitting_difference_witness (S := S) (σ := σ) (σ' := σ')))

/-- Helper for Lemma 13.9.10: the first square in the identity-on-objects triangle comparison
commutes because the first arrow depends only on the short complex. -/
private theorem triangleh_first_morphism_comm_of_splittings :
    (trianglehOfDegreewiseSplit S σ).mor₁ ≫ (Iso.refl _).hom =
      (Iso.refl _).hom ≫ (trianglehOfDegreewiseSplit S σ').mor₁ := by
  -- Both sides are the same image of `S.f`.
  simp

/-- Helper for Lemma 13.9.10: the second square in the identity-on-objects triangle comparison
commutes because the second arrow depends only on the short complex. -/
private theorem triangleh_second_morphism_comm_of_splittings :
    (trianglehOfDegreewiseSplit S σ).mor₂ ≫ (Iso.refl _).hom =
      (Iso.refl _).hom ≫ (trianglehOfDegreewiseSplit S σ').mor₂ := by
  -- Both sides are the same image of `S.g`.
  simp

/-- Helper for Lemma 13.9.10: the third square commutes because the two connecting morphisms are
equal in the homotopy category. -/
private theorem triangleh_third_morphism_comm_of_splittings :
    (trianglehOfDegreewiseSplit S σ).mor₃ ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory V (up ℤ)) 1).map (Iso.refl _).hom =
      (Iso.refl _).hom ≫ (trianglehOfDegreewiseSplit S σ').mor₃ := by
  -- Postcompose the equality of connecting morphisms with the fixed shift comparison used in the
  -- triangle construction.
  simpa [triangleOfDegreewiseSplit] using
    congrArg
      (fun k ↦ k ≫ (Functor.commShiftIso Q 1).hom.app S.X₁)
      (homOfDegreewiseSplit_eq_in_homotopy_category_of_splittings
        (S := S) (σ := σ) (σ' := σ')).symm

/-- Lemma 13.9.10: for two choices of degreewise splittings of the same termwise split exact
sequence of cochain complexes, the associated triangles in the homotopy category are isomorphic by
the identity on all three terms. -/
noncomputable def trianglehOfDegreewiseSplit_iso_of_splittings :
    trianglehOfDegreewiseSplit S σ ≅ trianglehOfDegreewiseSplit S σ' :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (triangleh_first_morphism_comm_of_splittings (S := S) (σ := σ) (σ' := σ'))
    (triangleh_second_morphism_comm_of_splittings (S := S) (σ := σ) (σ' := σ'))
    (triangleh_third_morphism_comm_of_splittings (S := S) (σ := σ) (σ' := σ'))

end

end CochainComplex
