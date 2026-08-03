import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap01.Text_1_0_10
import BauschkeLean.Chap20.Definition_20_1
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap20.Proposition_20_56
import BauschkeLean.Chap20.Definition_20_51
import BauschkeLean.Chap25.Definition_25_10
import BauschkeLean.Chap25.Theorem_25_24

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Corollary 25.27 states the surjectivity conclusion for `A + B` under the
  chapter's `3*`-monotonicity hypotheses.
- `core/canonical`: the Chapter 25 owner for those hypotheses is
  `SetValuedOperator.IsThreeStarMonotone`.
- `bridge/view`: `BauschkeLean.Chap25.Definition_25_10` already exposes the canonical bridge to
  the Fitzpatrick-domain inclusions used in downstream Chapter 25 arguments, while
  `Theorem_25_24` now owns the reusable Chapter 25 bridges from the stronger `3*` hypotheses to
  `FitzpatrickDomainCondition`. -/

/-- Helper for Corollary 25.27: Theorem 25.23 turns the Fitzpatrick-domain condition into the
surjectivity of `A + B` once one summand is already surjective. -/
private theorem range_add_eq_univ_of_fitzpatrick_domain_condition
    {A B : SetValuedOperator H H} (hA_mono : A.IsMonotone) (hB_mono : B.IsMonotone)
    (hAB_max : Maximal IsMonotone (A + B))
    (hsurj : A.range = Set.univ ∨ B.range = Set.univ) (hfitz : FitzpatrickDomainCondition A B) :
    (A + B).range = Set.univ := by
  rcases exists_mem_dom_inter_of_maximal_add hAB_max with ⟨x0, hx0⟩
  rcases (SetValuedOperator.mem_dom_iff A x0).1 hx0.1 with ⟨u0, hu0⟩
  rcases (SetValuedOperator.mem_dom_iff B x0).1 hx0.2 with ⟨v0, hv0⟩
  have hu0_range : u0 ∈ A.range := (SetValuedOperator.mem_range_iff A u0).2 ⟨x0, hu0⟩
  have hv0_range : v0 ∈ B.range := (SetValuedOperator.mem_range_iff B v0).2 ⟨x0, hv0⟩
  have hrange_sum : A.range + B.range = Set.univ := by
    rcases hsurj with hAuniv | hBuniv
    · -- Use the fixed point of `range B` to split every vector through the surjective `A`.
      apply Set.eq_univ_iff_forall.2
      intro w
      refine Set.mem_add.2 ⟨w - v0, ?_, v0, hv0_range, by abel_nf⟩
      simp [hAuniv]
    · -- Symmetrically, use the fixed point of `range A` to split every vector through `B`.
      apply Set.eq_univ_iff_forall.2
      intro w
      refine Set.mem_add.2 ⟨u0, hu0_range, w - u0, ?_, by abel_nf⟩
      simp [hBuniv]
  have hinterior :
      interior (A + B).range = Set.univ := by
    -- Theorem 25.23 identifies the interior of `range (A + B)` with the interior of the range sum.
    calc
      interior (A + B).range
          = interior (A.range + B.range) :=
            interior_range_add_eq_interior_range_sum_of_fitzpatrick_domain_condition
              hA_mono hB_mono hAB_max hfitz
      _ = Set.univ := by simp [hrange_sum]
  -- Since the interior is already all of `H`, the range itself must be all of `H`.
  exact Set.eq_univ_iff_forall.2 fun w ↦ by
    have hw_int : w ∈ interior (A + B).range := by
      simp [hinterior]
    exact interior_subset hw_int

/-- Corollary 25.27 (1): if `A` and `B` are monotone, `A + B` is maximally monotone, one of
`A` or `B` is surjective, and both operators are `3*` monotone, then `A + B` is surjective. -/
theorem range_add_eq_univ_of_isThreeStarMonotone
    {A B : SetValuedOperator H H} (hA_mono : A.IsMonotone) (hB_mono : B.IsMonotone)
    (hAB_max : Maximal IsMonotone (A + B))
    (hsurj : A.range = Set.univ ∨ B.range = Set.univ)
    (hA_threeStar : A.IsThreeStarMonotone) (hB_threeStar : B.IsThreeStarMonotone) :
    (A + B).range = Set.univ := by
  have hfitz : FitzpatrickDomainCondition A B :=
    fitzpatrickDomainCondition_of_isThreeStarMonotone hAB_max hA_threeStar hB_threeStar
  -- The common domain point supplies the Chapter 25 hypothesis, and the shared closing lemma
  -- turns it into the desired surjectivity statement.
  exact range_add_eq_univ_of_fitzpatrick_domain_condition
    hA_mono hB_mono hAB_max hsurj hfitz

/-- Corollary 25.27 (2): if `A` and `B` are monotone, `A + B` is maximally monotone, one of
`A` or `B` is surjective, `dom A ⊆ dom B`, and `B` is `3*` monotone, then `A + B` is surjective. -/
theorem range_add_eq_univ_of_dom_subset_and_isThreeStarMonotone
    {A B : SetValuedOperator H H} (hA_mono : A.IsMonotone) (hB_mono : B.IsMonotone)
    (hAB_max : Maximal IsMonotone (A + B))
    (hsurj : A.range = Set.univ ∨ B.range = Set.univ) (hdom : A.dom ⊆ B.dom)
    (hB_threeStar : B.IsThreeStarMonotone) :
    (A + B).range = Set.univ := by
  have hfitz : FitzpatrickDomainCondition A B :=
    fitzpatrickDomainCondition_of_dom_subset_and_isThreeStarMonotone hA_mono hdom hB_threeStar
  -- The asymmetric domain inclusion furnishes the same Fitzpatrick-domain hypothesis, so the
  -- closing argument from Theorem 25.23 applies unchanged.
  exact range_add_eq_univ_of_fitzpatrick_domain_condition
    hA_mono hB_mono hAB_max hsurj hfitz

end SetValuedOperator
