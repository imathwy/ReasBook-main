import Mathlib.Topology.Bornology.Basic
import BauschkeLean.Chap21.Proposition_21_11
import BauschkeLean.Chap21.Proposition_21_12

open scoped InnerProductSpace SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Source/core/bridge triage:
-- - `source-facing`: Corollary 21.19 asserts boundedness of the image `A(C)` of a compact set.
-- - `core/canonical`: Chapter 21 packages local boundedness as
--   `SetValuedOperator.IsLocallyBoundedAt`.
-- - `bridge/view`: `A.fstImageDomFitzpatrick` upgrades `interior A.dom` to the pointwise owner
--   `SetValuedOperator.IsLocallyBoundedAt`, and compactness then upgrades pointwise boundedness to
--   boundedness of `A.image C`.

-- Semantic recall: `lean_leansearch` returned only generic bornology bounded-image results, so the
-- local Chapter 21 owners stay `A.image C`, `interior A.dom`, and `A.IsMonotone`. The source
-- statement is kept at that monotone level rather than strengthened to a maximal-monotonicity
-- corollary.

/-- Corollary 21.19: if `A : H → 2^H` is monotone and `C` is a compact subset of
`interior A.dom`, then `A(C)` is bounded, formalized as `Bornology.IsBounded (A.image C)`. -/
theorem image_bounded_of_isCompact_of_subset_interior_dom
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) (C : Set H)
    (hCcompact : IsCompact C) (hCsubset : C ⊆ interior A.dom) :
    Bornology.IsBounded (A.image C) := by
  classical
  -- Route correction: use the monotone-level Fitzpatrick interior bridge pointwise on `C`,
  -- then compactness converts those local bounded neighborhoods into a finite bounded cover.
  have hlocal :
      ∀ x ∈ C, ∃ ε > 0, Bornology.IsBounded (A.image (Metric.ball x ε)) := by
    intro x hx
    -- Each point of `C` lies in `interior A.dom`, so Proposition 21.11 gives a bounded image ball.
    rcases isLocallyBoundedAt_of_mem_interior_fst_image_dom_fitzpatrick A hA_mono
        (interior_dom_subset_interior_fst_image_dom_fitzpatrick A hA_mono (hCsubset hx)) with
      ⟨ε, hε, hbounded⟩
    exact ⟨ε, hε, hbounded⟩
  choose ε hε hbounded using hlocal
  -- Compactness extracts finitely many of the pointwise balls that still cover `C`.
  rcases hCcompact.elim_nhds_subcover'
      (fun x hx ↦ Metric.ball x (ε x hx))
      (fun x hx ↦ Metric.ball_mem_nhds x (hε x hx)) with
    ⟨t, htcover⟩
  have hbounded_union :
      Bornology.IsBounded (⋃ x ∈ t, A.image (Metric.ball (x : H) (ε x x.2))) := by
    -- The image of each selected ball is bounded, so the finite union stays bounded.
    rw [Bornology.isBounded_biUnion_finset]
    intro x hx
    exact hbounded x x.2
  -- Any `y ∈ A.image C` comes from some `z ∈ C`, and the finite cover places `z` in one chosen ball.
  refine hbounded_union.subset ?_
  intro y hy
  rcases (SetValuedOperator.mem_image A C y).1 hy with ⟨z, hzC, hyz⟩
  rcases Set.mem_iUnion.1 (htcover hzC) with ⟨x, hxcover⟩
  rcases Set.mem_iUnion.1 hxcover with ⟨hx, hzball⟩
  exact Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨hx,
    (SetValuedOperator.mem_image A (Metric.ball (x : H) (ε x x.2)) y).2 ⟨z, hzball, hyz⟩⟩⟩

end SetValuedOperator
