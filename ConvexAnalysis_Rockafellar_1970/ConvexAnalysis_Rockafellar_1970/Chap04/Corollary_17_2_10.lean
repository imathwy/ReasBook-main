import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Lemma_17_2_9

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

open scoped BigOperators Rockafellar

variable {E : Type u} {R : Type v}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup E] [Module R E] [FiniteDimensional R E]

local notation "EStar" => E × R

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 17.2.10 sharpens the finite conic-combination representation from
  Lemma 17.2.9 by bounding the number of generators drawn from `SStar`.
- `core/canonical`: the owner abstraction is the generated cone `K⋆[R] SStar` in `E × R`,
  together with the source-facing bridge
  `mem_generated_cone_iff_exists_conicCombination`.
- `bridge/view`: clause (1) is the ambient Caratheodory reduction in `E × R`, giving at most
  `Module.finrank R E + 1` generators from `SStar`; clause (2) is the sharper reduction obtained
  by lowering to the bottom face of the simplex, exactly as in the proof pattern of
  Corollary 17.1.3.

Domain-style sampling used here:
- `K⋆[R]` from Definition 17.2.5;
- `mem_generated_cone_iff_exists_conicCombination` from Lemma 17.2.9;
- `exists_linearIndependent_nonnegativeCombination_of_ne_zero_mem_cone_iUnion` from
  Corollary 17.1.2.

Primitive data vs derived API:
- primitive input: membership of `(xStar, μStar)` in `K⋆[R] SStar`;
- derived output: a finite subset `s ⊆ SStar` and a nonnegative coefficient family indexed by
  `s.attach`, with the scalar-coordinate inequality from Lemma 17.2.9 and a bounded cardinality
  on `s`.

Layer target: `bridge/view`; the corollary keeps the source-facing representation language of
Lemma 17.2.9 directly as finite-support existential data, rather than introducing a wrapper owner.
-/

-- Proof sketch: apply the conic Caratheodory theorem in the ambient space `E × R` to the
-- directions from `SStar` together with the vertical unit `((0 : E), 1)`. Then rewrite the
-- resulting finite cone certificate through `mem_generated_cone_iff_exists_conicCombination`,
-- keeping only the points of `SStar` and preserving the finite-support witness data. This
-- leaves at most `Module.finrank R E + 1` generators from
-- `SStar`.
/-- Corollary 17.2.10 (1): the finite conic representation from Lemma 17.2.9 may be chosen with
at most `Module.finrank R E + 1` generators from `SStar`. Equivalently, every point of the
generated cone `K⋆[R] SStar` admits such a finite-support witness with cardinality at most
`dim E + 1`. -/
theorem mem_generated_cone_iff_exists_conicCombination_card_le_finrank_add_one
    {SStar : Set EStar} {xStar : E} {muStar : R} :
    (xStar, muStar) ∈ (K⋆[R] SStar) ↔
      ∃ s : Finset EStar,
        s.card ≤ Module.finrank R E + 1 ∧
          (∀ y ∈ s, y ∈ SStar) ∧
            ∃ weights : {y // y ∈ s} → R,
              (∀ y, 0 ≤ weights y) ∧
                xStar = s.attach.sum (fun y ↦ weights y • (y : EStar).1) ∧
                s.attach.sum (fun y ↦ weights y * (y : EStar).2) ≤ muStar := sorry

-- Proof sketch: start from clause (1). If the support has maximal size
-- `Module.finrank R E + 1`, the chosen generators determine a simplex in `E × R`; moving
-- downward along the vertical direction to the bottom face, exactly as in the "bottoms of
-- simplices" argument from Corollary 17.1.3, removes one generator while preserving the first
-- coordinate and only enlarging the available vertical slack. Rewriting again through
-- `mem_generated_cone_iff_exists_conicCombination` gives the sharper bound while preserving the
-- same finite-support witness data.
/-- Corollary 17.2.10 (2): the conic representation from Lemma 17.2.9 may in fact be chosen with
at most `Module.finrank R E` generators from `SStar`, by the bottoms-of-simplices reduction in
the ambient cone `K⋆[R] SStar`. Equivalently, one may choose the same finite-support witness data
with that smaller bound. -/
theorem mem_generated_cone_iff_exists_conicCombination_card_le_finrank
    {SStar : Set EStar} {xStar : E} {muStar : R} :
    (xStar, muStar) ∈ (K⋆[R] SStar) ↔
      ∃ s : Finset EStar,
        s.card ≤ Module.finrank R E ∧
          (∀ y ∈ s, y ∈ SStar) ∧
            ∃ weights : {y // y ∈ s} → R,
              (∀ y, 0 ≤ weights y) ∧
                xStar = s.attach.sum (fun y ↦ weights y • (y : EStar).1) ∧
                s.attach.sum (fun y ↦ weights y * (y : EStar).2) ≤ muStar := sorry

end
