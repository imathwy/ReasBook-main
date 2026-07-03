import Mathlib
import StacksProject_2024.Chap19.«19_2_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite

noncomputable section

/-- The transition map between consecutive finite initial segments of `ℕ`, modeled by
`Fin (n + 1) ⟶ Fin (n + 2)`. -/
def nat_initial_segment_map (n : ℕ) : Fin (n + 1) ⟶ Fin (n + 2) :=
  Fin.castSucc

/-- The sequential diagram of finite initial segments of `ℕ` in the category of sets. -/
def nat_initial_segment_diagram : ℕ ⥤ Type :=
  Functor.ofSequence nat_initial_segment_map

/-- The map `ℕ → colimit nat_initial_segment_diagram` sending `n` to the class of the top element
of the `n`-th finite initial segment. -/
def nat_initial_segment_colimit_map : ℕ → colimit nat_initial_segment_diagram :=
  fun n ↦ colimit.ι nat_initial_segment_diagram n (Fin.last n)

/-- The canonical map from `ℕ` to the colimit of the finite initial segments does not factor
through any single stage `Fin (m + 1)`. -/
-- Proof sketch: if such a factorization through `Fin (m + 1)` existed, the image of every natural
-- number in the colimit would already come from that finite stage, contradicting the fact that the
-- elements represented by `Fin.last n` require arbitrarily large stages.
theorem nat_initial_segment_colimit_map_not_factor_through_stage (m : ℕ) :
    ¬ ∃ f : ℕ → Fin (m + 1),
        nat_initial_segment_colimit_map = fun n ↦ colimit.ι nat_initial_segment_diagram m (f n) :=
  sorry

/-- Example 19.2.1: in the category of sets, for the sequential system of finite initial
segments of `ℕ` modeled by `Fin (n + 1)`, the canonical comparison map from the colimit of the
stagewise Hom-sets `ℕ → Fin (n + 1)` to the Hom-set `ℕ → colimit nat_initial_segment_diagram` is
not surjective. -/
-- Proof sketch: apply `nat_initial_segment_colimit_map_not_factor_through_stage` to the map
-- `nat_initial_segment_colimit_map`. Any element in the image of the comparison map comes from a
-- single stage, so this specific map cannot lie in the image.
theorem nat_initial_segment_hom_colimit_comparison_not_surjective :
    ¬ Function.Surjective
      (colimit.post nat_initial_segment_diagram (coyoneda.obj (op ℕ))) := sorry
