import Mathlib
import stacks_project.Chap15.Lemma_15_87_14_Emmanouil

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
namespace CategoryTheory

namespace SequentialInverseSystem

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat

/- Domain-style sampling for Lemma 15.87.15:
- primary domain: short exact sequences of sequential inverse systems of abelian groups, the
  first derived inverse limit, and the Emmanouil criterion for the Mittag-Leffler condition;
- sampled owner declarations:
  `SequentialInverseSystem.IsMittagLeffler`,
  `SequentialInverseSystem.countableCoproduct`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `sequentialAbelianGroupLimit_exact₅`,
  `ShortComplex.ShortExact.map_of_exact`;
- best owner abstraction: the tower owner is `SequentialInverseSystem AddCommGrpCat`, the
  vanishing obstruction is `firstDerivedLimit`, the countable direct-sum tower is the canonical
  derived owner `countableCoproduct`, and preservation of short exactness under stagewise countable
  coproducts should be expressed by mapping along the exact functor rather than by a parallel
  stagewise wrapper;
- primitive-vs-derived split:
  primitive data are only the short exact sequence `S` and the two source-facing
  hypotheses `S.X₁.IsMittagLeffler` and `S.X₃.IsMittagLeffler`;
  the vanishing of the two `R^1 lim` terms and the mapped short exact sequence on countable
  coproduct towers are derived API from the canonical owners above.

Source/core/bridge triage:
- `source-facing`: the middle-term Mittag-Leffler conclusion for a short exact sequence of towers;
- `core/canonical`: `IsMittagLeffler`, `countableCoproduct`, `firstDerivedLimit`, and the five-term
  exact sequence `sequentialAbelianGroupLimit_exact₅`;
- `bridge/view`: applying Emmanouil's criterion to the three towers and, proof-theoretically, the
  exact `R^1 lim` sequence and stagewise countable direct sums in abelian groups.
-/

/-- Lemma 15.87.15: for a short exact sequence `0 ⟶ (A_i) ⟶ (B_i) ⟶ (C_i) ⟶ 0` of inverse
systems of abelian groups, if `(A_i)` and `(C_i)` are Mittag-Leffler, then `(B_i)` is
Mittag-Leffler. -/
theorem isMittagLeffler_middle_of_shortExact
    (S : ShortComplex AbSeq)
    (hS : S.ShortExact)
    (hA : S.X₁.IsMittagLeffler)
    (hC : S.X₃.IsMittagLeffler) :
    S.X₂.IsMittagLeffler := by
  -- Apply Emmanouil's criterion to `S.X₂`. The proof uses the exact sequence for `R^1 lim`
  -- together with the same argument after taking stagewise countable direct sums.
  sorry

end SequentialInverseSystem

end CategoryTheory
