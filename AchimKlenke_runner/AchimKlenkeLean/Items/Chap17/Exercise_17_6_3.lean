import AchimKlenkeLean.Items.Chap14.Lemma_14_27
import AchimKlenkeLean.Items.Chap17.Definition_17_16
import AchimKlenkeLean.Items.Chap17.Definition_17_30
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {G : Type u} [AddCommGroup G]

section

variable {Ω : Type v} [MeasurableSpace Ω]
variable [Countable G] [MeasurableSpace G] [DiscreteMeasurableSpace G]

/- Layering for Exercise 17.6.3:
- core/canonical owner: a step law `ν : ProbabilityMeasure G` together with
  `[IsMarkovProcessRealization (fun n ↦ dirac_convolution_kernel (ν : Measure G) ^ n) P X]`;
- bridge/view: a translation-invariant transition matrix `p`, whose row at `0` is the common
  increment law;
- source-facing conclusion: an irreducible random walk on a countable Abelian group is positive
  recurrent exactly when the group is finite. -/

-- Proof sketch: Theorem 17.51 identifies positive recurrence of an irreducible chain with the
-- existence of an invariant distribution. For the canonical convolution kernel of a group step law
-- `ν`, any invariant distribution must be constant on all translates, so it can have total mass
-- `1` only when `G` is finite; conversely, if `G` is finite, the normalized counting measure is
-- invariant under the walk, and Theorem 17.51 yields positive recurrence.
/-- Exercise 17.6.3 at the owner layer: an irreducible random walk on a countable Abelian group
with step law `ν` is positive recurrent if and only if the group is finite. The canonical public
interface is the convolution-kernel realization of the walk. -/
theorem irreducible_abelianGroupRandomWalk_isPositiveRecurrent_iff_finite
    (ν : ProbabilityMeasure G)
    (P : G → ProbabilityMeasure Ω) (X : ℕ → Ω → G)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure G) ^ n) P X]
    [Kernel.IsIrreducible
      (Measure.count : Measure G) (dirac_convolution_kernel (ν : Measure G))] :
    IsPositiveRecurrentMarkovChain P X ↔ Finite G := sorry

-- Proof sketch: the hypothesis `∀ x y, p x y = p 0 (y - x)` identifies the row `p 0` as the
-- intrinsic increment law of the walk. The realization instance forces `discreteMatrixKernel p`
-- to be a Markov kernel, so the row-sum condition is derivable internally; thus this is exactly
-- the owner theorem above read in the source matrix presentation.
/-- Bridge form of Exercise 17.6.3: if the transition matrix depends only on the increment
`y - x`, then the irreducible walk is positive recurrent exactly when the group is finite. The
translation-invariant matrix presentation is kept only as a source-facing view of the owner
step-law theorem. -/
theorem irreducible_translationInvariant_groupRandomWalk_isPositiveRecurrent_iff_finite
    (p : G → G → ℝ≥0∞)
    (htranslation : ∀ x y : G, p x y = p 0 (y - x))
    (P : G → ProbabilityMeasure Ω) (X : ℕ → Ω → G)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [Kernel.IsIrreducible (Measure.count : Measure G) (discreteMatrixKernel p)] :
    IsPositiveRecurrentMarkovChain P X ↔ Finite G := sorry

end

end ProbabilityTheory
