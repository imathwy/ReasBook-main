import StacksProject_2024.stacks_project.Chap10.Lemma_10_66_6
import StacksProject_2024.stacks_project.Chap17.Definition_17_5_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_2_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules)

-- Semantic recall: Chapter 10 already provides the ring-level inclusions
-- `associatedPrimes.subset_weaklyAssociatedPrimes` and
-- `weaklyAssociatedPrimes.subset_support`, while Chapter 31 fixes the sheaf-side owners as
-- `associatedPoints` and `weakAss`. The source-facing statements below keep the lemma labels while
-- exposing the canonical Chapter 31 set owners for downstream reuse.

section

variable [ℱ.IsQuasicoherent]

/-- Lemma 31.5.3 (1): for a quasi-coherent `\mathcal O_X`-module `\mathcal F` on a scheme `X`,
every associated point of `\mathcal F` is weakly associated to `\mathcal F`. -/
@[stacks 05AM]
theorem associatedPoints_subset_weaklyAssociatedPoints :
    associatedPoints ℱ ⊆ ℱ.weakAss := sorry

end

/-- Lemma 31.5.3 (2): for an `\mathcal O_X`-module `\mathcal F` on a scheme `X`, every weakly
associated point of `\mathcal F` lies in the support of `\mathcal F`. -/
@[stacks 05AM]
theorem weaklyAssociatedPoints_subset_support :
    ℱ.weakAss ⊆ moduleSupport ℱ := sorry

end AlgebraicGeometry.Scheme.Modules
