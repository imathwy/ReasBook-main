import Mathlib
import StacksProject_2024.Chap25.Lemma_25_6_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory

-- Semantic search note: no `lean_leansearch` tool was available in this run; this item is the
-- terminal-presheaf specialization of the local Lemma 25.6.4 spectral-sequence owner.

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [Limits.HasEqualizers C] [Limits.HasPullbacks C]
variable [HasWeakSheafify J (Type (max w v))]
variable [HasWeakSheafify J AddCommGrpCat.{max w v}]
variable [HasSheafify J AddCommGrpCat.{max w v}]
variable [HasExt.{max u v w} (Sheaf J AddCommGrpCat.{max w v})]

/-- Lemma 25.6.5: if `K` is a hypercovering of the site and `\mathcal F` is an abelian
sheaf, then the Lemma 25.6.4 spectral sequence for the terminal presheaf has
`E_2^{p,q} = \check H^p(K, \underline H^q(\mathcal F))` and converges to the global cohomology
groups `H^{p+q}(\mathcal F)`. -/
@[stacks 09VY]
theorem hypercoveringCohomologySpectralSequence_exists
    (K : HypercoveringOf.Terminal J)
    (ℱ : Sheaf J AddCommGrpCat.{max w v}) :
    Nonempty (HypercoveringOfCohomologySpectralSequence K ℱ) := sorry

end CategoryTheory
