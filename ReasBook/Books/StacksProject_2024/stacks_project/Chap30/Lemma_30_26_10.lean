import StacksProject_2024.stacks_project.Chap30.Lemma_30_4_5
import StacksProject_2024.stacks_project.Chap30.Definition_30_26_2
import StacksProject_2024.stacks_project.Chap30.Lemma_30_12_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme}

/- Semantic recall: `lean_leansearch` returned no dedicated higher-direct-image coherence
theorem for proper support; nearby Chapter 30 files use `ClosedSubset.IsProperOver` for closed
subsets proper over a base and `((Scheme.Modules.pushforward f).rightDerived p).obj ℱ` for
`R^p f_* ℱ`. The tag evidence is consistent for Stacks tag `08DS`. -/

/-- Lemma 30.26.10: let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be locally of
finite type, and let `ℱ` be a coherent `\mathcal O_X`-module whose support, represented by a
closed subset `Z`, is proper over `S`. Then every higher direct image `R^p f_* ℱ` is a coherent
`\mathcal O_S`-module. -/
@[stacks 08DS]
theorem higherDirectImageModule_isCoherent_of_locallyOfFiniteType_hasProperSupportOver
    (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    [HasInjectiveResolutions X.Modules]
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (Z : TopologicalSpace.Closeds X)
    (hZ : (Z : Set X) = Scheme.Modules.moduleSupport ℱ)
    [ClosedSubset.IsProperOver f Z]
    (p : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived p).obj ℱ).IsCoherent := sorry

end AlgebraicGeometry.Scheme
