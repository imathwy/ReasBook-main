import Mathlib
import StacksProject_2024.stacks_project.Chap30.«30_23_3_1»

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u v

-- Semantic recall: `lean_leansearch` identified `CategoryTheory.exactFunctor` as the canonical
-- exactness predicate for a functor; the local equation file `30_23_3_1` supplies the chosen
-- completion functor owner `CoherentCompletionFunctor`.

/-- Lemma 30.23.4: the completion functor (30.23.3.1)
`\textit{Coh}(\mathcal{O}_X) \to \textit{Coh}(X, \mathcal{I})` is exact. -/
@[stacks 0881]
theorem coherentCompletionFunctor_exact
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I) :
    exactFunctor (RingedSpace.Coh X.toRingedSpace) (Scheme.CoherentFormalModules X I) ctx := sorry
