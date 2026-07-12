import Mathlib
import StacksProject_2024.Chap30.«30_23_3_1»

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u v

-- Semantic recall: `lean_leansearch` surfaced `Scheme.IdealSheafData.support` as the canonical
-- closed subset cut out by an ideal sheaf; local file `30_23_3_1` supplies the chosen completion
-- functor owner into the source-facing category `\textit{Coh}(X, \mathcal I)`.

/-- Lemma 30.23.11: let `X` be a Noetherian scheme and let `I` and `J` be quasi-coherent
ideal sheaves. If they cut out the same closed subset, represented by
`I.support = J.support`, then the coherent formal-module categories
`\textit{Coh}(X, I)` and `\textit{Coh}(X, J)` are equivalent. -/
@[stacks 0EHR]
theorem coherentFormalModules_equivalent_of_idealSheaf_support_eq
    {X : Scheme.{u}} [IsNoetherian X] {I J : X.IdealSheafData}
    (ctxI : CoherentCompletionFunctor X I)
    (ctxJ : CoherentCompletionFunctor X J)
    (hIJ : I.support = J.support) :
    ∃ F : Scheme.CoherentFormalModules X I ⥤ Scheme.CoherentFormalModules X J, F.IsEquivalence :=
      sorry
