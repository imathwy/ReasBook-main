import Mathlib
import StacksProject_2024.Chap30.«30_23_3_1»

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

-- Semantic recall: `lean_leansearch` surfaced `AdicCompletion`, the tensor-product model for
-- finite-module completions, and the local source-facing chosen completion functor. The current
-- scheme-level formal-module category is `Scheme.CoherentFormalModules X I`, while the inverse
-- system below is the source system `n ↦ H⁰(X, 𝓗 / Iⁿ𝓗)`.

/-- Lemma 30.23.5: for a Noetherian scheme `X`, a quasi-coherent ideal sheaf `I`, and coherent
modules `F` and `G`, if `𝓗 = Hom(G, F)` and `homSections` is the inverse system
`n ↦ H⁰(X, 𝓗 / Iⁿ𝓗)`, then its limit is the morphism set in
`\textit{Coh}(X, I)` from `G^∧` to `F^∧`. -/
@[stacks 0882]
theorem coherentCompletion_hom_equiv_sectionsLimit
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (F G : RingedSpace.Coh X.toRingedSpace)
    (homSections : ℕᵒᵖ ⥤ Type v) :
    Nonempty (limit homSections ≃
      (ctx.obj G ⟶ ctx.obj F)) := sorry
