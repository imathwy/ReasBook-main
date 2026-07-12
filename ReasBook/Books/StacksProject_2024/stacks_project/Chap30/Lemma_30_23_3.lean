import Mathlib
import StacksProject_2024.Chap30.«30_23_3_1»

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u v

-- Semantic recall: `lean_leansearch` surfaced `ModuleCat.epi_iff_surjective` and
-- `Functor.ReflectsEpimorphisms`; locally, `30_23_3_1` provides the existing target category
-- context for `Coh(X, I)`. The stage-one test is therefore recorded as an epimorphism criterion
-- for a chosen first-stage functor out of that target category.

/-- Lemma 30.23.3: for a Noetherian scheme `X` and a quasi-coherent ideal sheaf
`I : X.IdealSheafData`, a morphism in `Coh(X, I)` is surjective if and only if its first-stage
map `F₁ ⟶ G₁` is surjective, where `firstStage` is the functor sending a coherent formal module
to its first stage. -/
@[stacks 087Y]
theorem coherentFormalModules_epi_iff_firstStage_epi
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (firstStage : Scheme.CoherentFormalModules X I ⥤ RingedSpace.Coh X.toRingedSpace)
    {F G : Scheme.CoherentFormalModules X I} (φ : F ⟶ G) :
    Epi φ ↔ Epi (firstStage.map φ) := sorry
