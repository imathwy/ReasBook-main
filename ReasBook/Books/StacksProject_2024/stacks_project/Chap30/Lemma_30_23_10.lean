import Mathlib
import StacksProject_2024.Chap30.Lemma_30_23_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced `Scheme.IdealSheafData.comap`,
-- `Scheme.Modules.pullback`, and `Functor.IsEquivalence`; local Chapter 30 precedent uses
-- `CoherentFormalModules X I` and `IsCoherentFormalModulesPullbackFunctor` for the pullback
-- functor of Lemma 30.23.9.

/-- Lemma 30.23.10: let `f : X' ⟶ X` be a morphism of Noetherian schemes, let
`I : X.IdealSheafData` define a closed subscheme `Z ⊆ X`, and let `I.comap f` define the
scheme-theoretic inverse image `Z' = f^{-1} Z`. If `f` is flat and the induced morphism
`Z' ⟶ Z` is an isomorphism, then the pullback functor
`f^* : Coh(X, I) ⥤ Coh(X', I.comap f)` from Lemma 30.23.9 is an equivalence. -/
@[stacks 0EHQ]
theorem coherentFormalModules_pullbackFunctor_isEquivalence_of_flat_isIso_subschemeMap
    {X X' : Scheme.{u}} [IsNoetherian X] [IsNoetherian X']
    (f : X' ⟶ X) [Flat f] (I : X.IdealSheafData)
    [IsIso (IdealSheafData.subschemeMap (I.comap f) I f (I.le_map_comap f))]
    (pullbackFunctor : CoherentFormalModules X I ⥤ CoherentFormalModules X' (I.comap f))
    [IsCoherentFormalModulesPullbackFunctor f I pullbackFunctor] :
    Functor.IsEquivalence pullbackFunctor := sorry

end AlgebraicGeometry.Scheme
