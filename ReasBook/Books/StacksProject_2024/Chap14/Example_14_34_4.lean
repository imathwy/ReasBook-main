import Mathlib
import stacks_project.Chap14.Definition_14_26_6
import stacks_project.Chap14.Example_14_33_1
import stacks_project.Chap14.Lemma_14_33_2
import stacks_project.Chap14.Lemma_14_34_2

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open CategoryTheory
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Augmented
open AlgebraicTopology
open Functor
open scoped Simplicial
open scoped IteratedEndofunctor

universe u

noncomputable section

namespace CategoryTheory

variable (R : Type u) [Ring R]

private abbrev freeForgetResolutionFunctor (R : Type u) [Ring R] :
    ModuleCat R ⥤ ModuleCat R :=
  (ModuleCat.adj R).toComonad.toFunctor

private theorem freeForgetAdjunctionResolution_realization :
    IteratedEndofunctorRealization (ModuleCat.adj R).toComonad.ε
      (ModuleCat.adj R).toComonad.δ
      (iteratedEndofunctorResolution
        (ModuleCat.adj R).toComonad.ε
        (ModuleCat.adj R).toComonad.δ
        (adjunction_iteratedEndofunctor_hσδ₀ (ModuleCat.adj R))
        (adjunction_iteratedEndofunctor_hσδ₁ (ModuleCat.adj R))
        (adjunction_iteratedEndofunctor_hσσ (ModuleCat.adj R))) :=
  iteratedEndofunctorResolution_realization
    (ModuleCat.adj R).toComonad.ε
    (ModuleCat.adj R).toComonad.δ
    (adjunction_iteratedEndofunctor_hσδ₀ (ModuleCat.adj R))
    (adjunction_iteratedEndofunctor_hσδ₁ (ModuleCat.adj R))
    (adjunction_iteratedEndofunctor_hσσ (ModuleCat.adj R))

/-- The augmented simplicial endofunctor resolution attached to the free-forgetful adjunction on
`ModuleCat R`. -/
private noncomputable def freeForgetAdjunctionAugmentedResolution :
    SimplicialObject.Augmented (ModuleCat R ⥤ ModuleCat R) where
  left :=
    iteratedEndofunctorResolution
      (ModuleCat.adj R).toComonad.ε
      (ModuleCat.adj R).toComonad.δ
      (adjunction_iteratedEndofunctor_hσδ₀ (ModuleCat.adj R))
      (adjunction_iteratedEndofunctor_hσδ₁ (ModuleCat.adj R))
      (adjunction_iteratedEndofunctor_hσσ (ModuleCat.adj R))
  right := 𝟭 (ModuleCat R)
  hom :=
    iteratedEndofunctorAugmentation
      (ModuleCat.adj R).toComonad.ε
      (ModuleCat.adj R).toComonad.δ
      (freeForgetAdjunctionResolution_realization R)

/-- Evaluating the canonical augmented free-forgetful adjunction resolution at an `R`-module `M`
gives the augmented simplicial `R`-module whose `n`-simplices are the `n`-fold iterates of the
comonad `ModuleCat.free R ⋙ forget (ModuleCat R)` applied to `M`. -/
abbrev freeForgetAdjunctionAugmentedModuleResolution (M : ModuleCat R) :
    SimplicialObject.Augmented (ModuleCat R) :=
  (whiskeringObj (ModuleCat R ⥤ ModuleCat R) (ModuleCat R)
      ((evaluation (ModuleCat R) (ModuleCat R)).obj M)).obj
    (freeForgetAdjunctionAugmentedResolution R)

/- The source-facing underlying simplicial object is the left side of the evaluated augmented
resolution. -/
abbrev freeForgetAdjunctionModuleResolution (M : ModuleCat R) :
    SimplicialObject (ModuleCat R) :=
  (freeForgetAdjunctionAugmentedModuleResolution R M).left

-- Proof sketch: evaluate the object-part equality from
-- `freeForgetAdjunctionResolution_realization R` in degree `n` at the module `M`.
/-- The degree-`n` term of the evaluated free-forgetful resolution is the value at `M` of the
iterated comonad endofunctor. -/
theorem freeForgetAdjunctionModuleResolution_obj_eq (M : ModuleCat R) (n : ℕ) :
    (freeForgetAdjunctionModuleResolution R M).obj (op ⦋n⦌) =
      ((ModuleCat.adj R).toComonad.toFunctor)⦅n⦆.obj M := sorry

/-- Forgetting the evaluated augmented free-forgetful resolution to sets. -/
abbrev freeForgetAdjunctionAugmentedUnderlyingSet (M : ModuleCat R) :
    SimplicialObject.Augmented (Type u) :=
  (whiskeringObj (ModuleCat R) (Type u) (forget (ModuleCat R))).obj
    (freeForgetAdjunctionAugmentedModuleResolution R M)

-- Proof sketch: apply `postcompose_adjunctionResolutionAugmentation_isHomotopyEquivalence` to the
-- free-forgetful adjunction `ModuleCat.adj R`, then evaluate the resulting simplicial homotopy
-- equivalence in the module `M`.
/-- Example 14.34.4: for a ring `R` and an `R`-module `M`, evaluating the standard simplicial
resolution of the free-forgetful adjunction at `M` gives a simplicial `R`-module with terms
`R[M]`, `R[R[M]]`, `R[R[R[M]]]`, and so on, whose augmentation to the constant simplicial object
on `M` becomes a simplicial homotopy equivalence after forgetting to sets. -/
theorem freeForgetAdjunctionModuleResolutionForgetAugmentation_isHomotopyEquivalence
    (M : ModuleCat R) :
    IsHomotopyEquivalence (freeForgetAdjunctionAugmentedUnderlyingSet R M).hom := sorry

-- Proof sketch: use the simplicial homotopy equivalence of the augmentation together with the
-- comparison lemmas between simplicial homotopy equivalences and quasi-isomorphisms of Moore or
-- alternating-face complexes; the target is `ChainComplex.single₀ (ModuleCat R)` on `M`, so this
-- says exactly that the associated chain complex has homology `M` in degree `0` and vanishing
-- homology in positive degrees.
/-- The augmentation of the alternating face map complex of the free-forgetful resolution is a
quasi-isomorphism to the complex concentrated in degree `0` at `M`. -/
theorem freeForgetAdjunctionModuleResolutionAlternatingFaceMapComplex_quasiIso
    (M : ModuleCat R) :
    QuasiIso (AlternatingFaceMapComplex.ε.app (freeForgetAdjunctionAugmentedModuleResolution R M)) :=
  sorry

end CategoryTheory
