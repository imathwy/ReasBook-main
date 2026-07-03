import Mathlib
import StacksProject_2024.Chap20.Lemma_20_32_3
import StacksProject_2024.Chap20.Lemma_20_32_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

-- Proof sketch: evaluate the presheaf
-- `ringedSpaceObjectwiseCohomologyPresheaf Y ((moduleDerivedPushforward f).obj K) i` on `V`.
-- By Lemma `20.32.5`, the derived sections of `Rf_* K` on `V` identify with the derived
-- sections of `K` on `f^{-1}(V)`. Taking degree-`i` homology and forgetting to abelian groups
-- gives the stated objectwise comparison.
/-- The canonical cohomology presheaf of `Rf_* K` has value `H^i(f^{-1}(V), K)` on each open
subset `V ⊆ Y`. -/
lemma pushforward_objectwiseCohomologyPresheaf_obj_isomorphic_preimageHypercohomology
    (f : X ⟶ Y)
    [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat Y)]
    (K : DerivedCategory (RingedSpace.Modules X)) (i : ℤ) (V : Opens Y.carrier) :
    IsIsomorphic
      ((ringedSpaceObjectwiseCohomologyPresheaf Y ((moduleDerivedPushforward f).obj K) i).obj
        (op V))
      (moduleOpenHypercohomology X (preimageOpen f V) K i) := sorry

-- Proof sketch: apply Lemma `20.32.3` on the target ringed space `Y` to the derived object
-- `Rf_* K`. By the previous lemma and Lemma `20.32.5`, this objectwise cohomology presheaf is
-- exactly the presheaf `V ↦ H^i(f^{-1}(V), K)` from the textbook statement.
/-- Lemma 20.32.6: for a morphism of ringed spaces `f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)`
and an object `K` of `D(\mathcal O_X)`, the degree-`i` cohomology sheaf `H^i(Rf_* K)` is the
sheaf associated to the presheaf on `Y` whose value on an open subset `V ⊆ Y` is
`H^i(f^{-1}(V), K) = H^i(V, Rf_* K)`. In the formalization, this is the sheafification of the
canonical objectwise cohomology presheaf of `Rf_* K`. -/
lemma pushforward_objectwiseCohomologyPresheaf_sheafification_isomorphic_cohomologySheaf
    (f : X ⟶ Y)
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat Y)]
    (K : DerivedCategory (RingedSpace.Modules X)) (i : ℤ) :
    IsIsomorphic
      ((presheafToSheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}).obj
        (ringedSpaceObjectwiseCohomologyPresheaf Y ((moduleDerivedPushforward f).obj K) i))
      (ringedSpaceCohomologySheaf Y ((moduleDerivedPushforward f).obj K) i) := sorry

end AlgebraicGeometry.RingedSpace
