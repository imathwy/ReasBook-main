module

public import Topology_Munkres_2000.Book.Theorem_62_1.CechDuality
public import Topology_Munkres_2000.Book.Theorem_62_1.GraphHomology

public section

namespace InvarianceOfDomainSupport

universe u

/-- Helper for Theorem 62.1: a finite cochain complex with degree-reversing
cell correspondences whose dual incidence complex is the augmented complex of
a finite graph. -/
structure FiniteGraphDualCochainModel {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (low middle high : Type u) [Fintype low] [Fintype middle] [Fintype high] where
  /-- The first primal coboundary matrix. -/
  lower : Matrix middle low (ZMod 2)
  /-- The second primal coboundary matrix. -/
  upper : Matrix high middle (ZMod 2)
  /-- Low primal cells correspond to the unique augmented degree. -/
  lowDual : low ≃ Unit
  /-- Middle primal cells correspond to graph vertices. -/
  middleDual : middle ≃ V
  /-- High primal cells correspond to graph edge indices. -/
  highDual : high ≃ Sym2 V
  /-- Consecutive primal coboundaries compose to zero. -/
  squareZero : upper * lower = 0
  /-- The dual of the upper primal incidence is graph incidence. -/
  dualUpper_eq_graphIncidence :
    dualIncidenceMatrix upper highDual middleDual = G.incMatrix (ZMod 2)
  /-- The dual of the lower primal incidence is vertex augmentation. -/
  dualLower_eq_vertexAugmentation :
    dualIncidenceMatrix lower middleDual lowDual = vertexAugmentationMatrix V

namespace FiniteGraphDualCochainModel

/-- Helper for Theorem 62.1: the bundled cell correspondences identify primal
exactness with exactness of the model's two dual incidence matrices. -/
lemma exact_iff_dualExact
    {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableEq V]
    [DecidableRel G.Adj] {low middle high : Type u}
    [Fintype low] [Fintype middle] [Fintype high]
    (M : FiniteGraphDualCochainModel G low middle high) :
    Function.Exact M.lower.mulVecLin M.upper.mulVecLin ↔
      Function.Exact
        (dualIncidenceMatrix M.upper M.highDual M.middleDual).mulVecLin
        (dualIncidenceMatrix M.lower M.middleDual M.lowDual).mulVecLin := by
  -- Expose the concrete matrices so the duality theorem avoids dependent projections.
  rcases M with ⟨lower, upper, lowDual, middleDual, highDual, hSquare, _, _⟩
  -- Apply finite transpose duality with the model's square-zero certificate.
  exact dualIncidenceMatrix_exact_iff_modTwo lower upper lowDual middleDual
    highDual hSquare

/-- Helper for Theorem 62.1: exactness of a finite graph-dual cochain model is
equivalent to vanishing of reduced mod-two graph homology. -/
lemma exact_iff_graphHomologySubsingleton
    {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableEq V]
    [DecidableRel G.Adj] {low middle high : Type u}
    [Fintype low] [Fintype middle] [Fintype high]
    (M : FiniteGraphDualCochainModel G low middle high) :
    Function.Exact M.lower.mulVecLin M.upper.mulVecLin ↔
      Subsingleton (graphReducedHomologyZeroModTwo G) := by
  -- First reverse the primal complex, then use the two geometric incidence rules.
  calc
    Function.Exact M.lower.mulVecLin M.upper.mulVecLin ↔
        Function.Exact
          (dualIncidenceMatrix M.upper M.highDual M.middleDual).mulVecLin
          (dualIncidenceMatrix M.lower M.middleDual M.lowDual).mulVecLin :=
      M.exact_iff_dualExact
    _ ↔ Function.Exact (G.incMatrix (ZMod 2)).mulVecLin
          (vertexAugmentationMatrix V).mulVecLin := by
      rw [M.dualUpper_eq_graphIncidence, M.dualLower_eq_vertexAugmentation]
    _ ↔ Subsingleton (graphReducedHomologyZeroModTwo G) :=
      (graphReducedHomologyZeroModTwo_subsingleton_iff_exact G).symm

end FiniteGraphDualCochainModel

end InvarianceOfDomainSupport

end
