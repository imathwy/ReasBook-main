import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_2_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_3_4

noncomputable section

open CategoryTheory
open Topology

variable {X Y : TopCat}
variable [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
variable {f g : X ⟶ Y}

-- Semantic recall via `lean_leansearch`: `Homotopy.homologyMap_eq` is the canonical algebraic
-- statement that chain-homotopic chain maps induce the same map on homology. The space-level
-- homotopy owner is the existing Chapter 10 `Topology.CWComplex.CellularHomotopy`, and the
-- induced cellular chain maps are carried by the bundled Chapter 13 owner
-- `InducedCellularChainMap`.

/-- Lemma 13.3.5 (1). If `f, g : X ⟶ Y` are related by a Chapter 10 cellular homotopy and `φF`,
`φG` are the chosen Chapter 13 cellular chain maps for `f` and `g` attached to the same cellular
differential data `dataX` and `dataY`, then `φF` and `φG` are chain homotopic. -/
theorem cellularHomotopic_inducedCellularChainMap_chainHomotopic
    (H : Topology.CWComplex.CellularHomotopy f.hom g.hom)
    (dataX : CellularDifferentialFamily X) (dataY : CellularDifferentialFamily Y)
    (inducedF : InducedCellularChainMap f H.left_isCellular)
    (hF_dataX : inducedF.dataX = dataX) (hF_dataY : inducedF.dataY = dataY)
    (inducedG : InducedCellularChainMap g H.right_isCellular)
    (hG_dataX : inducedG.dataX = dataX) (hG_dataY : inducedG.dataY = dataY) :
    Nonempty
      (Homotopy
        (inducedF.toChainMap hF_dataX hF_dataY)
        (inducedG.toChainMap hG_dataX hG_dataY)) := sorry

/-- Lemma 13.3.5 (2). Under the same chosen Chapter 13 induced cellular chain maps for a Chapter
10 cellular homotopy `f ≃ g`, the induced maps on homology agree in every degree. -/
theorem cellularHomotopic_inducedCellularHomologyMap_eq
    (H : Topology.CWComplex.CellularHomotopy f.hom g.hom)
    (dataX : CellularDifferentialFamily X) (dataY : CellularDifferentialFamily Y)
    (inducedF : InducedCellularChainMap f H.left_isCellular)
    (hF_dataX : inducedF.dataX = dataX) (hF_dataY : inducedF.dataY = dataY)
    (inducedG : InducedCellularChainMap g H.right_isCellular)
    (hG_dataX : inducedG.dataX = dataX) (hG_dataY : inducedG.dataY = dataY)
    (n : ℕ) :
    HomologicalComplex.homologyMap
        (inducedF.toChainMap hF_dataX hF_dataY) n =
      HomologicalComplex.homologyMap
        (inducedG.toChainMap hG_dataX hG_dataY) n := by
  obtain ⟨hφ⟩ :=
    cellularHomotopic_inducedCellularChainMap_chainHomotopic
      H dataX dataY inducedF hF_dataX hF_dataY inducedG hG_dataX hG_dataY
  exact hφ.homologyMap_eq n
