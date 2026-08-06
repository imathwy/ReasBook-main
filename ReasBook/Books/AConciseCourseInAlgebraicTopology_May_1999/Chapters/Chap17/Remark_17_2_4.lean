import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Theorem_13_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Theorem_17_2_2

noncomputable section

open Topology

-- Semantic recall via `lean_leansearch`: no direct mathlib owner surfaced for the Kunneth
-- computation of Cartesian products of CW complexes, so the faithful formalization here is a
-- local recall block combining the Chapter 13 product-chain comparison with the Chapter 17
-- Kunneth short exact sequence through the source-facing cellular-chain bridge below.

namespace CellularProductChainComparison

/-- Remark 17.2.4 bridge: the Chapter 13 cellular product-chain comparison identifies the middle
Kunneth homology term for the chosen cellular chain complexes of `X` and `Y` with the homology of
the chosen cellular chain complex of `X × Y`. -/
abbrev kunnethHomologyTermIso
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (comparison : CellularProductChainComparison X Y) (n : ℕ) :
    comparison.prodChainComplex.homology (n + 1) ≅
      kunnethHomologyTerm ℤ
        (cellularChainComplex X comparison.dataX)
        (cellularChainComplex Y comparison.dataY) n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) (n + 1)).mapIso
    comparison.comparisonIso

/-- Remark 17.2.4 bridge: if the chosen cellular chain complex of `X` is degreewise flat over
`ℤ`, then the Kunneth theorem yields a short exact sequence for the chosen cellular chain
complexes of `X` and `Y`. -/
theorem nonemptyKunnethHomologySequence
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (comparison : CellularProductChainComparison X Y) (n : ℕ)
    (hFlat : ∀ i : ℕ, Module.Flat ℤ ((cellularChainComplex X comparison.dataX).X i)) :
    Nonempty
      (KunnethHomologySequence ℤ
        (cellularChainComplex X comparison.dataX)
        (cellularChainComplex Y comparison.dataY) n) := by
  rcases
      kunnethHomologyShortExact ℤ (cellularChainComplex X comparison.dataX) n hFlat with
    ⟨S⟩
  exact ⟨S (cellularChainComplex Y comparison.dataY)⟩

end CellularProductChainComparison

/- Remark 17.2.4. Combined with cellular chains of products, the Kunneth theorem computes
homology of Cartesian products of CW complexes. In this development,
`existsCellularProductChainComparison` from Theorem 13.4.1 provides the cellular product-chain
comparison `C_*(X × Y) ≅ C_*(X) ⊗ C_*(Y)`. The companion bridge
`CellularProductChainComparison.kunnethHomologyTermIso` identifies the middle Kunneth term with
the homology of the chosen cellular chain complex of `X × Y`, and
`CellularProductChainComparison.nonemptyKunnethHomologySequence` specializes Theorem 17.2.2 to
the chosen cellular chain complexes of `X` and `Y`. Since the source item is a summary remark
rather than a new theorem, the faithful formalization remains a labeled recall block. -/
#check existsCellularProductChainComparison
#check CellularProductChainComparison.kunnethHomologyTermIso
#check CellularProductChainComparison.nonemptyKunnethHomologySequence
