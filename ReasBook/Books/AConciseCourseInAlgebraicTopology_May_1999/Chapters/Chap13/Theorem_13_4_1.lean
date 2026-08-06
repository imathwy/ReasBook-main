import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Topology.Category.TopCat.Limits.Products
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Lemma_10_2_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.CellularCWMap
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_3_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_2_11

noncomputable section

open CategoryTheory
open HomologicalComplex
open Topology
open scoped MonoidalCategory

-- Semantic recall via `lean_leansearch`: Chapter 12 already records the canonical chain-complex
-- tensor-product owner with surface `X ⊗ Y` and morphism-level naturality `tensorHom`. This item
-- therefore uses the existing Chapter 13 owners `cellularChainComplex X data` for chosen
-- cellular chain complexes, the canonical product CW structure on `X × Y`, and
-- `InducedCellularChainMap` for the quotient-induced chain maps attached to cellular maps.

/-- Chosen Chapter 13 data for a cellular product-chain comparison for CW complexes `X` and `Y`,
using the canonical product CW structure on `X × Y`. The witness consists of explicit cellular
differential families on `X`, `Y`, and `X × Y`, a comparison isomorphism
`C_*(X × Y) ≅ C_*(X) ⊗ C_*(Y)`, and chosen quotient-induced cellular chain maps for cellular maps
whose source and target differential families agree with the chosen comparison data. -/
structure CellularProductChainComparison
    (X Y : TopCat) [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)] where
  productCW : CWComplex (Set.univ : Set (X × Y))
  dataX : CellularDifferentialFamily X
  dataY : CellularDifferentialFamily Y
  dataProd : @CellularDifferentialFamily (X × Y) inferInstance productCW
  comparisonIso :
    @cellularChainComplex (X × Y) inferInstance productCW dataProd ≅
      ((cellularChainComplex X dataX) ⊗
        (cellularChainComplex Y dataY) : ChainComplex (ModuleCat ℤ) ℕ)
  inducedX :
    ∀ {X' : TopCat} [CWComplex (Set.univ : Set X')]
      (f : X ⟶ X') (hf : IsCellularCWMap f) (dataX' : CellularDifferentialFamily X'),
      { induced : InducedCellularChainMap f hf //
          induced.dataX = dataX ∧ induced.dataY = dataX' }
  inducedY :
    ∀ {Y' : TopCat} [CWComplex (Set.univ : Set Y')]
      (g : Y ⟶ Y') (hg : IsCellularCWMap g) (dataY' : CellularDifferentialFamily Y'),
      { induced : InducedCellularChainMap g hg //
          induced.dataX = dataY ∧ induced.dataY = dataY' }
  productCellular :
    ∀ {X' Y' : TopCat}
      [CWComplex (Set.univ : Set X')] [CWComplex (Set.univ : Set Y')]
      (productCW' : CWComplex (Set.univ : Set (X' × Y')))
      (f : X ⟶ X') (_ : IsCellularCWMap f) (g : Y ⟶ Y') (_ : IsCellularCWMap g),
      @IsCellularCWMap
        (TopCat.of (X × Y)) (TopCat.of (X' × Y')) productCW productCW'
        ((TopCat.prodIsoProd X Y).inv ≫
          Limits.prod.map f g ≫
          (TopCat.prodIsoProd X' Y').hom)
  inducedProd :
    ∀ {X' Y' : TopCat}
      [CWComplex (Set.univ : Set X')] [CWComplex (Set.univ : Set Y')]
      (productCW' : CWComplex (Set.univ : Set (X' × Y')))
      (f : X ⟶ X') (hf : IsCellularCWMap f) (g : Y ⟶ Y') (hg : IsCellularCWMap g)
      (dataProd' : @CellularDifferentialFamily (X' × Y') inferInstance productCW'),
      { induced :
          @InducedCellularChainMapFromQuotients
            (TopCat.of (X × Y)) (TopCat.of (X' × Y')) productCW productCW'
            ((TopCat.prodIsoProd X Y).inv ≫
              Limits.prod.map f g ≫
              (TopCat.prodIsoProd X' Y').hom)
            (productCellular productCW' f hf g hg) //
          induced.dataX = dataProd ∧ induced.dataY = dataProd' }

/-- The chosen cellular chain complex of `X × Y` carried by a cellular product-chain comparison.
-/
abbrev CellularProductChainComparison.prodChainComplex
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (comparison : CellularProductChainComparison X Y) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  @cellularChainComplex (X × Y) inferInstance comparison.productCW comparison.dataProd

/-- The canonical quotient-induced cellular chain map on `X` chosen by the comparison data for the
cellular map `f`. -/
abbrev CellularProductChainComparison.inducedMapXFromQuotients
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (comparison : CellularProductChainComparison X Y)
    {X' Y' : TopCat}
    [CWComplex (Set.univ : Set X')] [CWComplex (Set.univ : Set Y')]
    (f : X ⟶ X') (hf : IsCellularCWMap f) (comparison' : CellularProductChainComparison X' Y') :
    InducedCellularChainMap f hf :=
  (comparison.inducedX f hf comparison'.dataX).1

/-- The chosen induced cellular-chain morphism on `X` for the target comparison data
`comparison'`, induced by the cellular map `f`. -/
abbrev CellularProductChainComparison.inducedMapX
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (comparison : CellularProductChainComparison X Y)
    {X' Y' : TopCat}
    [CWComplex (Set.univ : Set X')] [CWComplex (Set.univ : Set Y')]
    (f : X ⟶ X') (hf : IsCellularCWMap f) (comparison' : CellularProductChainComparison X' Y') :
    cellularChainComplex X comparison.dataX ⟶
      cellularChainComplex X' comparison'.dataX :=
  (comparison.inducedMapXFromQuotients f hf comparison').toChainMap
    (comparison.inducedX f hf comparison'.dataX).2.1
    (comparison.inducedX f hf comparison'.dataX).2.2

/-- The canonical quotient-induced cellular chain map on `Y` chosen by the comparison data for the
cellular map `g`. -/
abbrev CellularProductChainComparison.inducedMapYFromQuotients
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (comparison : CellularProductChainComparison X Y)
    {X' Y' : TopCat}
    [CWComplex (Set.univ : Set X')] [CWComplex (Set.univ : Set Y')]
    (g : Y ⟶ Y') (hg : IsCellularCWMap g) (comparison' : CellularProductChainComparison X' Y') :
    InducedCellularChainMap g hg :=
  (comparison.inducedY g hg comparison'.dataY).1

/-- The chosen induced cellular-chain morphism on `Y` for the target comparison data
`comparison'`, induced by the cellular map `g`. -/
abbrev CellularProductChainComparison.inducedMapY
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (comparison : CellularProductChainComparison X Y)
    {X' Y' : TopCat}
    [CWComplex (Set.univ : Set X')] [CWComplex (Set.univ : Set Y')]
    (g : Y ⟶ Y') (hg : IsCellularCWMap g) (comparison' : CellularProductChainComparison X' Y') :
    cellularChainComplex Y comparison.dataY ⟶
      cellularChainComplex Y' comparison'.dataY :=
  (comparison.inducedMapYFromQuotients g hg comparison').toChainMap
    (comparison.inducedY g hg comparison'.dataY).2.1
    (comparison.inducedY g hg comparison'.dataY).2.2

/-- The canonical quotient-induced cellular chain map on `X × Y` chosen by the comparison data
for the product cellular map `Limits.prod.map f g`. -/
abbrev CellularProductChainComparison.inducedMapProdFromQuotients
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (comparison : CellularProductChainComparison X Y)
    {X' Y' : TopCat}
    [CWComplex (Set.univ : Set X')] [CWComplex (Set.univ : Set Y')]
    (f : X ⟶ X') (hf : IsCellularCWMap f) (g : Y ⟶ Y') (hg : IsCellularCWMap g)
    (comparison' : CellularProductChainComparison X' Y') :
    @InducedCellularChainMapFromQuotients
      (TopCat.of (X × Y)) (TopCat.of (X' × Y')) comparison.productCW comparison'.productCW
      ((TopCat.prodIsoProd X Y).inv ≫
        Limits.prod.map f g ≫
        (TopCat.prodIsoProd X' Y').hom)
      (comparison.productCellular comparison'.productCW f hf g hg) :=
  (comparison.inducedProd comparison'.productCW f hf g hg comparison'.dataProd).1

/-- The chosen induced cellular-chain morphism on `X × Y` for the target comparison data
`comparison'`, induced by the cellular maps `f` and `g`. -/
abbrev CellularProductChainComparison.inducedMapProd
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (comparison : CellularProductChainComparison X Y)
    {X' Y' : TopCat}
    [CWComplex (Set.univ : Set X')] [CWComplex (Set.univ : Set Y')]
    (f : X ⟶ X') (hf : IsCellularCWMap f) (g : Y ⟶ Y') (hg : IsCellularCWMap g)
    (comparison' : CellularProductChainComparison X' Y') :
    comparison.prodChainComplex ⟶ comparison'.prodChainComplex :=
  @InducedCellularChainMapFromQuotients.toChainMap
    (TopCat.of (X × Y)) (TopCat.of (X' × Y'))
    comparison.productCW comparison'.productCW _ _
    (comparison.inducedMapProdFromQuotients f hf g hg comparison')
    comparison.dataProd comparison'.dataProd
    (comparison.inducedProd comparison'.productCW f hf g hg comparison'.dataProd).2.1
    (comparison.inducedProd comparison'.productCW f hf g hg comparison'.dataProd).2.2

/-- Naturality of chosen cellular product-chain comparison data with respect to the chosen induced
cellular-chain morphisms on `X`, `Y`, and `X × Y`, where the induced maps come from the Chapter 13
quotient-skeleton construction. -/
def CellularProductChainComparison.IsNatural
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (comparison : CellularProductChainComparison X Y) : Prop :=
  ∀ {X' Y' : TopCat}
    [CWComplex (Set.univ : Set X')] [CWComplex (Set.univ : Set Y')]
    (comparison' : CellularProductChainComparison X' Y')
    (f : X ⟶ X') (hf : IsCellularCWMap f) (g : Y ⟶ Y') (hg : IsCellularCWMap g),
    comparison.inducedMapProd f hf g hg comparison' ≫ comparison'.comparisonIso.hom =
      comparison.comparisonIso.hom ≫
        (tensorHom
          (comparison.inducedMapX f hf comparison')
          (comparison.inducedMapY g hg comparison') :
          (cellularChainComplex X comparison.dataX) ⊗
              (cellularChainComplex Y comparison.dataY) ⟶
            (cellularChainComplex X' comparison'.dataX) ⊗
              (cellularChainComplex Y' comparison'.dataY))

/-- Theorem 13.4.1: for CW complexes `X` and `Y`, there exist explicit cellular differential
families on `X`, `Y`, and `X × Y` for the canonical product CW structure, together with a
comparison isomorphism
`cellularChainComplex (X × Y) dataProd ≅ cellularChainComplex X dataX ⊗ cellularChainComplex Y
dataY` that is natural for the chosen quotient-induced cellular-chain morphisms of cellular maps.
-/
theorem existsCellularProductChainComparison
    (X Y : TopCat) [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)] :
    ∃ comparison : CellularProductChainComparison X Y, comparison.IsNatural := sorry

/-- Naturality of the chosen cellular product-chain comparison with respect to the same
comparison data on the source and target spaces for cellular maps `f` and `g`. -/
theorem cellularProductChainComparison_natural
    {X X' Y Y' : TopCat}
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set X')]
    [CWComplex (Set.univ : Set Y)] [CWComplex (Set.univ : Set Y')]
    {comparison : CellularProductChainComparison X Y}
    {comparison' : CellularProductChainComparison X' Y'}
    (hcomparison : comparison.IsNatural)
    (f : X ⟶ X') (hf : IsCellularCWMap f) (g : Y ⟶ Y') (hg : IsCellularCWMap g) :
    comparison.inducedMapProd f hf g hg comparison' ≫ comparison'.comparisonIso.hom =
      comparison.comparisonIso.hom ≫
        (tensorHom
          (comparison.inducedMapX f hf comparison')
          (comparison.inducedMapY g hg comparison') :
          (cellularChainComplex X comparison.dataX) ⊗
              (cellularChainComplex Y comparison.dataY) ⟶
            (cellularChainComplex X' comparison'.dataX) ⊗
              (cellularChainComplex Y' comparison'.dataY)) := sorry
