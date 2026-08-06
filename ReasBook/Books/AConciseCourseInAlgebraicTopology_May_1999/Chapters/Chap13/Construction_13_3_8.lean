import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.Single
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap12.Definition_12_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap12.Proposition_12_4_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_3_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_3_7

noncomputable section

open CategoryTheory
open Topology
open scoped CellularHomology

-- Semantic recall via `lean_leansearch`: `HomologicalComplex.tensorHom` and
-- `HomologicalComplex.homologyMap` give the canonical coefficient-change map on tensor-product
-- chain complexes, while `shortExactChainComplexHomologyBoundary_naturality` is the canonical
-- naturality statement for connecting morphisms.

/-- The chain map induced by a coefficient-group homomorphism on the degree-zero tensor factor of
`X ⊗ G`. -/
abbrev chainComplexCoefficientsChange
    (X : ChainComplex (ModuleCat ℤ) ℕ)
    {G H : Type} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) :
    HomologicalComplex.tensorObj X
        (coefficientComplex ℤ (ModuleCat.of ℤ G)) ⟶
      HomologicalComplex.tensorObj X
        (coefficientComplex ℤ (ModuleCat.of ℤ H)) :=
  HomologicalComplex.tensorHom (𝟙 X)
    (coefficientComplexMap ℤ (ModuleCat.ofHom f.toIntLinearMap))

/-- The homology map induced in degree `q` by a coefficient-group homomorphism on a chain
complex. -/
abbrev chainComplexHomologyWithCoefficientsMap
    (X : ChainComplex (ModuleCat ℤ) ℕ)
    {G H : Type} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (q : ℕ) :
    homologyWithCoefficients ℤ X (ModuleCat.of ℤ G) q ⟶
      homologyWithCoefficients ℤ X (ModuleCat.of ℤ H) q :=
  HomologicalComplex.homologyMap (chainComplexCoefficientsChange X f) q

/-- The fixed-pair component of coefficient change on relative cellular homology with
coefficients. -/
abbrev relativeCellularHomologyWithCoefficientsMap
    (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    {G H : Type} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (q : ℕ) :
    H[q](X, A, data, G) ⟶ H[q](X, A, data, H) :=
  chainComplexHomologyWithCoefficientsMap
    (relativeCellularChainComplex X A data) f q

/-- The map on relative cellular homology with coefficients induced by a morphism of relative
cellular chain complexes. -/
abbrev relativeCellularHomologyWithCoefficientsMapOfChainMap
    (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (dataX : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A dataX]
    (Y : Type) [TopologicalSpace Y] [CWComplex (Set.univ : Set Y)]
    (B : Topology.CWComplex.Subcomplex (Set.univ : Set Y))
    (dataY : CellularDifferentialFamily Y)
    [RelativeCellularDifferentialDescends Y B dataY]
    (φ : relativeCellularChainComplex X A dataX ⟶ relativeCellularChainComplex Y B dataY)
    (G : Type) [AddCommGroup G] (q : ℕ) :
    H[q](X, A, dataX, G) ⟶ H[q](Y, B, dataY, G) :=
  HomologicalComplex.homologyMap
    (HomologicalComplex.tensorHom φ
      (𝟙 (coefficientComplex ℤ (ModuleCat.of ℤ G)))) q

/-- The coefficient-homology map induced by a morphism of relative cellular chain complexes is the
homology map of the tensor-product chain map obtained by applying that morphism on the relative
cellular factor and the identity on the coefficient complex. -/
theorem relativeCellularHomologyWithCoefficientsMapOfChainMap_def
    (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (dataX : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A dataX]
    (Y : Type) [TopologicalSpace Y] [CWComplex (Set.univ : Set Y)]
    (B : Topology.CWComplex.Subcomplex (Set.univ : Set Y))
    (dataY : CellularDifferentialFamily Y)
    [RelativeCellularDifferentialDescends Y B dataY]
    (φ : relativeCellularChainComplex X A dataX ⟶ relativeCellularChainComplex Y B dataY)
    (G : Type) [AddCommGroup G] (q : ℕ) :
    relativeCellularHomologyWithCoefficientsMapOfChainMap X A dataX Y B dataY φ G q =
      HomologicalComplex.homologyMap
        (HomologicalComplex.tensorHom φ
          (𝟙 (coefficientComplex ℤ (ModuleCat.of ℤ G)))) q :=
  rfl

/-- Construction 13.3.8 (1). A chosen morphism of relative cellular chain complexes, for example
one induced by a map of CW pairs, determines maps on relative cellular homology with
coefficients, and these commute with change of coefficient group in degree `q`. -/
theorem relativeCellularHomologyWithCoefficientsMap_naturality
    (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (dataX : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A dataX]
    (Y : Type) [TopologicalSpace Y] [CWComplex (Set.univ : Set Y)]
    (B : Topology.CWComplex.Subcomplex (Set.univ : Set Y))
    (dataY : CellularDifferentialFamily Y)
    [RelativeCellularDifferentialDescends Y B dataY]
    (φ : relativeCellularChainComplex X A dataX ⟶ relativeCellularChainComplex Y B dataY)
    {G H : Type} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (q : ℕ) :
    relativeCellularHomologyWithCoefficientsMapOfChainMap
        X A dataX Y B dataY φ G q ≫
      relativeCellularHomologyWithCoefficientsMap Y B dataY f q =
        relativeCellularHomologyWithCoefficientsMap X A dataX f q ≫
          relativeCellularHomologyWithCoefficientsMapOfChainMap
            X A dataX Y B dataY φ H q := sorry

/-- The coefficient-change morphism on relative cellular homology is the homology map induced by
the coefficient-change chain map on the relative cellular chain complex. -/
theorem relativeCellularHomologyWithCoefficientsMap_def
    (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    {G H : Type} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (q : ℕ) :
    relativeCellularHomologyWithCoefficientsMap X A data f q =
      chainComplexHomologyWithCoefficientsMap
        (relativeCellularChainComplex X A data) f q :=
  rfl

/-- Tensoring a short complex of chain complexes with the degree-zero coefficient complex on `G`
preserves the relation that the two consecutive maps compose to zero. -/
theorem shortComplexWithCoefficients_zero
    (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ))
    (G : Type) [AddCommGroup G] :
    HomologicalComplex.tensorHom S.f
        (𝟙 (coefficientComplex ℤ (ModuleCat.of ℤ G))) ≫
      HomologicalComplex.tensorHom S.g
        (𝟙 (coefficientComplex ℤ (ModuleCat.of ℤ G))) =
        0 := sorry

/-- The short complex obtained by tensoring each term and arrow of `S` with the degree-zero chain
complex on the coefficient group `G`. -/
abbrev shortComplexWithCoefficients
    (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ))
    (G : Type) [AddCommGroup G] :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk
    (HomologicalComplex.tensorHom S.f
      (𝟙 (coefficientComplex ℤ (ModuleCat.of ℤ G))))
    (HomologicalComplex.tensorHom S.g
      (𝟙 (coefficientComplex ℤ (ModuleCat.of ℤ G))))
    (shortComplexWithCoefficients_zero S G)

/-- The left square for the morphism of coefficient-tensored short complexes induced by a
coefficient-group homomorphism `f : G →+ H`. -/
theorem shortComplexWithCoefficientsMap_comm₁₂
    (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ))
    {G H : Type} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) :
    chainComplexCoefficientsChange S.X₁ f ≫
        HomologicalComplex.tensorHom S.f
          (𝟙 (coefficientComplex ℤ (ModuleCat.of ℤ H))) =
      HomologicalComplex.tensorHom S.f
          (𝟙 (coefficientComplex ℤ (ModuleCat.of ℤ G))) ≫
        chainComplexCoefficientsChange S.X₂ f := sorry

/-- The right square for the morphism of coefficient-tensored short complexes induced by a
coefficient-group homomorphism `f : G →+ H`. -/
theorem shortComplexWithCoefficientsMap_comm₂₃
    (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ))
    {G H : Type} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) :
    chainComplexCoefficientsChange S.X₂ f ≫
        HomologicalComplex.tensorHom S.g
          (𝟙 (coefficientComplex ℤ (ModuleCat.of ℤ H))) =
      HomologicalComplex.tensorHom S.g
          (𝟙 (coefficientComplex ℤ (ModuleCat.of ℤ G))) ≫
        chainComplexCoefficientsChange S.X₃ f := sorry

/-- The morphism of short complexes obtained by applying a coefficient-group homomorphism to the
degree-zero tensor factor. -/
def shortComplexWithCoefficientsMap
    (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ))
    {G H : Type} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) :
    shortComplexWithCoefficients S G ⟶ shortComplexWithCoefficients S H where
  τ₁ := chainComplexCoefficientsChange S.X₁ f
  τ₂ := chainComplexCoefficientsChange S.X₂ f
  τ₃ := chainComplexCoefficientsChange S.X₃ f
  comm₁₂ := shortComplexWithCoefficientsMap_comm₁₂ S f
  comm₂₃ := shortComplexWithCoefficientsMap_comm₂₃ S f

/-- Tensoring the canonical pair short complex `C_*(A) ⟶ C_*(X) ⟶ C_*(X, A)` with the
degree-zero coefficient complex on `G` preserves short exactness. -/
theorem relativeCellularPairShortComplex_shortExactWithCoefficients
    (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (G : Type) [AddCommGroup G] :
    (shortComplexWithCoefficients (relativeCellularPairShortComplex X A data) G).ShortExact := sorry

/-- The connecting morphism on coefficient homology attached to the coefficient-tensored
canonical pair short complex `C_*(A; G) ⟶ C_*(X; G) ⟶ C_*(X, A; G)`. -/
abbrev relativeCellularHomologyBoundaryWithCoefficients
    (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (G : Type) [AddCommGroup G]
    (n : ℕ) :
    H[n + 1](X, A, data, G) ⟶
      homologyWithCoefficients ℤ (subcomplexCellularChainComplex X A data) (ModuleCat.of ℤ G) n :=
  shortExactChainComplexHomologyBoundary
    (shortComplexWithCoefficients (relativeCellularPairShortComplex X A data) G)
    (relativeCellularPairShortComplex_shortExactWithCoefficients X A data G) n

/-- Construction 13.3.8 (2). For a CW pair `(X, A)`, a homomorphism of coefficient groups
`f : G →+ H` induces maps on coefficient homology that commute with the connecting morphisms of
the coefficient-tensored canonical pair short complex. -/
theorem relativeCellularHomologyBoundaryWithCoefficients_naturality
    (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    {G H : Type} [AddCommGroup G] [AddCommGroup H] (f : G →+ H)
    (n : ℕ) :
    relativeCellularHomologyBoundaryWithCoefficients
        X A data G n ≫
      chainComplexHomologyWithCoefficientsMap
        (subcomplexCellularChainComplex X A data) f n =
        relativeCellularHomologyWithCoefficientsMap X A data f (n + 1) ≫
          relativeCellularHomologyBoundaryWithCoefficients
            X A data H n := by
  change shortExactChainComplexHomologyBoundary
      (shortComplexWithCoefficients (relativeCellularPairShortComplex X A data) G)
      (relativeCellularPairShortComplex_shortExactWithCoefficients X A data G) n ≫
    HomologicalComplex.homologyMap
      (shortComplexWithCoefficientsMap (relativeCellularPairShortComplex X A data) f).τ₁ n =
      HomologicalComplex.homologyMap
        (shortComplexWithCoefficientsMap (relativeCellularPairShortComplex X A data) f).τ₃
          (n + 1) ≫
        shortExactChainComplexHomologyBoundary
          (shortComplexWithCoefficients (relativeCellularPairShortComplex X A data) H)
          (relativeCellularPairShortComplex_shortExactWithCoefficients X A data H) n
  exact shortExactChainComplexHomologyBoundary_naturality
    (shortComplexWithCoefficientsMap (relativeCellularPairShortComplex X A data) f)
    (relativeCellularPairShortComplex_shortExactWithCoefficients X A data G)
    (relativeCellularPairShortComplex_shortExactWithCoefficients X A data H) n
