import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap12.Definition_12_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_3_2

noncomputable section

open CategoryTheory
open Topology
open scoped CellularHomology MonoidalCategory

-- Semantic recall via `lean_leansearch`: Chapter 12 already fixes `coefficientComplex` and the
-- coefficient-homology owner `homologyWithCoefficients`, while Definitions 13.2.11 and 13.3.2
-- provide the absolute and relative cellular chain complexes. This item keeps the source-facing
-- Chapter 13 coefficient-chain names as thin specializations of those canonical owners. In the
-- current Lean environment, the needed monoidal structure on `ModuleCat ℤ` is available only in
-- the small universe, so the statements are recorded for `X : Type` and `π : Type`.

/-- The cellular chain complex of `X` with coefficients in `π`, formalized as the tensor product
of `cellularChainComplex X data` with the coefficient complex `coefficientComplex ℤ
(ModuleCat.of ℤ π)`. -/
abbrev cellularChainComplexWithCoefficients
    (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (data : CellularDifferentialFamily X)
    (π : Type) [AddCommGroup π] :
    ChainComplex (ModuleCat ℤ) ℕ :=
  cellularChainComplex X data ⊗ coefficientComplex ℤ (ModuleCat.of ℤ π)

/-- Lean notation for the cellular chain complex with coefficients `C_*(X; π)`, keeping the
chosen cellular differential family `data` explicit as a second argument. -/
scoped[CellularChainComplex] notation "C_*(" X ", " data ", " π ")" =>
  cellularChainComplexWithCoefficients X data π

open scoped CellularChainComplex

/-- Unfolding `C_*(X, data, π)` gives the tensor product `C_*(X) ⊗ π` with `π` concentrated in
degree `0`. -/
theorem cellularChainComplexWithCoefficients_def
    (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (data : CellularDifferentialFamily X)
    (π : Type) [AddCommGroup π] :
    C_*(X, data, π) =
      cellularChainComplex X data ⊗ coefficientComplex ℤ (ModuleCat.of ℤ π) :=
  rfl

/-- The cellular homology of `X` with coefficients in `π`, computed from `C_*(X; π)`. -/
abbrev cellularHomologyWithCoefficients
    (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (data : CellularDifferentialFamily X)
    (π : Type) [AddCommGroup π] :
    ℕ → ModuleCat ℤ :=
  homologyWithCoefficients ℤ
    (cellularChainComplex X data)
    (ModuleCat.of ℤ π)

/-- Lean notation for the cellular homology groups `H_n(X; π)` computed from the chosen cellular
differential family `data`, with `π` kept explicit as a third argument. -/
scoped[CellularHomology] notation "H[" n "](" X ", " data ", " π ")" =>
  cellularHomologyWithCoefficients X data π n

/-- Evaluating `H[n](X, data, π)` in degree `n` gives the degree-`n` homology object of
`C_*(X, data, π)`. -/
@[simp] theorem cellularHomologyWithCoefficients_apply
    (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (data : CellularDifferentialFamily X)
    (π : Type) [AddCommGroup π] (n : ℕ) :
    H[n](X, data, π) = (C_*(X, data, π)).homology n :=
  rfl

/-- Definition 13.3.7. For a CW pair `(X, A)` and an Abelian group `π`, the relative cellular
chain complex with coefficients in `π` is `C_*(X, A; π) = C_*(X, A) ⊗ π`, formalized as the
tensor product of `relativeCellularChainComplex X A data` with the coefficient complex
`coefficientComplex ℤ (ModuleCat.of ℤ π)`. -/
abbrev relativeCellularChainComplexWithCoefficients
    (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (π : Type) [AddCommGroup π] :
    ChainComplex (ModuleCat ℤ) ℕ :=
  relativeCellularChainComplex X A data ⊗ coefficientComplex ℤ (ModuleCat.of ℤ π)

/-- Lean notation for the relative cellular chain complex with coefficients `C_*(X, A; π)`,
keeping the chosen cellular differential family `data` explicit as a fourth argument. -/
scoped[CellularChainComplex] notation "C_*(" X ", " A ", " data ", " π ")" =>
  relativeCellularChainComplexWithCoefficients X A data π

open scoped CellularChainComplex

/-- Unfolding `C_*(X, A, data, π)` gives the tensor product `C_*(X, A) ⊗ π` with `π`
concentrated in degree `0`. -/
theorem relativeCellularChainComplexWithCoefficients_def
    (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (π : Type) [AddCommGroup π] :
    C_*(X, A, data, π) =
      relativeCellularChainComplex X A data ⊗ coefficientComplex ℤ (ModuleCat.of ℤ π) :=
  rfl

/-- The relative cellular homology of `(X, A)` with coefficients in `π`, computed from the chain
complex `C_*(X, A; π)`. -/
abbrev relativeCellularHomologyWithCoefficients
    (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (π : Type) [AddCommGroup π] :
    ℕ → ModuleCat ℤ :=
  homologyWithCoefficients ℤ
    (relativeCellularChainComplex X A data)
    (ModuleCat.of ℤ π)

/-- Lean notation for the relative cellular homology groups `H_n(X, A; π)` computed from the
chosen cellular differential family `data`, with `π` kept explicit as a fourth argument. -/
scoped[CellularHomology] notation "H[" n "](" X ", " A ", " data ", " π ")" =>
  relativeCellularHomologyWithCoefficients X A data π n

/-- Evaluating `H[n](X, A, data, π)` in degree `n` gives the degree-`n` homology object of
`C_*(X, A, data, π)`. -/
@[simp] theorem relativeCellularHomologyWithCoefficients_apply
    (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (π : Type) [AddCommGroup π] (n : ℕ) :
    H[n](X, A, data, π) = (C_*(X, A, data, π)).homology n :=
  rfl
