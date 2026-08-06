import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Theorem_19_5_2

open CategoryTheory Limits
open Topology

noncomputable section

universe u

-- Semantic recall via `lean_leansearch`: `CategoryTheory.Limits.kernel` is the canonical owner
-- for the kernel of a morphism in an abelian category. Local Chapter 13/19 precedent from
-- `Construction_13_3_3`, `Definition_13_3_2`, and `Definition_19_4_1` keeps the CW-pair data
-- explicit and uses the chosen restriction morphism itself as the source-facing input.

/-- Definition 19.5.3. For a CW pair `(X, A)`, once chosen absolute cellular cochain complexes
`C^*(X; π)` and `C^*(A; π)` and the restriction map induced by the inclusion `A ↪ X` are fixed,
the relative cellular cochain complex `C^*(X, A; π)` is the kernel of that restriction map. -/
abbrev axiomaticRelativeCellularCochainComplex
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    [CWComplex (Set.univ : Set A)]
    (dataX : CellularDifferentialFamily X) (dataA : CellularDifferentialFamily A)
    (CX : AxiomaticCellularCochainComplex H X dataX)
    (CA : AxiomaticCellularCochainComplex H A dataA)
    (restriction : CX.complex ⟶ CA.complex) :
    CochainComplex AddCommGrpCat ℕ :=
  kernel restriction

/-- The inclusion `C^*(X, A; π) ⟶ C^*(X; π)` of the relative cellular cochain complex into the
ambient absolute cellular cochain complex. -/
abbrev relativeCellularCochainComplexι
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    [CWComplex (Set.univ : Set A)]
    (dataX : CellularDifferentialFamily X) (dataA : CellularDifferentialFamily A)
    (CX : AxiomaticCellularCochainComplex H X dataX)
    (CA : AxiomaticCellularCochainComplex H A dataA)
    (restriction : CX.complex ⟶ CA.complex) :
    axiomaticRelativeCellularCochainComplex H X A dataX dataA CX CA restriction ⟶ CX.complex :=
  kernel.ι restriction

/-- The inclusion `C^*(X, A; π) ⟶ C^*(X; π)` followed by the restriction map to `C^*(A; π)` is
zero. -/
theorem relativeCellularCochainComplexι_comp_restriction
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    [CWComplex (Set.univ : Set A)]
    (dataX : CellularDifferentialFamily X) (dataA : CellularDifferentialFamily A)
    (CX : AxiomaticCellularCochainComplex H X dataX)
    (CA : AxiomaticCellularCochainComplex H A dataA)
    (restriction : CX.complex ⟶ CA.complex) :
    relativeCellularCochainComplexι H X A dataX dataA CX CA restriction ≫ restriction = 0 := by
  change kernel.ι restriction ≫ restriction = 0
  exact kernel.condition restriction

/-- The relative cellular cochain complex together with its inclusion into `C^*(X; π)` carries
the expected kernel universal-property datum for the chosen restriction map associated to the CW
pair `(X, A)`. -/
abbrev relativeCellularCochainComplexIsKernel
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    [CWComplex (Set.univ : Set A)]
    (dataX : CellularDifferentialFamily X) (dataA : CellularDifferentialFamily A)
    (CX : AxiomaticCellularCochainComplex H X dataX)
    (CA : AxiomaticCellularCochainComplex H A dataA)
    (restriction : CX.complex ⟶ CA.complex) :
    IsLimit
      (KernelFork.ofι
        (relativeCellularCochainComplexι H X A dataX dataA CX CA restriction)
        (relativeCellularCochainComplexι_comp_restriction
          H X A dataX dataA CX CA restriction)) :=
  kernelIsKernel restriction
