import Mathlib.CategoryTheory.Abelian.Ext
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_3_2

noncomputable section

open CategoryTheory
open Topology

universe u

-- Semantic recall via `lean_leansearch`: `ChainComplex.linearYonedaObj` is the canonical owner
-- for the cochain complex `Hom(C_*, π)`. Definition 17.3.2 packages the same pattern for
-- `ℤ`-graded chain complexes; since `relativeCellularChainComplex X A data` is `ℕ`-graded in the
-- current project, this item records the cellular-cochain owner directly by `linearYonedaObj`.

/-- Construction 18.2.1 (1). For a CW pair `(X, A)` and an Abelian group `π`, the cellular
cochains with coefficients in `π` are the cochain complex `Hom(C_*(X, A), π)`, formalized as the
canonical `linearYonedaObj` of the relative cellular chain complex `C_*(X, A)`. -/
abbrev relativeCellularCochainComplex
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (π : Type u) [AddCommGroup π] :
    CochainComplex (ModuleCat ℤ) ℕ :=
  (relativeCellularChainComplex X A data).linearYonedaObj ℤ (ModuleCat.of ℤ π)

/-- Degree `n` of `relativeCellularCochainComplex X A data π` is the `ℤ`-module of `ℤ`-linear
maps from the degree-`n` relative cellular chain group `C_n(X, A)` to `π`. -/
@[simp] theorem relativeCellularCochainComplex_X
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (π : Type u) [AddCommGroup π] (n : ℕ) :
    (relativeCellularCochainComplex X A data π).X n =
      ModuleCat.of ℤ
        (((relativeCellularChainComplex X A data).X n) ⟶ ModuleCat.of ℤ π) :=
  rfl

/-- Construction 18.2.1 (2). The cellular cohomology of a CW pair `(X, A)` with coefficients in
`π` is the cohomology of the cellular cochain complex `Hom(C_*(X, A), π)`. -/
abbrev relativeCellularCohomology
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (π : Type u) [AddCommGroup π] :
    ℕ → ModuleCat ℤ :=
  fun n ↦ (relativeCellularCochainComplex X A data π).homology n

/-- Lean notation for the relative cellular cohomology groups `Hˢᶜⁿ(X, A; π)` computed from the
chosen cellular differential family `data`. -/
scoped[CellularCohomology] notation "Hˢᶜ[" n "](" X ", " A ", " data "; " π ")" =>
  relativeCellularCohomology X A data π n

open scoped CellularCohomology

/-- Evaluating `Hˢᶜ[n](X, A, data; π)` in degree `n` gives the degree-`n`
cohomology object of `relativeCellularCochainComplex X A data π`. -/
@[simp] theorem relativeCellularCohomology_apply
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (π : Type u) [AddCommGroup π] (n : ℕ) :
    Hˢᶜ[n](X, A, data; π) =
      (relativeCellularCochainComplex X A data π).homology n :=
  rfl
