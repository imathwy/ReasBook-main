import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Abelian.Ext
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_2_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_5_1

noncomputable section

open CategoryTheory
open Topology

universe u

-- Semantic recall via `lean_leansearch`: `ChainComplex.linearYonedaObj` is the canonical owner
-- for the cochain complex `Hom(C_*(X), π)`. This file keeps the Chapter 19 source-facing
-- cellular cochain complex as chosen support data and makes Theorem 19.5.2 a direct bridge from
-- that source-facing complex to the canonical Hom complex.

/-- The cochain complex `Hom(C_*(X), π)` attached to the chosen cellular chain complex `C_*(X)`,
viewed in `AddCommGrpCat`. -/
abbrev cellularChainHomComplex
    (π : Type u) [AddCommGroup π]
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (data : CellularDifferentialFamily X) :
    CochainComplex AddCommGrpCat ℕ :=
  (((forget₂ (ModuleCat ℤ) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
    ((cellularChainComplex X data).linearYonedaObj ℤ (ModuleCat.of ℤ π)))

/-- A chosen axiomatic cellular cochain complex `C^*(X; π)` packages a cochain complex whose
degree-`n` term is identified with `H^n(X^n, X^(n - 1); π)`, together with a specified cochain
comparison to the canonical Hom complex `Hom(C_*(X), π)`. -/
structure AxiomaticCellularCochainComplex
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (space : Type u) [TopologicalSpace space] [CWComplex (Set.univ : Set space)]
    (data : CellularDifferentialFamily space)
    extends toCochainComplex : CochainComplex AddCommGrpCat ℕ where
  /-- Each degree of the chosen cochain complex identifies with the axiomatic cellular cochains
  `H^n(X^n, X^(n - 1); π)`. -/
  degreeIso : ∀ n : ℕ, toCochainComplex.X n ≅ axiomaticCellularCochains H space n
  /-- The chosen comparison identifying this axiomatic cellular cochain complex with the
  canonical Hom complex `Hom(C_*(X), π)`. -/
  comparisonIso : toCochainComplex ≅ cellularChainHomComplex π space data

namespace AxiomaticCellularCochainComplex

/-- The underlying cochain complex of a chosen axiomatic cellular cochain model. -/
abbrev complex
    {π : Type u} [AddCommGroup π] {H : PairCohomologyTheory π}
    {space : Type u} [TopologicalSpace space] [CWComplex (Set.univ : Set space)]
    {data : CellularDifferentialFamily space}
    (C : AxiomaticCellularCochainComplex H space data) :
    CochainComplex AddCommGrpCat ℕ :=
  C.toCochainComplex

/-- A companion to Theorem 19.5.2: in degree `n`, a chosen axiomatic cellular cochain complex
realizes the axiomatic cellular cochains `H^n(X^n, X^(n - 1); π)`. -/
abbrev degreewiseIso
    {π : Type u} [AddCommGroup π] {H : PairCohomologyTheory π}
    {space : Type u} [TopologicalSpace space] [CWComplex (Set.univ : Set space)]
    {data : CellularDifferentialFamily space}
    (C : AxiomaticCellularCochainComplex H space data) (n : ℕ) :
    C.complex.X n ≅ axiomaticCellularCochains H space n :=
  C.degreeIso n

/-- Theorem 19.5.2. A chosen axiomatic cellular cochain complex `C^*(X; π)` carries the
source-facing comparison isomorphism to the canonical Hom complex `Hom(C_*(X), π)`. -/
abbrev homComplexIso
    {π : Type u} [AddCommGroup π] {H : PairCohomologyTheory π}
    {space : Type u} [TopologicalSpace space] [CWComplex (Set.univ : Set space)]
    {data : CellularDifferentialFamily space}
    (C : AxiomaticCellularCochainComplex H space data) :
    C.complex ≅ cellularChainHomComplex π space data :=
  C.comparisonIso

end AxiomaticCellularCochainComplex

/-- A companion existence statement for later Chapter 19 constructions that need an explicit
chosen model for `C^*(X; π)`. -/
theorem exists_axiomaticCellularCochainComplex
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (data : CellularDifferentialFamily X) :
    Nonempty (AxiomaticCellularCochainComplex H X data) := by
  sorry
