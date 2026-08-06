import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Remark_18_2_3.LinearYoneda
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Construction_18_2_1

open CategoryTheory
open CategoryTheory.Linear
open HomologicalComplex
open Topology
open scoped CellularCohomology

noncomputable section

universe u

section RelativeCellularCochainComplexMapOfChainMap

variable
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {A : Topology.CWComplex.Subcomplex (Set.univ : Set X)}
    {dataX : CellularDifferentialFamily X}
    [RelativeCellularDifferentialDescends X A dataX]
    {Y : Type u} [TopologicalSpace Y] [CWComplex (Set.univ : Set Y)]
    {B : Topology.CWComplex.Subcomplex (Set.univ : Set Y)}
    {dataY : CellularDifferentialFamily Y}
    [RelativeCellularDifferentialDescends Y B dataY]
    (φ : relativeCellularChainComplex X A dataX ⟶ relativeCellularChainComplex Y B dataY)
    (π : Type u) [AddCommGroup π]

/-- Remark 18.2.3. A morphism of relative cellular chain complexes induces the corresponding
contravariant morphism on the relative cellular cochain complexes from `Construction 18.2.1`. -/
abbrev relativeCellularCochainComplexMapOfChainMap
    :
    relativeCellularCochainComplex Y B dataY π ⟶ relativeCellularCochainComplex X A dataX π :=
  ChainComplex.linearYonedaMap φ π

/-- In degree `n`, the induced cochain map on relative cellular cochains is precomposition by the
chain-group map `φ.f n`. -/
@[simp] theorem relativeCellularCochainComplexMapOfChainMap_f (n : ℕ) :
    (relativeCellularCochainComplexMapOfChainMap φ π).f n =
      ModuleCat.ofHom (leftComp ℤ (ModuleCat.of ℤ π) (φ.f n)) :=
  rfl

end RelativeCellularCochainComplexMapOfChainMap

section RelativeCellularCochainComplexMapOfChainMapId

variable
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {A : Topology.CWComplex.Subcomplex (Set.univ : Set X)}
    {data : CellularDifferentialFamily X}
    [RelativeCellularDifferentialDescends X A data]
    (π : Type u) [AddCommGroup π]

@[simp] theorem relativeCellularCochainComplexMapOfChainMap_id
    :
    relativeCellularCochainComplexMapOfChainMap
      (𝟙 (relativeCellularChainComplex X A data)) π =
        𝟙 (relativeCellularCochainComplex X A data π) :=
  rfl

end RelativeCellularCochainComplexMapOfChainMapId

section RelativeCellularCochainComplexMapOfChainMapComp

variable
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {A : Topology.CWComplex.Subcomplex (Set.univ : Set X)}
    {dataX : CellularDifferentialFamily X}
    [RelativeCellularDifferentialDescends X A dataX]
    {Y : Type u} [TopologicalSpace Y] [CWComplex (Set.univ : Set Y)]
    {B : Topology.CWComplex.Subcomplex (Set.univ : Set Y)}
    {dataY : CellularDifferentialFamily Y}
    [RelativeCellularDifferentialDescends Y B dataY]
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    {C : Topology.CWComplex.Subcomplex (Set.univ : Set Z)}
    {dataZ : CellularDifferentialFamily Z}
    [RelativeCellularDifferentialDescends Z C dataZ]
    (φ : relativeCellularChainComplex X A dataX ⟶ relativeCellularChainComplex Y B dataY)
    (ψ : relativeCellularChainComplex Y B dataY ⟶ relativeCellularChainComplex Z C dataZ)
    (π : Type u) [AddCommGroup π]

@[simp] theorem relativeCellularCochainComplexMapOfChainMap_comp
    :
    relativeCellularCochainComplexMapOfChainMap (φ ≫ ψ) π =
      relativeCellularCochainComplexMapOfChainMap ψ π ≫
        relativeCellularCochainComplexMapOfChainMap φ π :=
  rfl

end RelativeCellularCochainComplexMapOfChainMapComp

section RelativeCellularCohomologyMapOfChainMap

variable
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {A : Topology.CWComplex.Subcomplex (Set.univ : Set X)}
    {dataX : CellularDifferentialFamily X}
    [RelativeCellularDifferentialDescends X A dataX]
    {Y : Type u} [TopologicalSpace Y] [CWComplex (Set.univ : Set Y)]
    {B : Topology.CWComplex.Subcomplex (Set.univ : Set Y)}
    {dataY : CellularDifferentialFamily Y}
    [RelativeCellularDifferentialDescends Y B dataY]
    (φ : relativeCellularChainComplex X A dataX ⟶ relativeCellularChainComplex Y B dataY)
    (π : Type u) [AddCommGroup π]

/-- Taking degree-`n` homology of `relativeCellularCochainComplexMapOfChainMap` gives the induced
contravariant map on relative cellular cohomology. -/
abbrev relativeCellularCohomologyMapOfChainMap
    (n : ℕ) :
    Hˢᶜ[n](Y, B, dataY; π) ⟶ Hˢᶜ[n](X, A, dataX; π) :=
  homologyMap (relativeCellularCochainComplexMapOfChainMap φ π) n

/-- `relativeCellularCohomologyMapOfChainMap` is the homology map induced by the corresponding
cochain-complex morphism. -/
theorem relativeCellularCohomologyMapOfChainMap_def (n : ℕ) :
    relativeCellularCohomologyMapOfChainMap φ π n =
      homologyMap (relativeCellularCochainComplexMapOfChainMap φ π) n :=
  rfl

end RelativeCellularCohomologyMapOfChainMap

section RelativeCellularCohomologyMapOfChainMapId

variable
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {A : Topology.CWComplex.Subcomplex (Set.univ : Set X)}
    {data : CellularDifferentialFamily X}
    [RelativeCellularDifferentialDescends X A data]
    (π : Type u) [AddCommGroup π]

@[simp] theorem relativeCellularCohomologyMapOfChainMap_id
    (n : ℕ) :
    relativeCellularCohomologyMapOfChainMap
      (𝟙 (relativeCellularChainComplex X A data)) π n =
        𝟙 (Hˢᶜ[n](X, A, data; π)) := by
  simp [relativeCellularCohomologyMapOfChainMap]

end RelativeCellularCohomologyMapOfChainMapId

section RelativeCellularCohomologyMapOfChainMapComp

variable
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {A : Topology.CWComplex.Subcomplex (Set.univ : Set X)}
    {dataX : CellularDifferentialFamily X}
    [RelativeCellularDifferentialDescends X A dataX]
    {Y : Type u} [TopologicalSpace Y] [CWComplex (Set.univ : Set Y)]
    {B : Topology.CWComplex.Subcomplex (Set.univ : Set Y)}
    {dataY : CellularDifferentialFamily Y}
    [RelativeCellularDifferentialDescends Y B dataY]
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    {C : Topology.CWComplex.Subcomplex (Set.univ : Set Z)}
    {dataZ : CellularDifferentialFamily Z}
    [RelativeCellularDifferentialDescends Z C dataZ]
    (φ : relativeCellularChainComplex X A dataX ⟶ relativeCellularChainComplex Y B dataY)
    (ψ : relativeCellularChainComplex Y B dataY ⟶ relativeCellularChainComplex Z C dataZ)
    (π : Type u) [AddCommGroup π]

@[simp] theorem relativeCellularCohomologyMapOfChainMap_comp
    (n : ℕ) :
    relativeCellularCohomologyMapOfChainMap (φ ≫ ψ) π n =
      relativeCellularCohomologyMapOfChainMap ψ π n ≫
        relativeCellularCohomologyMapOfChainMap φ π n := by
  rw [relativeCellularCohomologyMapOfChainMap_def,
    relativeCellularCochainComplexMapOfChainMap_comp, homologyMap_comp]

end RelativeCellularCohomologyMapOfChainMapComp
