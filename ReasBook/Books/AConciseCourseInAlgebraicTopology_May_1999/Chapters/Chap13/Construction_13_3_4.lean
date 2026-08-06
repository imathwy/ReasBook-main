import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Homotopy.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.CellularCWMap
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_2_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Lemma_13_2_9

noncomputable section

open CategoryTheory
open Topology
open scoped unitInterval

-- Semantic recall via `lean_leansearch`: `ContinuousMap.Homotopic` is the canonical owner for
-- homotopy-commutative squares of continuous maps, and a morphism of `ChainComplex` is the
-- canonical owner for the resulting chain map once compatible degreewise components are fixed.

/-- The suspension-model owner `Σ(X^n / X^(n - 1))` used in Construction 13.3.4 after
specializing Construction 13.2.4 to the nested skeleta `X^(n - 1) ⊆ X^n ⊆ X^(n + 1)`. -/
abbrev cellularSkeletonBoundarySuspensionType
    (X : TopCat) [CWComplex (Set.univ : Set X)] (n : ℕ+) :=
  previousSkeletonQuotientSuspensionType
    (secondPredecessorSkeleton X n)
    (previousSkeletonLowerSubset
      (cellularSkeleton X (n : ℕ))
      (cellularSkeleton X ((n : ℕ) + 1)))

/-- The quotient-model owner `X^(n + 1) / X^n` used in Construction 13.3.4. -/
abbrev cellularSkeletonQuotientType
    (X : TopCat) [CWComplex (Set.univ : Set X)] (n : ℕ) :=
  collapseSubsetType
    (cellularSkeleton X (n + 1))
    (previousSkeletonLowerSubset
      (cellularSkeleton X n)
      (cellularSkeleton X (n + 1)))

/-- The quotient-model owner `X^n / X^(n - 1)` sitting inside the ambient `(n + 1)`-skeleton
model used in Construction 13.3.4. -/
abbrev cellularSkeletonBoundaryPreviousQuotientType
    (X : TopCat) [CWComplex (Set.univ : Set X)] (n : ℕ+) :=
  collapseSubsetType
    (previousSkeletonLowerSubset
      (cellularSkeleton X (n : ℕ))
      (cellularSkeleton X ((n : ℕ) + 1)))
    (previousSkeletonLowerSubset
      (secondPredecessorSkeleton X n)
      (previousSkeletonLowerSubset
        (cellularSkeleton X (n : ℕ))
        (cellularSkeleton X ((n : ℕ) + 1))))

/-- The identity bridge from the compactly generated quotient owner to the raw quotient owner
used internally by `topologicalBoundaryMapModel`. -/
private def cellularSkeletonQuotientCompactlyGeneratedToRaw
    (X : TopCat) [CWComplex (Set.univ : Set X)] (n : ℕ+) :
    @ContinuousMap
      (cellularSkeletonQuotientType X (n : ℕ))
      (collapseSubsetType
        (cellularSkeleton X ((n : ℕ) + 1))
        (previousSkeletonLowerSubset
          (cellularSkeleton X (n : ℕ))
          (cellularSkeleton X ((n : ℕ) + 1))))
      (previousSkeletonQuotientTypeTopologicalSpace
        (cellularSkeleton X (n : ℕ))
        (cellularSkeleton X ((n : ℕ) + 1)))
      instTopologicalSpaceQuotient :=
  @ContinuousMap.mk
    _
    _
    (previousSkeletonQuotientTypeTopologicalSpace
      (cellularSkeleton X (n : ℕ))
      (cellularSkeleton X ((n : ℕ) + 1)))
    instTopologicalSpaceQuotient
    id
    (by sorry)

private def cellularTopologicalBoundaryMapRaw
    (X : TopCat) [CWComplex (Set.univ : Set X)] (n : ℕ+) :
    C(cellularSkeletonQuotientType X (n : ℕ), cellularSkeletonBoundarySuspensionType X n) :=
  by
    -- The Chapter 13.2 boundary owner requires a chosen quotient/cofiber comparison.  The
    -- previous term accidentally supplied only a topology-change identity map in its place and
    -- therefore did not typecheck.  Keep this already proof-deferred construction isolated until
    -- that comparison is added to the public Construction 13.3.4 data.
    sorry

/-- The quotient-model boundary map `X^(n + 1) / X^n ⟶ Σ(X^n / X^(n - 1))` obtained by
specializing Construction 13.2.4 to the chosen skeleta of `X`. -/
def cellularTopologicalBoundaryMap
    (X : TopCat) [CWComplex (Set.univ : Set X)] (n : ℕ+) :
    C(cellularSkeletonQuotientType X (n : ℕ), cellularSkeletonBoundarySuspensionType X n) :=
  cellularTopologicalBoundaryMapRaw X n

/-- A cellular map `f : X ⟶ Y` sends the chosen `(n + 1)`-skeleton of `X` into the chosen
`(n + 1)`-skeleton of `Y`. -/
def cellularSkeletonSuccMap
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) (n : ℕ) :
    cellularSkeleton X (n + 1) → cellularSkeleton Y (n + 1) :=
  fun x ↦ ⟨f x.1, hf.mapsToSkeleton (n + 1) x.2⟩

/-- The map induced by a cellular map on `(n + 1)`-skeleta preserves the quotient relation
collapsing the chosen `n`-skeleton. -/
theorem cellularSkeletonSuccMap_respects
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) (n : ℕ)
    {x y : cellularSkeleton X (n + 1)}
    (hxy :
      collapseSubsetSetoid
        (previousSkeletonLowerSubset
          (cellularSkeleton X n)
          (cellularSkeleton X (n + 1))) x y) :
    collapseSubsetSetoid
      (previousSkeletonLowerSubset
        (cellularSkeleton Y n)
        (cellularSkeleton Y (n + 1)))
      (cellularSkeletonSuccMap f hf n x)
      (cellularSkeletonSuccMap f hf n y) := sorry

/-- The point-set map induced by a cellular map on the quotient skeleta `X^(n + 1) / X^n`. -/
def cellularSkeletonQuotientMapFun
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) (n : ℕ) :
    cellularSkeletonQuotientType X n → cellularSkeletonQuotientType Y n :=
  Quotient.map
    (cellularSkeletonSuccMap f hf n)
    (fun _ _ hxy ↦ cellularSkeletonSuccMap_respects f hf n hxy)

/-- The quotient-skeleton map induced by a cellular map is continuous. -/
theorem cellularSkeletonQuotientMapFun_continuous
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) (n : ℕ) :
    Continuous (cellularSkeletonQuotientMapFun f hf n) := sorry

/-- The continuous map induced by a cellular map on the quotient skeleta `X^(n + 1) / X^n`. -/
def cellularSkeletonQuotientMap
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) (n : ℕ) :
    C(cellularSkeletonQuotientType X n, cellularSkeletonQuotientType Y n) :=
  ⟨cellularSkeletonQuotientMapFun f hf n,
    cellularSkeletonQuotientMapFun_continuous f hf n⟩

/-- A cellular map induces a map on the copy of `X^n` sitting inside the chosen `(n + 1)`-skeleton
owner used in Construction 13.3.4. -/
def cellularSkeletonPredecessorInSuccMap
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) (n : ℕ+) :
    previousSkeletonLowerSubset
        (cellularSkeleton X (n : ℕ))
        (cellularSkeleton X ((n : ℕ) + 1)) →
      previousSkeletonLowerSubset
        (cellularSkeleton Y (n : ℕ))
        (cellularSkeleton Y ((n : ℕ) + 1)) :=
  fun x ↦
    ⟨⟨f x.1.1, hf.mapsToSkeleton ((n : ℕ) + 1) x.1.2⟩,
      hf.mapsToSkeleton (n : ℕ) x.2⟩

/-- The induced map on the copy of `X^n` inside `X^(n + 1)` preserves the quotient relation
collapsing the copy of `X^(n - 1)`. -/
theorem cellularSkeletonPredecessorInSuccMap_respects
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) (n : ℕ+)
    {x y :
      previousSkeletonLowerSubset
        (cellularSkeleton X (n : ℕ))
        (cellularSkeleton X ((n : ℕ) + 1))}
    (hxy :
      collapseSubsetSetoid
        (previousSkeletonLowerSubset
          (secondPredecessorSkeleton X n)
          (previousSkeletonLowerSubset
            (cellularSkeleton X (n : ℕ))
            (cellularSkeleton X ((n : ℕ) + 1)))) x y) :
    collapseSubsetSetoid
      (previousSkeletonLowerSubset
        (secondPredecessorSkeleton Y n)
        (previousSkeletonLowerSubset
          (cellularSkeleton Y (n : ℕ))
          (cellularSkeleton Y ((n : ℕ) + 1))))
      (cellularSkeletonPredecessorInSuccMap f hf n x)
      (cellularSkeletonPredecessorInSuccMap f hf n y) := sorry

/-- The point-set quotient map on the lower quotient skeleta `X^n / X^(n - 1)` inside the
ambient `(n + 1)`-skeleton model used in Construction 13.3.4. -/
def cellularSkeletonBoundaryPreviousQuotientMapFun
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) (n : ℕ+) :
    cellularSkeletonBoundaryPreviousQuotientType X n →
      cellularSkeletonBoundaryPreviousQuotientType Y n :=
  Quotient.map
    (cellularSkeletonPredecessorInSuccMap f hf n)
    (fun _ _ hxy ↦ cellularSkeletonPredecessorInSuccMap_respects f hf n hxy)

/-- The lower quotient-skeleton map induced by a cellular map is continuous. -/
theorem cellularSkeletonBoundaryPreviousQuotientMapFun_continuous
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) (n : ℕ+) :
    Continuous (cellularSkeletonBoundaryPreviousQuotientMapFun f hf n) := sorry

/-- The continuous lower quotient-skeleton map `X^n / X^(n - 1) ⟶ Y^n / Y^(n - 1)` induced by a
cellular map inside the ambient `(n + 1)`-skeleton model of Construction 13.3.4. -/
def cellularSkeletonBoundaryPreviousQuotientMap
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) (n : ℕ+) :
    C(cellularSkeletonBoundaryPreviousQuotientType X n,
      cellularSkeletonBoundaryPreviousQuotientType Y n) :=
  ⟨cellularSkeletonBoundaryPreviousQuotientMapFun f hf n,
    cellularSkeletonBoundaryPreviousQuotientMapFun_continuous f hf n⟩

/-- The representative-level suspension map on `Σ(X^n / X^(n - 1))` induced by a cellular map. -/
def cellularSkeletonBoundarySuspensionMapRaw
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) (n : ℕ+) :
    previousSkeletonQuotientSuspensionCarrier
        (secondPredecessorSkeleton X n)
        (previousSkeletonLowerSubset
          (cellularSkeleton X (n : ℕ))
          (cellularSkeleton X ((n : ℕ) + 1))) →
      previousSkeletonQuotientSuspensionCarrier
        (secondPredecessorSkeleton Y n)
        (previousSkeletonLowerSubset
          (cellularSkeleton Y (n : ℕ))
          (cellularSkeleton Y ((n : ℕ) + 1)))
  | Sum.inl _ =>
      previousSkeletonQuotientSuspensionSouth
        (secondPredecessorSkeleton Y n)
        (previousSkeletonLowerSubset
          (cellularSkeleton Y (n : ℕ))
          (cellularSkeleton Y ((n : ℕ) + 1)))
  | Sum.inr (Sum.inl (q, t)) =>
      previousSkeletonQuotientSuspensionMk
        (secondPredecessorSkeleton Y n)
        (previousSkeletonLowerSubset
          (cellularSkeleton Y (n : ℕ))
          (cellularSkeleton Y ((n : ℕ) + 1)))
        (cellularSkeletonBoundaryPreviousQuotientMapFun f hf n q) t
  | Sum.inr (Sum.inr _) =>
      previousSkeletonQuotientSuspensionNorth
        (secondPredecessorSkeleton Y n)
        (previousSkeletonLowerSubset
          (cellularSkeleton Y (n : ℕ))
          (cellularSkeleton Y ((n : ℕ) + 1)))

/-- The representative-level suspension map induced by a cellular map respects the suspension
quotient relation. -/
theorem cellularSkeletonBoundarySuspensionMapRaw_respects
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) (n : ℕ+)
    {p q :
      previousSkeletonQuotientSuspensionCarrier
        (secondPredecessorSkeleton X n)
        (previousSkeletonLowerSubset
          (cellularSkeleton X (n : ℕ))
          (cellularSkeleton X ((n : ℕ) + 1)))}
    (hpq :
      previousSkeletonQuotientSuspensionSetoid
        (secondPredecessorSkeleton X n)
        (previousSkeletonLowerSubset
          (cellularSkeleton X (n : ℕ))
          (cellularSkeleton X ((n : ℕ) + 1))) p q) :
    previousSkeletonQuotientSuspensionSetoid
      (secondPredecessorSkeleton Y n)
      (previousSkeletonLowerSubset
        (cellularSkeleton Y (n : ℕ))
        (cellularSkeleton Y ((n : ℕ) + 1)))
      (cellularSkeletonBoundarySuspensionMapRaw f hf n p)
      (cellularSkeletonBoundarySuspensionMapRaw f hf n q) := sorry

/-- The point-set suspension map on `Σ(X^n / X^(n - 1))` induced by a cellular map. -/
def cellularSkeletonBoundarySuspensionMapFun
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) (n : ℕ+) :
    cellularSkeletonBoundarySuspensionType X n →
      cellularSkeletonBoundarySuspensionType Y n :=
  Quotient.map
    (cellularSkeletonBoundarySuspensionMapRaw f hf n)
    (fun _ _ hpq ↦ cellularSkeletonBoundarySuspensionMapRaw_respects f hf n hpq)

/-- The suspension map induced by a cellular map on `Σ(X^n / X^(n - 1))` is continuous. -/
theorem cellularSkeletonBoundarySuspensionMapFun_continuous
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) (n : ℕ+) :
    Continuous (cellularSkeletonBoundarySuspensionMapFun f hf n) := sorry

/-- The continuous map on the suspension owner `Σ(X^n / X^(n - 1))` canonically induced by a
cellular map `f`. -/
def cellularSkeletonBoundarySuspensionMap
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) (n : ℕ+) :
    C(cellularSkeletonBoundarySuspensionType X n, cellularSkeletonBoundarySuspensionType Y n) :=
  ⟨cellularSkeletonBoundarySuspensionMapFun f hf n,
    cellularSkeletonBoundarySuspensionMapFun_continuous f hf n⟩

/-- Construction 13.3.4 (1). A cellular map `f : X ⟶ Y` induces quotient-skeleton maps
`X^(n + 1) / X^n ⟶ Y^(n + 1) / Y^n`; on the quotient-model boundary maps from
Construction 13.2.4, these induced maps make the boundary square commute up to homotopy. -/
theorem cellularSkeletonQuotientMap_boundary_homotopic
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) (n : ℕ+) :
    ContinuousMap.Homotopic
      ((cellularSkeletonBoundarySuspensionMap f hf n).comp
        (cellularTopologicalBoundaryMap X n))
      ((cellularTopologicalBoundaryMap Y n).comp
        (cellularSkeletonQuotientMap f hf (n : ℕ))) := sorry

/-- Positive-degree comparison data showing that `component n` is the chain-level map obtained by
transporting the canonical quotient-skeleton map induced by `f` along chosen target comparison
isomorphisms `C_n ≃ H'_n(X^n / X^(n - 1))`. The chosen target predecessor point is required to
be the image of the chosen source predecessor point, and the pointed quotient map is required to
have underlying continuous map `cellularSkeletonQuotientMap f hf ((n : ℕ) - 1)`. -/
structure CellularChainComponentDegreeComparison
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f)
    (component :
      ∀ n : ℕ,
        ModuleCat.of ℤ (cellularChainGroup X n) ⟶
          ModuleCat.of ℤ (cellularChainGroup Y n))
    (n : ℕ+) where
  xPrevX : cellularSkeleton X ((n : ℕ) - 1)
  xPrevY : cellularSkeleton Y ((n : ℕ) - 1)
  xPrevY_spec : f xPrevX = xPrevY
  targetComparisonX : CellularTargetComparisonIso X n xPrevX
  targetComparisonY : CellularTargetComparisonIso Y n xPrevY
  quotientMap :
    cellularTargetQuotientPointed X n xPrevX ⟶
      cellularTargetQuotientPointed Y n xPrevY
  quotientMap_spec :
    (PointedCompactlyGenerated.Hom.hom quotientMap).hom.hom =
      cellularSkeletonQuotientMap f hf ((n : ℕ) - 1)
  component_spec :
    ∀ c : cellularChainGroup X (n : ℕ),
      targetComparisonY ((component (n : ℕ)) c) =
        provisionalReducedGroupPointedMap n quotientMap (targetComparisonX c)

/-- Degree-`0` comparison data showing that the map on `C₀(X)` is induced by `f` on the chosen
`0`-cells, equivalently on the quotient `X^0 / X^(-1)` of `0`-skeleta. -/
structure CellularChainDegreeZeroComparison
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y)
    (component :
      ModuleCat.of ℤ (cellularChainGroup X 0) ⟶
        ModuleCat.of ℤ (cellularChainGroup Y 0)) where
  zeroCellMap : cellularCell X 0 → cellularCell Y 0
  zeroCellMap_spec :
    ∀ i : cellularCell X 0,
      f (cellularZeroCellPoint X i) = cellularZeroCellPoint Y (zeroCellMap i)
  component_spec :
    component = ModuleCat.ofHom ((FreeAbelianGroup.map zeroCellMap).toIntLinearMap)

/-- A degreewise family on cellular chains is induced by the quotient-skeleton maps of a cellular
map when the boundary squares from Construction 13.3.4 (1) commute up to homotopy in every
positive degree and the resulting family is compatible with the chosen cellular differentials. The
positive-degree quotient comparison witnesses are carried separately by `componentSpec`. -/
def IsCellularChainComponentFamilyInducedByQuotients
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f)
    (dataX : CellularDifferentialFamily X) (dataY : CellularDifferentialFamily Y)
    (component :
      ∀ n : ℕ,
        ModuleCat.of ℤ (cellularChainGroup X n) ⟶
          ModuleCat.of ℤ (cellularChainGroup Y n)) : Prop :=
  (∀ n : ℕ+,
    ContinuousMap.Homotopic
      ((cellularSkeletonBoundarySuspensionMap f hf n).comp
        (cellularTopologicalBoundaryMap X n))
      ((cellularTopologicalBoundaryMap Y n).comp
        (cellularSkeletonQuotientMap f hf (n : ℕ)))) ∧
    ∀ n : ℕ,
      ModuleCat.ofHom (dataX.differential n).toIntLinearMap ≫ component n =
        component (n + 1) ≫ ModuleCat.ofHom (dataY.differential n).toIntLinearMap

/-- A cellular chain-complex morphism is induced by the quotient-skeleton maps of a cellular map
when its degree-`0` part comes from the induced map on `0`-cells and its positive-degree parts are
transported from the canonical quotient-skeleton maps via the chosen Chapter 13 comparison data.
-/
def IsCellularChainMapInducedByQuotients
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f)
    (dataX : CellularDifferentialFamily X) (dataY : CellularDifferentialFamily Y)
    (φ : cellularChainComplex X dataX ⟶ cellularChainComplex Y dataY) : Prop :=
  ∃ _ : CellularChainDegreeZeroComparison f (φ.f 0),
    ∃ _ : ∀ n : ℕ+, CellularChainComponentDegreeComparison f hf φ.f n,
      IsCellularChainComponentFamilyInducedByQuotients f hf dataX dataY φ.f

/-- Bundled data of a cellular chain map induced by the quotient-skeleton maps of a cellular
map `f`, including chosen cellular differential families on `X` and `Y`, the induced chain map
`C_*(X) ⟶ C_*(Y)`, and explicit degreewise quotient-comparison witnesses. -/
structure InducedCellularChainMapFromQuotients
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) where
  dataX : CellularDifferentialFamily X
  dataY : CellularDifferentialFamily Y
  φ : cellularChainComplex X dataX ⟶ cellularChainComplex Y dataY
  degreeZero :
    CellularChainDegreeZeroComparison f (φ.f 0)
  componentSpec :
    ∀ n : ℕ+, CellularChainComponentDegreeComparison f hf φ.f n
  inducedSpec :
    IsCellularChainComponentFamilyInducedByQuotients
      f hf dataX dataY φ.f

/-- The quotient-induced cellular chain-map owner attached to a cellular `TopCat` morphism. -/
abbrev InducedCellularChainMap
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) :=
  InducedCellularChainMapFromQuotients f hf

namespace InducedCellularChainMapFromQuotients

variable {X Y : TopCat}
variable [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
variable {f : X ⟶ Y} {hf : IsCellularCWMap f}

/-- Reindex a bundled quotient-induced cellular chain map along identified source and target
cellular differential families. -/
abbrev toChainMap
    (induced : InducedCellularChainMapFromQuotients f hf)
    {dataX' : CellularDifferentialFamily X} {dataY' : CellularDifferentialFamily Y}
    (hX : induced.dataX = dataX') (hY : induced.dataY = dataY') :
    cellularChainComplex X dataX' ⟶ cellularChainComplex Y dataY' :=
  eqToHom (congrArg (cellularChainComplex X) hX).symm ≫
    induced.φ ≫
      eqToHom (congrArg (cellularChainComplex Y) hY)

@[simp] theorem toChainMap_rfl
    (induced : InducedCellularChainMapFromQuotients f hf) :
    induced.toChainMap rfl rfl = induced.φ := by
  simp [toChainMap]

/-- A bundled quotient-induced cellular chain map satisfies the direct chain-map specification
from Construction 13.3.4 (2). -/
theorem isInduced
    (induced : InducedCellularChainMapFromQuotients f hf) :
    IsCellularChainMapInducedByQuotients f hf induced.dataX induced.dataY induced.φ :=
  ⟨induced.degreeZero, induced.componentSpec, induced.inducedSpec⟩

/-- The bundled induced cellular chain map carries the homotopy-commutative boundary squares from
Construction 13.3.4 (1) in every positive degree. -/
theorem boundary_homotopic
    (induced : InducedCellularChainMapFromQuotients f hf) (n : ℕ+) :
    ContinuousMap.Homotopic
      ((cellularSkeletonBoundarySuspensionMap f hf n).comp
        (cellularTopologicalBoundaryMap X n))
      ((cellularTopologicalBoundaryMap Y n).comp
        (cellularSkeletonQuotientMap f hf (n : ℕ))) :=
  induced.inducedSpec.1 n

/-- In positive degree, the component of a bundled induced cellular chain map is the map obtained
from the canonical quotient-skeleton map via the chosen target comparison isomorphisms. -/
theorem component_spec
    (induced : InducedCellularChainMapFromQuotients f hf) (n : ℕ+)
    (c : cellularChainGroup X (n : ℕ)) :
    let spec := induced.componentSpec n
    spec.targetComparisonY ((induced.φ.f (n : ℕ)) c) =
      provisionalReducedGroupPointedMap n spec.quotientMap (spec.targetComparisonX c) :=
  (induced.componentSpec n).component_spec c

/-- The degreewise components of a bundled induced cellular chain map commute with the chosen
cellular differentials. -/
theorem differential_comm
    (induced : InducedCellularChainMapFromQuotients f hf) (n : ℕ) :
    ModuleCat.ofHom (induced.dataX.differential n).toIntLinearMap ≫ induced.φ.f n =
      induced.φ.f (n + 1) ≫
        ModuleCat.ofHom (induced.dataY.differential n).toIntLinearMap :=
  induced.inducedSpec.2 n

end InducedCellularChainMapFromQuotients

/-- Construction 13.3.4 (2). A cellular map `f : X ⟶ Y` admits chosen cellular differential data
on `X` and `Y` together with a chain map `C_*(X) ⟶ C_*(Y)` induced by the quotient-skeleton maps
of part (1). The source-facing existence statement exposes the chosen chain-complex morphism
directly, while `InducedCellularChainMapFromQuotients f hf` remains the bundled bridge owner for
downstream constructions that need the accompanying comparison data. -/
theorem existsInducedCellularChainMap
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : IsCellularCWMap f) :
    ∃ dataX : CellularDifferentialFamily X,
      ∃ dataY : CellularDifferentialFamily Y,
        ∃ φ : cellularChainComplex X dataX ⟶ cellularChainComplex Y dataY,
          IsCellularChainMapInducedByQuotients f hf dataX dataY φ := by
  sorry
