import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.CWComplex.Classical.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_4_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Corollary_10_4_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Lemma_10_2_2

open Set
open scoped TopCat

noncomputable section

-- Semantic recall via `lean_leansearch`: `Topology.CWComplex`, `Topology.CWComplex.cell`,
-- `Topology.CWComplex.skeleton`, and Chapter 10's `ContinuousMap.IsCellular` are the canonical
-- owners for the source's sphere CW structure and cellularity statements, while earlier repo
-- precedent already uses `underTopOfPoint (𝕊 n) (sphereBasepoint n)` for actual based sphere
-- maps.

/-- The concrete Euclidean unit-sphere model underlying `𝕊 n`. -/
private abbrev SphereModel (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The topological sphere `𝕊 n` is homeomorphic to its concrete Euclidean sphere model. -/
private abbrev sphereModelHomeomorph (n : ℕ) : 𝕊 n ≃ₜ SphereModel n :=
  Homeomorph.ulift

/-- The sphere `𝕊 n` is Hausdorff. -/
private instance sphereT2Space (n : ℕ) : T2Space (𝕊 n) :=
  (sphereModelHomeomorph n).symm.t2Space

/-- The two cells in the standard CW decomposition of `S^n`: one `0`-cell and one `n`-cell. -/
private abbrev SphereStandardCell (n k : ℕ) :=
  PLift (k = 0) ⊕ PLift (k = n)

/-- The `0`-cell of the standard sphere CW structure is the chosen basepoint. -/
private def sphereZeroCellPartialEquiv (n : ℕ) :
    PartialEquiv (Fin 0 → ℝ) (𝕊 n) :=
  PartialEquiv.single 0 (sphereBasepoint n)

/-- The ambient Euclidean space of the sphere model has the expected finite dimension. -/
private instance sphereModel_finrank_fact (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨@finrank_euclideanSpace_fin ℝ _ (n + 1)⟩

/-- The standard `n`-cell of `S^n` is the punctured-sphere chart at `sphereBasepoint n`,
reparametrized by the open unit ball in `ℝ^n`. -/
private noncomputable def sphereTopCellPartialEquiv (n : ℕ) :
    PartialEquiv (Fin n → ℝ) (𝕊 n) :=
  let b : TopCat.sphere.{0} n := sphereBasepoint n
  let v : SphereModel n := b.down
  (((((EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph.toOpenPartialHomeomorph).trans
      OpenPartialHomeomorph.univUnitBall.symm).trans
      (stereographic' n v).symm).transHomeomorph
      (Homeomorph.ulift.symm : SphereModel n ≃ₜ TopCat.sphere.{0} n)).toPartialEquiv

/-- The characteristic maps of the standard sphere CW structure. -/
private noncomputable def sphereStandardCellMap (n k : ℕ) (c : SphereStandardCell n k) :
    PartialEquiv (Fin k → ℝ) (𝕊 n) :=
  match c with
  | Sum.inl h =>
      match k, h.down with
      | 0, rfl => sphereZeroCellPartialEquiv n
  | Sum.inr h =>
      match k, h.down with
      | _, rfl => sphereTopCellPartialEquiv n

/-- The standard sphere cell-index family is finite in each degree. -/
private theorem sphereStandardCell_finite (n k : ℕ) : Finite (SphereStandardCell n k) := sorry

/-- The source of each standard sphere cell map is the unit open ball. -/
private theorem sphereStandardCellMap_source_eq (n : ℕ) :
    ∀ (k : ℕ) (i : SphereStandardCell n k),
      (sphereStandardCellMap n k i).source = Metric.ball 0 1 := sorry

/-- Each standard sphere cell map is continuous on the closed unit ball. -/
private theorem sphereStandardCellMap_continuousOn (n : ℕ) :
    ∀ (k : ℕ) (i : SphereStandardCell n k),
      ContinuousOn (sphereStandardCellMap n k i) (Metric.closedBall 0 1) := sorry

/-- The inverses of the standard sphere cell maps are continuous on their targets. -/
private theorem sphereStandardCellMap_continuousOn_symm (n : ℕ) :
    ∀ (k : ℕ) (i : SphereStandardCell n k),
      ContinuousOn (sphereStandardCellMap n k i).symm (sphereStandardCellMap n k i).target := sorry

/-- Distinct open cells in the standard sphere CW structure are disjoint. -/
private theorem sphereStandardCellMap_pairwiseDisjoint (n : ℕ) :
    (Set.univ : Set (Σ k, SphereStandardCell n k)).PairwiseDisjoint
      (fun ki ↦ sphereStandardCellMap n ki.1 ki.2 '' Metric.ball 0 1) := sorry

/-- The boundary of each standard sphere cell lands in lower-dimensional closed cells. -/
private theorem sphereStandardCellMap_mapsTo (n : ℕ) :
    ∀ (k : ℕ) (i : SphereStandardCell n k),
      Set.MapsTo
        (sphereStandardCellMap n k i)
        (Metric.sphere 0 1)
        (⋃ (m : ℕ), ⋃ (_ : m < k) (j : SphereStandardCell n m),
          sphereStandardCellMap n m j '' Metric.closedBall 0 1) := sorry

/-- Closedness for the explicit standard sphere CW decomposition. -/
private theorem sphereStandardCellMap_closed (n : ℕ) :
    ∀ (A : Set (𝕊 n)) (_ : A ⊆ Set.univ),
      (∀ k j,
        IsClosed (A ∩ sphereStandardCellMap n k j '' Metric.closedBall 0 1)) →
      IsClosed A := sorry

/-- The closed cells of the standard sphere CW structure cover the whole sphere. -/
private theorem sphereStandardCellMap_union (n : ℕ) :
    (⋃ (k : ℕ) (j : SphereStandardCell n k),
      sphereStandardCellMap n k j '' Metric.closedBall 0 1) = (Set.univ : Set (𝕊 n)) := sorry

/-- The explicit standard CW complex on `S^n` used in Example 10.1.10. -/
private noncomputable abbrev sphereStandardCWComplex (n : ℕ) :
    Topology.CWComplex (Set.univ : Set (𝕊 n)) :=
  Topology.CWComplex.mkFiniteType
    (Set.univ : Set (𝕊 n))
    (SphereStandardCell n)
    (sphereStandardCellMap n)
    (sphereStandardCell_finite n)
    (sphereStandardCellMap_source_eq n)
    (sphereStandardCellMap_continuousOn n)
    (sphereStandardCellMap_continuousOn_symm n)
    (sphereStandardCellMap_pairwiseDisjoint n)
    (sphereStandardCellMap_mapsTo n)
    (sphereStandardCellMap_closed n)
    (sphereStandardCellMap_union n)

/-- In the standard sphere cell-index family, the `0`-cell is unique when `0 < n`. -/
private theorem sphereStandardCell_zero_eq {n : ℕ} (hn : 0 < n) (c : SphereStandardCell n 0) :
    c = Sum.inl ⟨rfl⟩ := sorry

/-- The `0`-cell of the standard sphere cell-index family is unique when `0 < n`. -/
private abbrev sphereStandardCellUniqueZero (n : ℕ) (hn : 0 < n) : Unique (SphereStandardCell n 0)
    where
  default := Sum.inl ⟨rfl⟩
  uniq c := sphereStandardCell_zero_eq hn c

/-- In the standard sphere cell-index family, the `n`-cell is unique when `0 < n`. -/
private theorem sphereStandardCell_top_eq {n : ℕ} (hn : 0 < n) (c : SphereStandardCell n n) :
    c = Sum.inr ⟨rfl⟩ := sorry

/-- The `n`-cell of the standard sphere cell-index family is unique when `0 < n`. -/
private abbrev sphereStandardCellUniqueTop (n : ℕ) (hn : 0 < n) : Unique (SphereStandardCell n n)
    where
  default := Sum.inr ⟨rfl⟩
  uniq c := sphereStandardCell_top_eq hn c

/-- There are no standard sphere cells away from degrees `0` and `n`. -/
private theorem sphereStandardCell_false_of_ne_zero_ne_top
    {n k : ℕ} (hk0 : k ≠ 0) (hkn : k ≠ n) (c : SphereStandardCell n k) : False := by
  cases c with
  | inl h => exact hk0 h.down
  | inr h => exact hkn h.down

/-- The standard sphere cell-index family is empty away from degrees `0` and `n`. -/
private abbrev sphereStandardCellIsEmptyOf_ne_zero_ne_top
    {n k : ℕ} (hk0 : k ≠ 0) (hkn : k ≠ n) : IsEmpty (SphereStandardCell n k) where
  false c := sphereStandardCell_false_of_ne_zero_ne_top hk0 hkn c

/-- The chosen basepoint is the `0`-vertex of the explicit standard CW structure on `S^n`. -/
private theorem sphereStandardCWComplex_basepoint_isVertex (n : ℕ) :
    letI : Topology.CWComplex (Set.univ : Set (𝕊 n)) := sphereStandardCWComplex n
    IsCWVertex (sphereBasepoint n) := sorry

/-- The canonical standard CW complex on `S^n` used in Example 10.1.10. -/
noncomputable abbrev standardSphereCWComplex (n : ℕ) :
    Topology.CWComplex (Set.univ : Set (𝕊 n)) :=
  sphereStandardCWComplex n

/-- The canonical standard CW complex on `S^n` supplies its underlying CWComplex instance. -/
instance standardSphereCWComplexInst (n : ℕ) :
    Topology.CWComplex (Set.univ : Set (𝕊 n)) :=
  standardSphereCWComplex n

/-- Example 10.1.10 (1). The chosen basepoint is a vertex of the standard CW complex on `S^n`,
so in particular this covers the source's `n > 0` case. -/
theorem standardSphereCWComplex_basepoint_isVertex (n : ℕ) :
    IsCWVertex (sphereBasepoint n) := sorry

/-- In the canonical standard CW complex on `S^n`, the `0`-cell is unique for `0 < n`. -/
instance standardSphereCWComplex_zeroCellUnique (n : ℕ) [Fact (0 < n)] :
    Unique (Topology.CWComplex.cell (Set.univ : Set (𝕊 n)) 0) :=
  sphereStandardCellUniqueZero n ‹Fact (0 < n)›.1

/-- In the canonical standard CW complex on `S^n`, the `n`-cell is unique for `0 < n`. -/
instance standardSphereCWComplex_topCellUnique (n : ℕ) [Fact (0 < n)] :
    Unique (Topology.CWComplex.cell (Set.univ : Set (𝕊 n)) n) :=
  sphereStandardCellUniqueTop n ‹Fact (0 < n)›.1

/-- In the canonical standard CW complex on `S^n`, there are no cells in dimensions other than
`0` and `n`. -/
theorem standardSphereCWComplex_isEmptyCell_of_ne_zero_ne_top
    {n k : ℕ} (hk0 : k ≠ 0) (hkn : k ≠ n) :
    IsEmpty (Topology.CWComplex.cell (Set.univ : Set (𝕊 n)) k) :=
  sphereStandardCellIsEmptyOf_ne_zero_ne_top hk0 hkn

/-- Example 10.1.10 (2). For the canonical standard one-vertex CW complexes on `S^m` and `S^n`
with `m < n`, a cellular map `S^m → S^n`, formalized by `ContinuousMap.IsCellular`, is the
constant map at `sphereBasepoint n`. -/
theorem cellularMap_eq_const_of_lt
    {m n : ℕ} (hm : 0 < m) (hmn : m < n) (f : C(𝕊 m, 𝕊 n))
    (hcell : f.IsCellular) :
    f = ContinuousMap.const (𝕊 m) (sphereBasepoint n) := sorry

/-- A cellular based map between the canonical standard sphere CW complexes is constant when
`m < n`. -/
theorem cellularBasedMap_eq_const_of_lt
    {m n : ℕ} (hm : 0 < m) (hmn : m < n)
    (f : underTopOfPoint (𝕊 m) (sphereBasepoint m) ⟶
      underTopOfPoint (𝕊 n) (sphereBasepoint n))
    (hcell : (UnderTopOfPoint.toContinuousMap f).IsCellular) :
    f = underTopOfPointMap (ContinuousMap.const (𝕊 m) (sphereBasepoint n)) (sphereBasepoint m) :=
  sorry

/-- Example 10.1.10 (3). For the canonical standard one-vertex sphere CW complexes on `S^m` and
`S^n` with `n ≤ m`, every based map `S^m → S^n` is cellular, formalized by
`ContinuousMap.IsCellular` on the underlying continuous map. -/
theorem basedMap_cellular_of_le
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : n ≤ m)
    (f : underTopOfPoint (𝕊 m) (sphereBasepoint m) ⟶
      underTopOfPoint (𝕊 n) (sphereBasepoint n)) :
    (UnderTopOfPoint.toContinuousMap f).IsCellular := sorry

/-- Under the source hypotheses `0 < m`, `0 < n`, and `n ≤ m`, every based map
`S^m → S^n` is cellular, available for typeclass search on its underlying continuous map. -/
instance basedMap_cellular_of_le_inst
    {m n : ℕ}
    [Fact (0 < m)] [Fact (0 < n)] [Fact (n ≤ m)]
    (f : underTopOfPoint (𝕊 m) (sphereBasepoint m) ⟶
      underTopOfPoint (𝕊 n) (sphereBasepoint n)) :
    (UnderTopOfPoint.toContinuousMap f).IsCellular :=
  basedMap_cellular_of_le ‹Fact (0 < m)›.1 ‹Fact (0 < n)›.1 ‹Fact (n ≤ m)›.1 f
