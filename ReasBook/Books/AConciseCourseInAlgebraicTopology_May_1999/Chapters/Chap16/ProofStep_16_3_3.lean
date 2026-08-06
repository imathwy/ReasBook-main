import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Definition_16_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Theorem_16_2_3
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

noncomputable section

universe u

open CategoryTheory Simplicial
open Topology
open Topology.CWComplex

-- Semantic recall via `lean_leansearch`: `CWComplex.iUnion_openCell_eq_skeleton`,
-- `CWComplex.iUnion_openCell_eq_skeletonLT`, and `RelCWComplex.disjoint_skeleton_openCell`
-- identify the canonical skeletal-filtration API for a chosen CW structure. For realizations
-- `Γ X`, Theorem 16.2.3 already packages the source-facing CW structure and simplex-indexing data
-- as `GammaRealizationCWStructure X`. The realization functor itself supplies the canonical maps
-- `Δ^n → Γ X` attached to singular `n`-simplices, so this file keeps the textbook stratum
-- statements as thin bridges between those simplex maps and the chosen CW owner.

/-- The stage `Γ^(n - 1) X` of the skeletal filtration of a chosen CW structure on `Γ X`,
formalized by the canonical strict skeleton `skeletonLT`. -/
abbrev gammaRealizationSkeletalFiltrationLT (X : TopCat.{u}) (Γ : GammaRealizationCWStructure X)
    (n : ℕ) : Set (gammaRealization X) :=
  let _ : Topology.CWComplex (Set.univ : Set (gammaRealization X)) :=
    GammaRealizationCWStructure.instCWComplex X Γ
  skeletonLT (Set.univ : Set (gammaRealization X)) n

/-- The stage `Γ^n X` of the skeletal filtration of a chosen CW structure on `Γ X`,
formalized by the canonical skeleton `skeleton`. -/
abbrev gammaRealizationSkeletalFiltration (X : TopCat.{u}) (Γ : GammaRealizationCWStructure X)
    (n : ℕ) : Set (gammaRealization X) :=
  let _ : Topology.CWComplex (Set.univ : Set (gammaRealization X)) :=
    GammaRealizationCWStructure.instCWComplex X Γ
  skeleton (Set.univ : Set (gammaRealization X)) n

/-- The `n`-th skeletal stratum `Γ^n X \ Γ^(n - 1) X` of a chosen CW structure on `Γ X`. -/
def gammaRealizationNthSkeletalStratum (X : TopCat.{u}) (Γ : GammaRealizationCWStructure X)
    (n : ℕ) : Set (gammaRealization X) :=
  gammaRealizationSkeletalFiltration X Γ n \ gammaRealizationSkeletalFiltrationLT X Γ n

/-- The open `n`-cell in `Γ X` corresponding, via `Γ.cellEquiv n`, to a nondegenerate singular
`n`-simplex `σ`. This is the source-facing bridge to the canonical owner
`Topology.CWComplex.openCell`, hence the CW-complex formalization of the factor
`σ × int Δ^n`. -/
abbrev gammaRealizationOpenCellOfNondegenerateSimplex
    (X : TopCat.{u}) (Γ : GammaRealizationCWStructure X) (n : ℕ)
    (σ : nondegenerateSingularSimplex n X) : Set (gammaRealization X) :=
  let _ : Topology.CWComplex (Set.univ : Set (gammaRealization X)) :=
    GammaRealizationCWStructure.instCWComplex X Γ
  let j : cell (Set.univ : Set (gammaRealization X)) n := (Γ.cellEquiv n).symm σ
  openCell n j

/-- The interior `int Δ^n`, formalized as the points of `Δ^n` with strictly positive
barycentric coordinates. -/
def standardSimplexInterior (n : ℕ) : Set (Δ^n) :=
  { x | ∀ i, 0 < x i }

/-- The canonical map `Δ^n → Γ X` attached to a singular `n`-simplex of `X` by geometric
realization. -/
noncomputable abbrev gammaRealizationSimplexMap
    (X : TopCat.{u}) (n : ℕ) (σ : nondegenerateSingularSimplex n X) :
    C(Δ^n, gammaRealization X) :=
  (SSet.toTop.map (SSet.yonedaEquiv.symm σ.1)).hom.comp
    ⟨(SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm,
      (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm.continuous_toFun⟩

/-- The image in `Γ X` of a pair `(σ, x)` consisting of a nondegenerate singular `n`-simplex
and a point of `int Δ^n`. -/
def gammaRealizationInteriorPointOfNondegenerateSimplex
    (X : TopCat.{u}) (n : ℕ) :
    nondegenerateSingularSimplex n X × { x : Δ^n // x ∈ standardSimplexInterior n } →
      gammaRealization X :=
  fun p ↦ gammaRealizationSimplexMap X n p.1 p.2.1

/-- The open `n`-cell indexed by `σ` is the image of the corresponding `int Δ^n` under the
canonical realization map of `σ`. -/
theorem gammaRealizationOpenCellOfNondegenerateSimplex_eq_range_standardSimplexInterior
    (X : TopCat.{u}) (Γ : GammaRealizationCWStructure X)
    (n : ℕ) (σ : nondegenerateSingularSimplex n X) :
    gammaRealizationOpenCellOfNondegenerateSimplex X Γ n σ =
      Set.range (fun x : { x : Δ^n // x ∈ standardSimplexInterior n } ↦
        gammaRealizationInteriorPointOfNondegenerateSimplex X n ⟨σ, x⟩) := sorry

/-- The `n`-th skeletal stratum is exactly the union of the open `n`-cells indexed by the
nondegenerate singular `n`-simplices of `X`. -/
theorem gammaRealizationNthSkeletalStratum_eq_iUnion_openCellOfNondegenerateSimplex
    (X : TopCat.{u}) (Γ : GammaRealizationCWStructure X) (n : ℕ) :
    gammaRealizationNthSkeletalStratum X Γ n =
      ⋃ σ : nondegenerateSingularSimplex n X,
        gammaRealizationOpenCellOfNondegenerateSimplex X Γ n σ := sorry

/-- Proof step 16.3.3. For a chosen CW structure `Γ` on `Γ X` whose `n`-cells are indexed by the
nondegenerate singular `n`-simplices of `X`, the `n`-th skeletal stratum is the image of the
pairs `(σ, x)` with `σ : nondegenerateSingularSimplex n X` and `x ∈ int Δ^n` under the
canonical realization map of `σ`. This is the chapter-local
formalization of `(Γ X)^n \ (Γ X)^(n - 1)` as nondegenerate `n`-simplices `× int Δ^n`. -/
theorem gammaRealizationNthSkeletalStratum_eq_range_nondegenerateSimplexProdInterior
    (X : TopCat.{u}) (Γ : GammaRealizationCWStructure X) (n : ℕ) :
    gammaRealizationNthSkeletalStratum X Γ n =
      Set.range (gammaRealizationInteriorPointOfNondegenerateSimplex X n) := sorry
