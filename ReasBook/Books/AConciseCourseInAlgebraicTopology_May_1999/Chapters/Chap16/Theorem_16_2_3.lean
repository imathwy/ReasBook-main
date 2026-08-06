import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Construction_16_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Construction_16_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Definition_16_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_2_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.CellularCWMap
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_3_4
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.CWComplex.Classical.Basic

open CategoryTheory Simplicial
open scoped SingularChains

noncomputable section

-- Semantic recall via `lean_leansearch`: Construction 16.2.1 already fixes the source-facing
-- owners `gammaRealization` and `gammaRealizationMap`, while `TopCat.toSSet` and `SSet.toTop`
-- remain the underlying canonical mathlib owners for the singular simplicial set and its
-- realization. Meanwhile,
-- `AlgebraicTopology.singularChainComplexFunctor`, `Topology.CWComplex`, and Chapter 13's
-- `cellularChainComplex` with explicit `CellularDifferentialFamily` data are the local owners for
-- the singular-chain and cellular-chain data used in this source-faithful comparison statement.

/-- A chosen CW structure on `Γ X` whose `n`-cells are indexed by the nondegenerate singular
`n`-simplices of `X`, and whose `(n + 1)`-cell frontiers are covered by the closed `n`-cells
indexed by the nondegenerate singular `n`-simplices of `X`. -/
structure GammaRealizationCWStructure (X : TopCat) where
  /-- The chosen CW-complex structure on `Γ X`. -/
  cwComplex : Topology.CWComplex (Set.univ : Set (gammaRealization X))
  /-- The chosen indexing of the `n`-cells of `Γ X` by the nondegenerate singular
  `n`-simplices of `X`. -/
  cellEquiv : ∀ n : ℕ, cwComplex.cell n ≃ nondegenerateSingularSimplex n X
  /-- The frontier of the `(n + 1)`-cell corresponding to `σ` is covered by closed `n`-cells
  indexed by nondegenerate singular `n`-simplices of `X`. -/
  attachingMap_subset_nondegenerateClosedCells :
    ∀ n : ℕ, ∀ σ : nondegenerateSingularSimplex (n + 1) X,
      ∃ I : Finset (nondegenerateSingularSimplex n X),
        cwComplex.map (n + 1) ((cellEquiv (n + 1)).symm σ) ''
            Metric.sphere (0 : Fin (n + 1) → ℝ) 1 ⊆
          ⋃ τ ∈ I, cwComplex.map n ((cellEquiv n).symm τ) '' Metric.closedBall (0 : Fin n → ℝ) 1

namespace GammaRealizationCWStructure

/-- A `GammaRealizationCWStructure X` provides the ambient `Topology.CWComplex` structure on
`Γ X`. -/
instance instCWComplex (X : TopCat) (Γ : GammaRealizationCWStructure X) :
    Topology.CWComplex (Set.univ : Set (gammaRealization X)) :=
  Γ.cwComplex

end GammaRealizationCWStructure

/-- Theorem 16.2.3 (1). The realization `Γ X` of the singular simplicial set of `X` admits a
CW-complex structure whose `n`-cells are indexed by the nondegenerate singular `n`-simplices of
`X`, and whose attaching data are compatible with the corresponding lower-dimensional singular
simplices. The existential witness `Γ` carries the chosen cell-indexing data, and this
source-facing existence statement is owned by
`GammaRealizationCWStructure X`. -/
theorem gammaRealization_existsCWComplexWithNondegenerateCells (X : TopCat) :
    ∃ Γ : GammaRealizationCWStructure X,
      (∀ n : ℕ, ∀ σ : nondegenerateSingularSimplex (n + 1) X,
        ∃ I : Finset (nondegenerateSingularSimplex n X),
          Γ.cwComplex.map (n + 1) ((Γ.cellEquiv (n + 1)).symm σ) ''
              Metric.sphere (0 : Fin (n + 1) → ℝ) 1 ⊆
            ⋃ τ ∈ I,
              Γ.cwComplex.map n ((Γ.cellEquiv n).symm τ) '' Metric.closedBall (0 : Fin n → ℝ) 1) :=
  sorry

/-- The degree-`n` cellular chain module attached to the chosen CW structure `hΓ` on `Γ X`. -/
abbrev gammaRealizationCellularChainModule
    {X : TopCat} (hΓ : Topology.CWComplex (Set.univ : Set (gammaRealization X))) (n : ℕ) :
    ModuleCat ℤ :=
  ModuleCat.of ℤ (FreeAbelianGroup (hΓ.cell n))

/-- The chosen Chapter 13 cellular differential data on the realization `Γ X` attached to a
chosen realization-compatible CW structure. -/
abbrev gammaRealizationCellularDifferentialFamily
    {X : TopCat} (Γ : GammaRealizationCWStructure X) : Type :=
  letI : Topology.CWComplex (Set.univ : Set (gammaRealization X)) := Γ.cwComplex
  CellularDifferentialFamily (gammaRealization X)

/-- The chosen Chapter 13 cellular chain complex of `Γ X` attached to a realization-compatible CW
structure and chosen cellular differential data. -/
abbrev gammaRealizationCellularChainComplex
    {X : TopCat} (Γ : GammaRealizationCWStructure X)
    (data : gammaRealizationCellularDifferentialFamily Γ) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  letI : Topology.CWComplex (Set.univ : Set (gammaRealization X)) := Γ.cwComplex
  cellularChainComplex (gammaRealization X) data

/-- The module morphism induced by `hcell n` from the free Abelian group on the `n`-cells of `hΓ`
to the singular chain group generated by the nondegenerate singular `n`-simplices of `X`. -/
abbrev gammaRealizationCellularToSingularChainMap
    (X : TopCat) (hΓ : Topology.CWComplex (Set.univ : Set (gammaRealization X)))
    (hcell : ∀ n : ℕ, hΓ.cell n ≃ nondegenerateSingularSimplex n X) (n : ℕ) :
    gammaRealizationCellularChainModule hΓ n ⟶ ModuleCat.of ℤ (singularChainGroup n X) :=
  ModuleCat.ofHom ((FreeAbelianGroup.map (hcell n)).toIntLinearMap)

/-- For the chosen CW structure `hΓ` on `Γ X` with chosen cellular differential data `data`, the
degree-`n` object of the cellular chain complex is canonically the free Abelian group on the
nondegenerate singular `n`-simplices of `X` via `hcell`. -/
abbrev gammaRealizationCellularChainComplex_degreeIso
    {X : TopCat} (Γ : GammaRealizationCWStructure X)
    (data : gammaRealizationCellularDifferentialFamily Γ) (n : ℕ) :
    (gammaRealizationCellularChainComplex Γ data).X n ≅
      ModuleCat.of ℤ (FreeAbelianGroup (nondegenerateSingularSimplex n X)) :=
  ((FreeAbelianGroup.equivOfEquiv (Γ.cellEquiv n)).toIntLinearEquiv).toModuleIso

/-- A chain complex `cellularChains` computes the cellular chains of `Γ X` relative to `hΓ` and
`hcell` when it comes with explicit degreewise identifications
`e n : cellularChains.X n ≅ gammaRealizationCellularChainModule hΓ n` and an explicit chain
complex isomorphism `Φ : cellularChains ≅ C_*(X)`, together with
degreewise identifications of the singular chain groups with the objects of that singular chain
complex, such that the degree-`n` component `Φ.hom.f n` is exactly the map induced by `hcell n`
after transport along those identifications. -/
def IsGammaRealizationCellularChainComparison
    (X : TopCat) (hΓ : Topology.CWComplex (Set.univ : Set (gammaRealization X)))
    (hcell : ∀ n : ℕ, hΓ.cell n ≃ nondegenerateSingularSimplex n X)
    (cellularChains : ChainComplex (ModuleCat ℤ) ℕ) : Prop :=
  ∃ e : ∀ n : ℕ, cellularChains.X n ≅ gammaRealizationCellularChainModule hΓ n,
    ∃ s : ∀ n : ℕ,
        ModuleCat.of ℤ (singularChainGroup n X) ≅ (C_*(X)).X n,
      ∃ Φ : cellularChains ≅ C_*(X),
        ∀ n : ℕ,
          (e n).hom ≫ gammaRealizationCellularToSingularChainMap X hΓ hcell n ≫ (s n).hom =
            Φ.hom.f n

/-- Unpacking `IsGammaRealizationCellularChainComparison` gives the degreewise cellular-chain
group comparison for `Γ X`, together with the coherent singular-chain and chain-complex
comparison data that witness the same comparison package. -/
theorem IsGammaRealizationCellularChainComparison.cellGroupIso
    {X : TopCat} {hΓ : Topology.CWComplex (Set.univ : Set (gammaRealization X))}
    {hcell : ∀ n : ℕ, hΓ.cell n ≃ nondegenerateSingularSimplex n X}
    {cellularChains : ChainComplex (ModuleCat ℤ) ℕ}
    (hcomparison : IsGammaRealizationCellularChainComparison X hΓ hcell cellularChains) :
    ∃ e : ∀ n : ℕ, cellularChains.X n ≅ gammaRealizationCellularChainModule hΓ n,
      ∃ s : ∀ n : ℕ, ModuleCat.of ℤ (singularChainGroup n X) ≅ (C_*(X)).X n,
        ∃ Φ : cellularChains ≅ C_*(X),
          ∀ n : ℕ,
            (e n).hom ≫ gammaRealizationCellularToSingularChainMap X hΓ hcell n ≫ (s n).hom =
              Φ.hom.f n :=
  hcomparison

/-- Unpacking `IsGammaRealizationCellularChainComparison` also gives the degreewise comparison
between the singular chain groups of `X` and the objects of its integral singular chain complex,
together with the coherent cellular and chain-complex comparison data. -/
theorem IsGammaRealizationCellularChainComparison.singularChainDegreeIso
    {X : TopCat} {hΓ : Topology.CWComplex (Set.univ : Set (gammaRealization X))}
    {hcell : ∀ n : ℕ, hΓ.cell n ≃ nondegenerateSingularSimplex n X}
    {cellularChains : ChainComplex (ModuleCat ℤ) ℕ}
    (hcomparison : IsGammaRealizationCellularChainComparison X hΓ hcell cellularChains) :
    ∃ s : ∀ n : ℕ, ModuleCat.of ℤ (singularChainGroup n X) ≅ (C_*(X)).X n,
      ∃ e : ∀ n : ℕ, cellularChains.X n ≅ gammaRealizationCellularChainModule hΓ n,
        ∃ Φ : cellularChains ≅ C_*(X),
          ∀ n : ℕ,
            (e n).hom ≫ gammaRealizationCellularToSingularChainMap X hΓ hcell n ≫ (s n).hom =
              Φ.hom.f n := by
  rcases hcomparison with ⟨e, s, Φ, hΦ⟩
  exact ⟨s, e, Φ, hΦ⟩

/-- Unpacking `IsGammaRealizationCellularChainComparison` also gives a chain-complex comparison
with the integral singular chains of `X`, together with the coherent degreewise comparison data.
-/
theorem IsGammaRealizationCellularChainComparison.singularChainIso
    {X : TopCat} {hΓ : Topology.CWComplex (Set.univ : Set (gammaRealization X))}
    {hcell : ∀ n : ℕ, hΓ.cell n ≃ nondegenerateSingularSimplex n X}
    {cellularChains : ChainComplex (ModuleCat ℤ) ℕ}
    (hcomparison : IsGammaRealizationCellularChainComparison X hΓ hcell cellularChains) :
    ∃ Φ : cellularChains ≅ C_*(X),
      ∃ e : ∀ n : ℕ, cellularChains.X n ≅ gammaRealizationCellularChainModule hΓ n,
        ∃ s : ∀ n : ℕ, ModuleCat.of ℤ (singularChainGroup n X) ≅ (C_*(X)).X n,
          ∀ n : ℕ,
            (e n).hom ≫ gammaRealizationCellularToSingularChainMap X hΓ hcell n ≫ (s n).hom =
              Φ.hom.f n := by
  rcases hcomparison with ⟨e, s, Φ, hΦ⟩
  exact ⟨Φ, e, s, hΦ⟩

/-- A chain map between the chosen cellular chain complexes of `Γ X` and `Γ Y` is realization
induced when it is induced by the actual realization map `Γ f` in the Chapter 13 sense, and
`Γ f` is cellular for the selected CW structures. -/
def IsGammaRealizationInducedCellularChainMap
    {X Y : TopCat}
    (ΓX : GammaRealizationCWStructure X)
    (dataX : gammaRealizationCellularDifferentialFamily ΓX)
    (ΓY : GammaRealizationCWStructure Y)
    (dataY : gammaRealizationCellularDifferentialFamily ΓY)
    (f : X ⟶ Y)
    (φ :
      gammaRealizationCellularChainComplex ΓX dataX ⟶
        gammaRealizationCellularChainComplex ΓY dataY) : Prop :=
  letI : Topology.CWComplex (Set.univ : Set (gammaRealization X)) := ΓX.cwComplex
  letI : Topology.CWComplex (Set.univ : Set (gammaRealization Y)) := ΓY.cwComplex
  ∃ hf : IsCellularCWMap (gammaRealizationMap f),
    IsCellularChainMapInducedByQuotients (gammaRealizationMap f) hf dataX dataY φ

/-- Chosen comparison data exhibiting the cellular chain complex of the realization `Γ X` as the
integral singular chain complex of `X`. -/
structure GammaRealizationCellularChainComparison (X : TopCat) where
  /-- The chosen realization-compatible CW structure on `Γ X`. -/
  cwStructure : GammaRealizationCWStructure X
  /-- The chosen Chapter 13 cellular differential data on `Γ X`. -/
  data : gammaRealizationCellularDifferentialFamily cwStructure
  /-- The degree-`n` object of the cellular chain complex identifies with the free Abelian group
  on the `n`-cells of the chosen CW structure. -/
  cellGroupIso :
    ∀ n : ℕ,
      (gammaRealizationCellularChainComplex cwStructure data).X n ≅
        gammaRealizationCellularChainModule cwStructure.cwComplex n
  /-- The singular chain group on nondegenerate simplices identifies with degree `n` of the
  integral singular chain complex of `X`. -/
  singularDegreeIso :
    ∀ n : ℕ,
      ModuleCat.of ℤ (singularChainGroup n X) ≅ (C_*(X)).X n
  /-- The resulting cellular chain complex is identified with the integral singular chain complex
  of `X`. -/
  singularChainIso :
    gammaRealizationCellularChainComplex cwStructure data ≅ C_*(X)
  /-- The degree-`n` component of `singularChainIso` is the map induced by the chosen indexing of
  the `n`-cells by nondegenerate singular `n`-simplices, after transport along the chosen
  degreewise identifications. -/
  comm :
    ∀ n : ℕ,
      (cellGroupIso n).hom ≫
          gammaRealizationCellularToSingularChainMap X cwStructure.cwComplex
            cwStructure.cellEquiv n ≫
          (singularDegreeIso n).hom =
        singularChainIso.hom.f n

/-- The chosen cellular chain complex of `Γ X` attached to a comparison package. -/
abbrev gammaRealizationCellularChains
    {X : TopCat} (comparison : GammaRealizationCellularChainComparison X) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  gammaRealizationCellularChainComplex comparison.cwStructure comparison.data

/-- A chosen family of singular-CW comparisons is natural when it comes with a chosen
functorial family of cellular-chain maps induced by the realization maps `Γ f` in the Chapter 13
sense and intertwining the comparison isomorphisms with the functorial singular-chain maps
induced by maps of spaces. -/
def GammaRealizationCellularChainComparison.IsNatural
    (comparison : ∀ X : TopCat, GammaRealizationCellularChainComparison X)
    (map :
      ∀ {X Y : TopCat}, (X ⟶ Y) →
        (gammaRealizationCellularChains (comparison X) ⟶
          gammaRealizationCellularChains (comparison Y))) : Prop :=
  (∀ X : TopCat, map (𝟙 X) = 𝟙 (gammaRealizationCellularChains (comparison X))) ∧
    (∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g) ∧
    (∀ {X Y : TopCat} (f : X ⟶ Y),
      IsGammaRealizationInducedCellularChainMap
        (comparison X).cwStructure (comparison X).data
        (comparison Y).cwStructure (comparison Y).data f (map f)) ∧
    ∀ {X Y : TopCat} (f : X ⟶ Y),
      map f ≫ (comparison Y).singularChainIso.hom =
        (comparison X).singularChainIso.hom ≫ integralTopologicalSingularChains.map f

/-- Unpacking a chosen singular-CW comparison recovers the degreewise and chain-level comparison
data expressed by `IsGammaRealizationCellularChainComparison`. -/
theorem GammaRealizationCellularChainComparison.toIsGammaRealizationCellularChainComparison
    {X : TopCat} (comparison : GammaRealizationCellularChainComparison X) :
    IsGammaRealizationCellularChainComparison
      X comparison.cwStructure.cwComplex comparison.cwStructure.cellEquiv
      (gammaRealizationCellularChains comparison) := sorry

/-- Theorem 16.2.3 (2). There is a chosen singular-CW comparison for every topological space
`X`, together with a chosen functorial family of cellular-chain maps induced by the realization
maps `Γ f`, and these data identify the resulting cellular chain complexes naturally with the
integral singular chain complexes of the spaces `X`. -/
theorem gammaRealizationCellularChainComplexIsoSingular
    :
    ∃ comparison : ∀ X : TopCat, GammaRealizationCellularChainComparison X,
      ∃ map :
        ∀ {X Y : TopCat}, (X ⟶ Y) →
          (gammaRealizationCellularChains (comparison X) ⟶
            gammaRealizationCellularChains (comparison Y)),
        GammaRealizationCellularChainComparison.IsNatural comparison map :=
  sorry
