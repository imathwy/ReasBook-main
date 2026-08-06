import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3

open CategoryTheory CategoryTheory.Limits
open scoped Manifold Topology

noncomputable section

-- Semantic recall: local Chapter 20 precedent already provides `ROrientedManifold`,
-- `rSingularHomology`, and `localTopHomologyMap` as the canonical orientability and top-homology
-- API. This corollary keeps the source-facing nonorientable vanishing statement and adds a
-- chosen-orientation companion for the orientable local-isomorphism statement.

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [ConnectedSpace M] [CompactSpace M]
variable [IsManifold I ⊤ M]
variable {n : ℕ} [Fact (Module.finrank ℝ E = n)]

/-- Corollary 20.3.5 (1): for a connected compact `n`-manifold `M`, if `M` is nonorientable,
then its top integral singular homology `H_n(M; ℤ)` vanishes. -/
theorem topIntegralSingularHomology_isZero_of_nonorientable
    (h_nonorientable : ¬ Nonempty (ROrientedManifold ℤ I n M)) :
    IsZero (rSingularHomology ℤ n (TopCat.of M)) := sorry

/-- Corollary 20.3.5 (2): for a connected compact `n`-manifold `M`, if `M` is orientable, then
for every `x : M` the localization map `H_n(M; ℤ) ⟶ H_n(M, M \ {x}; ℤ)` is an isomorphism. -/
theorem localTopHomologyMap_isIso_of_rOrientedManifold
    (o : ROrientedManifold ℤ I n M) (x : M) :
    IsIso (localTopHomologyMap ℤ n M x) := sorry

/-- Corollary 20.3.5 (2): for a connected compact `n`-manifold `M`, if `M` is orientable, then
for every `x : M` the localization map `H_n(M; ℤ) ⟶ H_n(M, M \ {x}; ℤ)` is an isomorphism. -/
theorem localTopHomologyMap_isIso_of_orientable
    (h_orientable : Nonempty (ROrientedManifold ℤ I n M)) (x : M) :
    IsIso (localTopHomologyMap ℤ n M x) := by
  rcases h_orientable with ⟨o⟩
  exact localTopHomologyMap_isIso_of_rOrientedManifold o x

end

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [ConnectedSpace M] [CompactSpace M]
variable {n : ℕ} [Fact (Module.finrank ℝ E = n)]
variable [IsManifold I ⊤ M]

/-- A `NonorientableManifold I n M` hypothesis recovers the vanishing conclusion of Corollary
20.3.5 (1). -/
instance topIntegralSingularHomology_isZero
    [NonorientableManifold I n M] :
    IsZero (rSingularHomology ℤ n (TopCat.of M)) := by
  exact topIntegralSingularHomology_isZero_of_nonorientable
    ‹NonorientableManifold I n M›.not_nonempty_rOrientedManifold

/-- An ambient integral orientation recovers the local-isomorphism conclusion of Corollary
20.3.5 (2). -/
instance localTopHomologyMap_isIso
    (x : M) [ROrientedManifold ℤ I n M] :
    IsIso (localTopHomologyMap ℤ n M x) :=
  localTopHomologyMap_isIso_of_rOrientedManifold
    ‹ROrientedManifold ℤ I n M› x

end
