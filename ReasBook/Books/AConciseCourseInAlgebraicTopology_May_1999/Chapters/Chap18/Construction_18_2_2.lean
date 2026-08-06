import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Homology.Opposite
import Mathlib.CategoryTheory.Abelian.Ext
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Theorem_16_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Definition_17_3_2

open CategoryTheory
open scoped SingularChains

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` surfaced general cochain-complex `Hom` owners but no
-- dedicated singular-cohomology owner beyond `ChainComplex.linearYonedaObj`. Local Chapter 16
-- precedent packages the singular-CW approximation comparison by
-- `IsGammaRealizationCellularChainComparison`, so clause (2) stays quantified over that explicit
-- source-faithful comparison data rather than an arbitrary cochain isomorphism.

/-- Construction 18.2.2 (1). For a space `X` and coefficient ring `R`, the singular cochains of
`X` are the cochain complex `Hom(C_*(X; R), R)`, realized as the canonical `linearYonedaObj` of
the singular chain complex of `X` with coefficients in `R`. -/
abbrev singularCochainComplex (R : Type u) [CommRing R] (X : TopCat.{u}) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.linearYonedaObj
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (ModuleCat.of.{u} R R)).obj X)
    R
    (ModuleCat.of.{u} R R)

/-- Degree `n` of `singularCochainComplex R X` is the `R`-module of `R`-linear maps from the
degree-`n` singular chain module of `X` to `R`. -/
theorem singularCochainComplex_X (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    (singularCochainComplex R X).X n =
      ModuleCat.of.{u} R
        ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
            (ModuleCat.of.{u} R R)).obj X).X n ⟶ ModuleCat.of.{u} R R) :=
  by
    change
      (((CategoryTheory.linearYoneda R (ModuleCat.{u} R)).obj (ModuleCat.of.{u} R R)).obj
          (Opposite.op
            ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
                (ModuleCat.of.{u} R R)).obj X).X n))) =
        ModuleCat.of.{u} R
          ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
              (ModuleCat.of.{u} R R)).obj X).X n ⟶ ModuleCat.of.{u} R R)
    rfl

/-- Integral singular cohomology of `X`, computed as the homology of
`singularCochainComplex ℤ X`. -/
abbrev singularCohomology (X : TopCat) (n : ℕ) : ModuleCat ℤ :=
  (singularCochainComplex ℤ X).homology n

/-- Integral cohomology of a chain complex `cellularChains`, computed by dualizing it with
`linearYonedaObj` and taking cohomology. In Construction 18.2.2 (2), this is applied to a chain
complex linked to the singular CW approximation by
`IsGammaRealizationCellularChainComparison`. -/
abbrev cellularCohomology (cellularChains : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    ModuleCat ℤ :=
  (ChainComplex.linearYonedaObj cellularChains ℤ (ModuleCat.of ℤ ℤ)).homology n

/-- A chain-complex isomorphism `cellularChains ≅ C_*(X)` induces the corresponding comparison
between the dualized cochain complex of `cellularChains` and the singular cochain complex of `X`.
-/
noncomputable abbrev singularCochainComparisonIsoOfSingularChainIso
    {X : TopCat} {cellularChains : ChainComplex (ModuleCat ℤ) ℕ}
    (comparison : cellularChains ≅ C_*(X)) :
    cellularChains.linearYonedaObj ℤ (ModuleCat.of ℤ ℤ) ≅ singularCochainComplex ℤ X :=
  (HomologicalComplex.unopEquivalence (ModuleCat ℤ) (ComplexShape.down ℕ)).functor.mapIso
    (((CategoryTheory.Functor.mapHomologicalComplex
        (((CategoryTheory.linearYoneda ℤ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).rightOp)
        (ComplexShape.down ℕ)).mapIso comparison).symm.op)

/-- Applying `homology` in degree `n` to an explicit singular-chain comparison yields the induced
cohomology comparison. -/
noncomputable abbrev singularCohomologyComparisonIsoOfSingularChainIso
    {X : TopCat} {cellularChains : ChainComplex (ModuleCat ℤ) ℕ}
    (comparison : cellularChains ≅ C_*(X)) (n : ℕ) :
    cellularCohomology cellularChains n ≅ singularCohomology X n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n).mapIso
    (singularCochainComparisonIsoOfSingularChainIso comparison)

/-- For a chosen Chapter 16 singular-CW comparison package, dualizing the chosen singular-chain
comparison yields the corresponding cochain-complex comparison. -/
noncomputable abbrev singularCochainComparisonIso
    {X : TopCat} (comparison : GammaRealizationCellularChainComparison X) :
    (gammaRealizationCellularChains comparison).linearYonedaObj ℤ (ModuleCat.of ℤ ℤ) ≅
      singularCochainComplex ℤ X :=
  singularCochainComparisonIsoOfSingularChainIso comparison.singularChainIso

/-- `singularCochainComparisonIso` is the cochain comparison induced by the chosen
`comparison.singularChainIso`. -/
theorem singularCochainComparisonIso_def
    {X : TopCat} (comparison : GammaRealizationCellularChainComparison X) :
    singularCochainComparisonIso comparison =
      singularCochainComparisonIsoOfSingularChainIso comparison.singularChainIso :=
  rfl

/-- If `hcomparison` exhibits `cellularChains` as a singular-CW cellular chain model for `X`,
then some singular-chain comparison furnished by `hcomparison` induces a cochain-complex
comparison with the singular cochains of `X`. -/
theorem IsGammaRealizationCellularChainComparison.exists_singularCochainComparisonIso
    (X : TopCat) (hΓ : Topology.CWComplex (Set.univ : Set (gammaRealization X)))
    (hcell : ∀ n : ℕ, hΓ.cell n ≃ nondegenerateSingularSimplex n X)
    {cellularChains : ChainComplex (ModuleCat ℤ) ℕ}
    (hcomparison : IsGammaRealizationCellularChainComparison X hΓ hcell cellularChains) :
    ∃ Ψ : cellularChains.linearYonedaObj ℤ (ModuleCat.of ℤ ℤ) ≅ singularCochainComplex ℤ X,
      ∃ comparison : cellularChains ≅ C_*(X),
        Ψ = singularCochainComparisonIsoOfSingularChainIso comparison := by
  rcases IsGammaRealizationCellularChainComparison.singularChainIso hcomparison with
    ⟨comparison, -, -, -⟩
  exact ⟨singularCochainComparisonIsoOfSingularChainIso comparison, comparison, rfl⟩

/-- For a chosen Chapter 16 singular-CW comparison package, applying homology in degree `n` to
the dualized singular-chain comparison yields the corresponding cohomology comparison. -/
noncomputable abbrev singularCohomologyComparisonIso
    {X : TopCat} (comparison : GammaRealizationCellularChainComparison X) (n : ℕ) :
    cellularCohomology (gammaRealizationCellularChains comparison) n ≅ singularCohomology X n :=
  singularCohomologyComparisonIsoOfSingularChainIso comparison.singularChainIso n

/-- Construction 18.2.2 (2). If `hΓ`, `hcell`, and `hcomparison` are the singular CW
approximation data from Theorem 16.2.3, then some singular-chain comparison furnished by
`hcomparison` induces a cohomology comparison identifying the cohomology of `cellularChains`
with the singular cohomology of `X`. -/
theorem IsGammaRealizationCellularChainComparison.exists_singularCohomologyComparisonIso
    (X : TopCat) (hΓ : Topology.CWComplex (Set.univ : Set (gammaRealization X)))
    (hcell : ∀ n : ℕ, hΓ.cell n ≃ nondegenerateSingularSimplex n X)
    {cellularChains : ChainComplex (ModuleCat ℤ) ℕ}
    (hcomparison : IsGammaRealizationCellularChainComparison X hΓ hcell cellularChains)
    (n : ℕ) :
    ∃ Ψ : cellularCohomology cellularChains n ≅ singularCohomology X n,
      ∃ comparison : cellularChains ≅ C_*(X),
        Ψ = singularCohomologyComparisonIsoOfSingularChainIso comparison n := by
  rcases IsGammaRealizationCellularChainComparison.singularChainIso hcomparison with
    ⟨comparison, -, -, -⟩
  exact ⟨singularCohomologyComparisonIsoOfSingularChainIso comparison n, comparison, rfl⟩

/-- `singularCohomologyComparisonIso` is the degree-`n` homology isomorphism induced by
`singularCochainComparisonIso`. -/
theorem singularCohomologyComparisonIso_def
    {X : TopCat} (comparison : GammaRealizationCellularChainComparison X) (n : ℕ) :
    singularCohomologyComparisonIso comparison n =
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n).mapIso
        (singularCochainComparisonIso comparison) := by
  simp [singularCohomologyComparisonIso, singularCochainComparisonIso,
    singularCohomologyComparisonIsoOfSingularChainIso,
    singularCochainComparisonIsoOfSingularChainIso]
