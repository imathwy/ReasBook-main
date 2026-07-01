import Mathlib
import stacks_project.Chap12.Definition_12_24_5
import stacks_project.Chap12.Definition_12_24_9
import stacks_project.Chap19.Remark_19_13_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open FilteredComplex

noncomputable section

universe w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [LocallySmall 𝒜] [WellPowered 𝒜]
  [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜] [IsGrothendieckAbelian.{w} 𝒜]
  [HasDerivedCategory 𝒜]

local notation "FilteredComplex" => CategoryTheory.FilteredComplex 𝒜
local notation "AbFilteredComplex" => CategoryTheory.FilteredComplex AddCommGrpCat

-- Proof sketch: composition in the derived category is additive in the second factor, so
-- precomposition with `f` defines an additive homomorphism on morphism groups.
/-- Precomposition with a morphism in the first variable is additive on derived `Ext` groups. -/
theorem derivedExtGroupPrecomp_add
    (K : DerivedCategory 𝒜) {X Y : DerivedCategory 𝒜} (f : X ⟶ Y) (n : ℤ)
    (α β : Y ⟶ K⟦n⟧) :
    f ≫ (α + β) = f ≫ α + f ≫ β := sorry

/-- The map on derived `Ext` groups induced contravariantly by a morphism in the first variable.
-/
def derivedExtGroupPrecomp
    (K : DerivedCategory 𝒜) {X Y : DerivedCategory 𝒜} (f : X ⟶ Y) (n : ℤ) :
    derivedExtGroup Y K n ⟶ derivedExtGroup X K n :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk'
      (fun α ↦ f ≫ α)
      (derivedExtGroupPrecomp_add K f n)

/-- For every total degree, the groups `Ext^n(M / F^p M, K)` vanish for all sufficiently small
filtration indices `p`. -/
def EventualQuotientDerivedExtVanishesBelow
    (M : FilteredComplex) (K : DerivedCategory 𝒜) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ ⦃p : ℤ⦄, p ≤ p₀ →
    IsZero (derivedExtGroup (DerivedCategory.Q.obj (M.quotient p)) K n)

/-- For every total degree, the canonical maps `Ext^n(M / F^p M, K) → Ext^n(M, K)` are
isomorphisms for all sufficiently large filtration indices `p`. -/
def EventualQuotientDerivedExtStabilizesAbove
    (M : FilteredComplex) (K : DerivedCategory 𝒜) : Prop :=
  ∀ n : ℤ, ∃ p₁ : ℤ, ∀ ⦃p : ℤ⦄, p₁ ≤ p →
    IsIso (derivedExtGroupPrecomp K (DerivedCategory.Q.map (M.underlyingToQuotient p)) n)

/-- A filtered-complex model for the dual Ext spectral sequence
`E_1^{p,q} = Ext^{p + q}(gr^{-p} M, K)` attached to a filtered complex `M^•` and a derived object
`K`. -/
structure FilteredComplexSourceExtSpectralSequenceData
    (M : FilteredComplex) (K : DerivedCategory 𝒜) where
  /-- The filtered complex of abelian groups producing the spectral sequence. -/
  filteredHomComplex : AbFilteredComplex
  /-- The cohomological spectral sequence attached to the chosen filtered Hom complex. -/
  spectralSequence : CohomologicalSpectralSequence AddCommGrpCat 0
  /-- The spectral sequence is associated to the chosen filtered Hom complex. -/
  associated : IsAssociatedToFilteredComplex filteredHomComplex spectralSequence
  /-- The `E₁`-page identifies with the derived `Ext` groups of the shifted graded pieces
  `gr^{-p}(M^•)`. -/
  pageOneIso : ∀ p q : ℤ,
    (spectralSequence.page 1).X (p, q) ≅
      derivedExtGroup (DerivedCategory.Q.obj (M.gradedPiece (-p))) K (p + q)
  /-- The abutment cohomology of the filtered Hom complex identifies with `Ext^n(M, K)`. -/
  abutmentIso : ∀ n : ℤ,
    filteredHomComplex.underlying.homology n ≅
      derivedExtGroup (DerivedCategory.Q.obj (M.underlying)) K n
  /-- The eventual quotient-Ext vanishing and stabilization hypotheses force the spectral
  sequence to be bounded. -/
  bounded_of_eventualQuotientExt_control :
    EventualQuotientDerivedExtVanishesBelow M K →
      EventualQuotientDerivedExtStabilizesAbove M K →
      CohomologicalSpectralSequence.IsBounded spectralSequence
  /-- The same hypotheses force convergence of the associated filtered complex to its abutment
  cohomology. -/
  converges_of_eventualQuotientExt_control :
    EventualQuotientDerivedExtVanishesBelow M K →
      EventualQuotientDerivedExtStabilizesAbove M K →
      CategoryTheory.FilteredComplex.convergesToCohomology filteredHomComplex spectralSequence

-- Proof sketch: choose a K-injective complex `I^•` representing `K`, form the filtered complex
-- `Hom^•(M^•, I^•)` with filtration
-- `F^p Hom^•(M^•, I^•) = Hom^•(M^• / F^{-p + 1} M^•, I^•)`, and apply the filtered-complex
-- spectral sequence from Chapter 12. The `E₁`-page identifies with
-- `Ext^{p+q}(gr^{-p} M, K)`, while Lemma 12.24.13 turns the eventual vanishing and eventual
-- stabilization hypotheses on `Ext^n(M / F^p M, K)` into boundedness and convergence to
-- `Ext^{p+q}(M, K)`.
/-- Remark 19.13.10: for a Grothendieck abelian category `𝒜`, a filtered complex `M^•`, and an
object `K` of `D(𝒜)`, there is a spectral sequence in abelian groups with
`E₁^{p,q} = Ext^{p + q}(gr^{-p}(M^•), K)`; moreover, if `Ext^n(M / F^p M, K)` vanishes for
`p ≪ 0` and the canonical map `Ext^n(M / F^p M, K) → Ext^n(M, K)` is an isomorphism for
`p ≫ 0`, then this spectral sequence is bounded and converges to `Ext^{p + q}(M, K)`. In this
file, the chosen spectral sequence is packaged as
`FilteredComplexSourceExtSpectralSequenceData M K`. -/
theorem filteredComplexSourceExtSpectralSequence_exists
    (M : FilteredComplex) (K : DerivedCategory 𝒜) :
    Nonempty (FilteredComplexSourceExtSpectralSequenceData M K) := sorry

end CategoryTheory
