import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable {ΓX : Type u} [CommRing ΓX]
variable {A : Type u} [CommRing A]
variable {DSh : Type u} [Category DSh]

/-- A packaged commutative diagram with exact rows and columns of the shape appearing in the
completion comparison for derived global sections. The object parameters are the usual completion,
the inverse limit of the cohomology of the completion tower, the Tate module term, the degree-zero
cohomology of the derived completion of the cohomology module, the cohomology of the completed
derived global sections object, and the two `R^1 lim` terms. -/
structure PrincipalCompletionComparisonDiagram
    (f : ΓX) (K : DerivedCategory (ModuleCat ΓX)) (p : ℤ) where
  /-- The usual `f`-adic completion of `H^p(K)`. -/
  completedCohomology : ModuleCat.{u} ΓX
  /-- The inverse limit `lim_n H^p(K_n)`. -/
  inverseLimitCohomology : ModuleCat.{u} ΓX
  /-- The `f`-adic Tate module `T_f(H^{p + 1}(K))`. -/
  tateModule : ModuleCat.{u} ΓX
  /-- The degree-zero cohomology of the derived completion of `H^p(K)`. -/
  derivedCompletionH0 : ModuleCat.{u} ΓX
  /-- The degree-`p` cohomology of the completed derived object. -/
  completedDerivedCohomology : ModuleCat.{u} ΓX
  /-- The `R^1 lim` term coming from the `f`-power torsion tower of `H^p(K)`. -/
  torsionR1Lim : ModuleCat.{u} ΓX
  /-- The `R^1 lim` term coming from the completion tower `K_n`. -/
  towerR1Lim : ModuleCat.{u} ΓX
  /-- The left map in the top short exact row. -/
  topRowLeft : completedCohomology ⟶ inverseLimitCohomology
  /-- The right map in the top short exact row. -/
  topRowRight : inverseLimitCohomology ⟶ tateModule
  /-- The left map in the middle short exact row. -/
  middleRowLeft : derivedCompletionH0 ⟶ completedDerivedCohomology
  /-- The right map in the middle short exact row. -/
  middleRowRight : completedDerivedCohomology ⟶ tateModule
  /-- The top map in the left short exact column. -/
  leftColumnTop : completedCohomology ⟶ derivedCompletionH0
  /-- The bottom map in the left short exact column. -/
  leftColumnBottom : derivedCompletionH0 ⟶ torsionR1Lim
  /-- The top map in the middle short exact column. -/
  middleColumnTop : inverseLimitCohomology ⟶ completedDerivedCohomology
  /-- The bottom map in the middle short exact column. -/
  middleColumnBottom : completedDerivedCohomology ⟶ towerR1Lim
  /-- The bottom horizontal comparison is an isomorphism between the two `R^1 lim` terms. -/
  bottomIso : torsionR1Lim ≅ towerR1Lim
  /-- The top row is a complex. -/
  topRowZero : topRowLeft ≫ topRowRight = 0
  /-- The middle row is a complex. -/
  middleRowZero : middleRowLeft ≫ middleRowRight = 0
  /-- The left column is a complex. -/
  leftColumnZero : leftColumnTop ≫ leftColumnBottom = 0
  /-- The middle column is a complex. -/
  middleColumnZero : middleColumnTop ≫ middleColumnBottom = 0
  /-- The top row is short exact. -/
  topRowShortExact : (ShortComplex.mk topRowLeft topRowRight topRowZero).ShortExact
  /-- The middle row is short exact. -/
  middleRowShortExact : (ShortComplex.mk middleRowLeft middleRowRight middleRowZero).ShortExact
  /-- The left column is short exact. -/
  leftColumnShortExact : (ShortComplex.mk leftColumnTop leftColumnBottom leftColumnZero).ShortExact
  /-- The middle column is short exact. -/
  middleColumnShortExact :
      (ShortComplex.mk middleColumnTop middleColumnBottom middleColumnZero).ShortExact
  /-- The upper-left square commutes. -/
  upperLeftComm : topRowLeft ≫ middleColumnTop = leftColumnTop ≫ middleRowLeft
  /-- The upper-right square commutes. -/
  upperRightComm : topRowRight = middleColumnTop ≫ middleRowRight
  /-- The lower-left square commutes after identifying the two `R^1 lim` terms. -/
  lowerLeftComm : middleRowLeft ≫ middleColumnBottom = leftColumnBottom ≫ bottomIso.hom

-- Proof sketch: apply the principal completion comparison on the derived global-sections side to
-- `RΓ(X, E)` and to the image of `f` under `A → Γ(X, \mathcal O_X)`. This is the formal
-- translation of the Stacks Project argument reducing the sheaf statement to the algebraic
-- completion diagram for derived global sections.
/-- Lemma 20.39.1: let `(X, \mathcal O_X)` be a ringed space, let `A → Γ(X, \mathcal O_X)` be a
ring map, let `f ∈ A`, and let `E ∈ D(\mathcal O_X)`. Formalized on the derived-global-sections
side, for every `p : ℤ` there is a canonical commutative diagram with exact rows and columns whose
top row is
`0 → \widehat{H^p(X, E)} → \varprojlim_n H^p(X, E_n) → T_f(H^{p + 1}(X, E)) → 0`
and whose middle row is
`0 → H^0(H^p(X, E)^∧) → H^p(X, E^∧) → T_f(H^{p + 1}(X, E)) → 0`. -/
theorem derivedGlobalSections_principalCompletion_has_comparison_diagram
    (RGamma : DSh ⥤ DerivedCategory (ModuleCat ΓX))
    (α : A →+* ΓX) (f : A) (E : DSh) (p : ℤ) :
    Nonempty (PrincipalCompletionComparisonDiagram (α f) (RGamma.obj E) p) := sorry

-- Proof sketch: the hypothesis identifies the derived global sections of the completed object with
-- the chosen derived completion object. Applying degree-`p` homology yields the comparison of
-- cohomology modules.
/-- If the derived global sections of a completed object are identified with a chosen derived
completion object, then their degree-`p` cohomology modules are canonically isomorphic. -/
theorem derivedGlobalSections_completion_cohomology_iso
    (RGamma : DSh ⥤ DerivedCategory (ModuleCat ΓX))
    (EHat : DSh)
    (completedRGamma : DerivedCategory (ModuleCat ΓX)) (p : ℤ)
    (hEHat : IsIsomorphic (RGamma.obj EHat) completedRGamma) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor (ModuleCat ΓX) p).obj (RGamma.obj EHat))
      ((DerivedCategory.homologyFunctor (ModuleCat ΓX) p).obj completedRGamma) := sorry

end

end AlgebraicGeometry.RingedSpace
