import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_34_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_59_13
import StacksProject_2024.stacks_project.Chap15.PrincipalIdeal
import StacksProject_2024.stacks_project.Chap15.Remark_15_92_11
import StacksProject_2024.stacks_project.Chap15.Situation_15_92_15
import StacksProject_2024.stacks_project.Chap15.Remark_15_94_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open scoped PrincipalIdeal PrincipalTateModule

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

private abbrev H (p : ℤ) :
    DerivedCategory (ModuleCat.{u} A) ⥤ ModuleCat.{u} A :=
  DerivedCategory.homologyFunctor (ModuleCat.{u} A) p

private abbrev single0 :
    ModuleCat.{u} A ⥤ DerivedCategory (ModuleCat.{u} A) :=
  DerivedCategory.singleFunctor (ModuleCat.{u} A) (0 : ℤ)

/- Domain-style sampling for Lemma `15.94.6`.
- primary domain: comparison of Milnor short exact sequences for principal derived completion in
  `DerivedCategory (ModuleCat A)`;
- sampled owner declarations:
  `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `CategoryTheory.ShortComplex.Hom`,
  `DerivedCategory.derivedCompletionOf`,
  `principalPowerQuotientTower`,
  `principalPowerTorsionTower`;
- best owner abstraction: the rows and columns of the textbook diagram should be expressed by the
  canonical owners `ShortComplex`, `ShortComplex.Hom`, and `CommSq`, while the quotient, torsion,
  and Koszul towers are reused directly from the earlier chapter owners instead of being recopied
  into a local diagram package;
- primitive vs. derived:
  primitive data are the four short complexes, the row morphism between the top and middle rows,
  and the bottom comparison isomorphism between the two `R^1 lim` terms;
  derived API is the short exactness of those short complexes and the remaining bottom
  commutative square.

Source/core/bridge triage:
- `source-facing`: the existence of the comparison diagram in Lemma `15.94.6`;
- `core/canonical`: `ShortComplex`, `ShortComplex.Hom`, `CommSq`,
  `CategoryTheory.derivedLimit_cohomology_shortExact`, `DerivedCategory.derivedCompletionOf`,
  `principalPowerQuotientTower`, and `principalPowerTorsionTower`;
- `bridge/view`: the specific four-row-and-column comparison assembling those owner constructions in
  the principal one-generator case. -/

variable (f : A)

local notation "I" => ((f) : Ideal A)
local notation "hI" => principalIdeal_fg f

private abbrev principalTower (f : A) (K : DerivedCategory (ModuleCat.{u} A)) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  derivedCompletionKoszulPowersDerivedInverseSystem (fun _ : Fin 1 ↦ f) ⋙
    derivedTensorProduct K

private abbrev principalDerivedCompletionComparisonTopLeft
    (f : A) (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) : ModuleCat.{u} A :=
  limit (principalPowerQuotientTower f ((H p).obj K))

private abbrev principalDerivedCompletionComparisonTopMiddle
    (f : A) (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) : ModuleCat.{u} A :=
  limit (principalTower f K ⋙ H p)

private abbrev principalDerivedCompletionComparisonMiddleLeft
    (f : A) (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) : ModuleCat.{u} A :=
  (H 0).obj
    (DerivedCategory.derivedCompletionOf
      ((f) : Ideal A)
      (principalIdeal_fg f)
      ((single0).obj ((H p).obj K)))

private abbrev principalDerivedCompletionComparisonMiddleMiddle
    (f : A) (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) : ModuleCat.{u} A :=
  (H p).obj
    (DerivedCategory.derivedCompletionOf ((f) : Ideal A) (principalIdeal_fg f) K)

private abbrev principalDerivedCompletionComparisonRight
    (f : A) (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) : ModuleCat.{u} A :=
  T[f] ((H (p + 1)).obj K)

private abbrev principalDerivedCompletionComparisonBottomLeft
    (f : A) (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) : ModuleCat.{u} A :=
  firstDerivedLimit (principalPowerTorsionTower f ((H p).obj K))

private abbrev principalDerivedCompletionComparisonBottomMiddle
    (f : A) (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) : ModuleCat.{u} A :=
  firstDerivedLimit (principalTower f K ⋙ H (p - 1))

-- Proof sketch: the top row comes from the inverse-limit short exact sequences
-- `0 → H^p(K) / f^(n+1) H^p(K) → H^p(K_n) → H^{p+1}(K)[f^(n+1)] → 0` after taking `lim`. The
-- middle row is Example `15.94.5`, the middle column is the Milnor short exact sequence for the
-- principal Koszul tensor tower `(K_n)_n`, and the left column is the module-level Milnor short
-- exact sequence for `H^p(K)`. Applying these to `L = τ_{\le p} K` and comparing `L_n → K_n`
-- gives the commutative diagram and the bottom isomorphism.
/-- Lemma 15.94.6: for `K_n = K ⊗_A^{\mathbf L} (A \xrightarrow{f^(n+1)} A)` and every
`p : ℤ`, there is a comparison diagram whose top and middle rows and left and middle columns are
short exact `ShortComplex`es, whose top-to-middle comparison is a morphism of short complexes with
right component the identity on `T[f] (H^{p+1}(K))`, and whose bottom horizontal map identifies the
two `R^1 lim` terms. The principal derived completion terms are written with the chapter owner
notation `K^∧[(f), principalIdeal_fg f]`. -/
theorem principalDerivedCompletion_cohomology_has_comparison_diagram
    (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) :
    let topLeft := principalDerivedCompletionComparisonTopLeft f K p
    let topMiddle := principalDerivedCompletionComparisonTopMiddle f K p
    let middleLeft := principalDerivedCompletionComparisonMiddleLeft f K p
    let middleMiddle := principalDerivedCompletionComparisonMiddleMiddle f K p
    let right := principalDerivedCompletionComparisonRight f K p
    let bottomLeft := principalDerivedCompletionComparisonBottomLeft f K p
    let bottomMiddle := principalDerivedCompletionComparisonBottomMiddle f K p
    ∃ (topRowLeft : topLeft ⟶ topMiddle)
      (topRowRight : topMiddle ⟶ right)
      (middleRowLeft : middleLeft ⟶ middleMiddle)
      (middleRowRight : middleMiddle ⟶ right)
      (leftColumnTop : topLeft ⟶ middleLeft)
      (leftColumnBottom : middleLeft ⟶ bottomLeft)
      (middleColumnTop : topMiddle ⟶ middleMiddle)
      (middleColumnBottom : middleMiddle ⟶ bottomMiddle)
      (topRowZero : topRowLeft ≫ topRowRight = 0)
      (middleRowZero : middleRowLeft ≫ middleRowRight = 0)
      (leftColumnZero : leftColumnTop ≫ leftColumnBottom = 0)
      (middleColumnZero : middleColumnTop ≫ middleColumnBottom = 0)
      (bottomIso : bottomLeft ≅ bottomMiddle),
      let topRow : ShortComplex (ModuleCat.{u} A) := ShortComplex.mk topRowLeft topRowRight topRowZero
      let middleRow : ShortComplex (ModuleCat.{u} A) := ShortComplex.mk middleRowLeft middleRowRight middleRowZero
      let leftColumn : ShortComplex (ModuleCat.{u} A) :=
        ShortComplex.mk leftColumnTop leftColumnBottom leftColumnZero
      let middleColumn : ShortComplex (ModuleCat.{u} A) :=
        ShortComplex.mk middleColumnTop middleColumnBottom middleColumnZero
      ∃ topToMiddle : topRow ⟶ middleRow,
        topRow.ShortExact ∧
          middleRow.ShortExact ∧
          leftColumn.ShortExact ∧
          middleColumn.ShortExact ∧
          topToMiddle.τ₁ = leftColumn.f ∧
          topToMiddle.τ₂ = middleColumn.f ∧
          topToMiddle.τ₃ = 𝟙 topRow.X₃ ∧
          CommSq middleRow.f leftColumn.g middleColumn.g bottomIso.hom := sorry

end
