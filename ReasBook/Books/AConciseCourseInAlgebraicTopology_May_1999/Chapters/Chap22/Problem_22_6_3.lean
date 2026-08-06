import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.Grp.Zero
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.ModTwoCohomologyTheory
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.ModTwoSingularCohomology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Theorem_16_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Problem_20_7_5

open CategoryTheory Limits
open scoped SingularChains

noncomputable section

/-- The Bockstein operation on mod-`2` singular cohomology induced by a short exact coefficient
sequence whose first and third terms are identified with `ZMod 2`. -/
abbrev modTwoBocksteinOperation
    (X : TopCat) (hX : ∀ n, Projective ((C_*(X)).X n))
    (zmodTwoFourTwo : ShortComplex (ModuleCat ℤ))
    (hX₁ : zmodTwoFourTwo.X₁ = ModuleCat.of ℤ (ZMod 2))
    (hX₃ : zmodTwoFourTwo.X₃ = ModuleCat.of ℤ (ZMod 2))
    (hShortExact : zmodTwoFourTwo.ShortExact) (n : ℕ) :
    modTwoSingularCohomology X n ⟶ modTwoSingularCohomology X (n + 1) :=
  coefficientCohomologyOperation
      (C_*(X)) (eqToIso hX₃.symm).hom n ≫
    bocksteinOperation (C_*(X)) hX zmodTwoFourTwo hShortExact n ≫
      coefficientCohomologyOperation
        (C_*(X)) (eqToIso hX₁).hom (n + 1)

private def zmodTwoToZmodFourFun (x : ZMod 2) : ZMod 4 :=
  (2 : ZMod 4) * ((x.val : ℕ) : ZMod 4)

private def zmodTwoToZmodFourAddHom : ZMod 2 →+ ZMod 4 where
  toFun := zmodTwoToZmodFourFun
  map_zero' := by decide
  map_add' := by
    intro x y
    fin_cases x <;> fin_cases y <;> decide

private def zmodTwoToZmodFour : ModuleCat.of ℤ (ZMod 2) ⟶ ModuleCat.of ℤ (ZMod 4) :=
  ModuleCat.ofHom zmodTwoToZmodFourAddHom.toIntLinearMap

private def zmodFourToZmodTwo : ModuleCat.of ℤ (ZMod 4) ⟶ ModuleCat.of ℤ (ZMod 2) :=
  ModuleCat.ofHom
    (ZMod.castHom (dvd_mul_right 2 2) (ZMod 2)).toIntLinearMap

private theorem zmodTwoFourTwo_comp_zero :
    zmodTwoToZmodFour ≫ zmodFourToZmodTwo = 0 := by
  ext x
  change ZMod 2 at x
  change
    ZMod.castHom (dvd_mul_right 2 2) (ZMod 2) (zmodTwoToZmodFourFun x) = 0
  fin_cases x
  · decide
  · decide

/-- The standard short coefficient sequence `ZMod 2 ⟶ ZMod 4 ⟶ ZMod 2`. -/
def standardModTwoCoefficientShortComplex : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk zmodTwoToZmodFour zmodFourToZmodTwo zmodTwoFourTwo_comp_zero

/-- The standard coefficient sequence `0 → ZMod 2 → ZMod 4 → ZMod 2 → 0` is short exact. -/
theorem standardModTwoCoefficientShortComplex_shortExact :
    standardModTwoCoefficientShortComplex.ShortExact := by
  have hExact :
      Function.Exact zmodTwoToZmodFour zmodFourToZmodTwo := by
    intro x
    change ZMod 4 at x
    change
      (ZMod.castHom (dvd_mul_right 2 2) (ZMod 2) x = 0 ↔
        ∃ y : ZMod 2, zmodTwoToZmodFourFun y = x)
    fin_cases x
    · decide
    · decide
    · decide
    · decide
  have hInjective : Function.Injective zmodTwoToZmodFourFun := by
    intro x y hxy
    fin_cases x
    · fin_cases y
      · rfl
      · exfalso
        exact (by decide : zmodTwoToZmodFourFun 0 ≠ zmodTwoToZmodFourFun 1) hxy
    · fin_cases y
      · exfalso
        exact (by decide : zmodTwoToZmodFourFun 1 ≠ zmodTwoToZmodFourFun 0) hxy
      · rfl
  have hSurjective : Function.Surjective (ZMod.castHom (dvd_mul_right 2 2) (ZMod 2)) :=
    ZMod.castHom_surjective (dvd_mul_right 2 2)
  refine ModuleCat.shortComplex_shortExact standardModTwoCoefficientShortComplex ?_ ?_ ?_
  · exact hExact
  · simpa [zmodTwoToZmodFour, zmodTwoToZmodFourFun] using hInjective
  · simpa [zmodFourToZmodTwo] using hSurjective

/-- The integral singular chain groups of a space are projective in every degree. -/
theorem integralTopologicalSingularChains_projective (X : TopCat) :
    ∀ n, Projective ((C_*(X)).X n) := by
  intro n
  exact integralSingularChainDegree_projective X n

/-- A degree-`1` singular cohomology operation is the standard mod-`2` Bockstein when it is the
operation induced by the standard short exact coefficient sequence
`0 → ZMod 2 → ZMod 4 → ZMod 2 → 0`. -/
def IsStandardModTwoBocksteinOperation
    (X : TopCat)
    (n : ℕ)
    (β : (forget₂ (ModuleCat ℤ) AddCommGrpCat).obj (modTwoSingularCohomology X n) ⟶
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).obj (modTwoSingularCohomology X (n + 1))) :
    Prop :=
  ∃ (hX : ∀ m, Projective ((C_*(X)).X m))
    (hShortExact : standardModTwoCoefficientShortComplex.ShortExact),
    β =
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
        (modTwoBocksteinOperation
          X hX standardModTwoCoefficientShortComplex rfl rfl hShortExact n)

/-- The standard singular Bockstein operation satisfies
`IsStandardModTwoBocksteinOperation X n`. -/
theorem isStandardModTwoBocksteinOperation_standard
    (X : TopCat)
    (hX : ∀ m, Projective ((C_*(X)).X m))
    (hShortExact : standardModTwoCoefficientShortComplex.ShortExact)
    (n : ℕ) :
    IsStandardModTwoBocksteinOperation X n
      ((forget₂ (ModuleCat ℤ) AddCommGrpCat).map
        (modTwoBocksteinOperation
          X hX standardModTwoCoefficientShortComplex rfl rfl hShortExact n)) := by
  exact ⟨hX, hShortExact, rfl⟩

/-- Problem 22.6.3. For a chosen Steenrod-square family `Sq` on mod-`2` singular cohomology, the
degree-`1` operation induced on singular cohomology by `Sq` is the standard mod-`2` Bockstein
operation attached to the short exact coefficient sequence `0 → ZMod 2 → ZMod 4 → ZMod 2 → 0`.
-/
theorem sq1_isStandardModTwoBocksteinOperation
    {H2 : ModTwoCohomologyTheory}
    {suspension : TopCat ⥤ TopCat}
    {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso)
    (X : TopCat)
    (n : ℕ) :
    IsStandardModTwoBocksteinOperation X n (Sq.singularSq 1 n X) := by
  -- TODO: finish the universal-class comparison on `K(ZMod 2, n)` from the source route.
  sorry

/-- The source-facing standard-Bockstein specification expands to the existence of projectivity
and short-exactness witnesses exhibiting `β` as the induced Bockstein. -/
theorem isStandardModTwoBocksteinOperation_iff
    (X : TopCat)
    (n : ℕ)
    (β : (forget₂ (ModuleCat ℤ) AddCommGrpCat).obj (modTwoSingularCohomology X n) ⟶
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).obj (modTwoSingularCohomology X (n + 1))) :
    IsStandardModTwoBocksteinOperation X n β ↔
      ∃ (hX : ∀ m, Projective ((C_*(X)).X m))
        (hShortExact : standardModTwoCoefficientShortComplex.ShortExact),
        β =
          (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
            (modTwoBocksteinOperation
              X hX standardModTwoCoefficientShortComplex rfl rfl hShortExact n) :=
  Iff.rfl
