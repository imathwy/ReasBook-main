import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Linear.Basic

noncomputable section

universe u

open CategoryTheory

/-- Helper for Definition 17.3.1: successive precomposition maps induced by the differentials of a
chain complex compose to zero. -/
private theorem leftCompSuccSqZero (R : Type u) [Ring R]
    (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (i : ℤ) :
    ModuleCat.ofHom (Linear.leftComp ℤ M (X.d (i + 1) i)) ≫
      ModuleCat.ofHom (Linear.leftComp ℤ M (X.d (i + 1 + 1) (i + 1))) = 0 := by
  -- Rewrite the categorical composition as a composition of linear maps on Hom-spaces.
  rw [← ModuleCat.ofHom_comp]
  apply ModuleCat.hom_ext
  ext φ x
  -- Evaluate the composed precomposition maps pointwise and use `d ∘ d = 0` in `X`.
  simpa [CategoryTheory.Linear.leftComp_apply, Category.assoc] using
    congrArg (fun f => ModuleCat.Hom.hom (f ≫ φ) x) (X.d_comp_d (i + 1 + 1) (i + 1) i)

/-- Definition 17.3.1. For a chain complex `X` of `R`-modules and an `R`-module `M`,
`homCochainComplex R X M` is the cochain complex `Hom(X, M)` of abelian groups, whose degree `n`
term is `Hom(X.X n, M)` and whose differential is induced by precomposition with `X.d`. -/
def homCochainComplex (R : Type u) [Ring R]
    (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) :
    CochainComplex (ModuleCat ℤ) ℤ where
  X n := ModuleCat.of ℤ (X.X n ⟶ M)
  d i j := if h : i + 1 = j then ModuleCat.ofHom (Linear.leftComp ℤ M (X.d j i)) else 0
  shape i j hij := by
    by_cases h : i + 1 = j
    · exact (hij (ComplexShape.up_mk i j h)).elim
    · simp [h]
  d_comp_d' i j k hij hjk := by
    -- Normalize the `ComplexShape.up` hypotheses to the consecutive degrees `i`, `i + 1`, `i + 2`.
    simp only [ComplexShape.up_Rel] at hij hjk
    subst j
    subst k
    -- After index normalization, invoke the square-zero helper for successive precomposition maps.
    simpa using leftCompSuccSqZero R X M i
