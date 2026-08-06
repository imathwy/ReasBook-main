import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex

universe u

-- Semantic recall: `ChainComplex (ModuleCat R) ℕ` is the canonical owner, and the source-facing
-- "graded modules plus differential squaring to zero" presentation is exposed by
-- `ChainComplex.of` together with its computation lemmas `ChainComplex.of_x` and
-- `ChainComplex.of_d`.

variable (R : Type u) [Ring R]

/- Definition 12.1.1: the canonical mathlib formalization of a chain complex of `R`-modules is
`ChainComplex (ModuleCat R) ℕ`, equivalently a sequence of `R`-modules with differentials
`d i : X (i + 1) ⟶ X i` satisfying `d (i + 1) ≫ d i = 0`. In the source's commutative-ring
setting, this is the same owner specialized to `[CommRing R]`. -/
#check ChainComplex (ModuleCat R) ℕ

/- `ChainComplex.of` packages the source-facing data of modules and differentials with square zero
into the canonical owner `ChainComplex (ModuleCat R) ℕ`. -/
#check (ChainComplex.of :
  ∀ (X : ℕ → ModuleCat R) (d : (n : ℕ) → X (n + 1) ⟶ X n),
    (∀ n : ℕ, CategoryTheory.CategoryStruct.comp (d (n + 1)) (d n) = 0) →
      ChainComplex (ModuleCat R) ℕ)

/- The objects of `ChainComplex.of X d sq` are definitionally the original graded modules `X n`. -/
#check (ChainComplex.of_x :
  ∀ (X : ℕ → ModuleCat R) (d : (n : ℕ) → X (n + 1) ⟶ X n)
    (sq : ∀ n : ℕ, CategoryTheory.CategoryStruct.comp (d (n + 1)) (d n) = 0) (n : ℕ),
      (ChainComplex.of X d sq).X n = X n)

/- The differential of `ChainComplex.of X d sq` in degree `j` is exactly the given map `d j`. -/
#check (ChainComplex.of_d :
  ∀ (X : ℕ → ModuleCat R) (d : (n : ℕ) → X (n + 1) ⟶ X n)
    (sq : ∀ n : ℕ, CategoryTheory.CategoryStruct.comp (d (n + 1)) (d n) = 0) (j : ℕ),
      (ChainComplex.of X d sq).d (j + 1) j = d j)
