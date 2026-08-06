import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.CochainComplexOpposite

open CategoryTheory

universe u

-- Semantic recall: `lean_leansearch` surfaced `CochainComplex.of` and
-- `ChainComplex.cochainComplexEquivalence`, so the textbook notion is recalled through
-- mathlib's canonical cochain-complex owner and its standard reindexing equivalence.

variable (R : Type u) [Ring R]

/- Definition 12.1.2. The canonical mathlib formalization of a cochain complex of `R`-modules is
`CochainComplex (ModuleCat R) ℕ`, equivalently a sequence of `R`-modules with differentials
`d n : X n ⟶ X (n + 1)` satisfying `d n ≫ d (n + 1) = 0`. In the source's commutative-ring
setting, this is the same owner specialized to `[CommRing R]`. For `ℤ`-indexed complexes, the
chain and cochain conventions are canonically equivalent by reindexing via
`ChainComplex.cochainComplexEquivalence (ModuleCat R)`. -/
#check CochainComplex (ModuleCat R) ℕ

/- `CochainComplex.of` packages a sequence of `R`-modules and degree-raising differentials with
square zero into the canonical owner `CochainComplex (ModuleCat R) ℕ`. -/
#check (CochainComplex.of :
  ∀ (X : ℕ → ModuleCat R) (d : (n : ℕ) → X n ⟶ X (n + 1)),
    (∀ n : ℕ, d n ≫ d (n + 1) = 0) →
      CochainComplex (ModuleCat R) ℕ)

/- The objects of `CochainComplex.of X d sq` are definitionally the original graded modules
`X n`. -/
#check (CochainComplex.of_x :
  ∀ (X : ℕ → ModuleCat R) (d : (n : ℕ) → X n ⟶ X (n + 1))
    (sq : ∀ n : ℕ, d n ≫ d (n + 1) = 0) (n : ℕ),
      (CochainComplex.of X d sq).X n = X n)

/- The differential of `CochainComplex.of X d sq` in degree `j` is exactly the given map `d j`. -/
#check (CochainComplex.of_d :
  ∀ (X : ℕ → ModuleCat R) (d : (n : ℕ) → X n ⟶ X (n + 1))
    (sq : ∀ n : ℕ, d n ≫ d (n + 1) = 0) (j : ℕ),
      (CochainComplex.of X d sq).d j (j + 1) = d j)

/- The chain and cochain indexing conventions for `ℤ`-graded complexes are equivalent by the
canonical reindexing equivalence. -/
#check (ChainComplex.cochainComplexEquivalence (ModuleCat R))
