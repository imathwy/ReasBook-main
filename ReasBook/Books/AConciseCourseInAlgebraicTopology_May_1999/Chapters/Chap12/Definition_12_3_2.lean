import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap12.Definition_12_3_1
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.Single

noncomputable section

open CategoryTheory
open scoped MonoidalCategory

universe u

-- Semantic recall via `lean_leansearch`: `ChainComplex.single₀` is the canonical chain complex
-- with an object concentrated in degree `0`, while Definition 12.3.1 already fixed
-- the tensor-product surface `X ⊗ Y` for chain complexes. The textbook
-- coefficient homology is therefore the degreewise homology of `X ⊗ coefficientComplex R M`.

/-- The coefficient module `M`, regarded as a chain complex concentrated in degree `0`. -/
abbrev coefficientComplex (R : Type u) [CommRing R] (M : ModuleCat R) :
    ChainComplex (ModuleCat R) ℕ :=
  (ChainComplex.single₀ (ModuleCat R)).obj M

/-- A morphism of coefficient modules induces the corresponding morphism of degree-zero
coefficient complexes. -/
abbrev coefficientComplexMap (R : Type u) [CommRing R] {M N : ModuleCat R} (f : M ⟶ N) :
    coefficientComplex R M ⟶ coefficientComplex R N :=
  (ChainComplex.single₀ (ModuleCat R)).map f

/-- Definition 12.3.2. For a chain complex `X` of `R`-modules and an `R`-module `M`, viewed as
the degree-zero chain complex `coefficientComplex R M`, the homology of `X` with coefficients in
`M` is the graded family obtained from the homology of `X ⊗ coefficientComplex R M`. -/
abbrev homologyWithCoefficients (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) :
    ℕ → ModuleCat R :=
  fun n ↦ (X ⊗ (coefficientComplex R M)).homology n

/-- Evaluating `homologyWithCoefficients R X M` in degree `n` recovers the homology object of the
tensor product of `X` with `M` concentrated in degree `0`. -/
@[simp] theorem homologyWithCoefficients_apply (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) :
    homologyWithCoefficients R X M n =
      (X ⊗ (coefficientComplex R M)).homology n :=
  rfl
