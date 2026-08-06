import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.RingTheory.Flat.CategoryTheory

open CategoryTheory MonoidalCategory
open HomologicalComplex HomologicalComplex.HomologySequence

-- Semantic recall: `CategoryTheory.ShortComplex.ShortExact.δ`,
-- `HomologicalComplex.HomologySequence.composableArrows₅`,
-- `ShortComplex.map`, and `Module.Flat` together with `tensorLeft` supply the Bockstein segment.

/-- Tensoring coefficients with a fixed chain complex degreewise. -/
abbrev coefficientTensorFunctor
    (C : ChainComplex (ModuleCat ℤ) ℕ) :
    ModuleCat ℤ ⥤ ChainComplex (ModuleCat ℤ) ℕ where
  obj A := (((tensoringRight (ModuleCat ℤ)).obj A).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj C
  map f := (NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat ℤ)).map f)
    (ComplexShape.down ℕ)).app C
  map_id A := by
    ext n x
    simp
  map_comp f g := by
    ext n x
    simp

instance coefficientTensorFunctor_preservesZeroMorphisms
    (C : ChainComplex (ModuleCat ℤ) ℕ) :
    (coefficientTensorFunctor C).PreservesZeroMorphisms where
  map_zero _ _ := by
    ext n x
    simp [coefficientTensorFunctor]
    rfl

/-- The short complex of chain complexes obtained by tensoring a coefficient short exact sequence
with a chain complex degreewise. -/
abbrev coefficientTensorShortComplex
    (S : ShortComplex (ModuleCat ℤ)) (C : ChainComplex (ModuleCat ℤ) ℕ) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  S.map (coefficientTensorFunctor C)

/-- Evaluating the tensor short complex in degree `n` recovers tensoring the coefficient short
complex with `C.X n`. -/
lemma coefficientTensorShortComplex_map_eval
    (S : ShortComplex (ModuleCat ℤ)) (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (coefficientTensorShortComplex S C).map
        (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n) =
      S.map (tensorLeft (C.X n)) := rfl

/-- If `C` is degreewise flat, tensoring a short exact sequence of coefficient groups with `C`
produces a short exact sequence of chain complexes. -/
theorem coefficientTensorShortComplex_shortExact
    (S : ShortComplex (ModuleCat ℤ)) (hS : S.ShortExact)
    (C : ChainComplex (ModuleCat ℤ) ℕ) (hC : ∀ n, Module.Flat ℤ (C.X n)) :
    (coefficientTensorShortComplex S C).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  haveI : Module.Flat ℤ (C.X n) := hC n
  simpa [coefficientTensorShortComplex_map_eval] using
    hS.map_of_exact (tensorLeft (C.X n))

/-- The Bockstein connecting homomorphism attached to tensoring the coefficient short exact
sequence with `C` degreewise. -/
noncomputable abbrev bocksteinBoundary
    (S : ShortComplex (ModuleCat ℤ)) (hS : S.ShortExact)
    (C : ChainComplex (ModuleCat ℤ) ℕ) (hC : ∀ n, Module.Flat ℤ (C.X n)) (n : ℕ) :
    (coefficientTensorShortComplex S C).X₃.homology (n + 1) ⟶
      (coefficientTensorShortComplex S C).X₁.homology n :=
  (coefficientTensorShortComplex_shortExact S hS C hC).δ (n + 1) n rfl

/-- The Bockstein five-arrow homology segment attached to a short exact coefficient sequence and
a degreewise flat chain complex. -/
noncomputable abbrev bocksteinComposableArrows₅
    (S : ShortComplex (ModuleCat ℤ)) (hS : S.ShortExact)
    (C : ChainComplex (ModuleCat ℤ) ℕ) (hC : ∀ n, Module.Flat ℤ (C.X n)) (n : ℕ) :
    ComposableArrows (ModuleCat ℤ) 5 :=
  composableArrows₅
    (coefficientTensorShortComplex_shortExact S hS C hC) (n + 1) n rfl

/-- The Bockstein connecting homomorphism is the middle map of the associated five-arrow
homology segment. -/
theorem bocksteinBoundary_def
    (S : ShortComplex (ModuleCat ℤ)) (hS : S.ShortExact)
    (C : ChainComplex (ModuleCat ℤ) ℕ) (hC : ∀ n, Module.Flat ℤ (C.X n)) (n : ℕ) :
    bocksteinBoundary S hS C hC n = (bocksteinComposableArrows₅ S hS C hC n).map' 2 3 := rfl

/-- Problem 12.5.3: a short exact sequence of abelian groups and a degreewise flat chain complex
`C` determine the corresponding Bockstein five-arrow homology segment, and that segment is exact.
-/
theorem bocksteinComposableArrows₅_exact
    (S : ShortComplex (ModuleCat ℤ)) (hS : S.ShortExact)
    (C : ChainComplex (ModuleCat ℤ) ℕ) (hC : ∀ n, Module.Flat ℤ (C.X n)) (n : ℕ) :
    (bocksteinComposableArrows₅ S hS C hC n).Exact :=
  composableArrows₅_exact (coefficientTensorShortComplex_shortExact S hS C hC) (n + 1) n rfl
