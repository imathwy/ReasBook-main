import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas

open CategoryTheory
open HomologicalComplex HomologicalComplex.HomologySequence

universe u

variable {R : Type u} [CommRing R]

-- Semantic recall via `lean_leansearch` timed out in this environment; direct mathlib inspection
-- identified `ShortComplex.ShortExact.δ`, `HomologicalComplex.HomologySequence.composableArrows₅`,
-- `HomologicalComplex.HomologySequence.composableArrows₅_exact`, and
-- `HomologicalComplex.HomologySequence.δ_naturality` as the canonical API.

/-- The connecting homomorphism `∂ : H_(n + 1)(X'') ⟶ H_n(X')` attached to a short exact sequence
of chain complexes `0 ⟶ X' ⟶ X ⟶ X'' ⟶ 0`. -/
noncomputable abbrev shortExactChainComplexHomologyBoundary
    (S : ShortComplex (ChainComplex (ModuleCat R) ℕ)) (hS : S.ShortExact) (n : ℕ) :
    S.X₃.homology (n + 1) ⟶ S.X₁.homology n :=
  hS.δ (n + 1) n rfl

/-- The degree-`n` five-arrow segment in the long exact homology sequence of a short exact
sequence of chain complexes. -/
noncomputable abbrev shortExactChainComplexHomologyComposableArrows₅
    (S : ShortComplex (ChainComplex (ModuleCat R) ℕ)) (hS : S.ShortExact) (n : ℕ) :
    ComposableArrows (ModuleCat R) 5 :=
  composableArrows₅ hS (n + 1) n rfl

/-- The connecting homomorphism is the middle map of the associated degree-`n` five-arrow
homology segment. -/
theorem shortExactChainComplexHomologyBoundary_def
    (S : ShortComplex (ChainComplex (ModuleCat R) ℕ)) (hS : S.ShortExact) (n : ℕ) :
    shortExactChainComplexHomologyBoundary S hS n =
      (shortExactChainComplexHomologyComposableArrows₅ S hS n).map' 2 3 := rfl

/-- The connecting homomorphisms attached to morphisms of short exact sequences of chain
complexes are natural on homology. -/
@[reassoc]
theorem shortExactChainComplexHomologyBoundary_naturality
    {S₁ S₂ : ShortComplex (ChainComplex (ModuleCat R) ℕ)} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (n : ℕ) :
    shortExactChainComplexHomologyBoundary S₁ hS₁ n ≫ homologyMap φ.τ₁ n =
      homologyMap φ.τ₃ (n + 1) ≫ shortExactChainComplexHomologyBoundary S₂ hS₂ n := by
  simpa [shortExactChainComplexHomologyBoundary] using
    δ_naturality φ hS₁ hS₂ (n + 1) n rfl

/-- Proposition 12.4.3: a short exact sequence of chain complexes yields the exact five-term
homology segment
`H_(n + 1)(X') ⟶ H_(n + 1)(X) ⟶ H_(n + 1)(X'') ⟶ H_n(X') ⟶ H_n(X) ⟶ H_n(X'')`,
namely `shortExactChainComplexHomologyComposableArrows₅ S hS n`, whose middle map is the
connecting homomorphism `∂ = shortExactChainComplexHomologyBoundary S hS n`. This is the
degree-`n` piece of the natural long exact homology sequence. -/
theorem shortExactChainComplexHomologyExactFiveTerm
    (S : ShortComplex (ChainComplex (ModuleCat R) ℕ)) (hS : S.ShortExact) (n : ℕ) :
    (shortExactChainComplexHomologyComposableArrows₅ S hS n).Exact :=
  composableArrows₅_exact hS (n + 1) n rfl
