import Mathlib
import StacksProject_2024.Chap12.Definition_12_14_2
import StacksProject_2024.Chap12.Lemma_12_14_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open HomologicalComplex

universe v u

namespace ChainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable (S : ShortComplex (ChainComplex 𝒜 ℤ)) (hS : S.ShortExact)

/- Domain-style sampling in the chain-complex long-exact-sequence API:
- core/canonical owner boundary: `ShortComplex.ShortExact.δ`
- core/canonical owner shifted homology map:
  `(homologyFunctor 𝒜 (ComplexShape.down ℤ) 0).shiftMap`
- source-facing bridge datum: `homOfDegreewiseSplit` from Lemma `12.14.4`

This item is a `bridge/view`: it compares the explicit chain-level connecting morphism from
Lemma `12.14.4` with the owner boundary map in the long exact homology sequence, using the owner
`Functor.ShiftSequence.shiftMap` interface on chain homology.
-/

variable (σ : ∀ n : ℤ, (ChainComplex.degreewiseShortComplex S n).Splitting)

-- Proof sketch: compare the explicit chain map `homOfDegreewiseSplit S σ` from
-- Lemma `12.14.4` with the canonical boundary map in the snake-lemma construction of
-- the homology long exact sequence; the identification `H_i(A[-1]) ≅ H_{i-1}(A)` is the owner
-- shift-map construction `(homologyFunctor 𝒜 (ComplexShape.down ℤ) 0).shiftMap` specialized to
-- `k = -1`.
/-- Lemma 12.14.5: after identifying `H_i(A[-1]_•)` with `H_{i-1}(A_•)`, the homology map
induced by the explicit chain map `δ(σ) : C_• ⟶ A[-1]_•` of Lemma 12.14.4 is exactly the
connecting morphism occurring in the long exact homology sequence of the short exact sequence of
chain complexes. -/
theorem homologyMap_homOfDegreewiseSplit_eq_δ (i : ℤ) :
    (homologyFunctor 𝒜 (down ℤ) 0).shiftMap (homOfDegreewiseSplit S σ) i (i - 1) (by omega) =
      hS.δ i (i - 1) (down_mk i (i - 1) (sub_add_cancel i 1)) := by
  sorry

end ChainComplex
