import Mathlib
import StacksProject_2024.Chap15.Definition_15_65_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

-- Proof sketch: choose a bounded-above finite-projective approximation `E^• ⟶ K^•` from the
-- definition of `m`-pseudo-coherence. Under the stated vanishing hypotheses, replace `E^•` by a
-- bounded finite-projective complex, peel off the top nonzero term inductively, and identify the
-- surviving top cohomology as a quotient of a finite module in degree `m` and as a cokernel of a
-- map between finite projectives in degree `m + 1`.
/-- Lemma 15.65.3: if an `R`-module cochain complex `K^•` is `m`-pseudo-coherent, then vanishing
of `H^i(K^•)` for `i > m` implies that `H^m(K^•)` is a finite `R`-module, and vanishing of
`H^i(K^•)` for `i > m + 1` implies that `H^{m + 1}(K^•)` is finitely presented. -/
theorem homology_finite_and_finitePresentation_of_isMPseudoCoherent
    {K : Cpx} {m : ℤ} (hK : K.IsMPseudoCoherent m) :
    ((∀ i : ℤ, m < i → IsZero (K.homology i)) → Module.Finite R (K.homology m)) ∧
      ((∀ i : ℤ, m + 1 < i → IsZero (K.homology i)) →
        Module.FinitePresentation R (K.homology (m + 1))) := sorry

-- Proof sketch: apply the first component of
-- `homology_finite_and_finitePresentation_of_isMPseudoCoherent` to the given vanishing range.
/-- The top surviving cohomology of an `m`-pseudo-coherent complex is finite when all higher
cohomology vanishes. -/
theorem homology_finite_of_isMPseudoCoherent
    {K : Cpx} {m : ℤ} (hK : K.IsMPseudoCoherent m)
    (hvanish : ∀ i : ℤ, m < i → IsZero (K.homology i)) :
    Module.Finite R (K.homology m) := sorry

-- Proof sketch: apply the second component of
-- `homology_finite_and_finitePresentation_of_isMPseudoCoherent` to the stronger vanishing range
-- above degree `m + 1`.
/-- The next cohomology of an `m`-pseudo-coherent complex is finitely presented when all
cohomology above degree `m + 1` vanishes. -/
theorem homology_finitePresentation_of_isMPseudoCoherent
    {K : Cpx} {m : ℤ} (hK : K.IsMPseudoCoherent m)
    (hvanish : ∀ i : ℤ, m + 1 < i → IsZero (K.homology i)) :
    Module.FinitePresentation R (K.homology (m + 1)) := sorry

end CochainComplex
