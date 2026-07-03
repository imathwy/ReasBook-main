import Mathlib
import StacksProject_2024.Chap15.Lemma_15_65_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace CochainComplex

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

/- Domain-style sampling for Lemma 15.65.7:
- primary domain: recognition of `m`-pseudo-coherence for cochain complexes from cohomology
  vanishing and finiteness conditions on the top surviving cohomology objects;
- sampled owner declarations:
  `CochainComplex.IsMPseudoCoherent`,
  `homology_finite_of_isMPseudoCoherent`,
  `homology_finitePresentation_of_isMPseudoCoherent`,
  `DerivedCategory.IsLE`;
- best owner abstraction: the pseudo-coherence owner stays `K.IsMPseudoCoherent m`; the explicit
  cohomology-vanishing hypotheses below are source-facing bridge data rather than a second owner,
  and the canonical derived `t`-structure bound `((DerivedCategory.Q : Cpx ⥤ _).obj K).IsLE _`
  remains a downstream view;
- primitive vs. derived:
  primitive data are the cochain complex `K`, the homology vanishing ranges, and the finiteness
  / finite-presentation hypotheses on the surviving cohomology modules;
  derived API is the resulting `m`-pseudo-coherence conclusion, whose converse finiteness
  consequences already belong to Lemma `15.65.3`;
- source/core/bridge triage:
  `source-facing`: the three recognition statements below in textbook homology language;
  `core/canonical`: the owner predicate `K.IsMPseudoCoherent m`;
  `bridge/view`: the cohomology-vanishing input and the derived `IsLE` reformulation of that
    input, which should not replace the source-facing statements here.
-/

-- Proof sketch: apply part `(3)` below with `H^(m + 1)(K)` and `H^m(K)` both zero, using that the
-- zero `R`-module is finitely presented and finite.
/-- Lemma 15.65.7 (1): if a cochain complex `K^•` of `R`-modules has vanishing cohomology
in every degree `i ≥ m`, then `K^•` is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_of_homology_isZero_ge
    {K : Cpx} {m : ℤ}
    (hvanish : ∀ i : ℤ, m ≤ i → IsZero (K.homology i)) :
    K.IsMPseudoCoherent m := sorry

-- Proof sketch: use the finite generation of `H^m(K)` to choose a finite free cover onto the top
-- surviving cohomology, realize it as a map `E[-m] ⟶ K`, and note that all higher cohomology
-- vanishes, so this map gives the required `m`-pseudo-coherent approximation.
/-- Lemma 15.65.7 (2): if a cochain complex `K^•` of `R`-modules has vanishing cohomology
in every degree `i > m` and `H^m(K^•)` is finite, then `K^•` is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_of_homology_isZero_gt_and_finite
    {K : Cpx} {m : ℤ}
    (hvanish : ∀ i : ℤ, m < i → IsZero (K.homology i))
    (hm : Module.Finite R (K.homology m)) :
    K.IsMPseudoCoherent m := sorry

-- Proof sketch: replace `τ≥m+1 K` by the shift of `H^(m + 1)(K)` using the higher vanishing,
-- apply Lemma `15.65.4` to that shifted module complex, and use the truncation triangle together
-- with Lemma `15.65.2` to reduce to the previous case for `τ≤m K`.
/-- Lemma 15.65.7 (3): if a cochain complex `K^•` of `R`-modules has vanishing cohomology
in every degree `i > m + 1`, `H^(m + 1)(K^•)` is finitely presented, and `H^m(K^•)` is finite,
then `K^•` is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_of_homology_isZero_gt_add_one_and_finite
    {K : Cpx} {m : ℤ}
    (hvanish : ∀ i : ℤ, m + 1 < i → IsZero (K.homology i))
    (hm_succ : Module.FinitePresentation R (K.homology (m + 1)))
    (hm : Module.Finite R (K.homology m)) :
    K.IsMPseudoCoherent m := sorry

end

end CochainComplex
