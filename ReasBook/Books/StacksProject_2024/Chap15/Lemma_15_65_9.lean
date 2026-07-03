import Mathlib
import StacksProject_2024.Chap15.Lemma_15_65_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

/- Domain-style sampling for Lemma 15.65.9:
- primary domain: pseudo-coherence of bounded-above cochain complexes of `R`-modules, with the
  source-facing hypotheses stated termwise on the underlying modules;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `CochainComplex.IsMPseudoCoherent`,
  `ModuleCat.IsMPseudoCoherent`,
  `CochainComplex.minus`;
- best owner abstraction: the chapter owners remain the existing predicates
  `CochainComplex.IsMPseudoCoherent` and `CochainComplex.IsPseudoCoherent`; this file is the
  source-facing bridge from termwise module pseudo-coherence plus the canonical bounded-above
  owner `CochainComplex.minus (ModuleCat R) K` to those owner predicates, and should not
  introduce any extra bounded-above wrapper or parallel pseudo-coherence API;
- primitive vs. derived:
  primitive data are the cochain complex `K`, the bounded-above hypothesis
  `CochainComplex.minus (ModuleCat R) K`,
  and the degreewise module hypotheses on `K.X i`;
  derived API is the resulting owner-level pseudo-coherence of `K`;
- source/core/bridge triage:
  `source-facing`: the two theorems below about bounded-above cochain complexes with termwise
    pseudo-coherent terms;
  `core/canonical`: `DerivedCategory.IsMPseudoCoherent`, `DerivedCategory.IsPseudoCoherent`,
    `CochainComplex.IsMPseudoCoherent`, `CochainComplex.IsPseudoCoherent`, and
    `CochainComplex.minus`;
  `bridge/view`: passage from the termwise module hypotheses on `K.X i` to the cochain-complex
    owner predicates. -/

-- Proof sketch: truncate the bounded-above complex far enough above degree `m` to reduce to a
-- bounded complex, then induct on the number of nonzero terms using stupid truncation triangles.
-- Apply Lemma `15.65.2` at each step, observing that the shifted single-term complex `K.X i[-i]`
-- is `m`-pseudo-coherent exactly when `K.X i` is `(m - i)`-pseudo-coherent.
/-- Lemma 15.65.9: a bounded-above cochain complex of `R`-modules whose term in degree `i` is
`(m - i)`-pseudo-coherent is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_of_boundedAbove_of_termwise
    (K : Cpx) (m : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) K)
    (hterm : ∀ i : ℤ, (K.X i).IsMPseudoCoherent (m - i)) :
    K.IsMPseudoCoherent m := sorry

-- Proof sketch: for each fixed `m`, use the first theorem and the hypothesis that every term of
-- `K` is pseudo-coherent, hence `(m - i)`-pseudo-coherent for every `i`, and then invoke Lemma
-- `15.65.5` to pass from `m`-pseudo-coherence for all `m` to pseudo-coherence.
/-- A bounded-above cochain complex of pseudo-coherent `R`-modules is pseudo-coherent. -/
theorem isPseudoCoherent_of_boundedAbove_of_termwise
    (K : Cpx)
    (hbounded : CochainComplex.minus (ModuleCat R) K)
    (hterm : ∀ i : ℤ, (K.X i).IsPseudoCoherent) :
    K.IsPseudoCoherent := sorry

end

end CochainComplex
