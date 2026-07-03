import Mathlib
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap15.Definition_15_65_1

noncomputable section

open CategoryTheory
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "DModMinus" => boundedAboveDerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling for Lemma 15.65.10:
- primary domain: pseudo-coherence of bounded-above derived `R`-complexes from degreewise
  pseudo-coherence of their cohomology modules;
- sampled owner declarations:
  `boundedAboveDerivedCategory`,
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.homologyFunctor`;
- best owner abstraction: bounded-above complexes should be carried by the chapter owner
  `boundedAboveDerivedCategory (ModuleCat R)` rather than by a separate membership proof in
  `t.minus`;
- primitive vs. derived:
  primitive data are the bounded-above derived object `K : DModMinus` and the degreewise
  cohomology hypotheses;
  derived API is the resulting owner conclusions `K.obj.IsMPseudoCoherent m` and
  `K.obj.IsPseudoCoherent`;
- source/core/bridge triage:
  `source-facing`: the bounded-above cohomology criteria below;
  `core/canonical`: `DModMinus`, `K.IsMPseudoCoherent`, `K.IsPseudoCoherent`, and
    `DerivedCategory.homologyFunctor`;
  `bridge/view`: reading the cohomology hypotheses via `K.obj` in the ambient unbounded derived
    category.
-/

-- Proof sketch: choose a bounded-above representative for `K` and induct on the largest degree
-- with nonvanishing cohomology. If this degree is `< m`, apply Lemma `15.65.7`; otherwise use the
-- truncation triangle with top cohomology `H^n(K)[-n]`, note that the hypothesis makes this shift
-- `m`-pseudo-coherent, and reduce to the lower truncation via Lemma `15.65.2`.
/-- Lemma 15.65.10: if `K` is a bounded-above derived `R`-complex and every cohomology module
`H^i(K)` is `(m - i)`-pseudo-coherent, then `K` is `m`-pseudo-coherent. -/
theorem boundedAbove_isMPseudoCoherent_of_homology
    (K : DModMinus) (m : ℤ)
    (hH : ∀ i : ℤ, ((H i).obj K.obj).IsMPseudoCoherent (m - i)) :
    K.obj.IsMPseudoCoherent m := sorry

-- Proof sketch: apply the previous theorem for each integer `m`, using that a pseudo-coherent
-- module is `(m - i)`-pseudo-coherent for every `i`, and conclude with the characterization of
-- pseudo-coherence from Lemma `15.65.5`.
/-- If every cohomology module of a bounded-above derived `R`-complex is pseudo-coherent, then the
complex itself is pseudo-coherent. -/
theorem boundedAbove_isPseudoCoherent_of_homology
    (K : DModMinus)
    (hH : ∀ i : ℤ, ((H i).obj K.obj).IsPseudoCoherent) :
    K.obj.IsPseudoCoherent := sorry

end

end CategoryTheory
