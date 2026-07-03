import Mathlib
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap15.Lemma_15_66_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DModMinus" => boundedAboveDerivedCategory (ModuleCat R)

-- Source/core/bridge triage:
-- * source-facing: the filtered-colimit Ext criterion for an object of `D^-(R)`.
-- * core/canonical:
--   `PreservesFilteredColimits (derivedExtToModuleFunctor K.obj n)`.
-- * bridge/view: the canonical comparison map `colimit.post F (derivedExtToModuleFunctor K.obj n)`.
--
-- Primitive data are the degree-`n` Ext functors `derivedExtToModuleFunctor K.obj n`; the
-- comparison morphisms are derived API attached to those functors.

-- Proof sketch: the forward implication combines Lemma `15.66.1` with the canonical owner
-- equivalence between preserving filtered colimits and invertibility of the filtered-colimit
-- comparison morphisms. For the converse, induct on the top nonvanishing cohomological degree of
-- `K`; use the degree `-t` injectivity criterion to show `H^t(K)` is finite via Lemma `10.11.1`,
-- kill it by a finite free module, transfer the filtered-colimit `Ext` criterion to the cone, and
-- then apply the induction hypothesis together with Lemmas `15.65.7` and `15.65.2`.
/-- Lemma 15.66.2: an object `K` of `D^-(R)` is `m`-pseudo-coherent if and only if for every
filtered diagram of `R`-modules the canonical comparison map
`\operatorname{colim}_i \operatorname{Ext}^n_R(K, M_i) \to
\operatorname{Ext}^n_R(K, \operatorname{colim}_i M_i)` is an isomorphism for `n < -m`,
equivalently the functor `Ext^n_R(K, -)` preserves filtered colimits in those degrees, and is
injective in degree `-m`. -/
theorem boundedAbove_isMPseudoCoherent_iff_filteredColimitExt
    (K : DModMinus) (m : ℤ) :
    K.obj.IsMPseudoCoherent m ↔
      (∀ n : ℤ, n < -m →
        PreservesFilteredColimits (derivedExtToModuleFunctor K.obj n)) ∧
      ∀ ⦃J : Type v⦄ [SmallCategory J] [IsFiltered J]
        (F : J ⥤ ModuleCat R),
          Mono (colimit.post F (derivedExtToModuleFunctor K.obj (-m))) := sorry

end

end CategoryTheory
