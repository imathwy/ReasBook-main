import Mathlib
import stacks_project.Chap19.«19_2_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits Opposite

universe u v

section FiniteModule

variable {R : Type u} [Ring R]
variable (N : ModuleCat.{v} R)

-- Source/core/bridge triage:
-- * primitive owner data: `Module.Finite R N`
-- * core/canonical owner map: `colimit.post F (coyoneda.obj (op N))`
-- * source-facing bridge: injectivity of that comparison map for filtered colimits
--
-- This item already uses the canonical owner object `ModuleCat R` and the canonical comparison
-- map from 19.2.0.1, so the refinement here is to use `colimit.post` directly rather than keep a
-- parallel local wrapper API.
-- Proof sketch: for the forward implication, choose finitely many generators of `N` and use
-- filteredness to find one stage where all of their images vanish, which forces eventual
-- vanishing of the whole map. For the converse, apply the injectivity criterion to the filtered
-- system of quotients `N / N_E` indexed by finite subsets `E ⊆ N`; the identity of `N` must come
-- from one stage, showing that some finite subset generates `N`.
/-- Lemma 10.11.1: an `R`-module `N` is finite if and only if for every filtered colimit of
`R`-modules, the canonical map `colim_i Hom_R(N, M_i) → Hom_R(N, colim_i M_i)` is injective. -/
lemma module_finite_iff_injective_filteredColimitHomComparison :
    Module.Finite R N ↔
      ∀ ⦃J : Type v⦄ [SmallCategory J] [IsFiltered J] (F : J ⥤ ModuleCat R),
        Function.Injective (colimit.post F (coyoneda.obj (op N))) := by
  constructor
  · intro hN J _ _ F
    -- Choose finite generators for `N`, reduce equality in the filtered colimit of Hom-sets to
    -- stagewise equality on those generators, and combine the finitely many stages using
    -- filteredness.
    sorry
  · intro hcmp
    -- Apply the injectivity criterion to the filtered diagram of quotients
    -- `N / span(E)` indexed by finite subsets `E ⊆ N`; its colimit is zero, so the class of the
    -- quotient map from the empty stage must vanish at some finite stage, forcing that stage to
    -- generate `N`.
    sorry

end FiniteModule
