import Mathlib
import StacksProject_2024.Chap14.Lemma_14_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped IteratedEndofunctor

attribute [local instance] endofunctorMonoidalCategory

universe uA uS vA vS

namespace CategoryTheory

variable {𝒜 : Type uA} {𝒮 : Type uS} [Category.{vA} 𝒜] [Category.{vS} 𝒮]
variable {U : 𝒮 ⥤ 𝒜} {V : 𝒜 ⥤ 𝒮}

section

variable (adj : U ⊣ V)

local notation "T" => adj.toComonad.toFunctor
local notation "ε" => adj.toComonad.ε
local notation "δ" => adj.toComonad.δ

/- Domain-style sampling:
- primary domain: simplicial endofunctor resolutions attached to an adjunction via its induced
  comonad;
- sampled owner declarations:
  `IteratedEndofunctorRealization`,
  `iteratedEndofunctorResolution`,
  `iteratedEndofunctorResolution_realization`,
  `iteratedEndofunctorAugmentation`;
- best owner abstraction: the chapter owner
  `iteratedEndofunctorResolution adj.toComonad.ε adj.toComonad.δ ...`, specialized directly to
  the comonad of `adj`;
- primitive data: the comonad attached to `adj`, namely the endofunctor
  `adj.toComonad.toFunctor` with counit `adj.toComonad.ε` and comultiplication
  `adj.toComonad.δ`;
- derived API: the canonical chapter owners specialized to `adj.toComonad`, together with the
  existence/uniqueness theorem below;
- source/core/bridge triage:
  - `source-facing`: the existence statement below;
  - `core/canonical`: the chapter owners `IteratedEndofunctorRealization`,
    `iteratedEndofunctorResolution`, and `iteratedEndofunctorAugmentation`;
  - `bridge/view`: the three low-degree comonad-law identities supplying the hypotheses of
    `iteratedEndofunctorResolution`, `iteratedEndofunctorResolution_realization`,
    `iteratedEndofunctorAugmentation`, and
    `iteratedEndofunctor_exists_unique_simplicial_object`.

This item should therefore expose only the low-degree bridge theorems and the source-facing
existence statement, so direct downstream files can call the canonical owners specialized to
`adj.toComonad` instead of going through a parallel local wrapper API.
-/

/-- The first degree-`0` simplicial identity for the comonad induced by an adjunction. -/
theorem adjunction_iteratedEndofunctor_hσδ₀ :
    (s[T, δ]⦅0, 0⦆) ≫ d[T, ε]⦅0, 0⦆ = 𝟙 T := by
  ext X
  dsimp [Adjunction.toComonad, iteratedFaceMap, iteratedDegeneracyMap]
  rw [show (0 : Fin 2) = Fin.castSucc 0 by rfl]
  rw [Fin.lastCases_castSucc, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app]
  have h : U.map (adj.unit.app (V.obj X)) ≫ (V ⋙ U).map (adj.counit.app X) =
      𝟙 (U.obj (V.obj X)) := by
    simpa [Adjunction.toComonad] using adj.toComonad.right_counit X
  have hs :
      U.map (adj.unit.app (V.obj X)) ≫ U.map (V.map (adj.counit.app X)) ≫ 𝟙 (U.obj (V.obj X)) =
        U.map (adj.unit.app (V.obj X)) ≫ U.map (V.map (adj.counit.app X)) := by
    simp
  exact hs.trans h

/-- The second degree-`0` simplicial identity for the comonad induced by an adjunction. -/
theorem adjunction_iteratedEndofunctor_hσδ₁ :
    (s[T, δ]⦅0, 0⦆) ≫ d[T, ε]⦅0, 1⦆ = 𝟙 T := by
  ext X
  dsimp [Adjunction.toComonad, iteratedFaceMap, iteratedDegeneracyMap]
  rw [show (1 : Fin 2) = Fin.last 1 by rfl]
  rw [Fin.lastCases_last, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app]
  have h : U.map (adj.unit.app (V.obj X)) ≫ adj.counit.app (U.obj (V.obj X)) =
      𝟙 (U.obj (V.obj X)) := by
    exact adj.toComonad.left_counit X
  have hs :
      U.map (adj.unit.app (V.obj X)) ≫ adj.counit.app (U.obj (V.obj X)) ≫ 𝟙 (U.obj (V.obj X)) =
        U.map (adj.unit.app (V.obj X)) ≫ adj.counit.app (U.obj (V.obj X)) := by
    simp
  exact hs.trans h

/-- The degree-`1` degeneracy compatibility for the comonad induced by an adjunction. -/
theorem adjunction_iteratedEndofunctor_hσσ :
    (s[T, δ]⦅0, 0⦆) ≫ s[T, δ]⦅1, 0⦆ = (s[T, δ]⦅0, 0⦆) ≫ s[T, δ]⦅1, 1⦆ := by
  ext X
  dsimp [Adjunction.toComonad, iteratedDegeneracyMap]
  rw [show (0 : Fin 2) = Fin.castSucc 0 by rfl, show (1 : Fin 2) = Fin.last 1 by rfl]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app]
  have h :
      U.map (adj.unit.app (V.obj X)) ≫ (V ⋙ U).map (U.map (adj.unit.app (V.obj X))) =
        U.map (adj.unit.app (V.obj X)) ≫ U.map (adj.unit.app (V.obj (U.obj (V.obj X)))) := by
    simpa [Adjunction.toComonad] using adj.toComonad.coassoc X
  have hs :
      U.map (adj.unit.app (V.obj X)) ≫ U.map (adj.unit.app (V.obj (U.obj (V.obj X)))) =
        U.map (adj.unit.app (V.obj X)) ≫
          U.map (adj.unit.app (V.obj ((V ⋙ U)⦅0⦆.obj X))) ≫
            𝟙 (U.obj (V.obj (U.obj (V.obj ((V ⋙ U)⦅0⦆.obj X))))) := by
    simp [iteratedEndofunctor]
  exact h.trans hs

-- Proof sketch: apply `iteratedEndofunctor_exists_unique_simplicial_object` to the comonad
-- `adj.toComonad`. The two degree-`0` identities are the comonad counit identities, and the
-- degree-`1` compatibility is comonad coassociativity.
/-- Lemma 14.34.2: in the situation of an adjunction `U ⊣ V`, the iterated endofunctor system on
`𝒜` obtained from the comonad `adj.toComonad` is realized by a unique simplicial object of
endofunctors of `𝒜`. -/
@[stacks 08NC]
theorem adjunction_resolution_exists_unique :
    ∃! X : SimplicialObject (𝒜 ⥤ 𝒜),
      IteratedEndofunctorRealization ε δ X := by
  simpa using
    iteratedEndofunctor_exists_unique_simplicial_object
      ε
      δ
      (adjunction_iteratedEndofunctor_hσδ₀ adj)
      (adjunction_iteratedEndofunctor_hσδ₁ adj)
      (adjunction_iteratedEndofunctor_hσσ adj)

end

end CategoryTheory
