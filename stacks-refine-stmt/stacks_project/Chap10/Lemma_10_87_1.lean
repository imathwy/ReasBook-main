import Mathlib
import stacks_project.Chap10.Lemma_10_86_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

variable {R : Type u} [Ring R]

local notation "ModuleInverseSystem" => OrderDual ℕ+ ⥤ ModuleCat R

-- Domain-style sampling:
-- * source-facing layer: short exact sequences of inverse systems of `R`-modules over `ℕ+`.
-- * core/canonical owner: `CategoryTheory.Functor.IsMittagLeffler` on the underlying
--   `Type`-valued inverse system, together with
--   `inverseSystem_limit_shortExact_of_countable_and_isMittagLeffler_left`.
-- * relevant sampled declarations:
--   `CategoryTheory.Functor.IsMittagLeffler`,
--   `CategoryTheory.Functor.isMittagLeffler_iff_eventualRange`,
--   `CategoryTheory.Functor.IsMittagLeffler.toPreimages`,
--   `inverseSystem_limit_shortExact_of_countable_and_isMittagLeffler_left`.
-- * primitive data: a short exact sequence of module inverse systems and the owner
--   Mittag-Leffler hypothesis on the left term.
-- * bridge/view output: short exactness after applying the inverse-limit functor on `ModuleCat R`.
--
-- Proof sketch: this is the module-valued bridge specialization of Lemma `10.86.4`. Apply that
-- inverse-limit short-exactness theorem to the underlying inverse system of abelian groups
-- attached to the short exact sequence of `R`-modules; the owner hypothesis here is unchanged,
-- namely the canonical `Functor.IsMittagLeffler` condition on the underlying `Type`-valued left
-- inverse system.
/-- Lemma 10.87.1: for a short exact sequence of inverse systems of `R`-modules over `ℕ+`, if the
left system is Mittag-Leffler, then the induced sequence on inverse limits
`0 ⟶ \varprojlim K_i ⟶ \varprojlim L_i ⟶ \varprojlim M_i ⟶ 0`
is short exact. -/
theorem moduleInverseLimit_shortExact_of_isMittagLeffler_left
    (S : ShortComplex ModuleInverseSystem)
    (hS : S.ShortExact)
    (hML : (S.X₁ ⋙ forget (ModuleCat R)).IsMittagLeffler) :
    (S.map (lim : ModuleInverseSystem ⥤ ModuleCat R)).ShortExact := sorry
