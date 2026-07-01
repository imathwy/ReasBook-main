import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u₁ u₂ v₁ v₂ u

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {F : C ⥤ D} [Functor.IsContinuous F J K]
variable {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
variable (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
variable [(SheafOfModules.pushforward φ).IsRightAdjoint]

/-
Domain-style sampling for Lemma 18.14.3:
- primary domain: pullback/pushforward of sheaves of modules along a morphism of ringed sites or
  ringed topoi, together with the generic exact-functor owners `leftExactFunctor` and
  `rightExactFunctor`;
- sampled owner declarations:
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `leftExactFunctor`,
  `rightExactFunctor`;
- best owner abstraction: the adjunction
  `SheafOfModules.pullbackPushforwardAdjunction φ`,
  together with the owner-level exactness predicates and the adjoint-preserves-(co)limits
  instances;
- primitive data: only the ring-sheaf morphism `φ`, with the right-adjoint structure on
  `SheafOfModules.pushforward φ`;
- derived API: preservation of limits/colimits and the bundled left/right exactness predicates for
  `SheafOfModules.pushforward φ` and `SheafOfModules.pullback φ`.

Source/core/bridge triage:
- `source-facing`: the four clauses asserting that `f_*` preserves limits and is left exact, and
  that `f^*` preserves colimits and is right exact;
- `core/canonical`: `SheafOfModules.pullbackPushforwardAdjunction φ` together with the generic
  owners `leftExactFunctor` and `rightExactFunctor`;
- `bridge/view`: the direct `#check` / `#synth` queries below, with no parallel local theorem API.
-/

/- Lemma 18.14.3 (1): the direct-image functor `f_*` on sheaves of modules is left exact. -/
#check
  (show leftExactFunctor (SheafOfModules R) (SheafOfModules S) (SheafOfModules.pushforward φ) from
    by
      simpa [leftExactFunctor_iff] using
        (inferInstance : PreservesFiniteLimits (SheafOfModules.pushforward φ)))

/- Lemma 18.14.3 (2): in fact, the direct-image functor `f_*` on sheaves of modules commutes with
all limits. -/
#synth PreservesLimits (SheafOfModules.pushforward φ)

/- Lemma 18.14.3 (3): the inverse-image functor `f^*` on sheaves of modules is right exact. -/
#check
  (show rightExactFunctor (SheafOfModules S) (SheafOfModules R) (SheafOfModules.pullback φ) from
    by
      simpa [rightExactFunctor_iff] using
        (inferInstance : PreservesFiniteColimits (SheafOfModules.pullback φ)))

/- Lemma 18.14.3 (4): in fact, the inverse-image functor `f^*` on sheaves of modules commutes
with all colimits. -/
#synth PreservesColimits (SheafOfModules.pullback φ)
