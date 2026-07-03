import Mathlib
import stacks_project.Chap15.Lemma_15_15_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {N : Type v} [AddCommGroup N] [Module R N] [Module.Projective R N]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module.Projective R M]

/- Domain triage:
- primary domain: universal injectivity of linear maps between projective modules over a
  commutative ring;
- sampled owner declarations:
  `LinearMap.UniversallyInjective`,
  `LinearMap.universallyInjective_iff_injective_mod_finite_ideal`,
  `proper_fg_ideal_annihilator_ne_bot_tfae`;
- best owner abstraction: `LinearMap.UniversallyInjective`;
- primitive data: the ring `R`, the projective modules `N` and `M`, and a linear map `u : N →ₗ[R] M`;
- derived API: the source-facing criterion below, with the `injective → universallyInjective`
  direction obtained canonically from clause `(1) ↔ (2)` of
  `proper_fg_ideal_annihilator_ne_bot_tfae`.

Layering:
- `source-facing`: the theorem below;
- `core/canonical`: `LinearMap.UniversallyInjective`;
- `bridge/view`: `proper_fg_ideal_annihilator_ne_bot_tfae`.
-/

-- Proof sketch: the forward implication holds for any ring by taking the tensor factor `Q = R`.
-- For the converse, use projectivity to split both source and target off free modules, reduce to
-- finite free source by expressing a projective module as a filtered colimit of finite free
-- modules, and then prove the finite free case by induction on the rank using property `(P)` to
-- split off the first basis vector.
/-- Lemma 15.15.3: if `R` has property `(P)` of Lemma 15.15.2, meaning every proper finitely
generated ideal of `R` has nonzero annihilator, then a homomorphism `u : N →ₗ[R] M` of
projective `R`-modules is universally injective if and only if it is injective. -/
theorem universallyInjective_iff_injective_of_projective_of_proper_fg_ideal_annihilator_ne_bot
    (hP : ∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R)) (u : N →ₗ[R] M) :
    u.UniversallyInjective ↔ Function.Injective u := by
  constructor
  · intro hu
    sorry
  · intro hu
    exact
      (proper_fg_ideal_annihilator_ne_bot_iff_injective_projective_maps_universallyInjective.mp
        hP) u hu

end

end LinearMap
