import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.CommSq
import stacks_project.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

open scoped nonZeroDivisors
open CategoryTheory CommRingCat

universe u

/- Source note: `0GLQ` is the current Stacks section tag for Section `15.117`, and the
principal-power quotient lifting statement formalized below is that section's Lemma `15.117.3`.
This avoids reading `0GLQ` as a lemma-number tag. The historical tag `09ER` is the older
weakly-unramified totally-ramified base-change lemma, which is already formalized in
`Lemma_15_116_3`. -/

/- Domain-style sampling for Lemma 15.117.3:
- primary domain: principal-power quotients and canonical localization-away comparison maps for
  finite injective extensions;
- sampled owner declarations:
  `principalIdeal`,
  `principalPowerIdeal`,
  `principalPowerIdealReductionMap`,
  `CommRingCat.ofHom`,
  `CategoryTheory.CommSq`,
  `Localization.awayMapₐ`;
- best owner abstraction:
  the chapter owners `principalIdeal` and `principalPowerIdeal` for the source-facing quotient
  rings, together with the canonical localization-away map
  `Localization.awayMapₐ (Algebra.ofId A' A) f` expressing the textbook comparison `A'_f → A_f`,
  while quotient-map compatibility is the canonical commuting-square owner
  `CategoryTheory.CommSq`, with the ring maps viewed through `CommRingCat.ofHom`;
- primitive data:
  the principal ideals, the quotient reduction map from modulo `x^n` to modulo the image of `x`,
  and the injective extension together with the canonical away-localization map;
- derived API:
  the source-facing quotient square, together with the final eventual-existence
  theorem using the explicit generator condition on power quotients.

Source/core/bridge triage:
- `source-facing`: the final eventual-existence theorem;
- `core/canonical`: `principalIdeal`, `principalPowerIdeal`,
  `principalPowerIdeal_le_comap_principalIdeal`, `principalPowerIdealReductionMap`,
  `CategoryTheory.CommSq`, and `Localization.awayMapₐ`;
- `bridge/view`: the quotient commuting square expressed by
  `principalPowerIdealReductionMap`. -/

section

variable {A' A : Type u}
variable [CommRing A'] [CommRing A] [Algebra A' A] [Module.Finite A' A]

-- Proof sketch: choose `t > 0` with `f ^ t A ⊆ A'` using finiteness of `A` over `A'` and
-- bijectivity of the canonical map `A'_f → A_f`, then take a positive threshold `n₀ = 2 * t`.
-- For `n ≥ n₀`,
-- transport the image of `f ^ t A` through `φ'` to construct a finite `B'`-subalgebra
-- `B ⊆ B'[1 / g]`, and compare the induced quotients modulo `f` and `g` in `CommRingCat`.
/-- Stacks Lemma 15.117.3 in Section `0GLQ`: if `A` is finite over `A'`, the image of `f` is a
nonzerodivisor on `A`, and the canonical localized map `A'_f → A_f` is bijective, then for all
sufficiently large positive integers `n` every isomorphism `A' / (f^n) ≃ B' / (g^n)` sending the
class of `f` to the class of `g` lifts to an injective finite extension `B' ⊆ B` together with a
compatible isomorphism
`A / (f) ≃ B / (g)`. -/
theorem exists_eventual_finite_extension_and_quotientIso_lift_of_power_quotientIso
    (f : A')
    (hinj : Function.Injective (algebraMap A' A))
    (hf : algebraMap A' A f ∈ nonZeroDivisors A)
    (hAway : Function.Bijective (Localization.awayMapₐ (Algebra.ofId A' A) f)) :
    ∃ n0 : ℕ+, ∀ ⦃n : ℕ+⦄, (hn : n0 ≤ n) →
        ∀ {B' : Type u} [CommRing B']
          (g : B') (hg : g ∈ nonZeroDivisors B')
          (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
          (hgen : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g),
            ∃ (B : Type u) (_ : CommRing B) (_ : Algebra B' B)
              (_ : Function.Injective (algebraMap B' B))
              (_ : Module.Finite B' B)
              (φ : A ⧸ principalIdeal (algebraMap A' A f) ≃+*
                B ⧸ principalIdeal (algebraMap B' B g)),
              CommSq
                (ofHom <|
                  principalPowerIdealReductionMap (algebraMap A' A) f
                    (Nat.succ_le_of_lt n.2))
                (ofHom φ'.toRingHom)
                (ofHom φ.toRingHom)
                (ofHom <|
                  principalPowerIdealReductionMap (algebraMap B' B) g
                    (Nat.succ_le_of_lt n.2)) := sorry

end
