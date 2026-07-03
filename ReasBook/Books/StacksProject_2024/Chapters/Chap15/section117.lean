import Mathlib
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.CategoryTheory.CommSq
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_117_1 (from Chap15) -/
universe u v w x y z

/-
Domain-style sampling for Lemma 15.117.1:
- primary domain: finite tower stability of the Chapter 15 solution predicate for extensions of
  discrete valuation rings, with branchwise formal smoothness on reduced tensor-product integral
  closures;
- sampled owner declarations:
  `IsSolutionFor`,
  `formallySmoothForAdic_localization_baseChange_integralClosure`,
  `Localization.localRingHom`,
  `RingHom.formally_smooth_for_adic`;
- best owner abstraction: the source-facing theorem should remain stated directly with the owner
  predicate `IsSolutionFor`; the localized branch formal-smoothness statement is derived API and
  should be reused from `Lemma_15_115_3` rather than rebuilt through a local branch wrapper;
- primitive-vs-derived split: the primitive data are the DVR extension `A ⊂ B`, the fraction
  fields `K ⊂ L`, and the finite tower `K ⊂ K₁ ⊂ K₂`; the branch localizations and their
  formal-smoothness properties are derived API.

Source/core/bridge triage:
- `source-facing`: `solutionFor_of_finite_extension`;
- `core/canonical`: `IsSolutionFor`, `Localization.localRingHom`,
  `RingHom.formally_smooth_for_adic`;
- `bridge/view`: `formallySmoothForAdic_localization_baseChange_integralClosure`.
-/

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y} {K2 : Type z}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field K1] [Algebra K K1] [Algebra A K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]
variable [Field K2] [Algebra K1 K2] [Algebra K K2] [Algebra A K2]
variable [IsScalarTower K K1 K2] [IsScalarTower A K K2] [IsScalarTower A K1 K2]
variable [FiniteDimensional K1 K2]

-- Proof sketch: for each maximal branch of the integral-closure base change over `K1 / K`, the
-- hypothesis gives formal smoothness of the corresponding localized extension. Apply
-- Lemma `15.115.3` to each such localized map after the finite extension `K2 / K1`; this yields
-- formal smoothness for every branch over `K2 / K`, which is exactly the definition of being a
-- solution.
/-- Lemma 15.117.1: if `K₁ / K` is a solution for the extension `A ⊂ B` of discrete valuation
rings, then every finite extension `K₂ / K₁` is again a solution for `A ⊂ B`, viewed as a finite
extension of `K`. -/
theorem solutionFor_of_finite_extension
    (hK1 : IsSolutionFor A B K L K1) :
    IsSolutionFor A B K L K2 := sorry

end

/-! ### Lemma_15_117_2 (from Chap15) -/
universe u v

/-
Domain-style sampling for Lemma 15.117.2:
- primary domain: Nagata and `N-2` descent for extensions of discrete valuation rings through
  finite purely inseparable fraction-field tests and faithfully flat finite descent;
- sampled owner declarations in this domain:
  `IsExtensionOfDiscreteValuationRings`,
  `NagataRing`,
  `IsN2Ring`,
  `nagataRing_iff_isN2Ring_of_isDiscreteValuationRing`,
  `IsN2Ring.integralClosure_finite_of_finiteDimensional`,
  `isN2Ring_iff_integralClosure_finite_for_finite_purelyInseparable_extensions`,
  `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`,
  `reducedTensorBaseChangeIntegralClosureMap`,
  `integralClosure_isDiscreteValuationRing_of_finite_purelyInseparable`;
- best owner abstraction: the source-facing theorem should stay stated for
  `IsExtensionOfDiscreteValuationRings A B`, while the core/canonical companion below should land
  in `IsN2Ring A`; the source-facing Nagata statement is then derived from the DVR equivalence
  `NagataRing A ↔ IsN2Ring A` instead of introducing a parallel local wrapper;
- primitive data: the two discrete valuation rings, their extension structure, the Nagata
  hypothesis on `B`, and the separability of the induced fraction-field extension;
- derived API: finite normalization over the Nagata target, the `N-2` reformulation on DVRs, the
  purely inseparable integral-closure test, the DVR structure on those integral closures, and
  faithful-flat finite descent.

Source/core/bridge triage:
- `source-facing`: the theorem below, which is the textbook Nagata descent statement for DVR
  extensions;
- `core/canonical`: `IsExtensionOfDiscreteValuationRings`, `NagataRing`, `IsN2Ring`, and
  `integralClosure`;
- `bridge/view`: finite normalization over Nagata rings, the Chapter 10 equivalence between
  Nagata and `N-2` for DVRs, and the faithfully flat finite-descent theorem for tensor base
  change.
-/

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]

attribute [local instance]
  FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

namespace IsExtensionOfDiscreteValuationRings

variable [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

-- Proof sketch: by Example `10.162.17 (1)`, a discrete valuation ring is Nagata exactly when it
-- is `N-2`. Let `K1 / FractionRing A` be a finite purely inseparable extension. Convert the
-- Nagata hypothesis on `B` to the canonical owner `[IsN2Ring B]`, so
-- `IsN2Ring.integralClosure_finite_of_finiteDimensional` gives finite normalization over `B`
-- in the generic fiber `FractionRing B ⊗[FractionRing A] K1`, which is a field because a
-- separable extension and a finite purely inseparable extension are linearly disjoint. The
-- reduced tensor-product comparison map from Remark `15.115.1` packages the corresponding
-- base-changed normalization canonically. The integral closure of `A` in `K1` base changes into
-- this finite `B`-algebra, and faithful flatness of the extension of discrete valuation rings `A → B`
-- descends module-finiteness back to `A`. Applying Lemma `10.161.12` again gives that `A` is
-- `N-2`, hence Nagata.
variable (A B) in
/-- Core companion to Lemma 15.117.2: with the canonical `N-2` owner hypothesis on the target
discrete valuation ring, the source discrete valuation ring is also `N-2`. -/
theorem isN2Ring_of_separable_fractionRingExtension
    [IsN2Ring B]
    : IsN2Ring A := by
  sorry

variable (A B) in
/-- Lemma 15.117.2: for an extension `A ⊆ B` of discrete valuation rings, if `B` is a Nagata ring
and the induced extension of fraction fields `FractionRing B / FractionRing A` is separable, then
`A` is a Nagata ring. This is the source-facing reformulation of the preceding canonical
`IsN2Ring` companion using the DVR equivalence `NagataRing A ↔ IsN2Ring A`. -/
theorem nagataRing_of_separable_fractionRingExtension
    [NagataRing B]
    : NagataRing A := by
  haveI : IsN2Ring B := (nagataRing_iff_isN2Ring_of_isDiscreteValuationRing B).mp inferInstance
  have hA : IsN2Ring A := isN2Ring_of_separable_fractionRingExtension A B
  exact
    (nagataRing_iff_isN2Ring_of_isDiscreteValuationRing A).mpr
      hA

end IsExtensionOfDiscreteValuationRings

end

/-! ### Lemma_15_117_3 (from Chap15) -/
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

/-! ### Remark_15_117_4 (from Chap15) -/
open scoped nonZeroDivisors
open CategoryTheory CommRingCat

universe u

/- Domain-style sampling for Remark 15.117.4:
- primary domain: functoriality of compatible principal-quotient lifts in finite commutative
  algebra;
- sampled owner declarations:
  `principalPowerIdealQuotientMap`,
  `principalIdealQuotientMap`,
  `CommRingCat.ofHom`,
  `CategoryTheory.CommSq`,
  `exists_eventual_finite_extension_and_quotientIso_lift_of_power_quotientIso`;
- best owner abstraction: the source-facing lift owner is already
  `CategoryTheory.CommSq`, and the functorial comparison data should be expressed by the owner-file
  bridge `principalPowerIdealQuotientMap` together with the canonical quotient maps on first-power
  quotients, rather than by a parallel local comparison wrapper;
- primitive data: the two lifted target rings, the quotient isomorphisms modulo the first powers,
  the comparison ring map fitting into a commutative square over `β'`, and the induced commuting
  quotient square;
- derived API: only the eventual-existence theorem below.

Source/core/bridge triage:
- `source-facing`: the eventual existence theorem for functorial compatible lifts;
- `core/canonical`: `principalPowerIdealQuotientMap`, `principalIdealQuotientMap`, and
  `CategoryTheory.CommSq` together with `CommRingCat.ofHom`;
- `bridge/view`: the quotient squares induced by the principal-power quotient bridge maps. -/

section PrincipalQuotientLiftFunctoriality

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S]

section

variable {R' : Type u} {S' : Type u} [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R' S']

private theorem map_algebraMap_eq_of_commSq
    (σ : S →+* S') (τ : R →+* R')
    (hsq :
      CommSq
        (ofHom (algebraMap R S))
        (ofHom τ)
        (ofHom σ)
        (ofHom (algebraMap R' S')))
    (x : R) :
    σ (algebraMap R S x) = algebraMap R' S' (τ x) := by
  simpa [CommRingCat.hom_comp, RingHom.comp_apply] using congr(($hsq.w) x)

end

section

variable {A₁' : Type u} {A₂' : Type u} {A₁ : Type u} {A₂ : Type u}
variable {B₁' : Type u} {B₂' : Type u} {C₁ : Type u} {C₂ : Type u}
variable [CommRing A₁'] [CommRing A₂'] [CommRing A₁] [CommRing A₂]
variable [CommRing B₁'] [CommRing B₂'] [CommRing C₁] [CommRing C₂]
variable [Algebra A₁' A₁] [Algebra A₂' A₂]
variable [Algebra B₁' C₁] [Algebra B₂' C₂]

-- Proof sketch: take the positive lower bounds `n₀,₁` and `n₀,₂` from the preceding lifting
-- theorem `exists_eventual_finite_extension_and_quotientIso_lift_of_power_quotientIso` for the two
-- pairs `(A₁' ⊆ A₁, f)` and `(A₂' ⊆ A₂, α'(f))`. For every positive `n` above both bounds, apply
-- that theorem to the lower and upper horizontal isomorphisms. Its construction of the lifted
-- finite extensions is
-- functorial from the commutative square modulo `f^n`, so the two outputs are connected by a ring
-- map fitting into a commutative square over `β'`, and the induced square modulo `f` and `g`
-- commutes.
/-- Remark 15.117.4: the construction of the preceding lifting theorem, formalizing Stacks
Lemma `15.117.3` in Section `0GLQ`, is functorial for a commutative square `A₁' → A₂'`,
`A₁ → A₂` and a compatible commutative square of quotient isomorphisms modulo `f^n` and `g^n`.
After replacing the two lower bounds supplied by
`exists_eventual_finite_extension_and_quotientIso_lift_of_power_quotientIso` for
`(A₁' ⊆ A₁, f)` and `(A₂' ⊆ A₂, α'(f))` by their maximum, every sufficiently large positive
integer `n` admits finite extensions over `B₁'` and `B₂'`, compatible quotient lifts modulo `f`
and `g`, a comparison morphism fitting into a commutative square over `β'`, and the induced
commutative square on the quotients modulo `f` and `g`. -/
theorem exists_functorial_principalQuotientLifts_of_power_quotientIso_square
    [Module.Finite A₁' A₁] [Module.Finite A₂' A₂]
    (α' : A₁' →+* A₂') (α : A₁ →+* A₂)
    (sqA :
      CommSq
        (ofHom (algebraMap A₁' A₁))
        (ofHom α')
        (ofHom α)
        (ofHom (algebraMap A₂' A₂)))
    (f : A₁')
    (hA₁_injective : Function.Injective (algebraMap A₁' A₁))
    (hA₂_injective : Function.Injective (algebraMap A₂' A₂))
    (hf₁ : algebraMap A₁' A₁ f ∈ nonZeroDivisors A₁)
    (hf₂ : algebraMap A₂' A₂ (α' f) ∈ nonZeroDivisors A₂)
    (hAway₁ : Function.Bijective (Localization.awayMapₐ (Algebra.ofId A₁' A₁) f))
    (hAway₂ : Function.Bijective (Localization.awayMapₐ (Algebra.ofId A₂' A₂) (α' f))) :
    ∃ n₀ : ℕ+, ∀ {n : ℕ+} (hn : n₀ ≤ n),
        ∀ (β' : B₁' →+* B₂') (g : B₁')
          (hg₁ : g ∈ nonZeroDivisors B₁') (hg₂ : β' g ∈ nonZeroDivisors B₂')
          (φ₁' : A₁' ⧸ principalPowerIdeal f n ≃+* B₁' ⧸ principalPowerIdeal g n)
          (φ₂' : A₂' ⧸ principalPowerIdeal (α' f) n ≃+*
            B₂' ⧸ principalPowerIdeal (β' g) n)
          (hgen : φ₁' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
          (hsquare :
            CommSq
              (ofHom <| principalPowerIdealQuotientMap α' f rfl n)
              (ofHom φ₁'.toRingHom)
              (ofHom φ₂'.toRingHom)
              (ofHom <| principalPowerIdealQuotientMap β' g rfl n)),
              ∃ (C₁ : Type u) (_ : CommRing C₁) (_ : Algebra B₁' C₁)
                (_ : Function.Injective (algebraMap B₁' C₁))
                (_ : Module.Finite B₁' C₁)
                (φ₁ : A₁ ⧸ principalIdeal (algebraMap A₁' A₁ f) ≃+*
                  C₁ ⧸ principalIdeal (algebraMap B₁' C₁ g)),
                CommSq
                  (ofHom <|
                    principalPowerIdealReductionMap (algebraMap A₁' A₁) f (Nat.succ_le_of_lt n.2))
                  (ofHom φ₁'.toRingHom)
                  (ofHom φ₁.toRingHom)
                  (ofHom <|
                    principalPowerIdealReductionMap (algebraMap B₁' C₁) g (Nat.succ_le_of_lt n.2))
                  ∧
                ∃ (C₂ : Type u) (_ : CommRing C₂) (_ : Algebra B₂' C₂)
                  (_ : Function.Injective (algebraMap B₂' C₂))
                  (_ : Module.Finite B₂' C₂)
                  (φ₂ : A₂ ⧸ principalIdeal (algebraMap A₂' A₂ (α' f)) ≃+*
                    C₂ ⧸ principalIdeal (algebraMap B₂' C₂ (β' g)))
                  (β : C₁ →+* C₂)
                  (sqβ :
                    CommSq
                      (ofHom (algebraMap B₁' C₁))
                      (ofHom β')
                      (ofHom β)
                      (ofHom (algebraMap B₂' C₂))),
                  CommSq
                    (ofHom <|
                      principalPowerIdealReductionMap (algebraMap A₂' A₂) (α' f)
                        (Nat.succ_le_of_lt n.2))
                    (ofHom φ₂'.toRingHom)
                    (ofHom φ₂.toRingHom)
                    (ofHom <|
                      principalPowerIdealReductionMap (algebraMap B₂' C₂) (β' g)
                        (Nat.succ_le_of_lt n.2)) ∧
                    CommSq
                      (ofHom <|
                        principalIdealQuotientMap α (algebraMap A₁' A₁ f)
                          (map_algebraMap_eq_of_commSq α α' sqA f))
                      (ofHom φ₁.toRingHom)
                      (ofHom φ₂.toRingHom)
                      (ofHom <|
                        principalIdealQuotientMap β (algebraMap B₁' C₁ g)
                          (map_algebraMap_eq_of_commSq β β' sqβ g)) := sorry

end

end PrincipalQuotientLiftFunctoriality

/-! ### Lemma_15_117_5 (from Chap15) -/
open scoped TensorProduct

universe u v w x y z

/-
Domain-style sampling for Lemma 15.117.5:
- primary domain: Epp-style elimination of inseparability for solution fields of extensions of
  discrete valuation rings;
- sampled owner declarations:
  `IsSolutionFor`,
  `IsSeparableSolutionFor`,
  `solutionFor_of_finite_extension`,
  `exists_separableSolution_of_exists_solution`;
- best owner abstraction: the source-facing content here is still the intermediate-field theorem,
  but its solution predicate should be the chapter owner `IsSolutionFor` from
  `Definition_15_116_1`; `IsSeparableSolutionFor` is only companion API because the source asks
  for `K₃ / K₁` to be separable, not necessarily `K₃ / K`;
- primitive-vs-derived split: the primitive data are the DVR extension `A ⊂ B`, its fraction
  fields `K ⊂ L`, the tower `K ⊂ K₁ ⊂ K₂`, and the hypotheses on separability, Nagata-ness, and
  purely inseparable degree; the characteristic-`p` consequence of a purely inseparable extension
  of degree `p` is derived theorem data, not a primitive ambient assumption; the conclusion that
  `K₃` remains a solution is expressed through the owner predicate `IsSolutionFor`, while the
  `K₁`-separability of `K₃` is derived theorem data, not a new owner.

Source/core/bridge triage:
- `source-facing`: the existence of a finite extension `K₃ / K₁` that is separable over `K₁` and
  still solves `A ⊂ B`;
- `core/canonical`: `IsSolutionFor`;
- `bridge/view`: `IsSeparableSolutionFor`, which packages the stronger special case of
  separability over the base field `K`.
-/

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y} {K2 : Type z}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field K1] [Algebra K K1] [Algebra A K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]
variable [Field K2] [Algebra K1 K2] [Algebra K K2] [Algebra A K2]
variable [IsScalarTower K K1 K2] [IsScalarTower A K K2] [IsScalarTower A K1 K2]
variable [FiniteDimensional K1 K2]
variable {p : ℕ} [Fact p.Prime]
variable [Algebra.IsSeparable K L] [NagataRing B] [IsPurelyInseparable K1 K2]

-- Proof sketch: start from the given solution over the purely inseparable degree-`p` extension
-- `K₂ / K₁`, use the Nagata and separability hypotheses to compare the integral closures after
-- base change, and then perform the Artin-Schreier deformation argument from the textbook to
-- replace the radicial extension by a finite separable extension `K₃ / K₁` while preserving the
-- solution property for `A ⊂ B`.
/-- Lemma 15.117.5: let `A ⊂ B` be an extension of discrete valuation rings with fraction fields
`K ⊂ L`, let `K₂ / K₁ / K` be a tower of finite field extensions, and assume `L / K` is
separable, `B` is Nagata, `p` is prime, `K₂ / K₁` is purely inseparable of degree `p`, and
`K₂ / K` is a solution for `A ⊂ B`. Then there exists a finite separable extension `K₃ / K₁`
such that
`K₃ / K` is again a solution for `A ⊂ B` in the sense of Definition `15.116.1`. -/
theorem exists_separable_solution_of_solution_of_purelyInseparable_degree_eq_prime
    (hK2 : IsSolutionFor A B K L K2)
    (hdeg : Module.finrank K1 K2 = p) :
    ∃ (K3 : Type (max u v w x y z)) (_ : Field K3) (_ : Algebra A K3) (_ : Algebra K K3)
      (_ : IsScalarTower A K K3) (_ : Algebra K1 K3) (_ : IsScalarTower K K1 K3)
      (_ : FiniteDimensional K1 K3) (_ : Algebra.IsSeparable K1 K3),
      IsSolutionFor A B K L K3 := sorry

end

/-! ### Lemma_15_117_6 (from Chap15) -/
universe u v w x

/- Domain-style sampling for Lemma 15.117.6:
- primary domain: Epp-style elimination of inseparability for solution fields of extensions of
  discrete valuation rings;
- sampled owner declarations:
  `IsSolutionFor`,
  `IsSeparableSolutionFor`,
  `solutionFor_of_finite_extension`,
  `exists_separable_solution_of_solution_of_purelyInseparable_degree_eq_prime`;
- best owner abstraction: the source-facing content is the existence upgrade from a solution to a
  separable solution, and the chapter owners from `Definition_15_116_1` already capture exactly
  that distinction; this file should therefore state the hypothesis and conclusion directly with
  `IsSolutionFor` and `IsSeparableSolutionFor`, rather than introducing a parallel wrapper for
  “having a solution”;
- primitive-vs-derived split: the primitive data are the DVR extension `A ⊂ B`, the fraction
  fields `K ⊂ L`, the separability of `L / K`, the Nagata hypothesis on `B`, and the existence of
  one finite solution field; the conclusion that one may choose such a field separable over `K`
  is derived API, recorded by `IsSeparableSolutionFor`.

Source/core/bridge triage:
- `source-facing`: the existence theorem upgrading an arbitrary solution to a separable one;
- `core/canonical`: `IsSolutionFor` and `IsSeparableSolutionFor`;
- `bridge/view`: the induction step through
  `exists_separable_solution_of_solution_of_purelyInseparable_degree_eq_prime` and stability under
  finite extension via `solutionFor_of_finite_extension`. -/

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [NagataRing B]

-- Proof sketch: choose a solution `K₂ / K` for `A ⊂ B` and argue by induction on the
-- inseparable degree `Field.insepDegree K K₂`. If this degree is `1`, the given solution is
-- already separable. Otherwise, factor `K₂ / K` through an intermediate field `K₁` with
-- `K₂ / K₁` purely inseparable of prime degree, apply Lemma `15.117.5` to replace `K₂` by a
-- separable solution over `K₁`, and use multiplicativity of inseparable degree to decrease the
-- induction parameter.
/-- Lemma 15.117.6: for an extension `A ⊂ B` of discrete valuation rings with fraction fields
`K ⊂ L`, if `L / K` is separable, `B` is Nagata, and there exists a solution for `A ⊂ B`, then
there exists a separable solution for `A ⊂ B`. -/
theorem exists_separableSolution_of_exists_solution
    (hsepKL : Algebra.IsSeparable K L)
    (hsol :
      ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
        (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
        IsSolutionFor A B K L K1) :
    ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsSeparableSolutionFor A B K L K1 := sorry

end

/-! ### Lemma_15_117_7 (from Chap15) -/
open scoped TensorProduct
open PrimeSpectrum

universe u v w x y

noncomputable section

/-
Domain-style sampling for Lemma 15.117.7:
- primary domain: reduced tensor-product base change for extensions of discrete valuation rings,
  together with the canonical comparison map from the base-changed integral closure `A'` to `B'`;
- sampled owner declarations:
  `reducedTensorBaseChangeIntegralClosureMap`,
  `reducedTensorBaseChangeIntegralClosure_isDedekindRing`,
  `primeSpectrumComap_surjective_of_reducedTensorBaseChangeIntegralClosure`,
  `Algebra.finite_of_essFiniteType_of_isAlgebraic`;
- best owner abstraction: the `core/canonical` owner is the comparison map
  `reducedTensorBaseChangeIntegralClosureMap` from Remark `15.115.1`; the three numbered clauses
  here are `source-facing` consequences of that owner;
- primitive data: the DVR extension `A ⊆ B`, the fraction fields `K ⊆ L`, the algebraic base
  change field `K' / K`, and the source hypothesis that the integral closure `A'` is Noetherian;
- derived API: Noetherian consequences for `B'`, the induced surjection on spectra, and the
  residue-field finite-type statement via the canonical residue-field algebra.

Source/core/bridge triage:
- `source-facing`: the Noetherian conclusion in clause `(1)` and the residue-field finiteness
  statement in clause `(3)`, both under the ambient source hypothesis `[IsNoetherianRing A']`;
- `core/canonical`: the map `reducedTensorBaseChangeIntegralClosureMap`, the owner theorem
  `reducedTensorBaseChangeIntegralClosure_isDedekindRing`, and its spectrum-surjectivity companion
  `primeSpectrumComap_surjective_of_reducedTensorBaseChangeIntegralClosure`;
- `bridge/view`: clause `(2)` is exact-interface reuse of that upstream spectrum-surjectivity
  theorem, reused inside the source-faithful Noetherian context rather than through a duplicate
  local shell; clause `(3)` should be derived from the canonical residue-field finiteness owner,
  with the induced
  `κ(comap q)`-algebra structure on `κ(q)` kept as proof-local scaffolding rather than as the main
  public datum.
-/

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K' : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B] [Algebra.EssFiniteType A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra B L] [Algebra A L] [Algebra K L]
variable [IsFractionRing B L] [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field K'] [Algebra A K'] [Algebra K K'] [IsScalarTower A K K']
variable [Algebra.IsAlgebraic K K']

local notation "A'" => integralClosure A K'
local notation "L'" => (L ⊗[K] K') ⧸ nilradical (L ⊗[K] K')
local notation "B'" => integralClosure B L'

local instance l'CommRing : CommRing L' :=
  Ideal.Quotient.commRing _

-- Proof sketch: write `B` as a localization of a finite type `A`-algebra, choose a finite
-- subextension `K₀ / K` inside `K' / K` containing the coefficients of a finite presentation
-- after base change, and descend the reduced tensor-product normalization to that finite stage.
-- The corresponding normalization over `K₀` is Noetherian by the finite base-change case of
-- Remark `15.115.1`; base change back to `K'` then recovers `B'`.
section BaseChange

section

/-- Lemma 15.117.7 (1): if `A → B` is an essentially finite type extension of discrete valuation
rings, `K'/K` is algebraic, and the integral closure `A'` of `A` in `K'` is Noetherian, then the
integral closure `B'` of `B` in `L' = (L ⊗[K] K')_red` is Noetherian. -/
theorem isNoetherianRing_integralClosure_of_reducedTensorProduct_baseChange
    (hA' : IsNoetherianRing (integralClosure A K'))
    : IsNoetherianRing B' := by
  sorry

-- Proof sketch: clause `(2)` is already the upstream owner theorem for the canonical map
-- `reducedTensorBaseChangeIntegralClosureMap : A' → B'` from Remark `15.115.1`, so the present
-- file should keep it as a direct recall rather than rebuilding a parallel local statement.
/- Lemma 15.117.7 (2): under the same Noetherian hypothesis on `A'`, the induced map
`Spec(B') → Spec(A')` is the upstream owner theorem
`primeSpectrumComap_surjective_of_reducedTensorBaseChangeIntegralClosure`. -/
recall primeSpectrumComap_surjective_of_reducedTensorBaseChangeIntegralClosure

/- Proof sketch: the canonical map `A' → B'` from Remark `15.115.1` is integral, so for every
prime `q` of `B'` the induced residue-field extension `κ(q ∩ A') → κ(q)` is algebraic. Since the
same residue-field map is also essentially of finite type by the canonical prime-residue-field
owner, the field-level theorem `Algebra.finite_of_essFiniteType_of_isAlgebraic` makes it module
finite, hence finite type. -/
/-- Lemma 15.117.7 (3): under the same hypotheses, including that `A'` is Noetherian, for every
prime `q` of `B'`, the corresponding residue field extension `κ(q) / κ(q ∩ A')` is finitely
generated. -/
theorem residueField_finiteType_of_reducedTensorProduct_baseChange
    (hA' : IsNoetherianRing (integralClosure A K'))
    (q : PrimeSpectrum B') :
    Algebra.FiniteType (q.asIdeal.under A').ResidueField q.asIdeal.ResidueField := by
  sorry

end

end BaseChange

end

/-! ### Proposition_15_117_8 (from Chap15) -/
open scoped TensorProduct

universe u v w x

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B] [Algebra.EssFiniteType A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]

-- Proof sketch: follow the textbook argument by first applying Epp's theorem to obtain a finite
-- weak solution after passing to a DVR with perfect residue field, use Lemma `15.112.5` to
-- identify weak solutions with solutions over the perfect-residue-field base, and then descend
-- the resulting formally smooth local branches to a finite stage using Lemma `15.117.7` and the
-- finite-type hypothesis on `B`.
/-- Proposition 15.117.8: if `A ⊂ B` is an essentially finite type extension of discrete valuation
rings with fraction fields `K ⊂ L`, then there exists a finite extension `K₁ / K` which is a
solution for `A ⊂ B` in the sense of Definition `15.116.1`. -/
theorem exists_finite_extension_solution_of_essentiallyFiniteType :
    ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsSolutionFor A B K L K1 := sorry

end

/-! ### Lemma_15_117_9 (from Chap15) -/
open scoped TensorProduct

universe u v w x

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B] [Algebra.EssFiniteType A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]

-- Proof sketch: if `A` is Nagata, then `B` is Nagata because an essentially finite type algebra
-- over a Nagata ring is again Nagata after passing through a finite type model and localizing.
-- With `B` Nagata in hand, Proposition `15.117.8` gives a solution for `A → B`, and then
-- Lemma `15.117.6` upgrades that solution to a separable solution because `L / K` is separable.
/-- Lemma 15.117.9: let `A → B` be an essentially finite type extension of discrete valuation
rings with fraction fields `K ⊂ L`. Assume either `A` or `B` is a Nagata ring, and assume `L / K`
is separable. Then there exists a separable solution for `A → B` in the sense of Definition
`15.116.1`. -/
lemma exists_separableSolution_of_essentiallyFiniteType_of_nagataRing_or
    (hNagata : NagataRing A ∨ NagataRing B)
    (hsepKL : Algebra.IsSeparable K L) :
    ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsSeparableSolutionFor A B K L K1 := sorry

end
