import StacksProject_2024.Chap15.Lemma_15_117_3

-- Declarations for this item will be appended below by the statement pipeline.

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
