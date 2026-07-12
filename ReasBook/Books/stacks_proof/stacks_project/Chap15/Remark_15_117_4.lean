import StacksProject_2024.Chap15.Lemma_15_117_3
import Mathlib.Tactic.StacksAttribute

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

/-- Helper for Remark 15.117.4: a denominator-clearing witness at exponent `t` can be enlarged to
any larger exponent `t'`. -/
lemma uniform_power_mul_mem_base_mono
    (f : A₁') {t t' : ℕ}
    (hclear : ∀ a : A₁, ∃ c : A₁', algebraMap A₁' A₁ c = (algebraMap A₁' A₁ f) ^ t * a)
    (htt' : t ≤ t') :
    ∀ a : A₁, ∃ c : A₁', algebraMap A₁' A₁ c = (algebraMap A₁' A₁ f) ^ t' * a := by
  intro a
  rcases hclear a with ⟨c, hc⟩
  refine ⟨f ^ (t' - t) * c, ?_⟩
  -- Raise the chosen numerator from exponent `t` to the larger common exponent `t'`.
  calc
    algebraMap A₁' A₁ (f ^ (t' - t) * c) =
        (algebraMap A₁' A₁ f) ^ (t' - t) * algebraMap A₁' A₁ c := by
          simp
    _ = (algebraMap A₁' A₁ f) ^ (t' - t) * ((algebraMap A₁' A₁ f) ^ t * a) := by
          rw [hc]
    _ = ((algebraMap A₁' A₁ f) ^ (t' - t) * (algebraMap A₁' A₁ f) ^ t) * a := by
          rw [mul_assoc]
    _ = (algebraMap A₁' A₁ f) ^ ((t' - t) + t) * a := by
          rw [← pow_add]
    _ = (algebraMap A₁' A₁ f) ^ t' * a := by
          rw [Nat.sub_add_cancel htt']

/-- Helper for Remark 15.117.4: the canonical denominator-clearing numerators commute with the
given square `A₁' → A₂'`, `A₁ → A₂` once both rows use the same exponent `t`. -/
lemma power_clearing_linearMap_natural
    (α' : A₁' →+* A₂') (α : A₁ →+* A₂)
    (sqA :
      CommSq
        (ofHom (algebraMap A₁' A₁))
        (ofHom α')
        (ofHom α)
        (ofHom (algebraMap A₂' A₂)))
    (f : A₁') (t : ℕ)
    (hinj₁ : Function.Injective (algebraMap A₁' A₁))
    (hinj₂ : Function.Injective (algebraMap A₂' A₂))
    (hclear₁ :
      ∀ a : A₁, ∃ c : A₁', algebraMap A₁' A₁ c = (algebraMap A₁' A₁ f) ^ t * a)
    (hclear₂ :
      ∀ a : A₂, ∃ c : A₂', algebraMap A₂' A₂ c = (algebraMap A₂' A₂ (α' f)) ^ t * a)
    (a : A₁) :
    α' (power_clearing_linearMap (A' := A₁') (A := A₁) f t hinj₁ hclear₁ a) =
      power_clearing_linearMap (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂ (α a) := by
  apply hinj₂
  -- Compare both canonical numerators after mapping them into `A₂`, where they realize the same
  -- cleared element `(α' f)^t * α(a)`.
  calc
    algebraMap A₂' A₂
        (α' (power_clearing_linearMap (A' := A₁') (A := A₁) f t hinj₁ hclear₁ a)) =
      α
        (algebraMap A₁' A₁
          (power_clearing_linearMap (A' := A₁') (A := A₁) f t hinj₁ hclear₁ a)) := by
            symm
            exact
              map_algebraMap_eq_of_commSq α α' sqA
                (power_clearing_linearMap (A' := A₁') (A := A₁) f t hinj₁ hclear₁ a)
    _ = α ((algebraMap A₁' A₁ f) ^ t * a) := by
          rw [power_clearing_linearMap_spec (A' := A₁') (A := A₁) f t hinj₁ hclear₁ a]
    _ = α (algebraMap A₁' A₁ f) ^ t * α a := by
          simp [map_mul]
    _ = (algebraMap A₂' A₂ (α' f)) ^ t * α a := by
          rw [map_algebraMap_eq_of_commSq α α' sqA f]
    _ = algebraMap A₂' A₂
          (power_clearing_linearMap (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂ (α a)) := by
          symm
          rw [power_clearing_linearMap_spec (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂ (α a)]

/-- Helper for Remark 15.117.4: the transported numerator ideal on the lower row maps into the
transported numerator ideal on the upper row under the compatible quotient square. -/
lemma map_mem_transported_power_clearing_ideal
    (α' : A₁' →+* A₂') (α : A₁ →+* A₂)
    (sqA :
      CommSq
        (ofHom (algebraMap A₁' A₁))
        (ofHom α')
        (ofHom α)
        (ofHom (algebraMap A₂' A₂)))
    (β' : B₁' →+* B₂')
    (f : A₁') (g : B₁') (n t : ℕ)
    (hinj₁ : Function.Injective (algebraMap A₁' A₁))
    (hinj₂ : Function.Injective (algebraMap A₂' A₂))
    (hclear₁ :
      ∀ a : A₁, ∃ c : A₁', algebraMap A₁' A₁ c = (algebraMap A₁' A₁ f) ^ t * a)
    (hclear₂ :
      ∀ a : A₂, ∃ c : A₂', algebraMap A₂' A₂ c = (algebraMap A₂' A₂ (α' f)) ^ t * a)
    (φ₁' : A₁' ⧸ principalPowerIdeal f n ≃+* B₁' ⧸ principalPowerIdeal g n)
    (φ₂' : A₂' ⧸ principalPowerIdeal (α' f) n ≃+* B₂' ⧸ principalPowerIdeal (β' g) n)
    (hsquare :
      CommSq
        (ofHom <| principalPowerIdealQuotientMap α' f rfl n)
        (ofHom φ₁'.toRingHom)
        (ofHom φ₂'.toRingHom)
        (ofHom <| principalPowerIdealQuotientMap β' g rfl n))
    {x : B₁'}
    (hx :
      x ∈ transported_power_clearing_ideal
        (A' := A₁') (A := A₁) f g n
        (power_clearing_linearMap (A' := A₁') (A := A₁) f t hinj₁ hclear₁)
        φ₁') :
    β' x ∈ transported_power_clearing_ideal
      (A' := A₂') (A := A₂) (α' f) (β' g) n
      (power_clearing_linearMap (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂)
      φ₂' := by
  rw [mem_transported_power_clearing_ideal_iff] at hx ⊢
  rcases hx with ⟨a, ha⟩
  refine ⟨α a, ?_⟩
  -- Transport the lower representative across the commutative quotient square, then rewrite the
  -- source numerator via `power_clearing_linearMap_natural`.
  have hsq :=
    congr(($hsquare.w)
      (Ideal.Quotient.mk _ <|
        power_clearing_linearMap (A' := A₁') (A := A₁) f t hinj₁ hclear₁ a))
  simpa [CommRingCat.hom_comp, RingHom.comp_apply, ha,
    power_clearing_linearMap_natural α' α sqA f t hinj₁ hinj₂ hclear₁ hclear₂ a,
    principalPowerIdealQuotientMap] using hsq

/-- Helper for Remark 15.117.4: a compatible square of quotient isomorphisms sends the upper
source generator `α'(f)` to the mapped target generator `β'(g)`. -/
lemma map_generator_eq_of_power_quotient_commSq
    (α' : A₁' →+* A₂') (β' : B₁' →+* B₂')
    (f : A₁') (g : B₁') (n : ℕ)
    (φ₁' : A₁' ⧸ principalPowerIdeal f n ≃+* B₁' ⧸ principalPowerIdeal g n)
    (φ₂' : A₂' ⧸ principalPowerIdeal (α' f) n ≃+* B₂' ⧸ principalPowerIdeal (β' g) n)
    (hgen : φ₁' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (hsquare :
      CommSq
        (ofHom <| principalPowerIdealQuotientMap α' f rfl n)
        (ofHom φ₁'.toRingHom)
        (ofHom φ₂'.toRingHom)
        (ofHom <| principalPowerIdealQuotientMap β' g rfl n)) :
    φ₂' (Ideal.Quotient.mk _ (α' f)) = Ideal.Quotient.mk _ (β' g) := by
  -- Evaluate the quotient square on the lower distinguished generator and simplify the two
  -- principal-power quotient maps on that class.
  have hsq := congr(($hsquare.w) (Ideal.Quotient.mk _ f))
  simpa [CommRingCat.hom_comp, RingHom.comp_apply, hgen, principalPowerIdealQuotientMap] using hsq

/-- Helper for Remark 15.117.4: the away-map induced by `β'` carries a fixed-denominator fraction
`x / g^t` to the corresponding fixed-denominator fraction `(β' x) / (β' g)^t`. -/
lemma away_map_fraction_map_of_transported_power_clearing
    (β' : B₁' →+* B₂') (g : B₁') (t : ℕ)
    (N₁ : Ideal B₁') (N₂ : Ideal B₂')
    (hmapN : ∀ {x : B₁'}, x ∈ N₁ → β' x ∈ N₂)
    (x : N₁) :
    IsLocalization.Away.map (Localization.Away g) (Localization.Away (β' g)) β' g
      (fraction_map_of_transported_power_clearing_ideal (g := g) t N₁ x) =
        fraction_map_of_transported_power_clearing_ideal (g := β' g) t N₂
          ⟨β' x.1, hmapN x.2⟩ := by
  -- Normalize both sides to `mk'` with the fixed denominator and then use the defining formula
  -- for `IsLocalization.Away.map`.
  have hpow_map :
      Submonoid.powers g ≤ Submonoid.comap β' (Submonoid.powers (β' g)) := by
    intro y hy
    rcases hy with ⟨m, rfl⟩
    exact ⟨m, by simp⟩
  rw [fraction_map_eq_mk'_fixed_denominator (g := g) (t := t) (N := N₁) x,
    fraction_map_eq_mk'_fixed_denominator (g := β' g) (t := t) (N := N₂) ⟨β' x.1, hmapN x.2⟩]
  simpa [IsLocalization.Away.map] using
    (IsLocalization.map_mk'
      (S := Localization.Away g)
      (Q := Localization.Away (β' g))
      (g := β')
      (hy := hpow_map)
      x.1
      ⟨g ^ t, pow_mem (Submonoid.mem_powers g) t⟩)

/-- Helper for Remark 15.117.4: if a localization element lies in the fixed-denominator range
`g^{-t} N₁`, then its image under the away-map induced by `β'` lies in the corresponding range
`(β' g)^{-t} N₂`. -/
lemma away_map_mem_range_fraction_map_of_transported_power_clearing
    (β' : B₁' →+* B₂') (g : B₁') (t : ℕ)
    (N₁ : Ideal B₁') (N₂ : Ideal B₂')
    (hmapN : ∀ {x : B₁'}, x ∈ N₁ → β' x ∈ N₂)
    {y : Localization.Away g}
    (hy : y ∈ Set.range (fraction_map_of_transported_power_clearing_ideal (g := g) t N₁)) :
    IsLocalization.Away.map (Localization.Away g) (Localization.Away (β' g)) β' g y ∈
      Set.range (fraction_map_of_transported_power_clearing_ideal (g := β' g) t N₂) := by
  rcases hy with ⟨x, rfl⟩
  -- Route correction: reduce the codomain-membership check to the explicit image formula on a
  -- single fixed-denominator fraction.
  refine ⟨⟨β' x.1, hmapN x.2⟩, ?_⟩
  simpa using
    (away_map_fraction_map_of_transported_power_clearing β' g t N₁ N₂ hmapN x).symm

section

variable {A' : Type u} {A : Type u} {B' : Type u}
variable [CommRing A'] [CommRing A] [CommRing B']
variable [Algebra A' A] [Module.Finite A' A]

/-- Helper for Remark 15.117.4: fixing the denominator-clearing exponent `t` makes the
construction of Lemma 15.117.3 completely explicit on one row, with target ring equal to the
transported subalgebra `g^{-t} N` and with an explicit pre-quotient lift `ψ`. -/
lemma explicit_principal_quotient_lift_data_of_power_quotient_iso
    (f : A') (g : B') (n t : ℕ)
    (hinj : Function.Injective (algebraMap A' A))
    (hf : algebraMap A' A f ∈ nonZeroDivisors A)
    (σ : A →ₗ[A'] A')
    (hσ : ∀ a : A, algebraMap A' A (σ a) = (algebraMap A' A f) ^ t * a)
    (hσmul : ∀ a b : A, σ a * σ b = f ^ t * σ (a * b))
    (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
    (hgen : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (hn_pos : 0 < n)
    (hn_transport : 2 * t ≤ n)
    (hn_shift : t + 1 ≤ n)
    (hn_large : 2 * t + 1 ≤ n)
    (hg : g ∈ nonZeroDivisors B') :
    let N : Ideal B' := transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ'
    let C :=
      transported_power_clearing_subalgebra
        (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen hn_transport
    Function.Injective (algebraMap B' C) ∧
      Module.Finite B' C ∧
      ∃ ψ : A →+* C ⧸ principalIdeal (algebraMap B' C g),
        ∃ φ : A ⧸ principalIdeal (algebraMap A' A f) ≃+*
          C ⧸ principalIdeal (algebraMap B' C g),
          (∀ a : A, φ (Ideal.Quotient.mk _ a) = ψ a) ∧
            (∀ a : A, ∃ x : N,
              ψ a =
                Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
                  (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N x,
                    ⟨x, rfl⟩⟩ : C) ∧
                Ideal.Quotient.mk (principalPowerIdeal g n) x.1 =
                  φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a))) ∧
            CommSq
              (ofHom <|
                principalPowerIdealReductionMap (algebraMap A' A) f
                  (Nat.succ_le_of_lt hn_pos))
              (ofHom φ'.toRingHom)
              (ofHom φ.toRingHom)
              (ofHom <|
                principalPowerIdealReductionMap (algebraMap B' C) g
                  (Nat.succ_le_of_lt hn_pos)) := by
  dsimp
  -- Route correction: replay the explicit denominator-clearing construction from
  -- `exists_eventual_finite_extension_and_quotientIso_lift_of_power_quotientIso` instead of
  -- unpacking its existential output, so the target ring remains definitionally the transported
  -- subalgebra `g^{-t} N`.
  let N : Ideal B' := transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ'
  have hpowN : g ^ n ∈ N := by
    -- Once `n ≥ 2 * t`, the full kernel `(g^n)` already lies in the transported numerator ideal.
    simpa [N] using
      large_pow_mem_transported_power_clearing_ideal
        (A' := A') (A := A) f g n t hinj σ hσ φ' hgen hn_transport
  have hNfg : N.FG := by
    -- The transported ideal is finitely generated before forming the fixed-denominator target ring.
    simpa [N] using
      transported_power_clearing_ideal_fg
        (A' := A') (A := A) f g n t hinj σ hσ φ' hgen hn_transport
  let C :=
    transported_power_clearing_subalgebra
      (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen hn_transport
  let FC : N →ₗ[B'] C :=
    { toFun := fun x ↦
        ⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N x, ⟨x, rfl⟩⟩
      map_add' := by
        intro x y
        ext
        -- The codomain subtype uses the same fixed-denominator map, so additivity is inherited
        -- from the ambient linear map.
        simp [fraction_map_of_transported_power_clearing_ideal, add_mul]
      map_smul' := by
        intro r x
        ext
        -- Scalar multiplication is still multiplication by `algebraMap B' _ r` in the localization.
        simp [fraction_map_of_transported_power_clearing_ideal, Algebra.smul_def] }
  have hFC_surjective : Function.Surjective FC := by
    intro c
    rcases c.2 with ⟨x, hx⟩
    refine ⟨x, Subtype.ext ?_⟩
    exact hx
  have hC_injective : Function.Injective (algebraMap B' C) := by
    have hdenom :
        Submonoid.powers g ≤ nonZeroDivisors B' := by
      intro x hx
      rcases hx with ⟨m, rfl⟩
      exact pow_mem hg m
    have hloc_injective :
        Function.Injective (algebraMap B' (Localization.Away g)) :=
      IsLocalization.injective (Localization.Away g) hdenom
    intro b₁ b₂ hEq
    apply hloc_injective
    -- Forgetting from the subtype `C` back to `Localization.Away g` reduces injectivity to the
    -- ambient localization.
    exact congrArg Subtype.val hEq
  letI : Module.Finite B' N := Module.Finite.of_fg hNfg
  have hCfinite : Module.Finite B' C := Module.Finite.of_surjective FC hFC_surjective
  classical
  let numerator : A → B' := fun a ↦
    Classical.choose
      (Ideal.Quotient.mk_surjective
        (φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a))))
  have hnumerator :
      ∀ a : A,
        Ideal.Quotient.mk (principalPowerIdeal g n) (numerator a) =
          φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a)) := by
    intro a
    exact Classical.choose_spec
      (Ideal.Quotient.mk_surjective
        (φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a))))
  have hnumerator_mem : ∀ a : A, numerator a ∈ N := by
    intro a
    rw [mem_transported_power_clearing_ideal_iff (A' := A') (A := A) f g n σ φ']
    exact ⟨a, (hnumerator a).symm⟩
  let liftedNumerator : A → C := fun a ↦
    ⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N
        ⟨numerator a, hnumerator_mem a⟩,
      ⟨⟨numerator a, hnumerator_mem a⟩, rfl⟩⟩
  have hpow_t_mem : g ^ t ∈ N := by
    -- The transported numerator ideal already contains the distinguished power `g ^ t`.
    simpa [N] using
      pow_mem_transported_power_clearing_ideal
        (A' := A') (A := A) f g n t hinj σ hσ φ' hgen
  let ψ₀ : A → C ⧸ principalIdeal (algebraMap B' C g) := fun a ↦
    Ideal.Quotient.mk _ (liftedNumerator a)
  have hσ_one : σ (1 : A) = f ^ t := by
    -- The clearing map sends `1` to the distinguished numerator `f ^ t`.
    apply hinj
    simpa using hσ (1 : A)
  have hσ_f : σ (algebraMap A' A f) = f ^ (t + 1) := by
    -- The base element `f` acquires one extra visible factor beyond the fixed denominator `f ^ t`.
    apply hinj
    simpa [pow_succ', mul_assoc, mul_left_comm, mul_comm] using hσ (algebraMap A' A f)
  have hψ₀_zero : ψ₀ 0 = 0 := by
    let x0 : N := ⟨numerator 0, hnumerator_mem 0⟩
    have hcongr :
        Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N x0, ⟨x0, rfl⟩⟩ : C) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N (0 : N),
              ⟨(0 : N), rfl⟩⟩ : C) := by
      -- The transported numerator of `0` already differs from the zero numerator by `(g ^ n)`.
      simpa [x0] using
        fraction_map_congr_mod_principalIdeal_of_sub_mem_principalPowerIdeal
          (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen
          hn_transport hn_shift
          (x := x0) (y := (0 : N))
          (by
            simpa [x0] using
              numerator_zero_mem_principalPowerIdeal
                (A' := A') (A := A) f g n σ φ' numerator hnumerator)
    -- Compare `ψ₀ 0` with the literal zero numerator class.
    simpa [ψ₀, liftedNumerator, x0, fraction_map_of_transported_power_clearing_ideal] using hcongr
  have hψ₀_one : ψ₀ 1 = 1 := by
    let x1 : N := ⟨numerator 1, hnumerator_mem 1⟩
    let y1 : N := ⟨g ^ t, hpow_t_mem⟩
    have hnum_one :
        numerator 1 - g ^ t ∈ principalPowerIdeal g n := by
      rw [← Ideal.Quotient.eq]
      -- Both numerators represent the class of `f ^ t` under `φ'`.
      calc
        Ideal.Quotient.mk (principalPowerIdeal g n) (numerator 1) =
            φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ (1 : A))) := by
              exact hnumerator 1
        _ = φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (f ^ t)) := by
              rw [hσ_one]
        _ = φ' (Ideal.Quotient.mk (principalPowerIdeal f n) f) ^ t := by
              simp
        _ = (Ideal.Quotient.mk (principalPowerIdeal g n) g) ^ t := by
              rw [hgen]
        _ = Ideal.Quotient.mk (principalPowerIdeal g n) (g ^ t) := by
              simp
    have hcongr :
        Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N x1, ⟨x1, rfl⟩⟩ : C) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N y1, ⟨y1, rfl⟩⟩ : C) := by
      -- After transport, `1` and the distinguished numerator `g ^ t` define the same quotient
      -- class modulo `(g)`.
      simpa [x1, y1] using
        fraction_map_congr_mod_principalIdeal_of_sub_mem_principalPowerIdeal
          (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen
          hn_transport hn_shift
          (x := x1) (y := y1) hnum_one
    have hy1 :
        (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N y1, ⟨y1, rfl⟩⟩ : C) = 1 := by
      apply Subtype.ext
      -- Cancelling the fixed denominator `g ^ t` leaves the scalar `1`.
      simpa [y1] using
        (fraction_map_of_transported_power_clearing_ideal_mul_pow
          (g := g) (t := t) N hpow_t_mem (1 : B'))
    calc
      ψ₀ 1 =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N y1, ⟨y1, rfl⟩⟩ : C) := by
              simpa [ψ₀, liftedNumerator, x1, y1] using hcongr
      _ = Ideal.Quotient.mk (principalIdeal (algebraMap B' C g)) (1 : C) := by
            rw [hy1]
      _ = 1 := by
            simp
  have hψ₀_add : ∀ a b : A, ψ₀ (a + b) = ψ₀ a + ψ₀ b := by
    intro a b
    let xab : N := ⟨numerator (a + b), hnumerator_mem (a + b)⟩
    let yab : N := ⟨numerator a + numerator b, N.add_mem (hnumerator_mem a) (hnumerator_mem b)⟩
    have hcongr :
        Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N xab, ⟨xab, rfl⟩⟩ : C) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N yab, ⟨yab, rfl⟩⟩ : C) := by
      -- The chosen numerator for `a + b` is congruent to the sum of the chosen numerators.
      simpa [xab, yab] using
        fraction_map_congr_mod_principalIdeal_of_sub_mem_principalPowerIdeal
          (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen
          hn_transport hn_shift
          (x := xab) (y := yab)
          (numerator_add_sub_mem_principalPowerIdeal
            (A' := A') (A := A) f g n σ φ' numerator hnumerator a b)
    have hyab :
        (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N yab, ⟨yab, rfl⟩⟩ : C) =
          liftedNumerator a + liftedNumerator b := by
      apply Subtype.ext
      -- The fixed-denominator map is additive because every numerator uses the same denominator.
      simp [liftedNumerator, yab, fraction_map_of_transported_power_clearing_ideal, add_mul]
    calc
      ψ₀ (a + b) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N yab, ⟨yab, rfl⟩⟩ : C) := by
              simpa [ψ₀, liftedNumerator, xab, yab] using hcongr
      _ = Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (liftedNumerator a + liftedNumerator b) := by
              rw [hyab]
      _ = ψ₀ a + ψ₀ b := by
            simp [ψ₀]
  have hpow_t_succ_mem : g ^ (t + 1) ∈ N := by
    -- Multiplying the distinguished element `g ^ t ∈ N` by `g` keeps us inside the ideal `N`.
    simpa [pow_succ', mul_assoc, mul_left_comm, mul_comm] using N.mul_mem_left g hpow_t_mem
  have hψ₀_f : ψ₀ (algebraMap A' A f) = 0 := by
    let xf : N := ⟨numerator (algebraMap A' A f), hnumerator_mem (algebraMap A' A f)⟩
    let yf : N := ⟨g ^ (t + 1), hpow_t_succ_mem⟩
    have hnum_f :
        numerator (algebraMap A' A f) - g ^ (t + 1) ∈ principalPowerIdeal g n := by
      rw [← Ideal.Quotient.eq]
      -- Both numerators represent the class of `f ^ (t + 1)` under `φ'`.
      calc
        Ideal.Quotient.mk (principalPowerIdeal g n) (numerator (algebraMap A' A f)) =
            φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ (algebraMap A' A f))) := by
              exact hnumerator (algebraMap A' A f)
        _ = φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (f ^ (t + 1))) := by
              rw [hσ_f]
        _ = φ' (Ideal.Quotient.mk (principalPowerIdeal f n) f) ^ (t + 1) := by
              simp
        _ = (Ideal.Quotient.mk (principalPowerIdeal g n) g) ^ (t + 1) := by
              rw [hgen]
        _ = Ideal.Quotient.mk (principalPowerIdeal g n) (g ^ (t + 1)) := by
              simp
    have hcongr :
        Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N xf, ⟨xf, rfl⟩⟩ : C) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N yf, ⟨yf, rfl⟩⟩ : C) := by
      -- Modulo `(g)`, the transported numerator of `f` matches the visible scalar `g`.
      simpa [xf, yf] using
        fraction_map_congr_mod_principalIdeal_of_sub_mem_principalPowerIdeal
          (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen
          hn_transport hn_shift
          (x := xf) (y := yf) hnum_f
    have hyf :
        (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N yf, ⟨yf, rfl⟩⟩ : C) =
          algebraMap B' C g := by
      apply Subtype.ext
      -- Cancelling the fixed denominator leaves one visible factor of `g`.
      simpa [yf, pow_succ', mul_assoc, mul_left_comm, mul_comm] using
        (fraction_map_of_transported_power_clearing_ideal_mul_pow
          (g := g) (t := t) N hpow_t_mem g)
    have hclass_g :
        Ideal.Quotient.mk (principalIdeal (algebraMap B' C g)) (algebraMap B' C g : C) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton.mpr ⟨1, by simp⟩
    calc
      ψ₀ (algebraMap A' A f) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N yf, ⟨yf, rfl⟩⟩ : C) := by
              simpa [ψ₀, liftedNumerator, xf, yf] using hcongr
      _ = Ideal.Quotient.mk (principalIdeal (algebraMap B' C g)) (algebraMap B' C g : C) := by
            rw [hyf]
      _ = 0 := hclass_g
  have htn : t ≤ n := Nat.le_trans (Nat.le_succ t) hn_shift
  have htail : t + 1 ≤ n - t := by
    -- The eventual threshold `2 * t + 1 ≤ n` leaves one visible factor of `g` after cancelling
    -- the fixed denominator power `g ^ t`.
    exact Nat.le_sub_of_add_le (by
      simpa [two_mul, add_assoc, add_left_comm, add_comm] using hn_large)
  have hψ₀_mul : ∀ a b : A, ψ₀ (a * b) = ψ₀ a * ψ₀ b := by
    intro a b
    let xa : N := ⟨numerator a, hnumerator_mem a⟩
    let xb : N := ⟨numerator b, hnumerator_mem b⟩
    let xab : N := ⟨numerator (a * b), hnumerator_mem (a * b)⟩
    obtain ⟨w, hw_eq⟩ :=
      exists_corrected_product_numerator
        (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen hn_transport xa xb
    have hmul_raw :
        g ^ t * (w.1 - numerator (a * b)) ∈ principalPowerIdeal g n := by
      -- Rewrite the transported multiplicative congruence using the exact corrected numerator.
      simpa [xa, xb, xab, hw_eq, mul_sub, mul_assoc, mul_left_comm, mul_comm] using
        numerator_mul_sub_pow_mem_principalPowerIdeal
          (A' := A') (A := A) f g n t σ hσmul φ' hgen numerator hnumerator a b
    have hmul_tail :
        w.1 - numerator (a * b) ∈ principalPowerIdeal g (n - t) := by
      -- Cancel the common factor `g ^ t` before descending from modulo `(g^n)` to modulo `(g)`.
      exact mem_principalPowerIdeal_of_mul_pow_mem_principalPowerIdeal
        (g := g) (n := n) (t := t) hg htn hmul_raw
    have hmul_succ :
        w.1 - numerator (a * b) ∈ principalPowerIdeal g (t + 1) := by
      -- The stronger threshold `2 * t + 1 ≤ n` upgrades the cancelled error term to one
      -- remaining visible factor of `g`.
      exact
        (show principalPowerIdeal g (n - t) ≤ principalPowerIdeal g (t + 1) from
            by
              simpa [principalPowerIdeal] using
                (Ideal.pow_le_pow_right (I := principalIdeal g) htail))
          hmul_tail
    have hw_congr :
        Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N w, ⟨w, rfl⟩⟩ : C) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' C g)) (liftedNumerator (a * b)) := by
      -- After cancelling the denominator, the corrected numerator and the chosen numerator of
      -- `a * b` define the same class modulo `(g)`.
      simpa [xab, ψ₀, liftedNumerator] using
        fraction_map_congr_mod_principalIdeal_of_sub_mem_principalPowerIdeal_succ
          (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen hn_transport
          (x := w) (y := xab) hmul_succ
    have hw_mul :
        (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N w, ⟨w, rfl⟩⟩ : C) =
          liftedNumerator a * liftedNumerator b := by
      apply Subtype.ext
      have hgt : g ^ t ∈ Submonoid.powers g := pow_mem (Submonoid.mem_powers g) t
      let s : Submonoid.powers g := ⟨g ^ t, hgt⟩
      change
        fraction_map_of_transported_power_clearing_ideal (g := g) t N w =
          fraction_map_of_transported_power_clearing_ideal (g := g) t N xa *
            fraction_map_of_transported_power_clearing_ideal (g := g) t N xb
      rw [fraction_map_eq_mk'_fixed_denominator (g := g) (t := t) (N := N) w,
        fraction_map_eq_mk'_fixed_denominator (g := g) (t := t) (N := N) xa,
        fraction_map_eq_mk'_fixed_denominator (g := g) (t := t) (N := N) xb]
      -- Compare the three fixed-denominator fractions by cross-multiplication.
      symm
      change IsLocalization.mk' (Localization.Away g) xa.1 s *
          IsLocalization.mk' (Localization.Away g) xb.1 s =
        IsLocalization.mk' (Localization.Away g) w.1 s
      calc
        IsLocalization.mk' (Localization.Away g) xa.1 s *
            IsLocalization.mk' (Localization.Away g) xb.1 s =
          IsLocalization.mk' (Localization.Away g) (xa.1 * xb.1) (s * s) := by
            rw [← IsLocalization.mk'_mul]
        _ = IsLocalization.mk' (Localization.Away g) w.1 s := by
            refine IsLocalization.mk'_eq_iff_eq'.2 ?_
            exact congrArg (algebraMap B' (Localization.Away g)) <|
              by
                simpa [s, xa, xb, hw_eq, mul_assoc, mul_left_comm, mul_comm]
    calc
      ψ₀ (a * b) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N w, ⟨w, rfl⟩⟩ : C) := by
              simpa [ψ₀, liftedNumerator, xab] using hw_congr.symm
      _ = Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (liftedNumerator a * liftedNumerator b) := by
              rw [hw_mul]
      _ = ψ₀ a * ψ₀ b := by
            simp [ψ₀]
  let ψ : A →+* C ⧸ principalIdeal (algebraMap B' C g) :=
    { toFun := ψ₀
      map_zero' := hψ₀_zero
      map_one' := hψ₀_one
      map_add' := hψ₀_add
      map_mul' := hψ₀_mul }
  have hψ_surj : Function.Surjective ψ := by
    intro z
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    rcases c with ⟨c, hc⟩
    rcases hc with ⟨x, rfl⟩
    rcases (mem_transported_power_clearing_ideal_iff
        (A' := A') (A := A) f g n σ φ' x.1).1 x.2 with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hnum_eq :
        x.1 - numerator a ∈ principalPowerIdeal g n := by
      rw [← Ideal.Quotient.eq]
      -- Both numerators represent the same transported class in `B' / (g ^ n)`.
      calc
        Ideal.Quotient.mk (principalPowerIdeal g n) x.1 =
            φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a)) := by
              simpa using ha.symm
        _ = Ideal.Quotient.mk (principalPowerIdeal g n) (numerator a) := by
              exact (hnumerator a).symm
    -- Descend the equality of transported numerators from modulo `(g ^ n)` to modulo `(g)`.
    simpa [ψ, ψ₀, liftedNumerator] using
      (fraction_map_congr_mod_principalIdeal_of_sub_mem_principalPowerIdeal
        (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen
        hn_transport hn_shift
        (x := x) (y := ⟨numerator a, hnumerator_mem a⟩) hnum_eq).symm
  have hker_mem :
      ∀ {a : A},
        a ∈ RingHom.ker ψ → a ∈ principalIdeal (algebraMap A' A f) := by
    intro a ha
    let x : N := ⟨numerator a, hnumerator_mem a⟩
    have hzero_x :
        Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N x,
              ⟨x, rfl⟩⟩ : C) = 0 := by
      -- Unpack `a ∈ ker ψ` into the vanishing of its fixed-denominator numerator class.
      exact RingHom.mem_ker.mp ha
    obtain ⟨y, hy⟩ :=
      numerator_eq_g_mul_of_zeroClass_fixed_denominator
        (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen hn_transport hg
        (x := x) hzero_x
    rcases (mem_transported_power_clearing_ideal_iff
        (A' := A') (A := A) f g n σ φ' y.1).1 y.2 with ⟨b, hb⟩
    have hsigma_eq :
        Ideal.Quotient.mk (principalPowerIdeal f n) (σ a) =
          Ideal.Quotient.mk (principalPowerIdeal f n) (f * σ b) := by
      apply φ'.injective
      -- Compare the two source classes after transporting them to `B' / (g ^ n)`.
      calc
        φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a)) =
            Ideal.Quotient.mk (principalPowerIdeal g n) (numerator a) := by
              exact (hnumerator a).symm
        _ = Ideal.Quotient.mk (principalPowerIdeal g n) (g * y.1) := by
              simpa [x] using congrArg (Ideal.Quotient.mk (principalPowerIdeal g n)) hy
        _ =
            Ideal.Quotient.mk (principalPowerIdeal g n) g *
              Ideal.Quotient.mk (principalPowerIdeal g n) y.1 := by
                simp
        _ =
            φ' (Ideal.Quotient.mk (principalPowerIdeal f n) f) *
              φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ b)) := by
                rw [hgen, hb]
        _ = φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (f * σ b)) := by
              rw [map_mul]
              simp
    have hsigma_sub :
        σ (a - algebraMap A' A f * b) = σ a - f * σ b := by
      -- Linearity identifies the visible source correction term with multiplication by `f`.
      calc
        σ (a - algebraMap A' A f * b) = σ a - σ (algebraMap A' A f * b) := by
          rw [LinearMap.map_sub]
        _ = σ a - σ (f • b) := by
              simp [Algebra.smul_def]
        _ = σ a - f • σ b := by
              rw [LinearMap.map_smul]
        _ = σ a - f * σ b := by
              simp
    have hsigma_mem :
        σ (a - algebraMap A' A f * b) ∈ principalPowerIdeal f n := by
      rw [hsigma_sub]
      rw [← Ideal.Quotient.eq]
      simpa using hsigma_eq
    have hsub_mem :
        a - algebraMap A' A f * b ∈ principalIdeal (algebraMap A' A f) := by
      -- Cancelling the fixed denominator power `f ^ t` leaves one visible factor of `f`.
      exact mem_principalIdeal_of_sigma_mem_principalPowerIdeal
        (A' := A') (A := A) f n t hf σ hσ hsigma_mem hn_shift
    have hgen_mem :
        algebraMap A' A f ∈ principalIdeal (algebraMap A' A f) := by
      rw [principalIdeal]
      exact Ideal.subset_span (by simp)
    have hmul_mem :
        algebraMap A' A f * b ∈ principalIdeal (algebraMap A' A f) := by
      -- The correction term is visibly a multiple of the generator of `(f)`.
      simpa [mul_comm] using
        (principalIdeal (algebraMap A' A f)).mul_mem_left b hgen_mem
    -- Add back the visible correction term to conclude that `a` itself is a multiple of `f`.
    simpa [sub_eq_add_neg, add_assoc] using
      (principalIdeal (algebraMap A' A f)).add_mem hsub_mem hmul_mem
  have hker :
      RingHom.ker ψ = principalIdeal (algebraMap A' A f) := by
    apply le_antisymm
    · intro a ha
      exact hker_mem ha
    · rw [principalIdeal, Ideal.span_le]
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact RingHom.mem_ker.mpr hψ₀_f
  let φ : A ⧸ principalIdeal (algebraMap A' A f) ≃+*
      C ⧸ principalIdeal (algebraMap B' C g) :=
    (Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective (f := ψ) hψ_surj)
  have hφ_mk : ∀ a : A, φ (Ideal.Quotient.mk _ a) = ψ a := by
    intro a
    -- Rewrite the kernel transport on representatives and then evaluate the quotient-kernel
    -- equivalence on the resulting class.
    change
      (RingHom.quotientKerEquivOfSurjective (f := ψ) hψ_surj)
          ((Ideal.quotEquivOfEq hker.symm)
            ((Ideal.Quotient.mk (principalIdeal (algebraMap A' A f))) a)) =
        ψ a
    rw [Ideal.quotEquivOfEq_mk]
    simp [RingHom.quotientKerEquivOfSurjective]
  have hσ_base : ∀ c : A', σ (algebraMap A' A c) = f ^ t * c := by
    intro c
    -- The clearing map sends base elements to the obvious cleared numerator `f ^ t * c`.
    apply hinj
    calc
      algebraMap A' A (σ (algebraMap A' A c)) =
          (algebraMap A' A f) ^ t * algebraMap A' A c := by
            simpa using hσ (algebraMap A' A c)
      _ = algebraMap A' A (f ^ t * c) := by
            simp
  have hψ_on_base :
      ∀ c : A',
        ψ (algebraMap A' A c) =
          principalPowerIdealReductionMap (algebraMap B' C) g
            (Nat.succ_le_of_lt hn_pos)
            (φ' (Ideal.Quotient.mk (principalPowerIdeal f n) c)) := by
    intro c
    obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective
      (φ' (Ideal.Quotient.mk (principalPowerIdeal f n) c))
    let xc : N := ⟨numerator (algebraMap A' A c), hnumerator_mem (algebraMap A' A c)⟩
    let yc : N := ⟨g ^ t * d, by
      simpa [mul_comm] using N.mul_mem_left d hpow_t_mem⟩
    have hnum_c :
        numerator (algebraMap A' A c) - g ^ t * d ∈ principalPowerIdeal g n := by
      rw [← Ideal.Quotient.eq]
      -- Compare the chosen numerator with the canonical representative `g ^ t * d` of the
      -- transported base class `φ'([c])`.
      calc
        Ideal.Quotient.mk (principalPowerIdeal g n) (numerator (algebraMap A' A c)) =
            φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ (algebraMap A' A c))) := by
              exact hnumerator (algebraMap A' A c)
        _ = φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (f ^ t * c)) := by
              rw [hσ_base c]
        _ =
            φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (f ^ t)) *
              φ' (Ideal.Quotient.mk (principalPowerIdeal f n) c) := by
              rw [map_mul]
              simp
        _ = φ' (Ideal.Quotient.mk (principalPowerIdeal f n) f) ^ t *
              Ideal.Quotient.mk (principalPowerIdeal g n) d := by
              rw [hd]
              simp
        _ = (Ideal.Quotient.mk (principalPowerIdeal g n) g) ^ t *
              Ideal.Quotient.mk (principalPowerIdeal g n) d := by
              rw [hgen]
        _ = Ideal.Quotient.mk (principalPowerIdeal g n) (g ^ t * d) := by
              simp
    have hcongr :
        Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N xc, ⟨xc, rfl⟩⟩ : C) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N yc, ⟨yc, rfl⟩⟩ : C) := by
      -- The fixed-denominator fractions of the two transported numerators already agree modulo
      -- `(g)` because their numerators differ by `(g ^ n)`.
      simpa [xc, yc] using
        fraction_map_congr_mod_principalIdeal_of_sub_mem_principalPowerIdeal
          (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen
          hn_transport hn_shift
          (x := xc) (y := yc) hnum_c
    have hyc :
        (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N yc, ⟨yc, rfl⟩⟩ : C) =
          algebraMap B' C d := by
      apply Subtype.ext
      -- Cancelling the fixed denominator `g ^ t` identifies the canonical base representative.
      simpa [yc, mul_comm] using
        (fraction_map_of_transported_power_clearing_ideal_mul_pow
          (g := g) (t := t) N hpow_t_mem d)
    calc
      ψ (algebraMap A' A c) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N yc, ⟨yc, rfl⟩⟩ : C) := by
              simpa [ψ, ψ₀, liftedNumerator, xc, yc] using hcongr
      _ = Ideal.Quotient.mk (principalIdeal (algebraMap B' C g)) (algebraMap B' C d : C) := by
            rw [hyc]
      _ = Ideal.Quotient.mk (principalIdeal (algebraMap B' C g)) ((algebraMap B' C) d) := by
            rfl
      _ =
          principalPowerIdealReductionMap (algebraMap B' C) g
            (Nat.succ_le_of_lt hn_pos)
            (Ideal.Quotient.mk (principalPowerIdeal g n) d) := by
              exact
                (Ideal.quotientMap_mk
                  (I := principalIdeal (algebraMap B' C g))
                  (J := principalPowerIdeal g n)
                  (f := algebraMap B' C)
                  (H := principalPowerIdeal_le_comap_principalIdeal
                    (algebraMap B' C) g (Nat.succ_le_of_lt hn_pos))
                  (x := d)).symm
      _ =
          principalPowerIdealReductionMap (algebraMap B' C) g
            (Nat.succ_le_of_lt hn_pos)
            (φ' (Ideal.Quotient.mk (principalPowerIdeal f n) c)) := by
              rw [hd]
  have hψ_repr :
      ∀ a : A, ∃ x : N,
        ψ a =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' C g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N x,
              ⟨x, rfl⟩⟩ : C) ∧
          Ideal.Quotient.mk (principalPowerIdeal g n) x.1 =
            φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a)) := by
    intro a
    let x : N := ⟨numerator a, hnumerator_mem a⟩
    refine ⟨x, ?_, ?_⟩
    · -- The explicit pre-quotient lift is represented by the chosen fixed-denominator numerator.
      simp [ψ, ψ₀, liftedNumerator, x]
    · -- The same chosen numerator is tracked upstairs in `B' / (g ^ n)` by construction.
      simpa [x] using hnumerator a
  refine ⟨hC_injective, hCfinite, ψ, φ, hφ_mk, hψ_repr, ?_⟩
  refine ⟨?_⟩
  ext x
  -- Quotient extensionality already reduces the square to a base generator `x : A'`.
  simpa [φ, principalPowerIdealReductionMap] using hψ_on_base x

end

/-- Helper for Remark 15.117.4: once the transported numerator ideals are synchronized at a common
exponent `t`, the ambient away-map induced by `β'` cod-restricts to a comparison morphism between
the explicit transported-power-clearing subalgebras. -/
lemma codrestrict_away_map_to_transported_power_clearing_subalgebra
    (α' : A₁' →+* A₂') (α : A₁ →+* A₂)
    (sqA :
      CommSq
        (ofHom (algebraMap A₁' A₁))
        (ofHom α')
        (ofHom α)
        (ofHom (algebraMap A₂' A₂)))
    (β' : B₁' →+* B₂')
    (f : A₁') (g : B₁') (n t : ℕ)
    (hinj₁ : Function.Injective (algebraMap A₁' A₁))
    (hinj₂ : Function.Injective (algebraMap A₂' A₂))
    (hclear₁ :
      ∀ a : A₁, ∃ c : A₁', algebraMap A₁' A₁ c = (algebraMap A₁' A₁ f) ^ t * a)
    (hclear₂ :
      ∀ a : A₂, ∃ c : A₂', algebraMap A₂' A₂ c = (algebraMap A₂' A₂ (α' f)) ^ t * a)
    (φ₁' : A₁' ⧸ principalPowerIdeal f n ≃+* B₁' ⧸ principalPowerIdeal g n)
    (φ₂' : A₂' ⧸ principalPowerIdeal (α' f) n ≃+* B₂' ⧸ principalPowerIdeal (β' g) n)
    (hgen : φ₁' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (hsquare :
      CommSq
        (ofHom <| principalPowerIdealQuotientMap α' f rfl n)
        (ofHom φ₁'.toRingHom)
        (ofHom φ₂'.toRingHom)
        (ofHom <| principalPowerIdealQuotientMap β' g rfl n))
    (hn : 2 * t ≤ n) :
    let σ₁ := power_clearing_linearMap (A' := A₁') (A := A₁) f t hinj₁ hclear₁
    let σ₂ := power_clearing_linearMap (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂
    let hσ₁ :
        ∀ a : A₁, algebraMap A₁' A₁ (σ₁ a) = (algebraMap A₁' A₁ f) ^ t * a :=
      fun a ↦ power_clearing_linearMap_spec (A' := A₁') (A := A₁) f t hinj₁ hclear₁ a
    let hσ₂ :
        ∀ a : A₂, algebraMap A₂' A₂ (σ₂ a) = (algebraMap A₂' A₂ (α' f)) ^ t * a :=
      fun a ↦ power_clearing_linearMap_spec (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂ a
    let hσmul₁ : ∀ a b : A₁, σ₁ a * σ₁ b = f ^ t * σ₁ (a * b) :=
      fun a b ↦ power_clearing_linearMap_mul (A' := A₁') (A := A₁) f t hinj₁ hclear₁ a b
    let hσmul₂ : ∀ a b : A₂, σ₂ a * σ₂ b = (α' f) ^ t * σ₂ (a * b) :=
      fun a b ↦
        power_clearing_linearMap_mul (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂ a b
    let C₁ :=
      transported_power_clearing_subalgebra
        (A' := A₁') (A := A₁) f g n t hinj₁ σ₁ hσ₁ hσmul₁ φ₁' hgen hn
    let hgen₂ := map_generator_eq_of_power_quotient_commSq α' β' f g n φ₁' φ₂' hgen hsquare
    let C₂ :=
      transported_power_clearing_subalgebra
        (A' := A₂') (A := A₂) (α' f) (β' g) n t hinj₂ σ₂ hσ₂ hσmul₂ φ₂' hgen₂ hn
    ∃ β : C₁ →+* C₂,
      ∃ hmapN : ∀ {x : B₁'}, x ∈ transported_power_clearing_ideal
        (A' := A₁') (A := A₁) f g n σ₁ φ₁' →
          β' x ∈ transported_power_clearing_ideal
            (A' := A₂') (A := A₂) (α' f) (β' g) n σ₂ φ₂',
        CommSq
          (ofHom (algebraMap B₁' C₁))
          (ofHom β')
          (ofHom β)
          (ofHom (algebraMap B₂' C₂)) ∧
          ∀ x :
              transported_power_clearing_ideal
                (A' := A₁') (A := A₁) f g n σ₁ φ₁',
            β
                (⟨fraction_map_of_transported_power_clearing_ideal
                    (g := g) t
                    (transported_power_clearing_ideal
                      (A' := A₁') (A := A₁) f g n σ₁ φ₁') x,
                  ⟨x, rfl⟩⟩ : C₁) =
              (⟨fraction_map_of_transported_power_clearing_ideal
                  (g := β' g) t
                  (transported_power_clearing_ideal
                    (A' := A₂') (A := A₂) (α' f) (β' g) n σ₂ φ₂')
                  ⟨β' x.1, hmapN x.2⟩,
                ⟨⟨β' x.1, hmapN x.2⟩, rfl⟩⟩ : C₂) := by
  dsimp
  let σ₁ := power_clearing_linearMap (A' := A₁') (A := A₁) f t hinj₁ hclear₁
  let σ₂ := power_clearing_linearMap (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂
  have hσ₁ :
      ∀ a : A₁, algebraMap A₁' A₁ (σ₁ a) = (algebraMap A₁' A₁ f) ^ t * a := by
    intro a
    simpa [σ₁] using
      power_clearing_linearMap_spec (A' := A₁') (A := A₁) f t hinj₁ hclear₁ a
  have hσ₂ :
      ∀ a : A₂, algebraMap A₂' A₂ (σ₂ a) = (algebraMap A₂' A₂ (α' f)) ^ t * a := by
    intro a
    simpa [σ₂] using
      power_clearing_linearMap_spec (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂ a
  have hσmul₁ : ∀ a b : A₁, σ₁ a * σ₁ b = f ^ t * σ₁ (a * b) := by
    intro a b
    simpa [σ₁] using
      power_clearing_linearMap_mul (A' := A₁') (A := A₁) f t hinj₁ hclear₁ a b
  have hσmul₂ : ∀ a b : A₂, σ₂ a * σ₂ b = (α' f) ^ t * σ₂ (a * b) := by
    intro a b
    simpa [σ₂] using
      power_clearing_linearMap_mul (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂ a b
  let C₁ :=
    transported_power_clearing_subalgebra
      (A' := A₁') (A := A₁) f g n t hinj₁ σ₁ hσ₁ hσmul₁ φ₁' hgen hn
  let hgen₂ := map_generator_eq_of_power_quotient_commSq α' β' f g n φ₁' φ₂' hgen hsquare
  let C₂ :=
    transported_power_clearing_subalgebra
      (A' := A₂') (A := A₂) (α' f) (β' g) n t hinj₂ σ₂ hσ₂ hσmul₂ φ₂' hgen₂ hn
  let N₁ : Ideal B₁' := transported_power_clearing_ideal (A' := A₁') (A := A₁) f g n σ₁ φ₁'
  let N₂ : Ideal B₂' :=
    transported_power_clearing_ideal (A' := A₂') (A := A₂) (α' f) (β' g) n σ₂ φ₂'
  have hmapN : ∀ {x : B₁'}, x ∈ N₁ → β' x ∈ N₂ := by
    intro x hx
    -- The quotient square transports numerator ideal membership from the lower row to the upper
    -- row before any cod-restriction to the explicit target subalgebras.
    simpa [N₁, N₂, σ₁, σ₂] using
      (map_mem_transported_power_clearing_ideal
        α' α sqA β' f g n t hinj₁ hinj₂ hclear₁ hclear₂ φ₁' φ₂' hsquare hx)
  let β : C₁ →+* C₂ :=
    RingHom.codRestrict
      ((IsLocalization.Away.map (Localization.Away g) (Localization.Away (β' g)) β' g).comp
        C₁.subtype)
      C₂ fun c ↦ by
      -- Route correction: prove codomain membership first on subtype values, then package the
      -- ambient localization map as the concrete comparison map `β : C₁ →+* C₂`.
      change
        IsLocalization.Away.map (Localization.Away g) (Localization.Away (β' g)) β' g c.1 ∈
          Set.range (fraction_map_of_transported_power_clearing_ideal (g := β' g) t N₂)
      have hc :
          c.1 ∈ Set.range (fraction_map_of_transported_power_clearing_ideal (g := g) t N₁) := by
        simpa [C₁, N₁] using c.2
      simpa [N₂] using
        (away_map_mem_range_fraction_map_of_transported_power_clearing β' g t N₁ N₂ hmapN hc)
  refine ⟨β, hmapN, ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨?_⟩
    ext b
    -- Both composites are the same ambient away-map on `Localization.Away g`, so the square is
    -- checked after forgetting the subtype packaging.
    simp [β, C₁, C₂, IsLocalization.Away.map]
  · intro x
    apply Subtype.ext
    -- On each fixed-denominator numerator, the cod-restricted comparison map is exactly the
    -- ambient away-map on the corresponding fraction.
    simpa [β, C₁, C₂, N₁, N₂] using
      (away_map_fraction_map_of_transported_power_clearing β' g t N₁ N₂ hmapN x)

/-- Helper for Remark 15.117.4: once both rows are synchronized at the same exponent `t`, the
explicit pre-quotient lifts `ψ₁` and `ψ₂` commute with the cod-restricted away-map comparison
`β`. -/
lemma explicit_principal_quotient_lift_psi_natural
    (α' : A₁' →+* A₂') (α : A₁ →+* A₂)
    (sqA :
      CommSq
        (ofHom (algebraMap A₁' A₁))
        (ofHom α')
        (ofHom α)
        (ofHom (algebraMap A₂' A₂)))
    (β' : B₁' →+* B₂')
    (f : A₁') (g : B₁') (n t : ℕ)
    (hinj₁ : Function.Injective (algebraMap A₁' A₁))
    (hinj₂ : Function.Injective (algebraMap A₂' A₂))
    (hclear₁ :
      ∀ a : A₁, ∃ c : A₁', algebraMap A₁' A₁ c = (algebraMap A₁' A₁ f) ^ t * a)
    (hclear₂ :
      ∀ a : A₂, ∃ c : A₂', algebraMap A₂' A₂ c = (algebraMap A₂' A₂ (α' f)) ^ t * a)
    (φ₁' : A₁' ⧸ principalPowerIdeal f n ≃+* B₁' ⧸ principalPowerIdeal g n)
    (φ₂' : A₂' ⧸ principalPowerIdeal (α' f) n ≃+* B₂' ⧸ principalPowerIdeal (β' g) n)
    (hgen : φ₁' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (hsquare :
      CommSq
        (ofHom <| principalPowerIdealQuotientMap α' f rfl n)
        (ofHom φ₁'.toRingHom)
        (ofHom φ₂'.toRingHom)
        (ofHom <| principalPowerIdealQuotientMap β' g rfl n))
    (hn : 2 * t ≤ n)
    (ht : t + 1 ≤ n) :
    let σ₁ := power_clearing_linearMap (A' := A₁') (A := A₁) f t hinj₁ hclear₁
    let σ₂ := power_clearing_linearMap (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂
    let hσ₁ :
        ∀ a : A₁, algebraMap A₁' A₁ (σ₁ a) = (algebraMap A₁' A₁ f) ^ t * a :=
      fun a ↦ power_clearing_linearMap_spec (A' := A₁') (A := A₁) f t hinj₁ hclear₁ a
    let hσ₂ :
        ∀ a : A₂, algebraMap A₂' A₂ (σ₂ a) = (algebraMap A₂' A₂ (α' f)) ^ t * a :=
      fun a ↦ power_clearing_linearMap_spec (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂ a
    let hσmul₁ : ∀ a b : A₁, σ₁ a * σ₁ b = f ^ t * σ₁ (a * b) :=
      fun a b ↦ power_clearing_linearMap_mul (A' := A₁') (A := A₁) f t hinj₁ hclear₁ a b
    let hσmul₂ : ∀ a b : A₂, σ₂ a * σ₂ b = (α' f) ^ t * σ₂ (a * b) :=
      fun a b ↦
        power_clearing_linearMap_mul (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂ a b
    let N₁ : Ideal B₁' := transported_power_clearing_ideal (A' := A₁') (A := A₁) f g n σ₁ φ₁'
    let N₂ : Ideal B₂' :=
      transported_power_clearing_ideal (A' := A₂') (A := A₂) (α' f) (β' g) n σ₂ φ₂'
    let hgen₂ := map_generator_eq_of_power_quotient_commSq α' β' f g n φ₁' φ₂' hgen hsquare
    let C₁ :=
      transported_power_clearing_subalgebra
        (A' := A₁') (A := A₁) f g n t hinj₁ σ₁ hσ₁ hσmul₁ φ₁' hgen hn
    let C₂ :=
      transported_power_clearing_subalgebra
        (A' := A₂') (A := A₂) (α' f) (β' g) n t hinj₂ σ₂ hσ₂ hσmul₂ φ₂' hgen₂ hn
    ∀ (β : C₁ →+* C₂)
      (hmapN : ∀ {x : B₁'}, x ∈ N₁ → β' x ∈ N₂)
      (sqβ :
        CommSq
          (ofHom (algebraMap B₁' C₁))
          (ofHom β')
          (ofHom β)
          (ofHom (algebraMap B₂' C₂)))
      (hβ_fraction :
        ∀ x : N₁,
          β
              (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N₁ x,
                ⟨x, rfl⟩⟩ : C₁) =
            (⟨fraction_map_of_transported_power_clearing_ideal (g := β' g) t N₂
                ⟨β' x.1, hmapN x.2⟩,
              ⟨⟨β' x.1, hmapN x.2⟩, rfl⟩⟩ : C₂))
      (ψ₁ : A₁ →+* C₁ ⧸ principalIdeal (algebraMap B₁' C₁ g))
      (ψ₂ : A₂ →+* C₂ ⧸ principalIdeal (algebraMap B₂' C₂ (β' g)))
      (hψ₁_repr :
        ∀ a : A₁, ∃ x : N₁,
          ψ₁ a =
            Ideal.Quotient.mk (principalIdeal (algebraMap B₁' C₁ g))
              (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N₁ x,
                ⟨x, rfl⟩⟩ : C₁) ∧
            Ideal.Quotient.mk (principalPowerIdeal g n) x.1 =
              φ₁' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ₁ a)))
      (hψ₂_repr :
        ∀ a : A₂, ∃ y : N₂,
          ψ₂ a =
            Ideal.Quotient.mk (principalIdeal (algebraMap B₂' C₂ (β' g)))
              (⟨fraction_map_of_transported_power_clearing_ideal (g := β' g) t N₂ y,
                ⟨y, rfl⟩⟩ : C₂) ∧
            Ideal.Quotient.mk (principalPowerIdeal (β' g) n) y.1 =
              φ₂' (Ideal.Quotient.mk (principalPowerIdeal (α' f) n) (σ₂ a))),
      ∀ a : A₁,
        principalIdealQuotientMap β (algebraMap B₁' C₁ g)
          (map_algebraMap_eq_of_commSq β β' sqβ g) (ψ₁ a) =
        ψ₂ (α a) := by
  dsimp
  intro β hmapN sqβ hβ_fraction ψ₁ ψ₂ hψ₁_repr hψ₂_repr a
  let N₁ : Ideal B₁' :=
    transported_power_clearing_ideal
      (A' := A₁') (A := A₁) f g n
      (power_clearing_linearMap (A' := A₁') (A := A₁) f t hinj₁ hclear₁) φ₁'
  let N₂ : Ideal B₂' :=
    transported_power_clearing_ideal
      (A' := A₂') (A := A₂) (α' f) (β' g) n
      (power_clearing_linearMap (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂) φ₂'
  let C₁ :=
    transported_power_clearing_subalgebra
      (A' := A₁') (A := A₁) f g n t hinj₁
      (power_clearing_linearMap (A' := A₁') (A := A₁) f t hinj₁ hclear₁)
      (fun a ↦ power_clearing_linearMap_spec (A' := A₁') (A := A₁) f t hinj₁ hclear₁ a)
      (fun a b ↦ power_clearing_linearMap_mul (A' := A₁') (A := A₁) f t hinj₁ hclear₁ a b)
      φ₁' hgen hn
  let hgen₂ := map_generator_eq_of_power_quotient_commSq α' β' f g n φ₁' φ₂' hgen hsquare
  let C₂ :=
    transported_power_clearing_subalgebra
      (A' := A₂') (A := A₂) (α' f) (β' g) n t hinj₂
      (power_clearing_linearMap (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂)
      (fun a ↦ power_clearing_linearMap_spec (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂ a)
      (fun a b ↦ power_clearing_linearMap_mul
        (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂ a b)
      φ₂' hgen₂ hn
  obtain ⟨x, hxψ, hxquot⟩ := hψ₁_repr a
  obtain ⟨y, hyψ, hyquot⟩ := hψ₂_repr (α a)
  have hσ_nat :
      α' (power_clearing_linearMap (A' := A₁') (A := A₁) f t hinj₁ hclear₁ a) =
        power_clearing_linearMap (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂ (α a) := by
    -- The two canonical denominator-clearing numerators agree after mapping across the source
    -- square.
    simpa using
      (power_clearing_linearMap_natural α' α sqA f t hinj₁ hinj₂ hclear₁ hclear₂ a)
  have hsquare_on_sigma :
      principalPowerIdealQuotientMap β' g rfl n
          (φ₁' (Ideal.Quotient.mk (principalPowerIdeal f n)
            (power_clearing_linearMap (A' := A₁') (A := A₁) f t hinj₁ hclear₁ a))) =
        φ₂'
          (Ideal.Quotient.mk (principalPowerIdeal (α' f) n)
            (power_clearing_linearMap (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂ (α a))) := by
    -- Evaluate the original power-quotient square on the synchronized numerator class.
    have hsq :=
      congr(($hsquare.w)
        (Ideal.Quotient.mk (principalPowerIdeal f n)
          (power_clearing_linearMap (A' := A₁') (A := A₁) f t hinj₁ hclear₁ a)))
    simpa [CommRingCat.hom_comp, RingHom.comp_apply, principalPowerIdealQuotientMap, hσ_nat] using
      hsq.symm
  have hβx_quot :
      Ideal.Quotient.mk (principalPowerIdeal (β' g) n) (β' x.1) =
        Ideal.Quotient.mk (principalPowerIdeal (β' g) n) y.1 := by
    -- The mapped lower-row numerator and the chosen upper-row numerator represent the same class
    -- in `B₂' / ((β' g)^n)`.
    calc
      Ideal.Quotient.mk (principalPowerIdeal (β' g) n) (β' x.1) =
          principalPowerIdealQuotientMap β' g rfl n
            (Ideal.Quotient.mk (principalPowerIdeal g n) x.1) := by
              simp [principalPowerIdealQuotientMap]
      _ =
          principalPowerIdealQuotientMap β' g rfl n
            (φ₁'
              (Ideal.Quotient.mk (principalPowerIdeal f n)
                (power_clearing_linearMap (A' := A₁') (A := A₁) f t hinj₁ hclear₁ a))) := by
              rw [hxquot]
      _ =
          φ₂'
            (Ideal.Quotient.mk (principalPowerIdeal (α' f) n)
              (power_clearing_linearMap (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂ (α a))) := by
              exact hsquare_on_sigma
      _ = Ideal.Quotient.mk (principalPowerIdeal (β' g) n) y.1 := by
            exact hyquot.symm
  have hβx_sub :
      β' x.1 - y.1 ∈ principalPowerIdeal (β' g) n := by
    -- Equality in the principal-power quotient is the desired divisibility statement.
    rw [← Ideal.Quotient.eq]
    exact hβx_quot
  let βx : transported_power_clearing_ideal
      (A' := A₂') (A := A₂) (α' f) (β' g) n
      (power_clearing_linearMap (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂) φ₂' :=
    ⟨β' x.1, hmapN x.2⟩
  calc
    principalIdealQuotientMap β
        (algebraMap B₁' C₁ g)
        (map_algebraMap_eq_of_commSq β β' sqβ g)
        (ψ₁ a) =
      Ideal.Quotient.mk (principalIdeal (algebraMap B₂' C₂ (β' g)))
        (β
          (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N₁ x,
            ⟨x, rfl⟩⟩ : C₁)) := by
            -- Rewrite the left-hand side using the chosen explicit representative for `ψ₁ a`.
            rw [hxψ]
            exact
              Ideal.quotientMap_mk
                (I := principalIdeal (algebraMap B₂' C₂ (β' g)))
                (J := principalIdeal (algebraMap B₁' C₁ g))
                (f := β)
                (H := principalIdeal_le_comap_of_map_eq β
                  (map_algebraMap_eq_of_commSq β β' sqβ g))
                (x := (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N₁ x,
                  ⟨x, rfl⟩⟩ : C₁))
    _ =
      Ideal.Quotient.mk (principalIdeal (algebraMap B₂' C₂ (β' g)))
        ((⟨fraction_map_of_transported_power_clearing_ideal (g := β' g) t N₂ βx,
          ⟨βx, rfl⟩⟩ : C₂)) := by
            rw [hβ_fraction x]
    _ =
      Ideal.Quotient.mk (principalIdeal (algebraMap B₂' C₂ (β' g)))
        (⟨fraction_map_of_transported_power_clearing_ideal (g := β' g) t N₂ y,
          ⟨y, rfl⟩⟩ : C₂) := by
            -- The two upper-row fractions differ by a numerator in `((β' g)^n)`, hence by a
            -- visible factor of `(β' g)` after cancelling the common denominator.
            simpa [βx] using
              (fraction_map_congr_mod_principalIdeal_of_sub_mem_principalPowerIdeal
                (A' := A₂') (A := A₂) (f := α' f) (g := β' g) n t hinj₂
                (power_clearing_linearMap (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂)
                (fun a ↦ power_clearing_linearMap_spec
                  (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂ a)
                (fun a b ↦ power_clearing_linearMap_mul
                  (A' := A₂') (A := A₂) (α' f) t hinj₂ hclear₂ a b)
                φ₂'
                (map_generator_eq_of_power_quotient_commSq α' β' f g n φ₁' φ₂' hgen hsquare)
                hn ht
                (x := βx) (y := y) hβx_sub)
    _ = ψ₂ (α a) := by
          rw [hyψ]

/-- Helper for Remark 15.117.4: once the explicit pre-quotient lifts commute with `α`, the final
square on the quotient isomorphisms `φ₁` and `φ₂` follows by extensionality on quotient
generators. -/
lemma explicit_principal_quotient_lift_phi_square_of_psi_natural
    (α' : A₁' →+* A₂') (α : A₁ →+* A₂)
    (sqA :
      CommSq
        (ofHom (algebraMap A₁' A₁))
        (ofHom α')
        (ofHom α)
        (ofHom (algebraMap A₂' A₂)))
    (β' : B₁' →+* B₂')
    {C₁ : Type u} {C₂ : Type u}
    [CommRing C₁] [CommRing C₂]
    [Algebra B₁' C₁] [Algebra B₂' C₂]
    (f : A₁') (g : B₁')
    (φ₁ : A₁ ⧸ principalIdeal (algebraMap A₁' A₁ f) ≃+*
      C₁ ⧸ principalIdeal (algebraMap B₁' C₁ g))
    (φ₂ : A₂ ⧸ principalIdeal (algebraMap A₂' A₂ (α' f)) ≃+*
      C₂ ⧸ principalIdeal (algebraMap B₂' C₂ (β' g)))
    (β : C₁ →+* C₂)
    (sqβ :
      CommSq
        (ofHom (algebraMap B₁' C₁))
        (ofHom β')
        (ofHom β)
        (ofHom (algebraMap B₂' C₂)))
    (ψ₁ : A₁ →+* C₁ ⧸ principalIdeal (algebraMap B₁' C₁ g))
    (ψ₂ : A₂ →+* C₂ ⧸ principalIdeal (algebraMap B₂' C₂ (β' g)))
    (hφ₁_mk : ∀ a : A₁, φ₁ (Ideal.Quotient.mk _ a) = ψ₁ a)
    (hφ₂_mk : ∀ a : A₂, φ₂ (Ideal.Quotient.mk _ a) = ψ₂ a)
    (hψ_nat :
      ∀ a : A₁,
        principalIdealQuotientMap β (algebraMap B₁' C₁ g)
          (map_algebraMap_eq_of_commSq β β' sqβ g) (ψ₁ a) =
        ψ₂ (α a)) :
    CommSq
      (ofHom <|
        principalIdealQuotientMap α (algebraMap A₁' A₁ f)
          (map_algebraMap_eq_of_commSq α α' sqA f))
      (ofHom φ₁.toRingHom)
      (ofHom φ₂.toRingHom)
      (ofHom <|
        principalIdealQuotientMap β (algebraMap B₁' C₁ g)
          (map_algebraMap_eq_of_commSq β β' sqβ g)) := by
  refine ⟨?_⟩
  ext x
  -- The quotient square is determined on generators, where it is exactly the pre-quotient
  -- naturality statement for `ψ₁` and `ψ₂`.
  simpa [CommRingCat.hom_comp, RingHom.comp_apply, principalIdealQuotientMap,
    hφ₁_mk x, hφ₂_mk (α x)] using (hψ_nat x).symm

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
@[stacks 0GLU]
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
                          (map_algebraMap_eq_of_commSq β β' sqβ g)) := by
  -- Route correction: rerun the explicit denominator-clearing construction from Lemma 15.117.3
  -- on both rows at one common exponent `t`, keep the cod-restricted away-map explicit on
  -- fixed-denominator fractions, and only then descend to the first-power quotient square.
  obtain ⟨t₁, -, hclear₁₀⟩ :=
    exists_uniform_power_mul_mem_base
      (A' := A₁') (A := A₁) f hf₁ hAway₁
  obtain ⟨t₂, -, hclear₂₀⟩ :=
    exists_uniform_power_mul_mem_base
      (A' := A₂') (A := A₂) (α' f) hf₂ hAway₂
  let t := max t₁ t₂
  let n₀ : ℕ+ := ⟨2 * t + 1, Nat.succ_pos _⟩
  refine ⟨n₀, ?_⟩
  intro n hn β' g hg₁ hg₂ φ₁' φ₂' hgen hsquare
  have hclear₁ :
      ∀ a : A₁, ∃ c : A₁', algebraMap A₁' A₁ c = (algebraMap A₁' A₁ f) ^ t * a := by
    -- Enlarge the lower-row denominator-clearing witness to the common exponent `t`.
    simpa [t] using
      (uniform_power_mul_mem_base_mono
        (A₁' := A₁') (A₁ := A₁) f hclear₁₀ (Nat.le_max_left t₁ t₂))
  have hclear₂ :
      ∀ a : A₂, ∃ c : A₂', algebraMap A₂' A₂ c = (algebraMap A₂' A₂ (α' f)) ^ t * a := by
    -- The upper row is enlarged to the same common exponent.
    simpa [t] using
      (uniform_power_mul_mem_base_mono
        (A₁' := A₂') (A₁ := A₂) (α' f) hclear₂₀ (Nat.le_max_right t₁ t₂))
  have hn_large : 2 * t + 1 ≤ (n : ℕ) := by
    -- The chosen threshold is exactly `2 * t + 1`.
    simpa [n₀] using hn
  have hn_transport : 2 * t ≤ (n : ℕ) := by
    exact Nat.le_trans (Nat.le_succ _) hn_large
  have hshift_aux : t + 1 ≤ 2 * t + 1 := by
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using
      (Nat.add_le_add_right (Nat.le_add_left t t) 1)
  have hn_shift : t + 1 ≤ (n : ℕ) := hshift_aux.trans hn_large
  let σ₁ := power_clearing_linearMap (A' := A₁') (A := A₁) f t hA₁_injective hclear₁
  let σ₂ := power_clearing_linearMap (A' := A₂') (A := A₂) (α' f) t hA₂_injective hclear₂
  have hσ₁ :
      ∀ a : A₁, algebraMap A₁' A₁ (σ₁ a) = (algebraMap A₁' A₁ f) ^ t * a := by
    intro a
    simpa [σ₁] using
      power_clearing_linearMap_spec (A' := A₁') (A := A₁) f t hA₁_injective hclear₁ a
  have hσ₂ :
      ∀ a : A₂, algebraMap A₂' A₂ (σ₂ a) = (algebraMap A₂' A₂ (α' f)) ^ t * a := by
    intro a
    simpa [σ₂] using
      power_clearing_linearMap_spec (A' := A₂') (A := A₂) (α' f) t hA₂_injective hclear₂ a
  have hσmul₁ : ∀ a b : A₁, σ₁ a * σ₁ b = f ^ t * σ₁ (a * b) := by
    intro a b
    simpa [σ₁] using
      power_clearing_linearMap_mul (A' := A₁') (A := A₁) f t hA₁_injective hclear₁ a b
  have hσmul₂ : ∀ a b : A₂, σ₂ a * σ₂ b = (α' f) ^ t * σ₂ (a * b) := by
    intro a b
    simpa [σ₂] using
      power_clearing_linearMap_mul (A' := A₂') (A := A₂) (α' f) t hA₂_injective hclear₂ a b
  let N₁ : Ideal B₁' := transported_power_clearing_ideal (A' := A₁') (A := A₁) f g (n : ℕ) σ₁ φ₁'
  let N₂ : Ideal B₂' :=
    transported_power_clearing_ideal (A' := A₂') (A := A₂) (α' f) (β' g) (n : ℕ) σ₂ φ₂'
  let hgen₂ := map_generator_eq_of_power_quotient_commSq α' β' f g (n : ℕ) φ₁' φ₂' hgen hsquare
  let C₁ :=
    transported_power_clearing_subalgebra
      (A' := A₁') (A := A₁) f g (n : ℕ) t hA₁_injective σ₁ hσ₁ hσmul₁ φ₁' hgen hn_transport
  let C₂ :=
    transported_power_clearing_subalgebra
      (A' := A₂') (A := A₂) (α' f) (β' g) (n : ℕ) t hA₂_injective σ₂ hσ₂ hσmul₂
      φ₂' hgen₂ hn_transport
  have hrow₁ :
      Function.Injective (algebraMap B₁' C₁) ∧
        Module.Finite B₁' C₁ ∧
        ∃ ψ₁ : A₁ →+* C₁ ⧸ principalIdeal (algebraMap B₁' C₁ g),
          ∃ φ₁ : A₁ ⧸ principalIdeal (algebraMap A₁' A₁ f) ≃+*
            C₁ ⧸ principalIdeal (algebraMap B₁' C₁ g),
            (∀ a : A₁, φ₁ (Ideal.Quotient.mk _ a) = ψ₁ a) ∧
              (∀ a : A₁, ∃ x : N₁,
                ψ₁ a =
                  Ideal.Quotient.mk (principalIdeal (algebraMap B₁' C₁ g))
                    (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N₁ x,
                      ⟨x, rfl⟩⟩ : C₁) ∧
                  Ideal.Quotient.mk (principalPowerIdeal g (n : ℕ)) x.1 =
                    φ₁' (Ideal.Quotient.mk (principalPowerIdeal f (n : ℕ)) (σ₁ a))) ∧
              CommSq
                (ofHom <|
                  principalPowerIdealReductionMap (algebraMap A₁' A₁) f
                    (Nat.succ_le_of_lt n.2))
                (ofHom φ₁'.toRingHom)
                (ofHom φ₁.toRingHom)
                (ofHom <|
                  principalPowerIdealReductionMap (algebraMap B₁' C₁) g
                    (Nat.succ_le_of_lt n.2)) := by
    simpa [N₁, C₁] using
      (explicit_principal_quotient_lift_data_of_power_quotient_iso
        (A' := A₁') (A := A₁) (B' := B₁') f g (n : ℕ) t hA₁_injective hf₁ σ₁ hσ₁ hσmul₁
        φ₁' hgen n.2 hn_transport hn_shift hn_large hg₁)
  rcases hrow₁ with ⟨hC₁_injective, hC₁_finite, ψ₁, φ₁, hφ₁_mk, hψ₁_repr, sqφ₁⟩
  have hrow₂ :
      Function.Injective (algebraMap B₂' C₂) ∧
        Module.Finite B₂' C₂ ∧
        ∃ ψ₂ : A₂ →+* C₂ ⧸ principalIdeal (algebraMap B₂' C₂ (β' g)),
          ∃ φ₂ : A₂ ⧸ principalIdeal (algebraMap A₂' A₂ (α' f)) ≃+*
            C₂ ⧸ principalIdeal (algebraMap B₂' C₂ (β' g)),
            (∀ a : A₂, φ₂ (Ideal.Quotient.mk _ a) = ψ₂ a) ∧
              (∀ a : A₂, ∃ y : N₂,
                ψ₂ a =
                  Ideal.Quotient.mk (principalIdeal (algebraMap B₂' C₂ (β' g)))
                    (⟨fraction_map_of_transported_power_clearing_ideal (g := β' g) t N₂ y,
                      ⟨y, rfl⟩⟩ : C₂) ∧
                  Ideal.Quotient.mk (principalPowerIdeal (β' g) (n : ℕ)) y.1 =
                    φ₂'
                      (Ideal.Quotient.mk (principalPowerIdeal (α' f) (n : ℕ)) (σ₂ a))) ∧
              CommSq
                (ofHom <|
                  principalPowerIdealReductionMap (algebraMap A₂' A₂) (α' f)
                    (Nat.succ_le_of_lt n.2))
                (ofHom φ₂'.toRingHom)
                (ofHom φ₂.toRingHom)
                (ofHom <|
                  principalPowerIdealReductionMap (algebraMap B₂' C₂) (β' g)
                    (Nat.succ_le_of_lt n.2)) := by
    simpa [N₂, C₂, hgen₂] using
      (explicit_principal_quotient_lift_data_of_power_quotient_iso
        (A' := A₂') (A := A₂) (B' := B₂') (α' f) (β' g) (n : ℕ) t hA₂_injective hf₂ σ₂
        hσ₂ hσmul₂ φ₂' hgen₂ n.2 hn_transport hn_shift hn_large hg₂)
  rcases hrow₂ with ⟨hC₂_injective, hC₂_finite, ψ₂, φ₂, hφ₂_mk, hψ₂_repr, sqφ₂⟩
  have hβ :
      ∃ β : C₁ →+* C₂,
        ∃ hmapN : ∀ {x : B₁'}, x ∈ N₁ → β' x ∈ N₂,
          CommSq
            (ofHom (algebraMap B₁' C₁))
            (ofHom β')
            (ofHom β)
            (ofHom (algebraMap B₂' C₂)) ∧
            ∀ x : N₁,
              β
                  (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N₁ x,
                    ⟨x, rfl⟩⟩ : C₁) =
                (⟨fraction_map_of_transported_power_clearing_ideal (g := β' g) t N₂
                    ⟨β' x.1, hmapN x.2⟩,
                  ⟨⟨β' x.1, hmapN x.2⟩, rfl⟩⟩ : C₂) := by
    simpa [N₁, N₂, C₁, C₂] using
      (codrestrict_away_map_to_transported_power_clearing_subalgebra
        α' α sqA β' f g (n : ℕ) t hA₁_injective hA₂_injective hclear₁ hclear₂
        φ₁' φ₂' hgen hsquare hn_transport)
  rcases hβ with ⟨β, hmapN, sqβ, hβ_fraction⟩
  have hψ_nat :
      ∀ a : A₁,
        principalIdealQuotientMap β (algebraMap B₁' C₁ g)
          (map_algebraMap_eq_of_commSq β β' sqβ g) (ψ₁ a) =
        ψ₂ (α a) := by
    simpa [N₁, N₂, C₁, C₂] using
      (explicit_principal_quotient_lift_psi_natural
        α' α sqA β' f g (n : ℕ) t hA₁_injective hA₂_injective hclear₁ hclear₂
        φ₁' φ₂' hgen hsquare hn_transport hn_shift β hmapN sqβ hβ_fraction ψ₁ ψ₂
        hψ₁_repr hψ₂_repr)
  have hφ_square :
      CommSq
        (ofHom <|
          principalIdealQuotientMap α (algebraMap A₁' A₁ f)
            (map_algebraMap_eq_of_commSq α α' sqA f))
        (ofHom φ₁.toRingHom)
        (ofHom φ₂.toRingHom)
        (ofHom <|
          principalIdealQuotientMap β (algebraMap B₁' C₁ g)
            (map_algebraMap_eq_of_commSq β β' sqβ g)) := by
    exact
      explicit_principal_quotient_lift_phi_square_of_psi_natural
        α' α sqA β' f g φ₁ φ₂ β sqβ ψ₁ ψ₂ hφ₁_mk hφ₂_mk hψ_nat
  refine ⟨C₁, inferInstance, inferInstance, hC₁_injective, hC₁_finite, φ₁, sqφ₁,
    C₂, inferInstance, inferInstance, hC₂_injective, hC₂_finite, φ₂, β, sqβ, sqφ₂,
    hφ_square⟩

end

end PrincipalQuotientLiftFunctoriality
