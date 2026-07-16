import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.CommSq
import stacks_proof.stacks_project.Chap15.PrincipalIdeal
import Mathlib.Tactic.StacksAttribute

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

/-- Helper for Lemma 15.117.3: a bijective canonical away map identifies the two away
localizations as `A'`-algebras. -/
noncomputable def away_comparison_equiv
    (f : A')
    (hAway : Function.Bijective (Localization.awayMapₐ (Algebra.ofId A' A) f)) :
    Localization.Away f ≃ₐ[A'] Localization.Away (algebraMap A' A f) :=
  AlgEquiv.ofBijective (Localization.awayMapₐ (Algebra.ofId A' A) f) hAway

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: every element of `A` becomes the image of an element of `A'`
after multiplication by a suitable power of `f`. -/
lemma exists_power_mul_mem_base
    (f : A')
    (hf : algebraMap A' A f ∈ nonZeroDivisors A)
    (hAway : Function.Bijective (Localization.awayMapₐ (Algebra.ofId A' A) f))
    (a : A) :
    ∃ n : ℕ, ∃ c : A', algebraMap A' A c = (algebraMap A' A f) ^ n * a := by
  let e := away_comparison_equiv (A' := A') (A := A) f hAway
  let locA := Localization.Away (algebraMap A' A f)
  let denomA' : Submonoid.powers f ≤
      Submonoid.comap (algebraMap A' A) (Submonoid.powers (algebraMap A' A f)) := by
    intro x hx
    rcases hx with ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  let denomA : Submonoid.powers (algebraMap A' A f) ≤ nonZeroDivisors A := by
    intro x hx
    rcases hx with ⟨n, rfl⟩
    exact pow_mem hf n
  have hinjLocA : Function.Injective (algebraMap A locA) :=
    IsLocalization.injective locA denomA
  -- Pull the localization class of `a` back to `A'_f`, so its numerator already lies in `A'`.
  obtain ⟨c, s, hs⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f)
    (e.symm (algebraMap A locA a))
  obtain ⟨n, hn⟩ := s.2
  have hpowf : f ^ n ∈ Submonoid.powers f := ⟨n, rfl⟩
  have hpowA : (algebraMap A' A f) ^ n ∈ Submonoid.powers (algebraMap A' A f) := ⟨n, rfl⟩
  have hs' :
      IsLocalization.mk' (Localization.Away f) c ⟨f ^ n, hpowf⟩ =
        e.symm (algebraMap A locA a) := by
    simpa [hn] using hs
  have hmap :
      (Localization.awayMapₐ (Algebra.ofId A' A) f)
          (IsLocalization.mk' (Localization.Away f) c
            ⟨f ^ n, hpowf⟩) =
        algebraMap A locA a := by
    -- Applying the comparison equivalence turns the chosen numerator/denominator expression in
    -- `A'_f` back into the target localization class of `a`.
    simpa [e] using congrArg e hs'
  have hmap_mk :
      (Localization.awayMapₐ (Algebra.ofId A' A) f)
          (IsLocalization.mk' (Localization.Away f) c
            ⟨f ^ n, hpowf⟩) =
        IsLocalization.mk' locA (algebraMap A' A c)
          ⟨(algebraMap A' A f) ^ n, hpowA⟩ := by
    -- This is the canonical compatibility of the away map with fraction representatives.
    simpa [locA, Localization.awayMapₐ] using
      (IsLocalization.map_mk' (Q := locA) (g := algebraMap A' A) denomA'
        c ⟨f ^ n, hpowf⟩)
  have hfrac :
      IsLocalization.mk' locA (algebraMap A' A c)
        ⟨(algebraMap A' A f) ^ n, hpowA⟩ =
      algebraMap A locA a := by
    exact hmap_mk.symm.trans hmap
  have hcleared :
      algebraMap A locA (((algebraMap A' A f) ^ n) * a) =
        algebraMap A locA (algebraMap A' A c) := by
    -- Multiply the fraction identity by its denominator inside the localization and then use the
    -- defining equation for `mk'`.
    calc
      algebraMap A locA (((algebraMap A' A f) ^ n) * a) =
          algebraMap A locA ((algebraMap A' A f) ^ n) * algebraMap A locA a := by
            simp
      _ =
          algebraMap A locA ((algebraMap A' A f) ^ n) *
            IsLocalization.mk' locA (algebraMap A' A c)
              ⟨(algebraMap A' A f) ^ n, hpowA⟩ := by
            rw [← hfrac]
      _ = algebraMap A locA (algebraMap A' A c) := by
            simpa using
              (IsLocalization.mk'_spec' locA (algebraMap A' A c)
                ⟨(algebraMap A' A f) ^ n, hpowA⟩)
  refine ⟨n, c, ?_⟩
  exact (hinjLocA hcleared).symm

/-- Helper for Lemma 15.117.3: one positive power of `f` clears denominators uniformly on all of
`A`. -/
lemma exists_uniform_power_mul_mem_base
    (f : A')
    (hf : algebraMap A' A f ∈ nonZeroDivisors A)
    (hAway : Function.Bijective (Localization.awayMapₐ (Algebra.ofId A' A) f)) :
    ∃ t : ℕ, 0 < t ∧ ∀ a : A, ∃ c : A', algebraMap A' A c = (algebraMap A' A f) ^ t * a := by
  classical
  let hfg : (⊤ : Submodule A' A).FG := Module.Finite.iff_fg.mp inferInstance
  rcases hfg with ⟨s, hs⟩
  let exponent : A → ℕ := fun a ↦
    Classical.choose (exists_power_mul_mem_base (A' := A') (A := A) f hf hAway a)
  let numerator : A → A' := fun a ↦
    Classical.choose
      (Classical.choose_spec (exists_power_mul_mem_base (A' := A') (A := A) f hf hAway a))
  have hnumerator :
      ∀ a : A,
        algebraMap A' A (numerator a) = (algebraMap A' A f) ^ exponent a * a := by
    intro a
    exact Classical.choose_spec
      (Classical.choose_spec (exists_power_mul_mem_base (A' := A') (A := A) f hf hAway a))
  let t : ℕ := s.sup exponent + 1
  refine ⟨t, Nat.succ_pos _, ?_⟩
  intro a
  have ha : a ∈ Submodule.span A' (↑s : Set A) := by
    -- The finite generating family spans all of `A`, so every element lies in its span.
    have : a ∈ (⊤ : Submodule A' A) := by simp
    simpa [hs] using this
  -- Apply span induction so the common exponent only has to be checked on the chosen generators.
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · intro x hx
    let nx := exponent x
    let cx := numerator x
    have hnx : algebraMap A' A cx = (algebraMap A' A f) ^ nx * x := by
      simpa [nx, cx] using hnumerator x
    have hle : nx ≤ t := by
      -- The exponent on each chosen generator is bounded by the finite supremum defining `t`.
      have hsup : exponent x ≤ s.sup exponent := Finset.le_sup hx
      simpa [nx, t] using Nat.le_trans hsup (Nat.le_succ (s.sup exponent))
    refine ⟨f ^ (t - nx) * cx, ?_⟩
    -- Raise the chosen numerator for `x` to the uniform exponent `t`.
    calc
      algebraMap A' A (f ^ (t - nx) * cx) =
          (algebraMap A' A f) ^ (t - nx) * algebraMap A' A cx := by
            simp
      _ = (algebraMap A' A f) ^ (t - nx) * ((algebraMap A' A f) ^ nx * x) := by
            rw [hnx]
      _ = ((algebraMap A' A f) ^ (t - nx) * (algebraMap A' A f) ^ nx) * x := by
            rw [mul_assoc]
      _ = (algebraMap A' A f) ^ ((t - nx) + nx) * x := by
            rw [← pow_add]
      _ = (algebraMap A' A f) ^ t * x := by
            rw [Nat.sub_add_cancel hle]
  · refine ⟨0, ?_⟩
    -- Zero is cleared by any power of `f`.
    simp
  · intro x y _ _ hx hy
    rcases hx with ⟨cx, hcx⟩
    rcases hy with ⟨cy, hcy⟩
    refine ⟨cx + cy, ?_⟩
    -- The cleared-numerator condition is additive.
    calc
      algebraMap A' A (cx + cy) = algebraMap A' A cx + algebraMap A' A cy := by
        simp
      _ = (algebraMap A' A f) ^ t * x + (algebraMap A' A f) ^ t * y := by
        rw [hcx, hcy]
      _ = (algebraMap A' A f) ^ t * (x + y) := by
        rw [mul_add]
  · intro r x _ hx
    rcases hx with ⟨cx, hcx⟩
    refine ⟨r * cx, ?_⟩
    -- Scalar multiplication stays in the cleared-numerator span because the `A'`-action on `A`
    -- is multiplication through `algebraMap`.
    calc
      algebraMap A' A (r * cx) = algebraMap A' A r * algebraMap A' A cx := by
        simp
      _ = algebraMap A' A r * ((algebraMap A' A f) ^ t * x) := by
        rw [hcx]
      _ = (algebraMap A' A f) ^ t * (r • x) := by
        simpa [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Lemma 15.117.3: the uniform denominator-clearing numerators assemble into an
`A'`-linear map. -/
noncomputable def power_clearing_linearMap
    (f : A') (t : ℕ)
    (hinj : Function.Injective (algebraMap A' A))
    (hclear : ∀ a : A, ∃ c : A', algebraMap A' A c = (algebraMap A' A f) ^ t * a) :
    A →ₗ[A'] A' :=
  by
    classical
    refine
      { toFun := fun a ↦ Classical.choose (hclear a)
        map_add' := ?_
        map_smul' := ?_ }
    · intro a b
      apply hinj
      -- The chosen numerator for `a + b` has the same image as the sum of the chosen numerators.
      calc
        algebraMap A' A (Classical.choose (hclear (a + b))) =
            (algebraMap A' A f) ^ t * (a + b) := by
              exact Classical.choose_spec (hclear (a + b))
        _ = (algebraMap A' A f) ^ t * a + (algebraMap A' A f) ^ t * b := by
              rw [mul_add]
        _ = algebraMap A' A (Classical.choose (hclear a)) +
              algebraMap A' A (Classical.choose (hclear b)) := by
              rw [Classical.choose_spec (hclear a), Classical.choose_spec (hclear b)]
        _ = algebraMap A' A
              (Classical.choose (hclear a) + Classical.choose (hclear b)) := by
              simp
    · intro r a
      apply hinj
      -- The chosen numerator respects the `A'`-scalar action because both source and target use
      -- multiplication through `algebraMap`.
      calc
        algebraMap A' A (Classical.choose (hclear (r • a))) =
            (algebraMap A' A f) ^ t * (r • a) := by
              exact Classical.choose_spec (hclear (r • a))
        _ = (algebraMap A' A f) ^ t * (algebraMap A' A r * a) := by
              simp [Algebra.smul_def]
        _ = algebraMap A' A r * ((algebraMap A' A f) ^ t * a) := by
              simp [mul_assoc, mul_left_comm, mul_comm]
        _ = algebraMap A' A r * algebraMap A' A (Classical.choose (hclear a)) := by
              rw [Classical.choose_spec (hclear a)]
        _ = algebraMap A' A (r • Classical.choose (hclear a)) := by
              simp

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: the linear numerator map realizes the uniform clearing formula on
the nose after applying `algebraMap`. -/
lemma power_clearing_linearMap_spec
    (f : A') (t : ℕ)
    (hinj : Function.Injective (algebraMap A' A))
    (hclear : ∀ a : A, ∃ c : A', algebraMap A' A c = (algebraMap A' A f) ^ t * a)
    (a : A) :
    algebraMap A' A (power_clearing_linearMap (A' := A') (A := A) f t hinj hclear a) =
      (algebraMap A' A f) ^ t * a := by
  -- The definition chooses precisely a numerator satisfying the uniform clearing equation.
  exact Classical.choose_spec (hclear a)

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: the canonical numerators multiply with one extra factor of `f ^ t`,
matching the source construction `f ^ t A · f ^ t A ⊆ f ^ t A`. -/
lemma power_clearing_linearMap_mul
    (f : A') (t : ℕ)
    (hinj : Function.Injective (algebraMap A' A))
    (hclear : ∀ a : A, ∃ c : A', algebraMap A' A c = (algebraMap A' A f) ^ t * a)
    (a b : A) :
    power_clearing_linearMap (A' := A') (A := A) f t hinj hclear a *
        power_clearing_linearMap (A' := A') (A := A) f t hinj hclear b =
      f ^ t * power_clearing_linearMap (A' := A') (A := A) f t hinj hclear (a * b) := by
  apply hinj
  -- Compare the two candidate numerators after mapping them into `A`, where both sides become the
  -- same normalized multiple of `a * b`.
  calc
    algebraMap A' A
        (power_clearing_linearMap (A' := A') (A := A) f t hinj hclear a *
          power_clearing_linearMap (A' := A') (A := A) f t hinj hclear b) =
        algebraMap A' A (power_clearing_linearMap (A' := A') (A := A) f t hinj hclear a) *
          algebraMap A' A (power_clearing_linearMap (A' := A') (A := A) f t hinj hclear b) := by
            simp
    _ = ((algebraMap A' A f) ^ t * a) * ((algebraMap A' A f) ^ t * b) := by
          rw [power_clearing_linearMap_spec (A' := A') (A := A) f t hinj hclear a,
            power_clearing_linearMap_spec (A' := A') (A := A) f t hinj hclear b]
    _ = (algebraMap A' A f) ^ t * ((algebraMap A' A f) ^ t * (a * b)) := by
          simp [mul_assoc, mul_left_comm, mul_comm]
    _ = algebraMap A' A (f ^ t) *
          algebraMap A' A
            (power_clearing_linearMap (A' := A') (A := A) f t hinj hclear (a * b)) := by
          rw [power_clearing_linearMap_spec (A' := A') (A := A) f t hinj hclear (a * b)]
          simp
    _ = algebraMap A' A
          (f ^ t *
            power_clearing_linearMap (A' := A') (A := A) f t hinj hclear (a * b)) := by
          simp

/-- Helper for Lemma 15.117.3: the source object `f ^ t A ⊆ A'` is the ideal-valued range of the
uniform denominator-clearing numerator map. -/
def power_clearing_ideal
    (σ : A →ₗ[A'] A') : Ideal A' :=
  σ.range

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: membership in `power_clearing_ideal σ` is exactly the existence of a
source element with that numerator. -/
lemma mem_power_clearing_ideal_iff
    (σ : A →ₗ[A'] A') (x : A') :
    x ∈ power_clearing_ideal (A' := A') σ ↔ ∃ a : A, σ a = x := by
  -- The ideal is defined as the literal range of `σ`, so membership is tautological.
  exact Iff.rfl

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: the distinguished element `f ^ t` belongs to the source numerator
ideal because `σ 1 = f ^ t`. -/
lemma pow_mem_power_clearing_ideal
    (f : A') (t : ℕ)
    (hinj : Function.Injective (algebraMap A' A))
    (σ : A →ₗ[A'] A')
    (hσ : ∀ a : A, algebraMap A' A (σ a) = (algebraMap A' A f) ^ t * a) :
    f ^ t ∈ power_clearing_ideal (A' := A') σ := by
  refine (mem_power_clearing_ideal_iff (A' := A') (A := A) σ (f ^ t)).2 ⟨1, ?_⟩
  -- Compare `σ 1` and `f ^ t` after applying the injective structural map into `A`.
  apply hinj
  calc
    algebraMap A' A (σ 1) = (algebraMap A' A f) ^ t * (1 : A) := by
      simpa using hσ 1
    _ = (algebraMap A' A f) ^ t := by simp
    _ = algebraMap A' A (f ^ t) := by simp

/-- Helper for Lemma 15.117.3: transport the source numerator ideal through the power-quotient
isomorphism and pull it back to an ideal of `B'`. -/
def transported_power_clearing_ideal
    {B' : Type u} [CommRing B']
    (f : A') (g : B') (n : ℕ)
    (σ : A →ₗ[A'] A')
    (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n) :
    Ideal B' :=
  Ideal.comap (Ideal.Quotient.mk (principalPowerIdeal g n))
    (Ideal.map φ'.toRingHom
      (Ideal.map (Ideal.Quotient.mk (principalPowerIdeal f n))
        (power_clearing_ideal (A' := A') σ)))

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: membership in the transported numerator ideal can be read on
representatives in the two power quotients. -/
lemma mem_transported_power_clearing_ideal_iff
    {B' : Type u} [CommRing B']
    (f : A') (g : B') (n : ℕ)
    (σ : A →ₗ[A'] A')
    (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
    (x : B') :
    x ∈ transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ' ↔
      ∃ a : A, φ' (Ideal.Quotient.mk _ (σ a)) = Ideal.Quotient.mk _ x := by
  -- Unfold the nested `Ideal.comap`/`Ideal.map` construction until only quotient representatives
  -- remain, then read both maps through surjectivity.
  rw [transported_power_clearing_ideal, Ideal.mem_comap,
    Ideal.mem_map_iff_of_surjective φ'.toRingHom φ'.surjective]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases (Ideal.mem_map_iff_of_surjective
      (Ideal.Quotient.mk (principalPowerIdeal f n)) Ideal.Quotient.mk_surjective).1 hy with
      ⟨z, hz, hyz⟩
    rcases (mem_power_clearing_ideal_iff (A' := A') (A := A) σ z).1 hz with ⟨a, rfl⟩
    exact ⟨a, by simpa [hyz] using hxy⟩
  · rintro ⟨a, ha⟩
    refine ⟨Ideal.Quotient.mk (principalPowerIdeal f n) (σ a), ?_, ha⟩
    -- The quotient class of `σ a` comes from the source ideal by construction.
    exact (Ideal.mem_map_iff_of_surjective
      (Ideal.Quotient.mk (principalPowerIdeal f n)) Ideal.Quotient.mk_surjective).2
      ⟨σ a,
        (mem_power_clearing_ideal_iff (A' := A') (A := A) σ (σ a)).2 ⟨a, rfl⟩,
        rfl⟩

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: the transported numerator ideal contains `g ^ t`, the image of the
distinguished source generator `f ^ t`. -/
lemma pow_mem_transported_power_clearing_ideal
    {B' : Type u} [CommRing B']
    (f : A') (g : B') (n t : ℕ)
    (hinj : Function.Injective (algebraMap A' A))
    (σ : A →ₗ[A'] A')
    (hσ : ∀ a : A, algebraMap A' A (σ a) = (algebraMap A' A f) ^ t * a)
    (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
    (hgen : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    g ^ t ∈ transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ' := by
  rw [mem_transported_power_clearing_ideal_iff]
  refine ⟨1, ?_⟩
  have hσone : σ 1 = f ^ t := by
    -- The source numerator map sends `1` to `f ^ t` after using injectivity of `algebraMap`.
    apply hinj
    calc
      algebraMap A' A (σ 1) = (algebraMap A' A f) ^ t * (1 : A) := by
        simpa using hσ 1
      _ = (algebraMap A' A f) ^ t := by simp
      _ = algebraMap A' A (f ^ t) := by simp
  -- Transport the quotient class of `f ^ t` and rewrite it as the class of `g ^ t`.
  calc
    φ' (Ideal.Quotient.mk _ (σ 1)) = φ' (Ideal.Quotient.mk _ (f ^ t)) := by
      simpa [hσone]
    _ = φ' (Ideal.Quotient.mk _ f) ^ t := by
      simp
    _ = (Ideal.Quotient.mk _ g) ^ t := by
      rw [hgen]
    _ = Ideal.Quotient.mk _ (g ^ t) := by
      simp

/-- Helper for Lemma 15.117.3: the transported numerator ideal maps into the away localization by
using the fixed denominator `g ^ t`, so the source object is literally `g^{-t} N`. -/
noncomputable def fraction_map_of_transported_power_clearing_ideal
    {B' : Type u} [CommRing B']
    (g : B') (t : ℕ)
    (N : Ideal B') :
    N →ₗ[B'] Localization.Away g :=
  by
    have hgt : g ^ t ∈ Submonoid.powers g := by
      exact pow_mem (Submonoid.mem_powers g) t
    let ug : Units (Localization.Away g) :=
      (IsLocalization.map_units (Localization.Away g) ⟨g ^ t, hgt⟩).unit
    refine
      { toFun := fun x ↦ algebraMap B' (Localization.Away g) x.1 * ↑(ug⁻¹)
        map_add' := ?_
        map_smul' := ?_ }
    · intro x y
      -- Keeping the denominator fixed turns addition into distributivity by a common inverse.
      simp [add_mul]
    · intro r x
      -- The `B'`-scalar action on the localization is multiplication through `algebraMap`.
      simp [Algebra.smul_def, mul_assoc]

/-- Helper for Lemma 15.117.3: if `g ^ t ∈ N`, then every scalar from `B'` lies in the range of
the fixed-denominator map `N → B'[1 / g]`. -/
lemma algebraMap_mem_range_fraction_map_of_pow_mem
    {B' : Type u} [CommRing B']
    (g : B') (t : ℕ)
    (N : Ideal B')
    (hpow : g ^ t ∈ N)
    (b : B') :
    algebraMap B' (Localization.Away g) b ∈
      Set.range (fraction_map_of_transported_power_clearing_ideal (g := g) t N) := by
  refine ⟨⟨b * g ^ t, N.mul_mem_left b hpow⟩, ?_⟩
  -- The chosen numerator is `b * g ^ t`, so the fixed inverse denominator cancels immediately.
  have hgt : g ^ t ∈ Submonoid.powers g := by
    exact pow_mem (Submonoid.mem_powers g) t
  let ug : Units (Localization.Away g) :=
    (IsLocalization.map_units (Localization.Away g) ⟨g ^ t, hgt⟩).unit
  calc
    fraction_map_of_transported_power_clearing_ideal (g := g) t N ⟨b * g ^ t, N.mul_mem_left b hpow⟩ =
        algebraMap B' (Localization.Away g) (b * g ^ t) * ↑(ug⁻¹) := by
          simp [fraction_map_of_transported_power_clearing_ideal, ug]
    _ = algebraMap B' (Localization.Away g) b * (↑ug * ↑(ug⁻¹)) := by
          simp [ug, mul_assoc, mul_comm]
    _ = algebraMap B' (Localization.Away g) b := by
          simp

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: the transported numerator ideal is closed under multiplication up to
an error term divisible by `g ^ t` modulo `g ^ n`, matching the source identity
`σ a * σ b = f ^ t * σ (a * b)`. -/
lemma mul_sub_pow_mem_principalPowerIdeal_of_mem_transported_power_clearing
    {B' : Type u} [CommRing B']
    (f : A') (g : B') (n t : ℕ)
    (σ : A →ₗ[A'] A')
    (hσmul : ∀ a b : A, σ a * σ b = f ^ t * σ (a * b))
    (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
    (hgen : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    {x y : B'}
    (hx : x ∈ transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ')
    (hy : y ∈ transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ') :
    ∃ z : B',
      z ∈ transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ' ∧
        x * y - g ^ t * z ∈ principalPowerIdeal g n := by
  rcases (mem_transported_power_clearing_ideal_iff (A' := A') (A := A) f g n σ φ' x).1 hx with
    ⟨a, ha⟩
  rcases (mem_transported_power_clearing_ideal_iff (A' := A') (A := A) f g n σ φ' y).1 hy with
    ⟨b, hb⟩
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective
    (φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ (a * b))))
  refine ⟨z, ?_, ?_⟩
  · -- Choose `z` to represent the transported class of `σ (a * b)`.
    rw [mem_transported_power_clearing_ideal_iff]
    exact ⟨a * b, hz.symm⟩
  · -- Compare `x * y` and `g ^ t * z` in the quotient ring, where both become the same class.
    refine (Ideal.Quotient.eq_zero_iff_mem).1 ?_
    calc
      Ideal.Quotient.mk (principalPowerIdeal g n) (x * y - g ^ t * z) =
          Ideal.Quotient.mk (principalPowerIdeal g n) (x * y) -
            Ideal.Quotient.mk (principalPowerIdeal g n) (g ^ t * z) := by
              simp
      _ =
          φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a * σ b)) -
            φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (f ^ t * σ (a * b))) := by
              congr 1
              · calc
                  Ideal.Quotient.mk (principalPowerIdeal g n) (x * y) =
                      Ideal.Quotient.mk (principalPowerIdeal g n) x *
                        Ideal.Quotient.mk (principalPowerIdeal g n) y := by
                          simp
                  _ =
                      φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a)) *
                        φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ b)) := by
                          rw [← ha, ← hb]
                  _ =
                      φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a) *
                        Ideal.Quotient.mk (principalPowerIdeal f n) (σ b)) := by
                          rw [← map_mul]
                  _ =
                      φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a * σ b)) := by
                          simp
              · calc
                  Ideal.Quotient.mk (principalPowerIdeal g n) (g ^ t * z) =
                      Ideal.Quotient.mk (principalPowerIdeal g n) (g ^ t) *
                        Ideal.Quotient.mk (principalPowerIdeal g n) z := by
                          simp
                  _ =
                      (Ideal.Quotient.mk (principalPowerIdeal g n) g) ^ t *
                        φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ (a * b))) := by
                          rw [hz]
                          simp
                  _ =
                      (φ' (Ideal.Quotient.mk (principalPowerIdeal f n) f)) ^ t *
                        φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ (a * b))) := by
                          rw [hgen]
                  _ =
                      φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (f ^ t)) *
                        φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ (a * b))) := by
                          simp
                  _ =
                      φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (f ^ t) *
                        Ideal.Quotient.mk (principalPowerIdeal f n) (σ (a * b))) := by
                          rw [← map_mul]
                  _ =
                      φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (f ^ t * σ (a * b))) := by
                          simp
      _ =
          φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (f ^ t * σ (a * b))) -
            φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (f ^ t * σ (a * b))) := by
              rw [hσmul]
      _ = 0 := sub_self _

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: once the transported numerator ideal contains `g ^ t`, every
higher power `g ^ n` with `2 * t ≤ n` also lies in the transported ideal. -/
lemma large_pow_mem_transported_power_clearing_ideal
    {B' : Type u} [CommRing B']
    (f : A') (g : B') (n t : ℕ)
    (hinj : Function.Injective (algebraMap A' A))
    (σ : A →ₗ[A'] A')
    (hσ : ∀ a : A, algebraMap A' A (σ a) = (algebraMap A' A f) ^ t * a)
    (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
    (hgen : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (hn : 2 * t ≤ n) :
    g ^ n ∈ transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ' := by
  have hpow_t :
      g ^ t ∈ transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ' :=
    pow_mem_transported_power_clearing_ideal
      (A' := A') (A := A) f g n t hinj σ hσ φ' hgen
  have htle : t ≤ n := by
    -- The eventual threshold `2 * t` is more than enough to raise `g ^ t ∈ N` to `g ^ n ∈ N`.
    have htwo : t ≤ 2 * t := by
      simpa [two_mul] using (Nat.le_add_right t t)
    exact htwo.trans hn
  -- Multiply the distinguished element `g ^ t ∈ N` by the remaining power of `g`.
  have hmul_mem :
      g ^ (n - t) * g ^ t ∈
        transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ' :=
    (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ').mul_mem_left
      (g ^ (n - t)) hpow_t
  have hpow_eq : g ^ (n - t) * g ^ t = g ^ n := by
    rw [← pow_add, Nat.sub_add_cancel htle]
  exact hpow_eq ▸ hmul_mem

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: for `n ≥ 2 * t`, the transported numerator ideal already contains
the principal power ideal `(g^n)`. -/
lemma principalPowerIdeal_le_transported_power_clearing_ideal
    {B' : Type u} [CommRing B']
    (f : A') (g : B') (n t : ℕ)
    (hinj : Function.Injective (algebraMap A' A))
    (σ : A →ₗ[A'] A')
    (hσ : ∀ a : A, algebraMap A' A (σ a) = (algebraMap A' A f) ^ t * a)
    (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
    (hgen : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (hn : 2 * t ≤ n) :
    principalPowerIdeal g n ≤
      transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ' := by
  have hpow_n :
      g ^ n ∈ transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ' :=
    large_pow_mem_transported_power_clearing_ideal
      (A' := A') (A := A) f g n t hinj σ hσ φ' hgen hn
  -- The principal-power ideal is generated by `g ^ n`, so the preceding membership is exactly the
  -- desired ideal inclusion.
  simpa [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow] using
    (Ideal.span_singleton_le_iff_mem
      (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ')).2 hpow_n

/-- Helper for Lemma 15.117.3: if `2 * t ≤ n`, then the exponent `n - t` still contains one
remaining factor `t`. -/
lemma pow_split_of_two_mul_le
    {B' : Type u} [CommRing B']
    (g : B') (n t : ℕ)
    (hn : 2 * t ≤ n) :
    g ^ (n - t) = g ^ (n - 2 * t) * g ^ t := by
  have hsub : t ≤ n - t := by
    -- The hypothesis `2 * t ≤ n` is exactly the statement that one copy of `t` remains after
    -- removing the first copy from `n`.
    exact Nat.le_sub_of_add_le (by simpa [two_mul] using hn)
  -- Rewrite the remaining exponent as `((n - t) - t) + t` and split the power.
  calc
    g ^ (n - t) = g ^ (((n - t) - t) + t) := by
      rw [Nat.sub_add_cancel hsub]
    _ = g ^ ((n - t) - t) * g ^ t := by
      rw [pow_add]
    _ = g ^ (n - 2 * t) * g ^ t := by
      rw [Nat.sub_sub, two_mul]

/-- Helper for Lemma 15.117.3: for `n ≥ 2 * t`, the fixed-denominator image of the transported
numerator ideal is closed under multiplication inside `B'[1 / g]`. -/
lemma fraction_map_eq_mk'_fixed_denominator
    {B' : Type u} [CommRing B']
    (g : B') (t : ℕ)
    (N : Ideal B')
    (x : N) :
    fraction_map_of_transported_power_clearing_ideal (g := g) t N x =
      IsLocalization.mk' (Localization.Away g) x.1
        ⟨g ^ t, pow_mem (Submonoid.mem_powers g) t⟩ := by
  -- Unfold the fixed-denominator construction once so later localization equalities use `mk'`.
  rfl

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: for `n ≥ 2 * t`, the fixed-denominator image of the transported
numerator ideal is closed under multiplication inside `B'[1 / g]`. -/
lemma mul_mem_range_fraction_map_of_mem_transported_power_clearing
    {B' : Type u} [CommRing B']
    (f : A') (g : B') (n t : ℕ)
    (hinj : Function.Injective (algebraMap A' A))
    (σ : A →ₗ[A'] A')
    (hσ : ∀ a : A, algebraMap A' A (σ a) = (algebraMap A' A f) ^ t * a)
    (hσmul : ∀ a b : A, σ a * σ b = f ^ t * σ (a * b))
    (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
    (hgen : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (hn : 2 * t ≤ n)
    {x y : B'}
    (hx : x ∈ transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ')
    (hy : y ∈ transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ') :
    fraction_map_of_transported_power_clearing_ideal
        (g := g) t (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ')
        ⟨x, hx⟩ *
    fraction_map_of_transported_power_clearing_ideal
        (g := g) t (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ')
        ⟨y, hy⟩ ∈
      Set.range
        (fraction_map_of_transported_power_clearing_ideal
          (g := g) t (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ')) := by
  let N : Ideal B' := transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ'
  have hgt : g ^ t ∈ Submonoid.powers g := pow_mem (Submonoid.mem_powers g) t
  let s : Submonoid.powers g := ⟨g ^ t, hgt⟩
  have hpow_t : g ^ t ∈ N := by
    -- The transported numerator ideal always contains the distinguished generator `g ^ t`.
    simpa [N] using
      pow_mem_transported_power_clearing_ideal
        (A' := A') (A := A) f g n t hinj σ hσ φ' hgen
  have hpow_tail : g ^ (n - t) ∈ N := by
    -- The eventual bound `2 * t ≤ n` leaves one visible copy of `g ^ t` after removing `t`.
    have hmul :
        g ^ (n - 2 * t) * g ^ t ∈ N :=
      N.mul_mem_left (g ^ (n - 2 * t)) hpow_t
    simpa [N, pow_split_of_two_mul_le (g := g) (n := n) (t := t) hn] using hmul
  obtain ⟨z, hzN, hzpow⟩ :=
    mul_sub_pow_mem_principalPowerIdeal_of_mem_transported_power_clearing
      (A' := A') (A := A) f g n t σ hσmul φ' hgen
      (by simpa [N] using hx) (by simpa [N] using hy)
  rcases
      (Ideal.mem_span_singleton.mp
        (by
          simpa [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow] using hzpow)) with
    ⟨c, hc⟩
  let w : B' := z + c * g ^ (n - t)
  have hwN : w ∈ N := by
    -- The correction term already lies in `N`, so the corrected numerator stays inside `N`.
    refine N.add_mem hzN ?_
    exact N.mul_mem_left c hpow_tail
  have htn : t ≤ n := by
    -- The multiplicative threshold `2 * t ≤ n` implies the weaker bound `t ≤ n`.
    exact Nat.le_trans (by simpa [two_mul] using Nat.le_add_right t t) hn
  have hpow_split : g ^ n = g ^ t * g ^ (n - t) := by
    -- Split the large power into the visible denominator `g ^ t` and the remaining correction term.
    calc
      g ^ n = g ^ (t + (n - t)) := by
        simpa using congrArg (fun m : ℕ => g ^ m) (Nat.add_sub_of_le htn).symm
      _ = g ^ t * g ^ (n - t) := by
        rw [pow_add]
  have hxyw : x * y = g ^ t * w := by
    -- Rewrite the quotient-level error term as an exact numerator correction in `B'`.
    calc
      x * y = c * g ^ n + g ^ t * z := by
        simpa [add_comm, add_left_comm, add_assoc, mul_comm] using (sub_eq_iff_eq_add.mp hc)
      _ = c * (g ^ t * g ^ (n - t)) + g ^ t * z := by
        rw [hpow_split]
      _ = g ^ t * (z + c * g ^ (n - t)) := by
        ring_nf
      _ = g ^ t * w := by
        rfl
  refine ⟨⟨w, hwN⟩, ?_⟩
  -- Route correction: compare fractions through `mk'` and the exact identity `x * y = g ^ t * w`,
  -- rather than normalizing the product by broad localization simplification.
  rw [fraction_map_eq_mk'_fixed_denominator (g := g) (t := t) (N := N) ⟨x, by simpa [N] using hx⟩,
    fraction_map_eq_mk'_fixed_denominator (g := g) (t := t) (N := N) ⟨y, by simpa [N] using hy⟩,
    fraction_map_eq_mk'_fixed_denominator (g := g) (t := t) (N := N) ⟨w, hwN⟩]
  symm
  change IsLocalization.mk' (Localization.Away g) x s *
      IsLocalization.mk' (Localization.Away g) y s =
    IsLocalization.mk' (Localization.Away g) w s
  calc
    IsLocalization.mk' (Localization.Away g) x s *
        IsLocalization.mk' (Localization.Away g) y s =
      IsLocalization.mk' (Localization.Away g) (x * y) (s * s) := by
        rw [← IsLocalization.mk'_mul]
    _ = IsLocalization.mk' (Localization.Away g) w s := by
      refine IsLocalization.mk'_eq_iff_eq'.2 ?_
      -- Cross-multiplication reduces the localization identity to the exact numerator equation.
      exact congrArg (algebraMap B' (Localization.Away g)) <|
        by
          simpa [s, hxyw, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Lemma 15.117.3: the source-faithful target ring is the fixed-denominator range
`g^{-t} N` inside `Localization.Away g`. -/
noncomputable def transported_power_clearing_subalgebra
    {B' : Type u} [CommRing B']
    (f : A') (g : B') (n t : ℕ)
    (hinj : Function.Injective (algebraMap A' A))
    (σ : A →ₗ[A'] A')
    (hσ : ∀ a : A, algebraMap A' A (σ a) = (algebraMap A' A f) ^ t * a)
    (hσmul : ∀ a b : A, σ a * σ b = f ^ t * σ (a * b))
    (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
    (hgen : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (hn : 2 * t ≤ n) :
    Subalgebra B' (Localization.Away g) where
  carrier :=
    Set.range
      (fraction_map_of_transported_power_clearing_ideal
        (g := g) t (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ'))
  zero_mem' := by
    -- Zero is represented by the zero numerator in the transported ideal.
    refine ⟨0, ?_⟩
    simp [fraction_map_of_transported_power_clearing_ideal]
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨x', rfl⟩
    rcases hy with ⟨y', rfl⟩
    refine ⟨x' + y', ?_⟩
    -- The fixed-denominator map is additive because all fractions use the same denominator.
    simp [fraction_map_of_transported_power_clearing_ideal, add_mul]
  one_mem' := by
    -- The transported ideal contains `g ^ t`, so `1 = g ^ t / g ^ t` lies in the range.
    simpa using
      algebraMap_mem_range_fraction_map_of_pow_mem
        (g := g) t
        (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ')
        (by
          exact pow_mem_transported_power_clearing_ideal
            (A' := A') (A := A) f g n t hinj σ hσ φ' hgen)
        1
  mul_mem' := by
    intro x y hx hy
    rcases hx with ⟨x', rfl⟩
    rcases hy with ⟨y', rfl⟩
    -- Multiplication is the direct range-closure statement proved above.
    exact
      mul_mem_range_fraction_map_of_mem_transported_power_clearing
        (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen hn x'.2 y'.2
  algebraMap_mem' := by
    intro b
    -- Every scalar from `B'` is represented by `b * g ^ t / g ^ t`.
    exact
      algebraMap_mem_range_fraction_map_of_pow_mem
        (g := g) t
        (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ')
        (by
          exact pow_mem_transported_power_clearing_ideal
            (A' := A') (A := A) f g n t hinj σ hσ φ' hgen)
        b

/-- Helper for Lemma 15.117.3: once `n ≥ 2 * t`, the transported numerator ideal is finitely
generated because it is the lift of a finitely generated quotient ideal together with the kernel
generator `g ^ n`. -/
lemma transported_power_clearing_ideal_fg
    {B' : Type u} [CommRing B']
    (f : A') (g : B') (n t : ℕ)
    (hinj : Function.Injective (algebraMap A' A))
    (σ : A →ₗ[A'] A')
    (hσ : ∀ a : A, algebraMap A' A (σ a) = (algebraMap A' A f) ^ t * a)
    (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
    (hgen : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (hn : 2 * t ≤ n) :
    (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ').FG := by
  classical
  let π : B' →+* B' ⧸ principalPowerIdeal g n := Ideal.Quotient.mk (principalPowerIdeal g n)
  let J : Ideal (B' ⧸ principalPowerIdeal g n) :=
    Ideal.map φ'.toRingHom
      (Ideal.map (Ideal.Quotient.mk (principalPowerIdeal f n))
        (power_clearing_ideal (A' := A') σ))
  have hsrcfg : (power_clearing_ideal (A' := A') σ).FG := by
    -- The source numerator ideal is the range of the linear map `σ` on the finite `A'`-module `A`.
    change σ.range.FG
    exact Submodule.fg_range σ
  obtain ⟨U, hUfinite, hUspan⟩ := Submodule.fg_def.mp hsrcfg
  have hmap_eq :
      Ideal.map (Ideal.Quotient.mk (principalPowerIdeal f n))
        (power_clearing_ideal (A' := A') σ) =
        Ideal.span ((Ideal.Quotient.mk (principalPowerIdeal f n)) '' U) := by
    -- Rewrite the first quotient image using a concrete finite generating set of the source ideal.
    rw [← hUspan]
    change Ideal.map (Ideal.Quotient.mk (principalPowerIdeal f n)) (Ideal.span U) =
      Ideal.span ((Ideal.Quotient.mk (principalPowerIdeal f n)) '' U)
    rw [Ideal.map_span]
  have hJ_eq :
      J = Ideal.span
        (φ'.toRingHom '' ((Ideal.Quotient.mk (principalPowerIdeal f n)) '' U)) := by
    -- Transport the same finite generating set across the quotient isomorphism.
    change Ideal.map φ'.toRingHom
        (Ideal.map (Ideal.Quotient.mk (principalPowerIdeal f n))
          (power_clearing_ideal (A' := A') σ)) =
      Ideal.span (φ'.toRingHom '' ((Ideal.Quotient.mk (principalPowerIdeal f n)) '' U))
    rw [hmap_eq, Ideal.map_span]
  have hJfg : J.FG := by
    rw [hJ_eq]
    exact Submodule.fg_span ((hUfinite.image _).image _)
  obtain ⟨T, hTfinite, hTspan⟩ := Submodule.fg_def.mp hJfg
  let lift : B' ⧸ principalPowerIdeal g n → B' := fun x ↦
    Classical.choose (Ideal.Quotient.mk_surjective x)
  have hlift : ∀ x : B' ⧸ principalPowerIdeal g n, π (lift x) = x := by
    intro x
    exact Classical.choose_spec (Ideal.Quotient.mk_surjective x)
  let S : Set B' := lift '' T
  have hSfinite : S.Finite := hTfinite.image lift
  have hmapS : Ideal.map π (Ideal.span S) = J := by
    -- Lift a finite generating set of the quotient ideal to `B'`; its span maps back to `J`.
    calc
      Ideal.map π (Ideal.span S) = Ideal.span (π '' S) := by
        rw [Ideal.map_span]
      _ = Ideal.span T := by
        apply congrArg Ideal.span
        ext x
        constructor
        · rintro ⟨y, ⟨z, hz, rfl⟩, hxy⟩
          have hz_eq_x : z = x := by
            simpa [hlift z] using hxy
          simpa [hz_eq_x] using hz
        · intro hx
          refine ⟨lift x, ?_, hlift x⟩
          exact ⟨x, hx, rfl⟩
      _ = J := hTspan
  have hmapN :
      Ideal.map π
          (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ') = J := by
    -- By definition the transported ideal is exactly the full preimage of `J` under `π`.
    simpa [transported_power_clearing_ideal, π, J] using
      Ideal.map_comap_of_surjective π Ideal.Quotient.mk_surjective J
  have hkernel_le :
      principalPowerIdeal g n ≤
        transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ' := by
    -- The eventual threshold already puts the kernel generator `g ^ n` inside the transported ideal.
    exact principalPowerIdeal_le_transported_power_clearing_ideal
      (A' := A') (A := A) f g n t hinj σ hσ φ' hgen hn
  have hsup :
      transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ' ⊔ RingHom.ker π =
        Ideal.span S ⊔ RingHom.ker π := by
    -- Equal quotient images force equality after adjoining the quotient kernel on both sides.
    have hmapEq :
        Ideal.map π
            (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ') =
          Ideal.map π (Ideal.span S) := by
      rw [hmapN, hmapS]
    rw [Ideal.map_eq_iff_sup_ker_eq_of_surjective π Ideal.Quotient.mk_surjective] at hmapEq
    exact hmapEq
  have htransported_eq :
      transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ' =
        Ideal.span (S ∪ ({g ^ n} : Set B')) := by
    -- Rewrite the ideal as a span of lifted generators together with the single kernel generator.
    have hkerle' :
        RingHom.ker π ≤ transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ' := by
      simpa [π, Ideal.mk_ker] using hkernel_le
    calc
      transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ' =
          transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ' ⊔ RingHom.ker π := by
            exact (sup_eq_left.mpr hkerle').symm
      _ = Ideal.span S ⊔ RingHom.ker π := hsup
      _ = Ideal.span S ⊔ principalPowerIdeal g n := by
            simp [π, Ideal.mk_ker]
      _ = Ideal.span S ⊔ Ideal.span ({g ^ n} : Set B') := by
            simp [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow]
      _ = Ideal.span (S ∪ ({g ^ n} : Set B')) := by
            rw [← Ideal.span_union]
  -- The displayed span is finite because it is generated by the finite lift set and one kernel
  -- generator.
  simpa [htransported_eq] using
    (Submodule.fg_span (hSfinite.union (Set.finite_singleton (g ^ n))) :
      (Ideal.span (S ∪ ({g ^ n} : Set B'))).FG)

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: if the cleared numerator `σ a` lands in `(f^n)` with
`t + 1 ≤ n`, then cancelling the visible factor `f ^ t` forces `a` to lie in `(f)`. -/
lemma mem_principalIdeal_of_sigma_mem_principalPowerIdeal
    (f : A') (n t : ℕ)
    (hf : algebraMap A' A f ∈ nonZeroDivisors A)
    (σ : A →ₗ[A'] A')
    (hσ : ∀ a : A, algebraMap A' A (σ a) = (algebraMap A' A f) ^ t * a)
    {a : A}
    (ha : σ a ∈ principalPowerIdeal f n)
    (ht : t + 1 ≤ n) :
    a ∈ principalIdeal (algebraMap A' A f) := by
  rcases
      (Ideal.mem_span_singleton.mp
        (by
          simpa [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow] using ha)) with
    ⟨c, hca⟩
  have htn : t ≤ n := Nat.le_trans (Nat.le_succ t) ht
  have hEq :
      (algebraMap A' A f) ^ t * a =
        (algebraMap A' A f) ^ t * ((algebraMap A' A f) ^ (n - t) * algebraMap A' A c) := by
    have hpow_split :
        (algebraMap A' A f) ^ n =
          (algebraMap A' A f) ^ t * (algebraMap A' A f) ^ (n - t) := by
      calc
        (algebraMap A' A f) ^ n =
            (algebraMap A' A f) ^ (t + (n - t)) := by
              simpa using congrArg (fun m : ℕ => (algebraMap A' A f) ^ m)
                (Nat.add_sub_of_le htn).symm
        _ = (algebraMap A' A f) ^ t * (algebraMap A' A f) ^ (n - t) := by
              rw [pow_add]
    -- Rewrite the image of `σ a` in two ways: once from the clearing formula, and once from the
    -- divisibility witness `σ a = f ^ n * c`.
    calc
      (algebraMap A' A f) ^ t * a = algebraMap A' A (σ a) := by
        symm
        exact hσ a
      _ = algebraMap A' A (f ^ n * c) := by
        simpa [hca]
      _ = (algebraMap A' A f) ^ n * algebraMap A' A c := by
        simp
      _ =
          ((algebraMap A' A f) ^ t * (algebraMap A' A f) ^ (n - t)) *
            algebraMap A' A c := by
            rw [hpow_split]
      _ =
          (algebraMap A' A f) ^ t *
            ((algebraMap A' A f) ^ (n - t) * algebraMap A' A c) := by
            simp [mul_assoc]
  have hcancel :
      a = (algebraMap A' A f) ^ (n - t) * algebraMap A' A c := by
    -- Cancel the common factor `(algebraMap A' A f) ^ t`, which remains a nonzerodivisor.
    have hpow_nd :
        (algebraMap A' A f) ^ t ∈ nonZeroDivisors A := pow_mem hf t
    have hpow_cancel :
        ∀ x : A, (algebraMap A' A f) ^ t * x = 0 → x = 0 :=
      (mem_nonZeroDivisors_iff.mp hpow_nd).1
    have hzero :
        (algebraMap A' A f) ^ t *
          (a - ((algebraMap A' A f) ^ (n - t) * algebraMap A' A c)) = 0 := by
      simpa [mul_sub] using sub_eq_zero.mpr hEq
    exact sub_eq_zero.mp (hpow_cancel _ hzero)
  have ha_pow :
      a ∈ principalPowerIdeal (algebraMap A' A f) (n - t) := by
    -- After cancellation, `a` is visibly a multiple of `(algebraMap f)^(n - t)`.
    rw [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.mpr ⟨algebraMap A' A c, hcancel⟩
  have hpow_pos : n - t ≠ 0 := by
    -- The strict inequality `t < n` comes from `t + 1 ≤ n`.
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self t) ht))
  -- Since `n - t ≥ 1`, membership in `((algebraMap f)^(n - t))` descends to membership in
  -- the first power `(algebraMap f)`.
  exact
    (show principalPowerIdeal (algebraMap A' A f) (n - t) ≤ principalIdeal (algebraMap A' A f) from
        by
          simpa [principalPowerIdeal] using
            (Ideal.pow_le_self (I := principalIdeal (algebraMap A' A f)) hpow_pos))
      ha_pow

/-- Helper for Lemma 15.117.3: the fixed-denominator map sends the numerator `b * g ^ t` to the
scalar `b` in the localization, since the visible denominator `g ^ t` cancels immediately. -/
lemma fraction_map_of_transported_power_clearing_ideal_mul_pow
    {B' : Type u} [CommRing B']
    (g : B') (t : ℕ)
    (N : Ideal B')
    (hpow : g ^ t ∈ N)
    (b : B') :
    fraction_map_of_transported_power_clearing_ideal (g := g) t N
        ⟨b * g ^ t, N.mul_mem_left b hpow⟩ =
      algebraMap B' (Localization.Away g) b := by
  have hgt : g ^ t ∈ Submonoid.powers g := by
    exact pow_mem (Submonoid.mem_powers g) t
  let ug : Units (Localization.Away g) :=
    (IsLocalization.map_units (Localization.Away g) ⟨g ^ t, hgt⟩).unit
  -- Expand the fixed denominator once and cancel the visible factor `g ^ t`.
  calc
    fraction_map_of_transported_power_clearing_ideal (g := g) t N
        ⟨b * g ^ t, N.mul_mem_left b hpow⟩ =
      algebraMap B' (Localization.Away g) (b * g ^ t) * ↑(ug⁻¹) := by
        simp [fraction_map_of_transported_power_clearing_ideal, ug]
    _ = algebraMap B' (Localization.Away g) b * (↑ug * ↑(ug⁻¹)) := by
        simp [ug, mul_assoc, mul_comm]
    _ = algebraMap B' (Localization.Away g) b := by
        simp

/-- Helper for Lemma 15.117.3: if `t + 1 ≤ n`, then one visible factor of `g` remains after
splitting off the fixed denominator power `g ^ t` from `g ^ n`. -/
lemma pow_split_off_fixed_denominator
    {R : Type u} [CommRing R]
    (g : R) (n t : ℕ)
    (ht : t + 1 ≤ n) :
    g ^ n = g * (g ^ (n - (t + 1)) * g ^ t) := by
  -- Rewrite `n` as the cleared denominator part `t + 1` plus the remaining exponent.
  calc
    g ^ n = g ^ ((t + 1) + (n - (t + 1))) := by
      simpa using congrArg (fun m : ℕ => g ^ m) (Nat.add_sub_of_le ht).symm
    _ = g ^ (t + 1) * g ^ (n - (t + 1)) := by
      rw [pow_add]
    _ = (g * g ^ t) * g ^ (n - (t + 1)) := by
      rw [pow_succ']
    _ = g * (g ^ (n - (t + 1)) * g ^ t) := by
      ring_nf

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: if two numerators differ by a multiple of `g ^ n`, then their
fixed-denominator fractions differ by a visible factor of `g` inside `g^{-t} N`. -/
lemma fixed_denominator_sub_mem_principalIdeal_of_sub_mem_principalPowerIdeal
    {B' : Type u} [CommRing B']
    (f : A') (g : B') (n t : ℕ)
    (hinj : Function.Injective (algebraMap A' A))
    (σ : A →ₗ[A'] A')
    (hσ : ∀ a : A, algebraMap A' A (σ a) = (algebraMap A' A f) ^ t * a)
    (hσmul : ∀ a b : A, σ a * σ b = f ^ t * σ (a * b))
    (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
    (hgen : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (hn : 2 * t ≤ n)
    (ht : t + 1 ≤ n)
    {x y : transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ'}
    (hxy : x.1 - y.1 ∈ principalPowerIdeal g n) :
    let N := transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ'
    let B :=
      transported_power_clearing_subalgebra
        (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen hn
    ((⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N x, ⟨x, rfl⟩⟩ : B) -
        ⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N y, ⟨y, rfl⟩⟩) ∈
      principalIdeal (algebraMap B' B g) := by
  dsimp
  let B :=
    transported_power_clearing_subalgebra
      (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen hn
  rw [principalIdeal]
  rcases
      (Ideal.mem_span_singleton.mp
        (by
          simpa [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow] using hxy)) with
    ⟨c, hc⟩
  refine Ideal.mem_span_singleton.mpr
    ⟨algebraMap B' B (g ^ (n - (t + 1)) * c), ?_⟩
  apply Subtype.ext
  change
    fraction_map_of_transported_power_clearing_ideal
        (g := g) t
        (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ') x -
      fraction_map_of_transported_power_clearing_ideal
        (g := g) t
        (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ') y =
      algebraMap B' (Localization.Away g) g *
        algebraMap B' (Localization.Away g) (g ^ (n - (t + 1)) * c)
  have hgt : g ^ t ∈ Submonoid.powers g := pow_mem (Submonoid.mem_powers g) t
  let ug : Units (Localization.Away g) :=
    (IsLocalization.map_units (Localization.Away g) ⟨g ^ t, hgt⟩).unit
  -- Rewrite the fraction difference with the common fixed denominator `g ^ t`.
  calc
    fraction_map_of_transported_power_clearing_ideal
        (g := g) t
        (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ') x -
      fraction_map_of_transported_power_clearing_ideal
        (g := g) t
        (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ') y =
      algebraMap B' (Localization.Away g) (x.1 - y.1) * ↑(ug⁻¹) := by
        simp [fraction_map_of_transported_power_clearing_ideal, ug, sub_eq_add_neg, add_mul]
    _ = algebraMap B' (Localization.Away g) (g ^ n * c) * ↑(ug⁻¹) := by
        rw [hc]
    _ =
        algebraMap B' (Localization.Away g)
            (g * (g ^ (n - (t + 1)) * c) * g ^ t) * ↑(ug⁻¹) := by
        congr 1
        exact congrArg (algebraMap B' (Localization.Away g)) <|
          by
            calc
              g ^ n * c = (g * (g ^ (n - (t + 1)) * g ^ t)) * c := by
                rw [pow_split_off_fixed_denominator (g := g) (n := n) (t := t) ht]
              _ = g * (g ^ (n - (t + 1)) * c) * g ^ t := by
                ring_nf
    _ = algebraMap B' (Localization.Away g) g *
          algebraMap B' (Localization.Away g) (g ^ (n - (t + 1)) * c) *
            (algebraMap B' (Localization.Away g) (g ^ t) * ↑(ug⁻¹)) := by
        simp [mul_assoc, mul_left_comm, mul_comm]
    _ = algebraMap B' (Localization.Away g) g *
          algebraMap B' (Localization.Away g) (g ^ (n - (t + 1)) * c) := by
        simp [ug, mul_comm]

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: the preceding in-`B` divisibility statement immediately descends to
equality of quotient classes modulo `(g)`. -/
lemma fraction_map_congr_mod_principalIdeal_of_sub_mem_principalPowerIdeal
    {B' : Type u} [CommRing B']
    (f : A') (g : B') (n t : ℕ)
    (hinj : Function.Injective (algebraMap A' A))
    (σ : A →ₗ[A'] A')
    (hσ : ∀ a : A, algebraMap A' A (σ a) = (algebraMap A' A f) ^ t * a)
    (hσmul : ∀ a b : A, σ a * σ b = f ^ t * σ (a * b))
    (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
    (hgen : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (hn : 2 * t ≤ n)
    (ht : t + 1 ≤ n)
    {x y : transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ'}
    (hxy : x.1 - y.1 ∈ principalPowerIdeal g n) :
    let N := transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ'
    let B :=
      transported_power_clearing_subalgebra
        (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen hn
    Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
        (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N x, ⟨x, rfl⟩⟩ : B) =
      Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
        (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N y, ⟨y, rfl⟩⟩ : B) := by
  dsimp
  rw [Ideal.Quotient.eq]
  -- The quotient equality is exactly the visible-factor divisibility statement applied to the
  -- difference of the two fixed-denominator fractions.
  simpa using
    fixed_denominator_sub_mem_principalIdeal_of_sub_mem_principalPowerIdeal
      (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen hn ht hxy

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: under the eventual bound `2 * t ≤ n`, the product of two
transported numerators is exactly `g ^ t` times another transported numerator. -/
lemma exists_corrected_product_numerator
    {B' : Type u} [CommRing B']
    (f : A') (g : B') (n t : ℕ)
    (hinj : Function.Injective (algebraMap A' A))
    (σ : A →ₗ[A'] A')
    (hσ : ∀ a : A, algebraMap A' A (σ a) = (algebraMap A' A f) ^ t * a)
    (hσmul : ∀ a b : A, σ a * σ b = f ^ t * σ (a * b))
    (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
    (hgen : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (hn : 2 * t ≤ n)
    (x y : transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ') :
    ∃ w : transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ',
      x.1 * y.1 = g ^ t * w.1 := by
  let N : Ideal B' := transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ'
  have hpow_t : g ^ t ∈ N := by
    -- The transported numerator ideal always contains the distinguished power `g ^ t`.
    simpa [N] using
      pow_mem_transported_power_clearing_ideal
        (A' := A') (A := A) f g n t hinj σ hσ φ' hgen
  have hpow_tail : g ^ (n - t) ∈ N := by
    -- The eventual bound leaves a second copy of `g ^ t` after removing the fixed denominator.
    have hmul : g ^ (n - 2 * t) * g ^ t ∈ N :=
      N.mul_mem_left (g ^ (n - 2 * t)) hpow_t
    simpa [N, pow_split_of_two_mul_le (g := g) (n := n) (t := t) hn] using hmul
  obtain ⟨z, hzN, hzpow⟩ :=
    mul_sub_pow_mem_principalPowerIdeal_of_mem_transported_power_clearing
      (A' := A') (A := A) f g n t σ hσmul φ' hgen x.2 y.2
  rcases
      (Ideal.mem_span_singleton.mp
        (by
          simpa [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow] using hzpow)) with
    ⟨c, hc⟩
  let w : B' := z + c * g ^ (n - t)
  have hwN : w ∈ N := by
    -- The correction term already lies in `N`, so the adjusted numerator stays transported.
    refine N.add_mem hzN ?_
    exact N.mul_mem_left c hpow_tail
  have htn : t ≤ n := by
    -- The multiplicative threshold immediately implies the weaker cancellation bound.
    exact Nat.le_trans (by simpa [two_mul] using Nat.le_add_right t t) hn
  have hpow_split : g ^ n = g ^ t * g ^ (n - t) := by
    -- Split the large power into the fixed denominator part and the visible correction term.
    calc
      g ^ n = g ^ (t + (n - t)) := by
        simpa using congrArg (fun m : ℕ => g ^ m) (Nat.add_sub_of_le htn).symm
      _ = g ^ t * g ^ (n - t) := by
        rw [pow_add]
  refine ⟨⟨w, hwN⟩, ?_⟩
  -- Route correction: the multiplicative step needs the exact corrected numerator witness,
  -- not only range-closure of the fixed-denominator fractions.
  calc
    x.1 * y.1 = c * g ^ n + g ^ t * z := by
      simpa [add_comm, add_left_comm, add_assoc, mul_comm] using (sub_eq_iff_eq_add.mp hc)
    _ = c * (g ^ t * g ^ (n - t)) + g ^ t * z := by
      rw [hpow_split]
    _ = g ^ t * (z + c * g ^ (n - t)) := by
      ring_nf
    _ = g ^ t * w := by
      rfl

/-- Helper for Lemma 15.117.3: cancelling a visible power of a nonzerodivisor lowers the exponent
of principal-power divisibility by the same amount. -/
lemma mem_principalPowerIdeal_of_mul_pow_mem_principalPowerIdeal
    {B' : Type u} [CommRing B']
    (g : B') (n t : ℕ)
    (hg : g ∈ nonZeroDivisors B')
    (htn : t ≤ n)
    {u : B'}
    (hu : g ^ t * u ∈ principalPowerIdeal g n) :
    u ∈ principalPowerIdeal g (n - t) := by
  rcases
      (Ideal.mem_span_singleton.mp
        (by
          simpa [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow] using hu)) with
    ⟨c, hcu⟩
  have hpow_split : g ^ n = g ^ t * g ^ (n - t) := by
    -- Rewrite `g ^ n` by splitting off the cancelled power `g ^ t`.
    calc
      g ^ n = g ^ (t + (n - t)) := by
        simpa using congrArg (fun m : ℕ => g ^ m) (Nat.add_sub_of_le htn).symm
      _ = g ^ t * g ^ (n - t) := by
        rw [pow_add]
  have hEq : g ^ t * u = g ^ t * (g ^ (n - t) * c) := by
    -- Express the divisibility witness with the visible factor `g ^ t` pulled out.
    calc
      g ^ t * u = g ^ n * c := by
        simpa [mul_comm] using hcu
      _ = (g ^ t * g ^ (n - t)) * c := by
        rw [hpow_split]
      _ = g ^ t * (g ^ (n - t) * c) := by
        simp [mul_assoc]
  have hpow_nd : g ^ t ∈ nonZeroDivisors B' := pow_mem hg t
  have hpow_cancel :
      ∀ z : B', g ^ t * z = 0 → z = 0 :=
    (mem_nonZeroDivisors_iff.mp hpow_nd).1
  have hzero : g ^ t * (u - g ^ (n - t) * c) = 0 := by
    simpa [mul_sub] using sub_eq_zero.mpr hEq
  have hu_eq : u = g ^ (n - t) * c := by
    exact sub_eq_zero.mp (hpow_cancel _ hzero)
  -- The cancelled equality is exactly the membership statement for `(g ^ (n - t))`.
  rw [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton.mpr ⟨c, hu_eq⟩

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: after cancelling the fixed denominator `g ^ t`, a numerator
difference divisible by `g ^ (t + 1)` already vanishes modulo `(g)` in `g^{-t} N`. -/
lemma fraction_map_congr_mod_principalIdeal_of_sub_mem_principalPowerIdeal_succ
    {B' : Type u} [CommRing B']
    (f : A') (g : B') (n t : ℕ)
    (hinj : Function.Injective (algebraMap A' A))
    (σ : A →ₗ[A'] A')
    (hσ : ∀ a : A, algebraMap A' A (σ a) = (algebraMap A' A f) ^ t * a)
    (hσmul : ∀ a b : A, σ a * σ b = f ^ t * σ (a * b))
    (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
    (hgen : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (hn : 2 * t ≤ n)
    {x y : transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ'}
    (hxy : x.1 - y.1 ∈ principalPowerIdeal g (t + 1)) :
    let N := transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ'
    let B :=
      transported_power_clearing_subalgebra
        (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen hn
    Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
        (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N x, ⟨x, rfl⟩⟩ : B) =
      Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
        (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N y, ⟨y, rfl⟩⟩ : B) := by
  dsimp
  let B :=
    transported_power_clearing_subalgebra
      (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen hn
  rw [Ideal.Quotient.eq]
  rw [principalIdeal]
  rcases
      (Ideal.mem_span_singleton.mp
        (by
          simpa [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow] using hxy)) with
    ⟨c, hc⟩
  refine Ideal.mem_span_singleton.mpr ⟨algebraMap B' B c, ?_⟩
  apply Subtype.ext
  change
    fraction_map_of_transported_power_clearing_ideal
        (g := g) t
        (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ') x -
      fraction_map_of_transported_power_clearing_ideal
        (g := g) t
        (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ') y =
      algebraMap B' (Localization.Away g) g * algebraMap B' (Localization.Away g) c
  have hgt : g ^ t ∈ Submonoid.powers g := pow_mem (Submonoid.mem_powers g) t
  let ug : Units (Localization.Away g) :=
    (IsLocalization.map_units (Localization.Away g) ⟨g ^ t, hgt⟩).unit
  -- Compare the difference with the common fixed denominator, then split off one visible factor
  -- of `g` from the numerator difference.
  calc
    fraction_map_of_transported_power_clearing_ideal
        (g := g) t
        (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ') x -
      fraction_map_of_transported_power_clearing_ideal
        (g := g) t
        (transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ') y =
      algebraMap B' (Localization.Away g) (x.1 - y.1) * ↑(ug⁻¹) := by
        simp [fraction_map_of_transported_power_clearing_ideal, ug, sub_eq_add_neg, add_mul]
    _ = algebraMap B' (Localization.Away g) (g ^ (t + 1) * c) * ↑(ug⁻¹) := by
        rw [hc]
    _ = algebraMap B' (Localization.Away g) (g * (g ^ t * c)) * ↑(ug⁻¹) := by
        congr 1
        rw [pow_succ']
        ring_nf
    _ =
        algebraMap B' (Localization.Away g) g *
          algebraMap B' (Localization.Away g) c *
            (algebraMap B' (Localization.Away g) (g ^ t) * ↑(ug⁻¹)) := by
        simp [mul_assoc, mul_comm]
    _ = algebraMap B' (Localization.Away g) g * algebraMap B' (Localization.Away g) c := by
        simp [ug, mul_comm]

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: the chosen transported numerator of `0` already vanishes modulo
`(g ^ n)`. -/
lemma numerator_zero_mem_principalPowerIdeal
    {B' : Type u} [CommRing B']
    (f : A') (g : B') (n : ℕ)
    (σ : A →ₗ[A'] A')
    (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
    (numerator : A → B')
    (hnumerator :
      ∀ a : A,
        Ideal.Quotient.mk (principalPowerIdeal g n) (numerator a) =
          φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a))) :
    numerator 0 ∈ principalPowerIdeal g n := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  -- The chosen numerator for `0` maps to the zero quotient class because `σ` is linear.
  calc
    Ideal.Quotient.mk (principalPowerIdeal g n) (numerator 0) =
        φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ 0)) := by
          exact hnumerator 0
    _ = 0 := by
          simp

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: the chosen transported numerators respect addition modulo
`(g ^ n)`. -/
lemma numerator_add_sub_mem_principalPowerIdeal
    {B' : Type u} [CommRing B']
    (f : A') (g : B') (n : ℕ)
    (σ : A →ₗ[A'] A')
    (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
    (numerator : A → B')
    (hnumerator :
      ∀ a : A,
        Ideal.Quotient.mk (principalPowerIdeal g n) (numerator a) =
          φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a)))
    (a b : A) :
    numerator (a + b) - (numerator a + numerator b) ∈ principalPowerIdeal g n := by
  rw [← Ideal.Quotient.eq]
  -- Compare both numerator choices in the quotient ring, where they both represent `[σ a] + [σ b]`.
  calc
    Ideal.Quotient.mk (principalPowerIdeal g n) (numerator (a + b)) =
        φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ (a + b))) := by
          exact hnumerator (a + b)
    _ =
        φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a) +
          Ideal.Quotient.mk (principalPowerIdeal f n) (σ b)) := by
          simp
    _ =
        φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a)) +
          φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ b)) := by
          rw [map_add]
    _ =
        Ideal.Quotient.mk (principalPowerIdeal g n) (numerator a) +
          Ideal.Quotient.mk (principalPowerIdeal g n) (numerator b) := by
          rw [hnumerator a, hnumerator b]
    _ = Ideal.Quotient.mk (principalPowerIdeal g n) (numerator a + numerator b) := by
          simp

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: the chosen transported numerators satisfy the source multiplication
identity modulo `(g ^ n)`. -/
lemma numerator_mul_sub_pow_mem_principalPowerIdeal
    {B' : Type u} [CommRing B']
    (f : A') (g : B') (n t : ℕ)
    (σ : A →ₗ[A'] A')
    (hσmul : ∀ a b : A, σ a * σ b = f ^ t * σ (a * b))
    (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
    (hgen : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (numerator : A → B')
    (hnumerator :
      ∀ a : A,
        Ideal.Quotient.mk (principalPowerIdeal g n) (numerator a) =
          φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a)))
    (a b : A) :
    numerator a * numerator b - g ^ t * numerator (a * b) ∈ principalPowerIdeal g n := by
  rw [← Ideal.Quotient.eq]
  -- Transport the source identity `σ a * σ b = f ^ t * σ (a * b)` across `φ'` and compare
  -- with the chosen representatives `numerator a`, `numerator b`, and `numerator (a * b)`.
  calc
    Ideal.Quotient.mk (principalPowerIdeal g n) (numerator a * numerator b) =
        Ideal.Quotient.mk (principalPowerIdeal g n) (numerator a) *
          Ideal.Quotient.mk (principalPowerIdeal g n) (numerator b) := by
            simp
    _ =
        φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a)) *
          φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ b)) := by
            rw [hnumerator a, hnumerator b]
    _ =
        φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a) *
          Ideal.Quotient.mk (principalPowerIdeal f n) (σ b)) := by
            rw [← map_mul]
    _ = φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ a * σ b)) := by
          simp
    _ = φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (f ^ t * σ (a * b))) := by
          rw [hσmul]
    _ =
        φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (f ^ t)) *
          φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (σ (a * b))) := by
          rw [map_mul]
          simp
    _ =
        φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (f ^ t)) *
          Ideal.Quotient.mk (principalPowerIdeal g n) (numerator (a * b)) := by
          rw [← hnumerator (a * b)]
    _ =
        (Ideal.Quotient.mk (principalPowerIdeal g n) g) ^ t *
          Ideal.Quotient.mk (principalPowerIdeal g n) (numerator (a * b)) := by
          congr 1
          calc
            φ' (Ideal.Quotient.mk (principalPowerIdeal f n) (f ^ t)) =
                φ' (Ideal.Quotient.mk (principalPowerIdeal f n) f) ^ t := by
                  simp
            _ = (Ideal.Quotient.mk (principalPowerIdeal g n) g) ^ t := by
                  rw [hgen]
    _ =
        (Ideal.Quotient.mk (principalPowerIdeal g n) g) ^ t *
          Ideal.Quotient.mk (principalPowerIdeal g n) (numerator (a * b)) := by
          simp
    _ = Ideal.Quotient.mk (principalPowerIdeal g n) (g ^ t * numerator (a * b)) := by
          simp

/-- Helper for Lemma 15.117.3: equality of fixed-denominator fractions in `B'[1 / g]` already
forces equality of the underlying transported numerators. -/
lemma fraction_map_of_transported_power_clearing_ideal_injective
    {B' : Type u} [CommRing B']
    (g : B') (t : ℕ)
    (N : Ideal B')
    (hg : g ∈ nonZeroDivisors B') :
    Function.Injective (fraction_map_of_transported_power_clearing_ideal (g := g) t N) := by
  intro x y hxy
  apply Subtype.ext
  have hdenom :
      Submonoid.powers g ≤ nonZeroDivisors B' := by
    intro z hz
    rcases hz with ⟨m, rfl⟩
    exact pow_mem hg m
  have hloc_injective :
      Function.Injective (algebraMap B' (Localization.Away g)) :=
    IsLocalization.injective (Localization.Away g) hdenom
  have hpow_nd : g ^ t ∈ nonZeroDivisors B' := pow_mem hg t
  have hpow_cancel :
      ∀ z : B', g ^ t * z = 0 → z = 0 :=
    (mem_nonZeroDivisors_iff.mp hpow_nd).1
  rw [fraction_map_eq_mk'_fixed_denominator (g := g) (t := t) (N := N) x,
    fraction_map_eq_mk'_fixed_denominator (g := g) (t := t) (N := N) y] at hxy
  have hcross :
      algebraMap B' (Localization.Away g) (x.1 * g ^ t) =
        algebraMap B' (Localization.Away g) (y.1 * g ^ t) := by
    exact (IsLocalization.mk'_eq_iff_eq'.1 hxy)
  have hmul_eq : x.1 * g ^ t = y.1 * g ^ t := hloc_injective hcross
  have hzero :
      g ^ t * (x.1 - y.1) = 0 := by
    calc
      g ^ t * (x.1 - y.1) = g ^ t * x.1 - g ^ t * y.1 := by
        rw [mul_sub]
      _ = x.1 * g ^ t - y.1 * g ^ t := by
        simp [mul_comm]
      _ = 0 := by
        rw [hmul_eq, sub_self]
  exact sub_eq_zero.mp (hpow_cancel _ hzero)

omit [Module.Finite A' A] in
/-- Helper for Lemma 15.117.3: if a fixed-denominator numerator class vanishes modulo `(g)` in the
transported target ring `g^{-t} N`, then the original numerator is already an exact multiple of
`g` in `B'`. -/
lemma numerator_eq_g_mul_of_zeroClass_fixed_denominator
    {B' : Type u} [CommRing B']
    (f : A') (g : B') (n t : ℕ)
    (hinj : Function.Injective (algebraMap A' A))
    (σ : A →ₗ[A'] A')
    (hσ : ∀ a : A, algebraMap A' A (σ a) = (algebraMap A' A f) ^ t * a)
    (hσmul : ∀ a b : A, σ a * σ b = f ^ t * σ (a * b))
    (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
    (hgen : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (hn : 2 * t ≤ n)
    (hg : g ∈ nonZeroDivisors B')
    {x : transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ'}
    (hzero :
      let N := transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ'
      let B :=
        transported_power_clearing_subalgebra
          (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen hn
      Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
        (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N x, ⟨x, rfl⟩⟩ : B) = 0) :
    ∃ y : transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ',
      x.1 = g * y.1 := by
  dsimp at hzero ⊢
  let N : Ideal B' := transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ'
  let B :=
    transported_power_clearing_subalgebra
      (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen hn
  rw [Ideal.Quotient.eq_zero_iff_mem] at hzero
  rw [principalIdeal] at hzero
  rcases Ideal.mem_span_singleton.mp hzero with ⟨b, hb⟩
  rcases b.2 with ⟨y, hy⟩
  let gy : N := ⟨g * y.1, N.mul_mem_left g y.2⟩
  refine ⟨y, ?_⟩
  have hloc :
      fraction_map_of_transported_power_clearing_ideal (g := g) t N x =
        algebraMap B' (Localization.Away g) g *
          fraction_map_of_transported_power_clearing_ideal (g := g) t N y := by
    -- Forgetting the subtype equality back to the localization exposes the visible scalar factor.
    have hlocB := congrArg Subtype.val hb
    calc
      fraction_map_of_transported_power_clearing_ideal (g := g) t N x =
          b.1 * algebraMap B' (Localization.Away g) g := by
            simpa [B, fraction_map_of_transported_power_clearing_ideal, mul_assoc, mul_left_comm,
              mul_comm] using hlocB
      _ =
          fraction_map_of_transported_power_clearing_ideal (g := g) t N y *
            algebraMap B' (Localization.Away g) g := by
            rw [← hy]
      _ =
          algebraMap B' (Localization.Away g) g *
            fraction_map_of_transported_power_clearing_ideal (g := g) t N y := by
            rw [mul_comm]
  have hfrac :
      fraction_map_of_transported_power_clearing_ideal (g := g) t N x =
        fraction_map_of_transported_power_clearing_ideal (g := g) t N gy := by
    -- Rewrite the scalar multiple of the fixed-denominator fraction as the fixed-denominator
    -- fraction of the exact numerator `g * y.1`.
    calc
      fraction_map_of_transported_power_clearing_ideal (g := g) t N x =
          algebraMap B' (Localization.Away g) g *
            fraction_map_of_transported_power_clearing_ideal (g := g) t N y := hloc
      _ =
          fraction_map_of_transported_power_clearing_ideal (g := g) t N gy := by
            simp [gy, fraction_map_of_transported_power_clearing_ideal, mul_assoc]
  have hxy :
      x = gy :=
    fraction_map_of_transported_power_clearing_ideal_injective
      (g := g) (t := t) N hg hfrac
  -- Injectivity of the fixed-denominator map now turns the localization equality back into the
  -- exact numerator equality in `B'`.
  calc
    x.1 = gy.1 := congrArg Subtype.val hxy
    _ = g * y.1 := by
          rfl

-- Proof sketch: choose `t > 0` with `f ^ t A ⊆ A'` using finiteness of `A` over `A'` and
-- bijectivity of the canonical map `A'_f → A_f`, then take a positive threshold `n₀ = 2 * t`.
-- For `n ≥ n₀`,
-- transport the image of `f ^ t A` through `φ'` to construct a finite `B'`-subalgebra
-- `B ⊆ B'[1 / g]`, and compare the induced quotients modulo `f` and `g` in `CommRingCat`.
/-- Lemma 15.117.3 in Section `0GLQ`: if `A` is finite over `A'`, the image of `f` is a
nonzerodivisor on `A`, and the canonical localized map `A'_f → A_f` is bijective, then for all
sufficiently large positive integers `n` every isomorphism `A' / (f^n) ≃ B' / (g^n)` sending the
class of `f` to the class of `g` lifts to an injective finite extension `B' ⊆ B` together with a
compatible isomorphism
`A / (f) ≃ B / (g)`. -/
@[stacks 0GLT]
theorem exists_eventual_finite_extension_and_quotientIso_lift_of_power_quotientIso
    (f : A')
    (hinj : Function.Injective (algebraMap A' A))
    (hf : algebraMap A' A f ∈ nonZeroDivisors A)
    (hAway : Function.Bijective (Localization.awayMapₐ (Algebra.ofId A' A) f)) :
    ∃ n0 : ℕ+, ∀ ⦃n : ℕ+⦄, (hn : n0 ≤ n) →
        ∀ {B' : Type u} [CommRing B']
          (g : B') (_hg : g ∈ nonZeroDivisors B')
          (φ' : A' ⧸ principalPowerIdeal f n ≃+* B' ⧸ principalPowerIdeal g n)
          (_hgen : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g),
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
                    (Nat.succ_le_of_lt n.2)) := by
  -- Route correction: the proof has to follow the source denominator-clearing construction,
  -- starting from a uniform exponent `t` extracted from `hAway` and `Module.Finite A' A`.
  obtain ⟨t, htpos, hclear⟩ :=
    exists_uniform_power_mul_mem_base (A' := A') (A := A) f hf hAway
  let σ := power_clearing_linearMap (A' := A') (A := A) f t hinj hclear
  have hσ : ∀ a : A, algebraMap A' A (σ a) = (algebraMap A' A f) ^ t * a := by
    intro a
    -- This fixes the numerator choice once and for all before transporting it through `φ'`.
    simpa [σ] using
      power_clearing_linearMap_spec (A' := A') (A := A) f t hinj hclear a
  have hσmul :
      ∀ a b : A, σ a * σ b = f ^ t * σ (a * b) := by
    intro a b
    -- This is the multiplicative source invariant needed for the later transported ideal `N`.
    simpa [σ] using
      power_clearing_linearMap_mul (A' := A') (A := A) f t hinj hclear a b
  refine ⟨⟨2 * t + 1, Nat.succ_pos _⟩, ?_⟩
  intro n hn B' _ g hg φ' hgen
  have hn_large : 2 * t + 1 ≤ (n : ℕ) := hn
  have hn_transport : 2 * t ≤ (n : ℕ) := by
    exact Nat.le_trans (Nat.le_succ (2 * t)) hn_large
  have hn_shift : t + 1 ≤ (n : ℕ) := by
    have hbound : t + 1 ≤ 2 * t + 1 := by
      exact Nat.add_le_add_right (by simpa [two_mul] using Nat.le_add_right t t) 1
    exact hbound.trans hn_large
  let N : Ideal B' := transported_power_clearing_ideal (A' := A') (A := A) f g n σ φ'
  have hpowN : g ^ (n : ℕ) ∈ N := by
    -- Step 1 of the source route is now verified: after transport, the full kernel `(g^n)` lies
    -- in the numerator ideal once `n ≥ 2 * t`.
    simpa [N] using
      large_pow_mem_transported_power_clearing_ideal
        (A' := A') (A := A) f g n t hinj σ hσ φ' hgen hn_transport
  have hkernel_le : principalPowerIdeal g n ≤ N := by
    -- This is the exact kernel-control input needed for the later quotient-independent
    -- denominator-clearing construction inside `Localization.Away g`.
    simpa [N] using
      principalPowerIdeal_le_transported_power_clearing_ideal
        (A' := A') (A := A) f g n t hinj σ hσ φ' hgen hn_transport
  have hscalarRange :
      ∀ b : B',
        algebraMap B' (Localization.Away g) b ∈
          Set.range (fraction_map_of_transported_power_clearing_ideal (g := g) t N) := by
    intro b
    -- The fixed denominator `g ^ t` already lets every scalar of `B'` enter the later target
    -- localization object `g^{-t} N`.
    exact algebraMap_mem_range_fraction_map_of_pow_mem (g := g) t N
      (by
        simpa [N] using
          pow_mem_transported_power_clearing_ideal
            (A' := A') (A := A) f g n t hinj σ hσ φ' hgen)
      b
  have hNfg : N.FG := by
    -- The transported ideal is now known to be finitely generated before packaging `g^{-t} N`.
    simpa [N] using
      transported_power_clearing_ideal_fg
        (A' := A') (A := A) f g n t hinj σ hσ φ' hgen hn_transport
  let B :=
    transported_power_clearing_subalgebra
      (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen
      hn_transport
  let FB : N →ₗ[B'] B :=
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
  have hFB_surjective : Function.Surjective FB := by
    intro b
    rcases b.2 with ⟨x, hx⟩
    refine ⟨x, Subtype.ext ?_⟩
    exact hx
  have hB_injective : Function.Injective (algebraMap B' B) := by
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
    -- Forgetting from the subtype `B` back to `Localization.Away g` reduces injectivity to the
    -- ambient localization.
    exact congrArg Subtype.val hEq
  letI : Module.Finite B' N := Module.Finite.of_fg hNfg
  have hBfinite : Module.Finite B' B := Module.Finite.of_surjective FB hFB_surjective
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
  let liftedNumerator : A → B := fun a ↦
    ⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N
        ⟨numerator a, hnumerator_mem a⟩,
      ⟨⟨numerator a, hnumerator_mem a⟩, rfl⟩⟩
  have hliftedNumerator_val :
      ∀ a : A,
        ((liftedNumerator a : B) : Localization.Away g) =
          fraction_map_of_transported_power_clearing_ideal (g := g) t N
            ⟨numerator a, hnumerator_mem a⟩ := by
    intro a
    rfl
  -- TODO for Lemma 15.117.3: the remaining source-faithful step is the quotient descent
  -- `A → B / (g)`. The stabilized frontier is now:
  -- 1. `B = g^{-t} N` is a finite injective `B'`-algebra;
  -- 2. each `a : A` has a fixed transported numerator `numerator a ∈ N` with
  --    `φ'([σ a]) = [numerator a]`;
  -- 3. the fixed-denominator congruence has been isolated in the reusable lemmas
  --    `fixed_denominator_sub_mem_principalIdeal_of_sub_mem_principalPowerIdeal` and
  --    `fraction_map_congr_mod_principalIdeal_of_sub_mem_principalPowerIdeal`;
  -- 4. the source-side cancellation lemma
  --    `mem_principalIdeal_of_sigma_mem_principalPowerIdeal` is ready for the kernel computation.
  --
  -- The next blocker is no longer well-definedness of the quotient class, but packaging the ring
  -- map `ψ : A → B / (g)` from `liftedNumerator`, then proving its surjectivity and kernel
  -- description before invoking the first isomorphism theorem.
  have hpow_t_mem : g ^ t ∈ N := by
    -- The transported numerator ideal already contains the distinguished power `g ^ t`.
    simpa [N] using
      pow_mem_transported_power_clearing_ideal
        (A' := A') (A := A) f g n t hinj σ hσ φ' hgen
  let ψ₀ : A → B ⧸ principalIdeal (algebraMap B' B g) := fun a ↦
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
        Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N x0, ⟨x0, rfl⟩⟩ : B) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N (0 : N),
              ⟨(0 : N), rfl⟩⟩ : B) := by
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
        Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N x1, ⟨x1, rfl⟩⟩ : B) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N y1, ⟨y1, rfl⟩⟩ : B) := by
      -- After transport, `1` and the distinguished numerator `g ^ t` define the same quotient
      -- class modulo `(g)`.
      simpa [x1, y1] using
        fraction_map_congr_mod_principalIdeal_of_sub_mem_principalPowerIdeal
          (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen
          hn_transport hn_shift
          (x := x1) (y := y1) hnum_one
    have hy1 :
        (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N y1, ⟨y1, rfl⟩⟩ : B) = 1 := by
      apply Subtype.ext
      -- Cancelling the fixed denominator `g ^ t` leaves the scalar `1`.
      simpa [y1] using
        (fraction_map_of_transported_power_clearing_ideal_mul_pow
          (g := g) (t := t) N hpow_t_mem (1 : B'))
    calc
      ψ₀ 1 =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N y1, ⟨y1, rfl⟩⟩ : B) := by
              simpa [ψ₀, liftedNumerator, x1, y1] using hcongr
      _ = Ideal.Quotient.mk (principalIdeal (algebraMap B' B g)) (1 : B) := by
            rw [hy1]
      _ = 1 := by
            simp
  have hψ₀_add : ∀ a b : A, ψ₀ (a + b) = ψ₀ a + ψ₀ b := by
    intro a b
    let xab : N := ⟨numerator (a + b), hnumerator_mem (a + b)⟩
    let yab : N := ⟨numerator a + numerator b, N.add_mem (hnumerator_mem a) (hnumerator_mem b)⟩
    have hcongr :
        Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N xab, ⟨xab, rfl⟩⟩ : B) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N yab, ⟨yab, rfl⟩⟩ : B) := by
      -- The chosen numerator for `a + b` is congruent to the sum of the chosen numerators.
      simpa [xab, yab] using
        fraction_map_congr_mod_principalIdeal_of_sub_mem_principalPowerIdeal
          (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen
          hn_transport hn_shift
          (x := xab) (y := yab)
          (numerator_add_sub_mem_principalPowerIdeal
            (A' := A') (A := A) f g n σ φ' numerator hnumerator a b)
    have hyab :
        (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N yab, ⟨yab, rfl⟩⟩ : B) =
          liftedNumerator a + liftedNumerator b := by
      apply Subtype.ext
      -- The fixed-denominator map is additive because every numerator uses the same denominator.
      simp [liftedNumerator, yab, fraction_map_of_transported_power_clearing_ideal, add_mul]
    calc
      ψ₀ (a + b) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N yab, ⟨yab, rfl⟩⟩ : B) := by
              simpa [ψ₀, liftedNumerator, xab, yab] using hcongr
      _ = Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
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
        Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N xf, ⟨xf, rfl⟩⟩ : B) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N yf, ⟨yf, rfl⟩⟩ : B) := by
      -- Modulo `(g)`, the transported numerator of `f` matches the visible scalar `g`.
      simpa [xf, yf] using
        fraction_map_congr_mod_principalIdeal_of_sub_mem_principalPowerIdeal
          (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen
          hn_transport hn_shift
          (x := xf) (y := yf) hnum_f
    have hyf :
        (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N yf, ⟨yf, rfl⟩⟩ : B) =
          algebraMap B' B g := by
      apply Subtype.ext
      -- Cancelling the fixed denominator leaves one visible factor of `g`.
      simpa [yf, pow_succ', mul_assoc, mul_left_comm, mul_comm] using
        (fraction_map_of_transported_power_clearing_ideal_mul_pow
          (g := g) (t := t) N hpow_t_mem g)
    have hclass_g :
        Ideal.Quotient.mk (principalIdeal (algebraMap B' B g)) (algebraMap B' B g : B) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton.mpr ⟨1, by simp⟩
    calc
      ψ₀ (algebraMap A' A f) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N yf, ⟨yf, rfl⟩⟩ : B) := by
              simpa [ψ₀, liftedNumerator, xf, yf] using hcongr
      _ = Ideal.Quotient.mk (principalIdeal (algebraMap B' B g)) (algebraMap B' B g : B) := by
            rw [hyf]
      _ = 0 := hclass_g
  have htn : t ≤ (n : ℕ) := Nat.le_trans (Nat.le_succ t) hn_shift
  have htail : t + 1 ≤ (n : ℕ) - t := by
    -- The eventual threshold `2 * t + 1 ≤ n` leaves one visible factor of `g` after cancelling
    -- the fixed denominator power `g ^ t`.
    exact Nat.le_sub_of_add_le (by simpa [two_mul, add_assoc, add_left_comm, add_comm] using hn_large)
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
        w.1 - numerator (a * b) ∈ principalPowerIdeal g ((n : ℕ) - t) := by
      -- Cancel the common factor `g ^ t` before descending from modulo `(g^n)` to modulo `(g)`.
      exact mem_principalPowerIdeal_of_mul_pow_mem_principalPowerIdeal
        (g := g) (n := n) (t := t) hg htn hmul_raw
    have hmul_succ :
        w.1 - numerator (a * b) ∈ principalPowerIdeal g (t + 1) := by
      -- The stronger threshold `2 * t + 1 ≤ n` upgrades the cancelled error term to one
      -- remaining visible factor of `g`.
      exact
        (show principalPowerIdeal g ((n : ℕ) - t) ≤ principalPowerIdeal g (t + 1) from
            by
              simpa [principalPowerIdeal] using
                (Ideal.pow_le_pow_right (I := principalIdeal g) htail))
          hmul_tail
    have hw_congr :
        Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N w, ⟨w, rfl⟩⟩ : B) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' B g)) (liftedNumerator (a * b)) := by
      -- After cancelling the denominator, the corrected numerator and the chosen numerator of
      -- `a * b` define the same class modulo `(g)`.
      simpa [xab, ψ₀, liftedNumerator] using
        fraction_map_congr_mod_principalIdeal_of_sub_mem_principalPowerIdeal_succ
          (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen hn_transport
          (x := w) (y := xab) hmul_succ
    have hw_mul :
        (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N w, ⟨w, rfl⟩⟩ : B) =
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
          Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N w, ⟨w, rfl⟩⟩ : B) := by
              simpa [ψ₀, liftedNumerator, xab] using hw_congr.symm
      _ = Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
            (liftedNumerator a * liftedNumerator b) := by
              rw [hw_mul]
      _ = ψ₀ a * ψ₀ b := by
            simp [ψ₀]
  let ψ : A →+* B ⧸ principalIdeal (algebraMap B' B g) :=
    { toFun := ψ₀
      map_zero' := hψ₀_zero
      map_one' := hψ₀_one
      map_add' := hψ₀_add
      map_mul' := hψ₀_mul }
  have hψ_surj : Function.Surjective ψ := by
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    rcases b with ⟨b, hb⟩
    rcases hb with ⟨x, rfl⟩
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
        Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N x,
              ⟨x, rfl⟩⟩ : B) = 0 := by
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
      B ⧸ principalIdeal (algebraMap B' B g) :=
    (Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective (f := ψ) hψ_surj)
  refine ⟨B, inferInstance, inferInstance, hB_injective, hBfinite, φ, ?_⟩
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
          principalPowerIdealReductionMap (algebraMap B' B) g
            (Nat.succ_le_of_lt n.2)
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
        Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N xc, ⟨xc, rfl⟩⟩ : B) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N yc, ⟨yc, rfl⟩⟩ : B) := by
      -- The fixed-denominator fractions of the two transported numerators already agree modulo
      -- `(g)` because their numerators differ by `(g ^ n)`.
      simpa [xc, yc] using
        fraction_map_congr_mod_principalIdeal_of_sub_mem_principalPowerIdeal
          (A' := A') (A := A) f g n t hinj σ hσ hσmul φ' hgen
          hn_transport hn_shift
          (x := xc) (y := yc) hnum_c
    have hyc :
        (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N yc, ⟨yc, rfl⟩⟩ : B) =
          algebraMap B' B d := by
      apply Subtype.ext
      -- Cancelling the fixed denominator `g ^ t` identifies the canonical base representative.
      simpa [yc, mul_comm] using
        (fraction_map_of_transported_power_clearing_ideal_mul_pow
          (g := g) (t := t) N hpow_t_mem d)
    calc
      ψ (algebraMap A' A c) =
          Ideal.Quotient.mk (principalIdeal (algebraMap B' B g))
            (⟨fraction_map_of_transported_power_clearing_ideal (g := g) t N yc, ⟨yc, rfl⟩⟩ : B) := by
              simpa [ψ, ψ₀, liftedNumerator, xc, yc] using hcongr
      _ = Ideal.Quotient.mk (principalIdeal (algebraMap B' B g)) (algebraMap B' B d : B) := by
            rw [hyc]
      _ = Ideal.Quotient.mk (principalIdeal (algebraMap B' B g)) ((algebraMap B' B) d) := by
            rfl
      _ =
          principalPowerIdealReductionMap (algebraMap B' B) g
            (Nat.succ_le_of_lt n.2)
            (Ideal.Quotient.mk (principalPowerIdeal g n) d) := by
              exact
                (Ideal.quotientMap_mk
                  (I := principalIdeal (algebraMap B' B g))
                  (J := principalPowerIdeal g n)
                  (f := algebraMap B' B)
                  (H := principalPowerIdeal_le_comap_principalIdeal
                    (algebraMap B' B) g (Nat.succ_le_of_lt n.2))
                  (x := d)).symm
      _ =
          principalPowerIdealReductionMap (algebraMap B' B) g
            (Nat.succ_le_of_lt n.2)
            (φ' (Ideal.Quotient.mk (principalPowerIdeal f n) c)) := by
              rw [hd]
  refine ⟨?_⟩
  ext x
  -- Quotient extensionality already reduces the square to a base generator `x : A'`.
  simpa [φ, principalPowerIdealReductionMap] using hψ_on_base x

end
