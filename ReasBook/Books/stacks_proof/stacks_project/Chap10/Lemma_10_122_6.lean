import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain triage:
* primary domain: quasi-finiteness at a prime under localization away from elements;
* sampled owner declarations:
  `Algebra.QuasiFiniteAt`,
  `Algebra.QuasiFiniteAt.baseChange`,
  `Algebra.QuasiFiniteAt.of_surjectiveOnStalks`,
  `IsLocalization.isPrime_of_isPrime_disjoint`;
* source-facing layer: `quasiFiniteAt_iff_quasiFiniteAt_away_mul`;
* core/canonical owner: `Algebra.QuasiFiniteAt`;
* bridge/view: the localized prime
  `q.map (algebraMap S (Localization.Away ((algebraMap R S f) * g)))` and the induced algebra
  `Localization.Away f → Localization.Away ((algebraMap R S f) * g)`.

Primitive data are only `f : R`, `g : S`, and the prime `q : Ideal S`. The localized prime and the
comparison algebra are derived from the owner abstraction, so they should not survive as separate
public wrapper declarations. The finite-type hypothesis from the source is redundant here: the
equivalence is a formal property of `Algebra.QuasiFiniteAt` under the canonical localization maps.
-/

-- Proof sketch: `q` is disjoint from the powers of `(algebraMap R S f) * g` because neither
-- `algebraMap R S f` nor `g` lies in `q`; then `IsLocalization.isPrime_of_isPrime_disjoint`
-- gives the corresponding prime in the localization.
/-- Helper for Chap10 Lemma 10 122 6: the powers of the product used for the target localization
avoid the given prime. -/
private theorem powersAwayMulDisjointPrime (f : R) (g : S) (q : Ideal S) [q.IsPrime]
    (hf : f ∉ q.under R) (hg : g ∉ q) :
    Disjoint (Submonoid.powers ((algebraMap R S f) * g) : Set S) q := by
  -- The only possible intersection would force a power of one factor into the prime.
  rw [Set.disjoint_left]
  intro x hxM hxq
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hxM
  have hqPrime : q.IsPrime := inferInstance
  rcases hqPrime.mem_or_mem (by simpa [mul_pow] using hxq) with hfq | hgq
  · exact hf <| hqPrime.mem_of_pow_mem n hfq
  · exact hg <| hqPrime.mem_of_pow_mem n hgq

/-- Helper for Chap10 Lemma 10 122 6: extending the prime to the localization away from the
product remains prime. -/
private theorem isPrime_map_away_mul (f : R) (g : S) (q : Ideal S) [q.IsPrime]
    (hf : f ∉ q.under R) (hg : g ∉ q) :
    (q.map (algebraMap S (Localization.Away ((algebraMap R S f) * g)))).IsPrime := by
  -- This is the standard localization-primality criterion applied to the disjointness helper.
  exact IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers ((algebraMap R S f) * g))
    (Localization.Away ((algebraMap R S f) * g)) q inferInstance
    (powersAwayMulDisjointPrime f g q hf hg)

/-- Helper for Chap10 Lemma 10 122 6: the prime extended to `S[(fg)⁻¹]` contracts back to `q`. -/
private theorem comap_map_awayMul (f : R) (g : S) (q : Ideal S) [q.IsPrime]
    (hf : f ∉ q.under R) (hg : g ∉ q) :
    (q.map (algebraMap S (Localization.Away ((algebraMap R S f) * g)))).comap
        (algebraMap S (Localization.Away ((algebraMap R S f) * g))) = q := by
  -- The contraction formula uses the same disjointness side condition as primality.
  simpa using
    (IsLocalization.comap_map_of_isPrime_disjoint
      (Submonoid.powers ((algebraMap R S f) * g))
      (Localization.Away ((algebraMap R S f) * g))
      (show q.IsPrime from inferInstance)
      (powersAwayMulDisjointPrime f g q hf hg))

/-- Helper for Chap10 Lemma 10 122 6: localization at a submonoid does not change the
quasi-finite stalk over the contracted prime. -/
private theorem quasiFiniteAt_iff_quasiFiniteAt_of_localization_comap (M : Submonoid S)
    (q : Ideal S) [q.IsPrime] (Q : Ideal (Localization M)) [Q.IsPrime]
    (hcomap : Ideal.comap (algebraMap S (Localization M)) Q = q) :
    Algebra.QuasiFiniteAt R q ↔ Algebra.QuasiFiniteAt R Q := by
  -- The canonical two-step localization equivalence identifies the two local rings over `R`.
  have hiff :
      Algebra.QuasiFinite R (Localization.AtPrime (Ideal.comap (algebraMap S (Localization M)) Q)) ↔
        Algebra.QuasiFinite R (Localization.AtPrime Q) := by
    exact Algebra.QuasiFinite.iff_of_algEquiv
      ((IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := M) Q).restrictScalars R)
  exact hcomap ▸ hiff

/-- Helper for Chap10 Lemma 10 122 6: localizing the target away from
`(algebraMap R S f) * g` does not change quasi-finiteness at `q` over the original base. -/
private theorem quasiFiniteAt_iff_quasiFiniteAt_awayMul_sameBase (f : R) (g : S)
    (q : Ideal S) [q.IsPrime] (hf : f ∉ q.under R) (hg : g ∉ q) :
    let fg : S := (algebraMap R S f) * g
    let qfg : Ideal (Localization.Away fg) := q.map (algebraMap S (Localization.Away fg))
    letI : qfg.IsPrime := isPrime_map_away_mul f g q hf hg
    Algebra.QuasiFiniteAt R q ↔ Algebra.QuasiFiniteAt R qfg := by
  -- The contraction helper puts the localization-comparison theorem in the needed normal form.
  dsimp
  let fg : S := (algebraMap R S f) * g
  let qfg : Ideal (Localization.Away fg) := q.map (algebraMap S (Localization.Away fg))
  haveI : qfg.IsPrime := isPrime_map_away_mul f g q hf hg
  have hcomap : Ideal.comap (algebraMap S (Localization.Away fg)) qfg = q := by
    simpa [fg, qfg] using comap_map_awayMul f g q hf hg
  exact quasiFiniteAt_iff_quasiFiniteAt_of_localization_comap
    (R := R) (S := S) (M := Submonoid.powers fg) q qfg hcomap

/-- Helper for Chap10 Lemma 10 122 6: a quasi-finite intermediate base does not change
quasi-finiteness at a target prime. -/
private theorem quasiFiniteAt_iff_quasiFiniteAt_of_quasiFiniteBase
    {A : Type*} {T : Type*} [CommRing A] [CommRing T]
    [Algebra R A] [Algebra A T] [Algebra R T] [IsScalarTower R A T]
    [Algebra.QuasiFinite R A] (p : Ideal T) [p.IsPrime] :
    Algebra.QuasiFiniteAt R p ↔ Algebra.QuasiFiniteAt A p := by
  -- One direction restricts scalars; the other composes with the quasi-finite base algebra.
  constructor
  · intro hp
    letI : Algebra.QuasiFinite R (Localization.AtPrime p) := hp
    exact Algebra.QuasiFinite.of_restrictScalars R A (Localization.AtPrime p)
  · intro hp
    letI : Algebra.QuasiFinite A (Localization.AtPrime p) := hp
    exact Algebra.QuasiFinite.trans R A (Localization.AtPrime p)

-- Proof sketch: localize `R → S` away from `f` on the source and away from `g` on the target.
-- The canonical owner API proves this by base change and the inverse localization-on-stalks map.
-- The finite-type hypothesis appearing in the source is redundant for `Algebra.QuasiFiniteAt`.
/-- Chap10 Lemma 10 122 6: if `q` is a prime of `S`, `f` avoids `q ∩ R`, and `g` avoids `q`, then
`R → S` is quasi-finite at `q` iff the localized map `R_f → S_{fg}` is quasi-finite at the
extended prime `qS_{fg}`. -/
@[stacks 077H]
theorem quasiFiniteAt_iff_quasiFiniteAt_away_mul (f : R) (g : S) (q : Ideal S) [q.IsPrime]
    (hf : f ∉ q.under R) (hg : g ∉ q) :
    let fg : S := (algebraMap R S f) * g
    let qfg : Ideal (Localization.Away fg) := q.map (algebraMap S (Localization.Away fg))
    letI : qfg.IsPrime := isPrime_map_away_mul f g q hf hg
    letI : Algebra (Localization.Away f) (Localization.Away fg) :=
      ((IsLocalization.Away.awayToAwayRight (algebraMap R S f) g).comp
        (Localization.awayMap (algebraMap R S) f)).toAlgebra
    Algebra.QuasiFiniteAt R q ↔
      Algebra.QuasiFiniteAt (Localization.Away f) qfg := by
  -- First pass from `q` to the localized target over `R`, then replace the base by `R_f`.
  dsimp
  let fg : S := (algebraMap R S f) * g
  let qfg : Ideal (Localization.Away fg) := q.map (algebraMap S (Localization.Away fg))
  haveI : qfg.IsPrime := isPrime_map_away_mul f g q hf hg
  letI : Algebra (Localization.Away f) (Localization.Away fg) :=
    ((IsLocalization.Away.awayToAwayRight (algebraMap R S f) g).comp
      (Localization.awayMap (algebraMap R S) f)).toAlgebra
  haveI : IsScalarTower R (Localization.Away f) (Localization.Away fg) := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    simp only [fg, RingHom.algebraMap_toAlgebra, RingHom.coe_comp, Function.comp_apply,
      Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq,
      IsLocalization.Away.awayToAwayRight_eq]
    exact IsScalarTower.algebraMap_apply R S (Localization.Away ((algebraMap R S f) * g)) r
  exact (quasiFiniteAt_iff_quasiFiniteAt_awayMul_sameBase f g q hf hg).trans
    (quasiFiniteAt_iff_quasiFiniteAt_of_quasiFiniteBase
      (R := R) (A := Localization.Away f) (T := Localization.Away fg) qfg)

end
