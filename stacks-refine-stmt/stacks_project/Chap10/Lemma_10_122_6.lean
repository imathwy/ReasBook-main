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
private theorem isPrime_map_away_mul (f : R) (g : S) (q : Ideal S) [q.IsPrime]
    (hf : f ∉ q.under R) (hg : g ∉ q) :
    (q.map (algebraMap S (Localization.Away ((algebraMap R S f) * g)))).IsPrime := by
  refine IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers ((algebraMap R S f) * g))
    (Localization.Away ((algebraMap R S f) * g)) q inferInstance ?_
  rw [Set.disjoint_left]
  intro x hxM hxq
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hxM
  have hqPrime : q.IsPrime := inferInstance
  rcases hqPrime.mem_or_mem (by simpa [mul_pow] using hxq) with hfq | hgq
  · exact hf <| hqPrime.mem_of_pow_mem n hfq
  · exact hg <| hqPrime.mem_of_pow_mem n hgq

-- Proof sketch: localize `R → S` away from `f` on the source and away from `g` on the target.
-- The canonical owner API proves this by base change and the inverse localization-on-stalks map.
-- The finite-type hypothesis appearing in the source is redundant for `Algebra.QuasiFiniteAt`.
/-- Lemma 10.122.6: if `q` is a prime of `S`, `f` avoids `q ∩ R`, and `g` avoids `q`, then
`R → S` is quasi-finite at `q` iff the localized map `R_f → S_{fg}` is quasi-finite at the
extended prime `qS_{fg}`. -/
theorem quasiFiniteAt_iff_quasiFiniteAt_away_mul (f : R) (g : S) (q : Ideal S) [q.IsPrime]
    (hf : f ∉ q.under R) (hg : g ∉ q) :
    let fg : S := (algebraMap R S f) * g
    let qfg : Ideal (Localization.Away fg) := q.map (algebraMap S (Localization.Away fg))
    letI : qfg.IsPrime := isPrime_map_away_mul f g q hf hg
    letI : Algebra (Localization.Away f) (Localization.Away fg) :=
      ((IsLocalization.Away.awayToAwayRight (algebraMap R S f) g).comp
        (Localization.awayMap (algebraMap R S) f)).toAlgebra
    Algebra.QuasiFiniteAt R q ↔
      Algebra.QuasiFiniteAt (Localization.Away f) qfg := sorry

end
