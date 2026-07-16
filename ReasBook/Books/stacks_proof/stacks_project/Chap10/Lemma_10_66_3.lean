import stacks_proof.stacks_project.Chap10.Lemma_10_66_2
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R] [IsReduced R]

/- Domain triage:
* `source-facing`: the textbook statement is the set equality
  `weaklyAssociatedPrimes R R = minimalPrimes R`.
* `core/canonical`: the chapter owner abstraction is the set-valued declaration
  `weaklyAssociatedPrimes R R`.
* `bridge/view`: membership in that owner set is the pointwise predicate
  `Ideal.IsWeaklyAssociatedToModule R R p` via `mem_weaklyAssociatedPrimes_iff`.

Primitive data are only the witness `x : R` in the definition of weak association. The pointwise
equivalence below is kept private and used only to recover the source-facing set equality. -/

private theorem isWeaklyAssociatedToModule_ring_iff_mem_minimalPrimes (p : Ideal R) :
    Ideal.IsWeaklyAssociatedToModule R R p ↔ p ∈ minimalPrimes R := by
  constructor
  · rintro ⟨x, hx⟩
    have hx_not_mem : x ∉ p := by
      intro hxp
      obtain ⟨y, hy, hxy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hx hxp
      have hkill : (x * y) * x = 0 := by
        rw [Ideal.mem_torsionOf_iff] at hxy
        simpa [mul_comm, mul_left_comm, mul_assoc] using hxy
      have hxy_sq : (x * y) ^ 2 = 0 := by
        calc
          (x * y) ^ 2 = ((x * y) * x) * y := by ring
          _ = 0 := by simp [hkill]
      have hxy_zero : x * y = 0 := by
        exact isNilpotent_iff_eq_zero.mp ⟨2, hxy_sq⟩
      exact hy <| by
        rw [Ideal.mem_torsionOf_iff]
        simpa [mul_comm] using hxy_zero
    change p ∈ (⊥ : Ideal R).minimalPrimes
    refine ⟨⟨hx.1.1, bot_le⟩, ?_⟩
    intro q hq hqp
    have hx_not_mem_q : x ∉ q := fun hxq ↦ hx_not_mem (hqp hxq)
    have htorsion_le : Ideal.torsionOf R R x ≤ q := by
      intro a ha
      rw [Ideal.mem_torsionOf_iff] at ha
      have hax : a * x = 0 := by
        simpa using ha
      exact (hq.1.mem_or_mem <| hax ▸ q.zero_mem).resolve_right hx_not_mem_q
    exact hx.2 ⟨hq.1, htorsion_le⟩ hqp
  · intro hp
    letI : p.IsPrime := Ideal.minimalPrimes_isPrime hp
    letI : Ring.KrullDimLE 0 (Localization.AtPrime p) :=
      Ring.KrullDimLE.of_isLocalization p hp (Localization.AtPrime p)
    let hField : IsField (Localization.AtPrime p) :=
      Ring.KrullDimLE.isField_of_isReduced
    letI : Field (Localization.AtPrime p) := hField.toField
    have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime p) = ⊥ := by
      exact IsLocalRing.isField_iff_maximalIdeal_eq.mp hField
    have hlocal :
        Ideal.IsWeaklyAssociatedToModule
          (Localization.AtPrime p) (Localization.AtPrime p)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p)) := by
      rw [hmax]
      refine ⟨1, ?_⟩
      have htorsion :
          Ideal.torsionOf (Localization.AtPrime p) (Localization.AtPrime p)
            (1 : Localization.AtPrime p) = ⊥ := by
        ext a
        rw [Ideal.mem_torsionOf_iff, Ideal.mem_bot]
        simp
      simpa [htorsion] using
        (show (⊥ : Ideal (Localization.AtPrime p)) ∈ (⊥ : Ideal (Localization.AtPrime p)).minimalPrimes by
          haveI : (⊥ : Ideal (Localization.AtPrime p)).IsPrime := Ideal.isPrime_bot
          rw [Ideal.minimalPrimes_eq_subsingleton_self]
          simp)
    exact
      (isWeaklyAssociatedToModule_iff_isWeaklyAssociatedToModule_maximalIdeal_atPrime p).mpr hlocal

/-- Lemma 10.66.3: for a reduced ring `R`, the weakly associated primes of `R` as an `R`-module
are exactly the minimal prime ideals of `R`. -/
-- Proof sketch: if `p` is weakly associated via `x`, then `p` is minimal over `ann(x)`. In a
-- reduced ring this forces `x ∉ p`: otherwise minimal-prime avoidance produces `y ∉ ann(x)` with
-- `xy ∈ ann(x)`, but then `(xy)^2 = 0`, hence `xy = 0`, contradiction. Once `x ∉ p`, any prime
-- ideal `q ≤ p` also contains `ann(x)`, so minimality over `ann(x)` gives `p ≤ q`, proving that
-- `p` is a minimal prime of `R`. Conversely, if `p` is minimal, then the localization `R_p` has
-- Krull dimension `0`; since reducedness localizes, `R_p` is a field, so its maximal ideal is
-- `(0)`, which is weakly associated to `R_p` via `1`. Lemma `10.66.2` then descends weak
-- association back to `R`.
@[stacks 0EMA]
theorem weaklyAssociatedPrimes_ring_eq_minimalPrimes :
    weaklyAssociatedPrimes R R = minimalPrimes R := by
  ext p
  simpa [mem_weaklyAssociatedPrimes_iff] using
    (isWeaklyAssociatedToModule_ring_iff_mem_minimalPrimes p :
      Ideal.IsWeaklyAssociatedToModule R R p ↔ p ∈ minimalPrimes R)

end
