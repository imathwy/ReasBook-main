import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_92_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: derived completeness and adic completeness for a ring viewed as a module over
  itself;
- sampled owner-side declarations:
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `powerIntersection_pow_two_pow_eq_bot_of_ring_isDerivedComplete`,
  `AdicCompletion.of_bijective_iff`,
  `nilradical_eq_zero`;
- best owner abstraction: the completion map `A → lim_n A / I^n` together with the ring-theoretic
  power intersection `⨅ n, I ^ n`;
- primitive data: the ideal `I`, finite generation `hI : I.FG`, and derived completeness of `A`
  with respect to `I`;
- derived API: the Hausdorff criterion for the self-module and the final adic-completeness
  conclusion once surjectivity of the completion map is available.

Layer triage:
- `source-facing`: Lemma `15.94.12`, which reduces adic completeness to the vanishing of the power
  intersection and the earlier surjectivity bridge from derived completeness;
- `core/canonical`: `IsAdicComplete`, `IsHausdorff`, and the completion map
  `AdicCompletion.of I A`;
- `bridge/view`: Lemma `15.94.11`, which turns derived completeness for finitely generated ideals
  into nilpotence of `⨅ n, I ^ n`. -/

/-- Helper for Lemma 15.94.12: a finitely generated ideal admits a finite generating family
indexed by `Fin r`. -/
lemma fg_generating_family (I : Ideal A) (hI : I.FG) :
    ∃ r : ℕ, ∃ f : Fin r → A, Ideal.span (Set.range f) = I := by
  obtain ⟨s, hs⟩ := hI
  let f : Fin s.card → A := fun i ↦ (s.equivFin.symm i : A)
  -- Proof comment: enumerate the finite generating set by `Fin s.card`.
  refine ⟨s.card, f, ?_⟩
  rw [← hs]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (s.equivFin.symm i).2
  · intro hx
    refine ⟨s.equivFin ⟨x, hx⟩, ?_⟩
    simp [f]

/-- Helper for Lemma 15.94.12: in a reduced ring, nilpotence of the power intersection forces the
intersection itself to vanish. -/
lemma power_intersection_eq_bot_of_nilpotent [IsReduced A] (I : Ideal A) {r : ℕ}
    (hpow : (⨅ n : ℕ, I ^ n : Ideal A) ^ (2 ^ r) = ⊥) :
    (⨅ n : ℕ, I ^ n : Ideal A) = ⊥ := by
  -- Proof comment: every element of the intersection becomes nilpotent, hence zero in a reduced
  -- ring.
  ext x
  constructor
  · intro hx
    have hxpow : x ^ (2 ^ r) = 0 := by
      have hxmem : x ^ (2 ^ r) ∈ (⨅ n : ℕ, I ^ n : Ideal A) ^ (2 ^ r) :=
        Ideal.pow_mem_pow hx _
      simpa [hpow] using hxmem
    have hxnil : x ∈ nilradical A := mem_nilradical.2 ⟨2 ^ r, hxpow⟩
    simpa [nilradical_eq_zero A] using hxnil
  · intro hx
    rw [Ideal.mem_iInf]
    intro i
    rcases Ideal.mem_bot.mp hx with rfl
    exact Ideal.zero_mem _

/-- Helper for Lemma 15.94.12: if the ideal intersection `⋂ n, I^n` is zero, then the ring `A`
is `I`-adically Hausdorff as a module over itself. -/
lemma isHausdorff_self_module_of_power_intersection_eq_bot (I : Ideal A)
    (hbot : (⨅ n : ℕ, I ^ n : Ideal A) = ⊥) :
    IsHausdorff I A := by
  -- Proof comment: lying in every `I^n A` is exactly membership in the ideal intersection.
  refine ⟨fun x hx ↦ ?_⟩
  have hx' : x ∈ (⨅ n : ℕ, I ^ n : Ideal A) := by
    rw [Ideal.mem_iInf]
    intro n
    simpa [SModEq.zero, smul_eq_mul, Ideal.one_eq_top] using hx n
  simpa [hbot] using hx'

/-- Helper for Lemma 15.94.12: derived completeness with respect to a finitely generated ideal
should force surjectivity of the completion map for the self-module. -/
theorem surjective_adicCompletion_of_self_of_isDerivedCompleteWithRespectTo_of_fg
    (I : Ideal A) (hI : I.FG) (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo I) :
    Function.Surjective (AdicCompletion.of I A) := by
  let _ := hI
  let _ := hA
  sorry

/-- Helper for Lemma 15.94.12: derived completeness with respect to a finitely generated ideal
forces a power of the ideal intersection to vanish. -/
theorem power_intersection_pow_two_pow_eq_bot_of_self_of_isDerivedCompleteWithRespectTo_of_fg
    (I : Ideal A) (r : ℕ) (hgen : ∃ f : Fin r → A, Ideal.span (Set.range f) = I)
    (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo I) :
    (⨅ n : ℕ, I ^ n : Ideal A) ^ (2 ^ r) = ⊥ := by
  let _ := hgen
  let _ := hA
  sorry

-- Proof sketch: Lemma `15.94.11` makes the power intersection `⋂ n, I^n` nilpotent. Reducedness
-- kills that nilpotent ideal, so the ring is `I`-adically Hausdorff. Once the earlier
-- surjectivity bridge from derived completeness is supplied, bijectivity of the completion map
-- gives ordinary adic completeness.
/-- Lemma 15.94.12: if a reduced ring `A`, viewed as an `A`-module, is derived complete with
respect to a finitely generated ideal `I`, then `A` is `I`-adically complete. -/
theorem isAdicComplete_of_isReduced_of_isDerivedCompleteWithRespectTo_of_fg
    [IsReduced A] (I : Ideal A) (hI : I.FG)
    (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo I) :
    IsAdicComplete I A := by
  obtain ⟨r, f, hspan⟩ := fg_generating_family I hI
  have hpow :
      (⨅ n : ℕ, I ^ n : Ideal A) ^ (2 ^ r) = ⊥ := by
    -- Proof comment: this is the nilpotence input for the power intersection.
    exact
      power_intersection_pow_two_pow_eq_bot_of_self_of_isDerivedCompleteWithRespectTo_of_fg
        I r ⟨f, hspan⟩ hA
  have hbot : (⨅ n : ℕ, I ^ n : Ideal A) = ⊥ :=
    power_intersection_eq_bot_of_nilpotent I hpow
  have hhaus : IsHausdorff I A :=
    isHausdorff_self_module_of_power_intersection_eq_bot I hbot
  have hsurj : Function.Surjective (AdicCompletion.of I A) :=
    surjective_adicCompletion_of_self_of_isDerivedCompleteWithRespectTo_of_fg I hI hA
  -- Proof comment: combine injectivity from Hausdorffness with the remaining surjectivity bridge.
  exact
    (AdicCompletion.of_bijective_iff).mp
      ⟨(AdicCompletion.of_injective_iff).mpr hhaus, hsurj⟩

end
