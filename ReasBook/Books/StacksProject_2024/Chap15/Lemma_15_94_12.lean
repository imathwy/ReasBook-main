import Mathlib
import stacks_project.Chap15.Definition_15_92_4
import stacks_project.Chap15.Lemma_15_94_11
import stacks_project.Chap15.Proposition_15_92_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A] [IsReduced A]

/- Domain-style sampling:
- primary domain: derived completeness and adic completeness for a ring viewed as a module over
  itself;
- sampled owner-side declarations:
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `ModuleCat.isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_isHausdorff`,
  `powerIntersection_pow_two_pow_eq_bot_of_ring_isDerivedComplete`,
  `nilradical_eq_zero`;
- best owner abstraction: the owner bridge from derived completeness plus `IsHausdorff` to
  `IsAdicComplete`, with Lemma `15.94.11` supplying the source-facing nilpotence input;
- primitive data: the ideal `I`, finite generation `hI : I.FG`, and derived completeness of `A`
  with respect to `I`;
- derived API: the adic-completeness conclusion and the intermediate Hausdorff property obtained
  from reducedness.

Layer triage:
- `source-facing`: Lemma `15.94.12`, which says reducedness kills the nilpotent intersection
  obstruction;
- `core/canonical`: `IsAdicComplete`, `IsHausdorff`, and
  `ModuleCat.IsDerivedCompleteWithRespectTo`;
- `bridge/view`: Lemma `15.94.11` turning derived completeness for finitely generated ideals into
  nilpotence of `⨅ n, I ^ n`. -/

-- Proof sketch: apply Proposition `15.92.5` to the `A`-module `A`. By Lemma `15.94.11`, finite
-- generation of `I` and derived completeness force the ideal intersection `⋂ n, I^n` to be
-- nilpotent. Since `A` is reduced, that nilpotent ideal is zero, giving the separatedness
-- hypothesis required by Proposition `15.92.5`.
/-- Lemma 15.94.12: if a reduced ring `A`, viewed as an `A`-module, is derived complete with
respect to a finitely generated ideal `I`, then `A` is `I`-adically complete. -/
theorem isAdicComplete_of_isReduced_of_isDerivedCompleteWithRespectTo_of_fg
    (I : Ideal A) (hI : I.FG) (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo I) :
    IsAdicComplete I A := by
  have hIfg : I.FG := hI
  obtain ⟨s, hs⟩ := hI
  let f : Fin s.card → A := fun i ↦ (s.equivFin.symm i : A)
  have hspan : Ideal.span (Set.range f) = I := by
    rw [← hs]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hx
      exact ⟨s.equivFin ⟨x, hx⟩, by simp [f]⟩
  change IsAdicComplete I (ModuleCat.of A A)
  rw [ModuleCat.isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_isHausdorff hIfg]
  refine ⟨hA, ?_⟩
  refine ⟨fun x hx ↦ ?_⟩
  have hx' : x ∈ (⨅ n : ℕ, I ^ n : Ideal A) := by
    rw [Ideal.mem_iInf]
    intro n
    simpa [SModEq.zero, smul_eq_mul, Ideal.one_eq_top] using hx n
  have hpow :
      (⨅ n : ℕ, I ^ n : Ideal A) ^ (2 ^ s.card) = ⊥ := by
    exact powerIntersection_pow_two_pow_eq_bot_of_ring_isDerivedComplete I s.card ⟨f, hspan⟩ hA
  have hxpow : x ^ (2 ^ s.card) = 0 := by
    have : x ^ (2 ^ s.card) ∈ (⨅ n : ℕ, I ^ n : Ideal A) ^ (2 ^ s.card) :=
      Ideal.pow_mem_pow hx' _
    simpa [hpow] using this
  have hxnil : x ∈ nilradical A := mem_nilradical.2 ⟨2 ^ s.card, hxpow⟩
  simpa [nilradical_eq_zero A] using hxnil

end
