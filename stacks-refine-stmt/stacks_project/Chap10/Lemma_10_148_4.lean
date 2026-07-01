import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Unramified.Locus

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain triage:
- primary domain: formal unramifiedness and its localization-at-prime behavior;
- sampled owner declarations:
  `Algebra.FormallyUnramified`,
  `Algebra.IsUnramifiedAt`,
  `Algebra.unramifiedLocus_eq_univ_iff`,
  `Algebra.FormallyUnramified.of_isLocalization`;
- best owner abstraction: `FormallyUnramified R S`, with `IsUnramifiedAt R q` as the primewise
  localized view;
- primitive data: the algebra map `R → S`;
- derived API: localization at a prime `q` of `S`, and the further base-localized map
  `Localization.AtPrime (q.under R) → Localization.AtPrime q`.

This lemma is `source-facing`: it keeps the textbook TFAE statement, but the proof should reuse the
canonical local/global owner bridge rather than rebuilding the argument through a separate
Kähler-differential wrapper.
-/

/-- Lemma 10.148.4: for a ring map `R → S`, the following are equivalent: `R → S` is formally
unramified, every localization `R → S_q` at a prime `q` of `S` is formally unramified, and every
localized map `R_p → S_q` with `p = q ∩ R` is formally unramified. -/
-- Proof sketch: clause (2) is exactly the statement that every prime of `Spec S` lies in the
-- canonical owner `Algebra.unramifiedLocus R S`, so `(1) ↔ (2)` is
-- `Algebra.unramifiedLocus_eq_univ_iff`. For `(2) ↔ (3)`, formal unramifiedness descends along
-- restriction of scalars from `R` to `R_p`, and conversely composing the formally unramified
-- localization `R → R_p` with `R_p → S_q` recovers formal unramifiedness of `R → S_q`.
theorem formallyUnramified_localization_tfae :
    List.TFAE [
      FormallyUnramified R S,
      ∀ (q : Ideal S) [_hq : q.IsPrime], IsUnramifiedAt R q,
      ∀ (q : Ideal S) [_hq : q.IsPrime],
        FormallyUnramified (Localization.AtPrime (q.under R)) (Localization.AtPrime q)
    ] := by
  tfae_have 1 → 2 := by
    intro h q _
    letI : FormallyUnramified R S := h
    infer_instance
  tfae_have 2 → 3 := by
    intro h q _
    letI : IsUnramifiedAt R q := h q
    infer_instance
  tfae_have 3 → 2 := by
    intro h q _
    letI : FormallyUnramified (Localization.AtPrime (q.under R)) (Localization.AtPrime q) := h q
    letI : FormallyUnramified R (Localization.AtPrime (q.under R)) :=
      FormallyUnramified.of_isLocalization (q.under R).primeCompl
    exact FormallyUnramified.comp R (Localization.AtPrime (q.under R)) (Localization.AtPrime q)
  tfae_have 2 → 1 := by
    intro h
    refine unramifiedLocus_eq_univ_iff.mp ?_
    ext q
    simp [unramifiedLocus, h q.asIdeal]
  tfae_finish

end
