import Mathlib.FieldTheory.Perfect
import Mathlib.Tactic.Recall
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {k : Type u} [Field k]

/- Domain triage:
- primary domain: perfect fields and perfect rings in characteristic `ringExpChar k`;
- `source-facing`: the textbook `iff` below in terms of characteristic `0` or existence of `p`-th
  roots;
- `core/canonical`: the mathlib owners `PerfectField`, `PerfectField.toPerfectRing`, and
  `PerfectRing.toPerfectField`;
- `bridge/view`: the source-facing criterion is proved by passing through Frobenius surjectivity,
  so no extra local comparison theorem between the owner abstractions is needed.

Primitive data vs. derived API: the owner abstractions are already upstream, and the textbook
criterion is a derived bridge statement. This file should therefore reuse the existing owners
directly instead of keeping a parallel local `PerfectField ↔ PerfectRing` wrapper theorem.
-/

/- Lemma 10.45.2, owner-level forward bridge: a perfect field is a perfect ring at exponential
characteristic via the canonical instance `PerfectField.toPerfectRing`. -/
recall PerfectField.toPerfectRing

/- Lemma 10.45.2, owner-level reverse bridge: a field that is perfect as a ring is a perfect
field via `PerfectRing.toPerfectField`. -/
recall PerfectRing.toPerfectField

/-- Lemma 10.45.2, source-facing textbook form: a field is perfect if and only if either it has
characteristic `0`, or it has characteristic `p > 0` and every element admits a `p`-th root. -/
@[stacks 030Z]
theorem perfectField_iff_charZero_or_exists_pth_root :
    PerfectField k ↔
      CharZero k ∨
        ∃ p : { n : ℕ // n.Prime }, CharP k p.1 ∧ ∀ x : k, ∃ y : k, y ^ p.1 = x := by
  constructor
  · intro hk
    obtain h0 | ⟨p, hp, hpchar⟩ := CharP.exists' k
    · exact Or.inl h0
    · letI := hk
      letI := hp
      letI := hpchar
      refine Or.inr ⟨⟨p, hp.out⟩, hpchar, fun x ↦ ?_⟩
      simpa using surjective_frobenius k p x
  · rintro (h0 | ⟨p, hp, hroot⟩)
    · letI := h0
      infer_instance
    · letI : Fact p.1.Prime := ⟨p.2⟩
      letI := hp
      haveI : PerfectRing k p.1 := PerfectRing.ofSurjective k p.1 hroot
      exact PerfectRing.toPerfectField k p.1

end
