import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: Dedekind linear independence of multiplicative characters and its specialization
  to power characters `e ↦ α ^ e`;
- sampled owner declarations:
  `linearIndependent_monoidHom`,
  `powersHom`,
  `Fintype.linearIndependent_iff`;
- best owner abstraction: `linearIndependent_monoidHom` is the canonical owner, while the
  textbook power-sum statement is the source-facing specialization obtained by composing that owner
  with the family `α : ι → L` through `powersHom`;
- primitive data vs. derived API:
  primitive data is the finite nonempty family `α : ι → L` together with injectivity;
  derived API is the character family `powersHom L ∘ α : ι → Multiplicative ℕ →* L`, its
  coercion to functions, and the nontrivial linear combination with all coefficients equal to `1`.

Source/core/bridge triage:
- `source-facing`: existence of an exponent with nonzero power-sum;
- `core/canonical`: `linearIndependent_monoidHom`;
- `bridge/view`: `powersHom L ∘ α`.
-/

/-- Lemma 9.13.2: for a nonempty finite family of pairwise distinct elements of a commutative
ring without zero divisors, some power-sum `∑ i, αᵢ^e` is nonzero. The source states this over a
field, but the canonical owner theorem `linearIndependent_monoidHom` already works over any
commutative domain. -/
-- Proof sketch: apply the canonical owner theorem `linearIndependent_monoidHom` to the
-- multiplicative characters `χ : ι → Multiplicative ℕ →* L` given by `powersHom L ∘ α`. The
-- coefficient family with every coefficient equal to `1` is nonzero because the index type is
-- nonempty, so linear independence yields an exponent where the corresponding power-sum does not
-- vanish.
@[stacks 0EM9]
theorem exists_power_sum_ne_zero
    {L : Type u} [CommRing L] [IsDomain L] {ι : Type v} [Fintype ι] [Nonempty ι]
    (α : ι → L) (hα : Function.Injective α) :
    ∃ e : ℕ, ∑ i, α i ^ e ≠ 0 := by
  let χ : ι → Multiplicative ℕ →* L := powersHom L ∘ α
  have hχ : LinearIndependent L fun i ↦ (χ i : Multiplicative ℕ → L) := by
    simpa [χ] using
      (linearIndependent_monoidHom (Multiplicative ℕ) L).comp χ
        (by simpa [χ] using ((powersHom L).injective.comp hα))
  have hsum_ne : ∑ i, (1 : L) • (χ i : Multiplicative ℕ → L) ≠ 0 := by
    intro hsum
    have hone := (Fintype.linearIndependent_iff.mp hχ) (fun _ ↦ (1 : L)) hsum
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact one_ne_zero (hone i)
  by_contra h
  apply hsum_ne
  ext e
  simpa [χ] using (not_exists.mp h e.toAdd)
