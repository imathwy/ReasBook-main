import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsDomain R]

/- Lemma 10.120.3 lives in factorization theory for domains with ACCP.

Domain-style sampling:
- `WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt` is the owner bridge from ACCP on principal
  ideals to the canonical `WfDvdMonoid` abstraction.
- `WfDvdMonoid.not_unit_iff_exists_factors_eq` is the owner theorem producing irreducible
  factorizations.
- `Ideal.setOf_isPrincipal_wellFoundedOn_gt` is the converse translation back to principal ideals.

Layer triage:
- `source-facing`: this lemma is the textbook ACCP specialization for domains.
- `core/canonical`: `WfDvdMonoid` and its factorization API.
- `bridge/view`: the ACCP hypothesis is converted to the owner abstraction; the output should stay
  in the owner theorem's canonical `Multiset` form rather than a local subtype wrapper. -/
/-- Lemma 10.120.3: if a domain satisfies the ascending chain condition on principal ideals,
then every nonzero nonunit element admits a factorization into irreducible elements whose
nonemptiness is forced by the nonunit hypothesis. -/
-- Proof sketch: use `WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt` to turn the ACC
-- hypothesis on principal ideals into a `WfDvdMonoid R` structure, then apply
-- `WfDvdMonoid.not_unit_iff_exists_factors_eq` to the given nonzero nonunit element; the
-- resulting factor multiset is automatically nonempty, since the empty product is a unit.
theorem exists_irreducible_factorization_of_accp
    (hacc : {I : Ideal R | I.IsPrincipal}.WellFoundedOn (· > ·))
    {a : R} (ha0 : a ≠ 0) (ha : ¬ IsUnit a) :
    ∃ f : Multiset R, (∀ b ∈ f, Irreducible b) ∧ f.prod = a := by
  -- Convert the ACCP hypothesis into the canonical well-founded divisibility structure.
  let _ : WfDvdMonoid R := WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt hacc
  -- Apply the owner factorization theorem and drop the extra nonemptiness conclusion.
  obtain ⟨f, hf, hprod, _⟩ := (WfDvdMonoid.not_unit_iff_exists_factors_eq a ha0).1 ha
  exact ⟨f, hf, hprod⟩

end
