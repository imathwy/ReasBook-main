import stacks_project.Chap15.Lemma_15_11_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A) [hH : HenselianRing A I] [Algebra.IsIntegral A B]

/- Domain-style sampling:
- primary domain: henselian pairs in commutative algebra under integral base change;
- sampled owner declarations:
  `HenselianRing`,
  `Ideal.HasIntegralAlgebraIdempotentLifting`,
  `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`;
- best owner abstraction: the public conclusion is still the canonical owner
  `HenselianRing B (Ideal.map (algebraMap A B) I)`, while the idempotent-lifting clause from
  Lemma `15.11.6` is derived API used only to bridge from `(A, I)` to `(B, I B)`;
- primitive data: the ideal `I`, the owner instance `HenselianRing A I`, the integral `A`-algebra
  `B`, and the mapped ideal `Ideal.map (algebraMap A B) I`;
- derived API: integral-idempotent lifting over `A`, its transport to integral `B`-algebras by
  transitivity of integrality, and the `3 → 0` implication of the chapter TFAE.

Source/core/bridge triage:
- `source-facing`: the henselianity of the mapped pair `(B, I B)`;
- `core/canonical`: `HenselianRing` and `Ideal.HasIntegralAlgebraIdempotentLifting`;
- `bridge/view`: the transfer of the integral-idempotent lifting clause from `A` to `B`.
-/

-- Proof sketch: extract the integral-idempotent lifting clause from Lemma `15.11.6` for `(A, I)`.
-- If `C` is integral over `B`, then it is integral over `A` by scalar-tower transitivity, so the
-- same clause applies to `I B`. Applying the reverse implication of the TFAE for `(B, I B)` gives
-- the desired henselian instance.
/-- Lemma 15.11.8: if `(A, I)` is a henselian pair and `A → B` is an integral ring map, then the
pair `(B, I B)` is henselian. -/
instance ideal_map_henselianRing_of_isIntegral :
    HenselianRing B (Ideal.map (algebraMap A B) I) := by
  sorry

end
