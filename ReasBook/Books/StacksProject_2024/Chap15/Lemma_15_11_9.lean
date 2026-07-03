import StacksProject_2024.Chap15.Lemma_15_11_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A] (I J : Ideal A)

/- Domain-style sampling:
- primary domain: henselian pairs in commutative algebra, compared along a subideal `I ≤ J` and the
  quotient pair on `A ⧸ I`;
- sampled owner declarations:
  `HenselianRing`,
  `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`,
  `Ideal.quotientMk_bijective_idempotentMap_of_henselianRing`,
  `ideal_map_henselianRing_of_isIntegral`;
- best owner abstraction: the public statement is source-facing, but its owner-level content is
  entirely expressed by the canonical predicate `HenselianRing`; the forward/reverse comparison with
  the quotient pair should therefore be stated directly in terms of `HenselianRing`, with the
  idempotent-lifting TFAE from Lemma `15.11.6` and the quotient transfer from Lemma `15.11.8`
  treated as derived bridge API rather than repackaged here;
- primitive data: the commutative ring `A`, ideals `I ≤ J`, and the canonical quotient ideal
  `J.map (Ideal.Quotient.mk I)` in `A ⧸ I`;
- derived API: henselianity of `(A, I)`, henselianity of the quotient pair
  `((A ⧸ I), J.map (Ideal.Quotient.mk I))`, and the integral-idempotent lifting criterion used in
  the proof strategy.

Source/core/bridge triage:
- `source-facing`: the equivalence decomposing henselianity of `(A, J)` into henselianity of
  `(A, I)` together with henselianity of the quotient pair;
- `core/canonical`: `HenselianRing`;
- `bridge/view`: Lemma `15.11.6` for idempotent lifting and Lemma `15.11.8` for passing henselian
  structures to quotient pairs.
-/

-- Proof sketch: for the forward implication, apply the idempotent-lifting characterization from
-- Lemma `15.11.6` to the composite maps `B → B / I B → B / J B` for integral `A`-algebras `B`,
-- using the two henselian hypotheses to get bijectivity on idempotents for the second arrow and
-- the composition. For the converse, first descend henselianity from `(A, J)` to the quotient pair
-- `(A ⧸ I, J / I)` by Lemma `15.11.8`, then use the same composite-idempotent argument to recover
-- henselianity of `(A, I)`.
/-- Lemma 15.11.9: for ideals `I ≤ J` in a commutative ring `A`, the pair `(A, J)` is henselian if
and only if both `(A, I)` and the quotient pair `(A ⧸ I, J / I)` are henselian, where `J / I` is
the image ideal `J.map (Ideal.Quotient.mk I)` in `A ⧸ I`. -/
theorem henselianRing_iff_henselianRing_and_quotient_henselianRing (hIJ : I ≤ J) :
    HenselianRing A J ↔
      HenselianRing A I ∧
        HenselianRing (A ⧸ I) (J.map (Ideal.Quotient.mk I)) := sorry

end
