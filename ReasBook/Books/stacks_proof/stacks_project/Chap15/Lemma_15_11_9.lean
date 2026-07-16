import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import stacks_proof.stacks_project.Chap10.IdempotentMap
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A] (I J : Ideal A)

/-- Helper for Lemma 15.11.9: if `g` and `g ∘ f` are bijective, then `f` is bijective. -/
private theorem bijective_left_of_bijective_right_and_comp
    {α β γ : Type*} {f : α → β} {g : β → γ}
    (hg : Function.Bijective g) (hgf : Function.Bijective (g ∘ f)) :
    Function.Bijective f := by
  constructor
  · intro x y hxy
    -- Proof comment: inject through `g ∘ f`, whose injectivity is part of the composite
    -- bijectivity.
    exact hgf.1 (by simp [Function.comp, hxy])
  · intro y
    -- Proof comment: first hit `g y`, then cancel `g` using its injectivity.
    obtain ⟨x, hx⟩ := hgf.2 (g y)
    refine ⟨x, hg.1 ?_⟩
    simpa [Function.comp] using hx

/-- Helper for Lemma 15.11.9: the quotient-of-a-quotient equivalence induces a bijection on
idempotents. -/
private theorem ringEquiv_bijective_idempotentMap {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    Function.Bijective e.toRingHom.idempotentMap := by
  constructor
  · intro x y hxy
    -- Proof comment: compare the underlying elements and use injectivity of the equivalence.
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val hxy)
  · intro y
    -- Proof comment: lift the idempotent back along the inverse equivalence.
    refine ⟨⟨e.symm y.1, y.2.map e.symm.toRingHom⟩, ?_⟩
    apply Subtype.ext
    exact e.apply_symm_apply y.1

/-- Helper for Lemma 15.11.9: along `I ≤ J`, the idempotent map for the second quotient morphism
`R ⧸ I → R ⧸ J` composed with the first quotient map is the direct quotient map `R → R ⧸ J`. -/
private theorem quotientMap_idempotentMap_comp_quotientMk_idempotentMap
    {R : Type*} [CommRing R] {I J : Ideal R} (hIJ : I ≤ J) :
    RingHom.idempotentMap (Ideal.quotientMap J (RingHom.id R) hIJ) ∘
        (Ideal.Quotient.mk I).idempotentMap =
      (Ideal.Quotient.mk J).idempotentMap := by
  funext e
  apply Subtype.ext
  -- Proof comment: reduce to the ring-hom identity `quotientMap_comp_mk`.
  change ((Ideal.quotientMap J (RingHom.id R) hIJ).comp (Ideal.Quotient.mk I)) e.1 =
    (Ideal.Quotient.mk J) e.1
  rw [Ideal.quotientMap_comp_mk]
  rfl

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
@[stacks 0DYD]
theorem henselianRing_iff_henselianRing_and_quotient_henselianRing (hIJ : I ≤ J) :
    HenselianRing A J ↔
      HenselianRing A I ∧
        HenselianRing (A ⧸ I) (J.map (Ideal.Quotient.mk I)) := by
  -- Route correction: the local quotient-composition helpers above now implement the source chain
  -- `B → B / I B → B / J B`; the only remaining gap is the unavailable compiled bridge API from
  -- Lemmas `15.11.6` and `15.11.8` that converts henselianity to/from integral idempotent lifting.
  -- TODO: once those compiled clauses are available in import scope, specialize the `0 ↔ 3` branch
  -- of Lemma `15.11.6` to `I`, `J`, and `J / I`, transport the quotient-pair hypothesis across
  -- `DoubleQuot.quotQuotEquivQuotOfLE`, and close the forward implication with
  -- `bijective_left_of_bijective_right_and_comp`.
  sorry

end
