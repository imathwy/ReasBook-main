import Mathlib
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_21_1 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R]

/- Domain-style sampling for Lemma 10.21.1:
- primary domain: idempotents and the topology of `Spec(R)`;
- sampled owner declarations:
  `PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem`,
  `PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem`,
  `PrimeSpectrum.isClopen_iff`,
  `PrimeSpectrum.isClopen_iff_zeroLocus`;
- best owner abstraction: the canonical `PrimeSpectrum` owner lemmas describing the basic open and
  zero locus attached to an idempotent;
- primitive data: a commutative ring `R`, an element `e : R`, and the proof that `e` is
  idempotent;
- derived API: clopen descriptions of subsets of `Spec(R)` and the decomposition of `Spec(R)` by
  complementary idempotents.

Source/core/bridge triage:
- `source-facing`: the textbook identification `D(e) = V(1 - e)` and its companion
  `V(e) = D(1 - e)` for an idempotent `e`;
- `core/canonical`: the upstream owner lemmas in `PrimeSpectrum`;
- `bridge/view`: the later clopen and decomposition results that reuse these owner lemmas.

This item adds no new mathematical data, so the file should recall the owner declarations directly
instead of keeping a parallel local theorem or alias.
-/
/- Lemma 10.21.1: for an idempotent `e : R`, the standard open `D(e)` is the zero locus
`V(1 - e)`. Together with `basicOpen_eq_zeroLocus_compl`, this is exactly the
standard decomposition `Spec(R) = D(e) ⨿ D(1 - e)`. -/
recall PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem

/- Companion recall: equivalently, `V(e) = D(1 - e)` for an idempotent `e`. -/
recall PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem

end

/-! ### Lemma_10_21_2 (from Chap10) -/
universe u v

section

variable {R₁ : Type u} {R₂ : Type v} [CommSemiring R₁] [CommSemiring R₂]

/- Lemma 10.21.2 (00ED): if `R = R₁ × R₂`, then the projection maps `R → R₁` and `R → R₂`
induce continuous maps `Spec(R₁) → Spec(R)` and `Spec(R₂) → Spec(R)`, and the induced map from
the disjoint union `Spec(R₁) ⨿ Spec(R₂)` to `Spec(R)` is a homeomorphism. Equivalently, this is
the owner-level mathlib homeomorphism `PrimeSpectrum (R₁ × R₂) ≃ₜ PrimeSpectrum R₁ ⊕
PrimeSpectrum R₂`, whose ring-specialized form is exactly the source statement.
-/
recall PrimeSpectrum.primeSpectrumProdHomeo

end

/-! ### Lemma_10_21_3 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R]

/- Lemma 10.21.3: for a commutative ring `R`, every open and closed subset `U ⊆ Spec(R)` is of
the form `D(e)` for a unique idempotent `e ∈ R`. This is exactly the canonical theorem
`PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen`. -/
recall PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen

/- Companion recall: the induced one-to-one correspondence between idempotents of `R` and clopen
subsets of `Spec(R)` is the canonical order isomorphism
`PrimeSpectrum.isIdempotentElemEquivClopens`. -/
recall PrimeSpectrum.isIdempotentElemEquivClopens

end

/-! ### Lemma_10_21_4 (from Chap10) -/
universe u

open PrimeSpectrum TopologicalSpace

section

variable {R : Type u} [CommRing R] [Nontrivial R]

/- Lemma 10.21.4 is a `bridge/view` item. Its owner abstractions are
`PrimeSpectrum.isIdempotentElemEquivClopens` for clopen subsets of `Spec(R)` and
`connectedSpace_iff_clopen` for connectedness. The theorem below is the source-facing unpacking of
those canonical declarations. -/
/-- Lemma 10.21.4: for a nonzero commutative ring `R`, the prime spectrum `Spec(R)` is connected if
and only if every idempotent of `R` is trivial. -/
theorem primeSpectrum_connectedSpace_iff_idempotents_trivial :
    ConnectedSpace (PrimeSpectrum R) ↔
      ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  let eToClopen : {e : R // IsIdempotentElem e} ≃o Clopens (PrimeSpectrum R) :=
    isIdempotentElemEquivClopens
  have htrivial :
      (∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) ↔
        ∀ s : Clopens (PrimeSpectrum R), s = ⊥ ∨ s = ⊤ := by
    constructor
    · intro htriv s
      let e := eToClopen.symm s
      rcases htriv e.1 e.2 with he | he
      · left
        have he' : e = eToClopen.symm ⊥ := by
          rw [isIdempotentElemEquivClopens_symm_bot]
          ext
          exact he
        exact eToClopen.symm.injective he'
      · right
        have he' : e = eToClopen.symm ⊤ := by
          rw [isIdempotentElemEquivClopens_symm_top]
          ext
          exact he
        exact eToClopen.symm.injective he'
    · intro hclopen e he
      let e' : {e : R // IsIdempotentElem e} := ⟨e, he⟩
      rcases hclopen (eToClopen e') with hs | hs
      · left
        have he' : e' = eToClopen.symm ⊥ := by
          simpa using congrArg eToClopen.symm hs
        simpa [eToClopen] using congrArg Subtype.val he'
      · right
        have he' : e' = eToClopen.symm ⊤ := by
          simpa using congrArg eToClopen.symm hs
        simpa [eToClopen] using congrArg Subtype.val he'
  constructor
  · intro hconn
    exact htrivial.mpr fun s ↦ by
      rcases (connectedSpace_iff_clopen.mp hconn).2 s s.isClopen with hs | hs
      · left
        exact Clopens.ext hs
      · right
        exact Clopens.ext hs
  · intro htriv
    refine connectedSpace_iff_clopen.mpr ?_
    refine ⟨nonempty_iff_nontrivial.mpr inferInstance, fun s hs ↦ ?_⟩
    rcases htrivial.mp htriv ⟨s, hs⟩ with ht | ht
    · left
      simpa using congrArg (fun u : Clopens (PrimeSpectrum R) ↦ (u : Set (PrimeSpectrum R))) ht
    · right
      simpa using congrArg (fun u : Clopens (PrimeSpectrum R) ↦ (u : Set (PrimeSpectrum R))) ht

end

/-! ### Lemma_10_21_5 (from Chap10) -/
universe u

open PrimeSpectrum

section

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 10.21.5: the principal-ideal notation `R ∙ e` is the singleton-span ideal
`Ideal.span {e}`. -/
private lemma principal_span_singleton_bridge (e : R) :
    (R ∙ e : Ideal R) = Ideal.span ({e} : Set R) := rfl

/-- Lemma 10.21.5 (1): if a finitely generated ideal `I` satisfies `I = I ^ 2`, then `I` is
generated by an idempotent element. -/
-- Proof sketch: rewrite `I = I ^ 2` as `IsIdempotentElem I`, then apply the finitely generated
-- ideal criterion `Ideal.isIdempotentElem_iff_of_fg`.
theorem exists_idempotent_generator_of_fg_of_sq {I : Ideal R} (hfg : I.FG) (hI2 : I = I ^ 2) :
    ∃ e : R, IsIdempotentElem e ∧ I = R ∙ e := by
  -- Convert the hypothesis `I = I ^ 2` into the ideal-idempotence predicate expected by the owner
  -- theorem for finitely generated ideals.
  have hI : IsIdempotentElem I := by
    simpa [IsIdempotentElem, pow_two] using hI2.symm
  -- The canonical finitely generated idempotent-ideal criterion produces the required generator.
  exact (Ideal.isIdempotentElem_iff_of_fg I hfg).mp hI

/-- Lemma 10.21.5 (2): if `I` is generated by an idempotent element `e`, then `R ⧸ I` is the
localization of `R` away from `1 - e`. -/
-- Proof sketch: replace `I` by the principal ideal `R ∙ e`, use
-- `IsLocalization.Away.quotient_of_isIdempotentElem` for `1 - e`, and transport the resulting
-- localization structure across the canonical quotient identification.
theorem quotient_isLocalization_Away_one_sub_of_idempotent_generator {I : Ideal R} {e : R}
    (he : IsIdempotentElem e) (hIe : I = R ∙ e) :
    IsLocalization.Away (1 - e) (R ⧸ I) := by
  -- First rewrite the quotient by `I` into the quotient by the principal idempotent ideal.
  subst I
  -- Rewrite the singleton generator `{e}` as `{1 - (1 - e)}` so that the owner theorem applies
  -- verbatim to the complementary idempotent `1 - e`.
  have hsingleton : ({e} : Set R) = ({1 - (1 - e)} : Set R) := by
    ext x
    simp [sub_sub_cancel]
  rw [principal_span_singleton_bridge, hsingleton]
  exact IsLocalization.Away.quotient_of_isIdempotentElem he.one_sub

/-- Lemma 10.21.5 (3): if `I` is generated by an idempotent element `e`, then `V(I) = D(1 - e)`
in `Spec(R)`. -/
-- Proof sketch: rewrite `I` as the principal ideal `R ∙ e`, identify its zero locus with the
-- zero locus of the singleton `{e}`, and apply the standard idempotent basic-open description.
theorem zeroLocus_eq_basicOpen_one_sub_of_idempotent_generator {I : Ideal R} {e : R}
    (he : IsIdempotentElem e) (hIe : I = R ∙ e) :
    zeroLocus (I : Set R) = basicOpen (1 - e) := by
  -- First rewrite `V(I)` to the principal idempotent ideal case.
  subst I
  -- Rewrite `V(I)` as the zero locus of the singleton generator `{e}`.
  rw [principal_span_singleton_bridge, PrimeSpectrum.zeroLocus_span]
  -- The standard idempotent description identifies `V(e)` with the basic open `D(1 - e)`.
  simpa using PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem e he

end
