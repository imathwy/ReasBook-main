import Mathlib
import stacks_project.Chap10.Lemma_10_17_7

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum

universe u

section

variable {R : Type u} [CommRing R]

/- Lemma 10.24.3 is `source-facing`: the public output should be a product decomposition of `R`
whose two factor spectra identify with the given open-and-closed pieces `U` and `V`. The owner
abstractions are the canonical classification of clopen subsets of `Spec(R)` by idempotents,
the idempotent splitting `AlgEquiv.prodQuotientOfIsIdempotentElem`, and the quotient-spectrum
homeomorphism onto a zero locus. The idempotent and quotient calculations remain internal proof
data; the public API records the textbook decomposition itself. -/
/-- Lemma 10.24.3: if `Spec(R)` is the disjoint union of two open subsets `U` and `V`, then there
exist commutative rings `R₁` and `R₂`, a ring isomorphism `R ≃ R₁ × R₂`, and homeomorphisms
`Spec(R₁) ≃ U` and `Spec(R₂) ≃ V` induced by the two factor maps. -/
theorem exists_idempotent_partition_of_isCompl_open {U V : Set (PrimeSpectrum R)}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : IsCompl U V) :
    ∃ (R₁ : Type u) (_ : CommRing R₁) (R₂ : Type u) (_ : CommRing R₂)
      (φ : R ≃+* R₁ × R₂) (h₁ : PrimeSpectrum R₁ ≃ₜ U) (h₂ : PrimeSpectrum R₂ ≃ₜ V),
        (∀ p, (h₁ p).1 = comap ((RingHom.fst R₁ R₂).comp φ.toRingHom) p) ∧
          ∀ p, (h₂ p).1 = comap ((RingHom.snd R₁ R₂).comp φ.toRingHom) p := by
  have hclopenU : IsClopen U := ⟨by
    rw [hUV.eq_compl]
    exact hV.isClosed_compl, hU⟩
  obtain ⟨e, he, hUe⟩ :=
    (existsUnique_idempotent_basicOpen_eq_of_isClopen hclopenU).exists
  have hVe : V = basicOpen (1 - e) := by
    calc
      V = Uᶜ := hUV.compl_eq.symm
      _ = (basicOpen e : Set (PrimeSpectrum R))ᶜ := by rw [hUe]
      _ = basicOpen (1 - e) := by
        rw [basicOpen_eq_zeroLocus_of_isIdempotentElem e he,
          ← basicOpen_eq_zeroLocus_compl (1 - e)]
  let R₁ : Type u := R ⧸ Ideal.span ({1 - e} : Set R)
  let R₂ : Type u := R ⧸ Ideal.span ({e} : Set R)
  let φ :
      R ≃ₐ[R] (R₁ × R₂) :=
    AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he (by simp) (by simp [sub_mul, he.eq])
  let h₁ : PrimeSpectrum R₁ ≃ₜ U :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus (Ideal.span ({1 - e} : Set R))).trans
      (Homeomorph.setCongr <| by
        calc
          zeroLocus (Ideal.span ({1 - e} : Set R) : Set R) = zeroLocus ({1 - e} : Set R) := by
            rw [zeroLocus_span]
          _ = basicOpen e := by
            simpa using (basicOpen_eq_zeroLocus_of_isIdempotentElem e he).symm
          _ = U := hUe.symm)
  let h₂ : PrimeSpectrum R₂ ≃ₜ V :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus (Ideal.span ({e} : Set R))).trans
      (Homeomorph.setCongr <| by
        calc
          zeroLocus (Ideal.span ({e} : Set R) : Set R) = zeroLocus ({e} : Set R) := by
            rw [zeroLocus_span]
          _ = basicOpen (1 - e) := by
            simpa using zeroLocus_eq_basicOpen_of_isIdempotentElem e he
          _ = V := hVe.symm)
  have hfst :
      (RingHom.fst R₁ R₂).comp φ.toRingHom =
        Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) := by
    ext r
    simp [φ, R₁, R₂]
  have hsnd :
      (RingHom.snd R₁ R₂).comp φ.toRingHom =
        Ideal.Quotient.mk (Ideal.span ({e} : Set R)) := by
    ext r
    simp [φ, R₁, R₂]
  refine ⟨R₁, inferInstance, R₂, inferInstance, φ.toRingEquiv, h₁, h₂, ?_⟩
  refine ⟨?_, ?_⟩
  · intro p
    change ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus
        (Ideal.span ({1 - e} : Set R)) p).1) =
      comap ((RingHom.fst R₁ R₂).comp φ.toRingHom) p
    rw [Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_apply, ← hfst, comap_comp]
  · intro p
    change ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus
        (Ideal.span ({e} : Set R)) p).1) =
      comap ((RingHom.snd R₁ R₂).comp φ.toRingHom) p
    rw [Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_apply, ← hsnd, comap_comp]

end
