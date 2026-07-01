import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable (R : Type u) (ι : Type v) (S : Type w)
variable [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]

/- Domain triage:
- primary domain: formal smoothness criteria for surjective polynomial presentations via the
  conormal sequence and Kähler differentials;
- sampled owner declarations:
  `Algebra.FormallySmooth.iff_split_injection`,
  `KaehlerDifferential.kerCotangentToTensor`,
  `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`,
  `KaehlerDifferential.mapBaseChange_surjective`,
  and the chapter bridge `kaehlerDifferential_exact_cotangent_tensor_of_surjective`;
- best owner abstraction: the canonical split-injection owner
  `Algebra.FormallySmooth.iff_split_injection`, specialized to the polynomial presentation
  `MvPolynomial ι R → S`;
- primitive data: the surjective polynomial presentation `algebraMap (MvPolynomial ι R) S`;
- derived API: the retraction map on the conormal morphism, expressed in owner form by the
  equation `τ ∘ₗ kerCotangentToTensor = LinearMap.id`.

This item is `source-facing`: it keeps the polynomial-presentation specialization from the source,
but there is no extra owner-level mathematics beyond the canonical split-injection criterion, so
the refined theorem should reuse that owner directly rather than restating it through
`Function.LeftInverse`. -/

-- Proof sketch: specialize `Algebra.FormallySmooth.iff_split_injection` to the chosen surjective
-- polynomial presentation `MvPolynomial ι R → S`. The map
-- `KaehlerDifferential.kerCotangentToTensor R (MvPolynomial ι R) S` is the left map
-- `J/J² → Ω[P⁄R] ⊗[P] S` in the conormal sequence, and Lemma `10.131.9` supplies the exactness
-- and surjectivity needed to read a left inverse as split exactness.
/-- Lemma 10.138.7: for a surjective polynomial presentation `MvPolynomial ι R → S`, the
`R`-algebra `S` is formally smooth over `R` if and only if the conormal map
`J/J² → Ω[MvPolynomial ι R⁄R] ⊗[MvPolynomial ι R] S` is split injective, equivalently admits a
retraction; by Lemma `10.131.9`, this is exactly the split exactness of
`0 → J/J² → Ω[MvPolynomial ι R⁄R] ⊗[MvPolynomial ι R] S → Ω[S⁄R] → 0`. -/
theorem formallySmooth_iff_polynomial_conormal_has_retraction
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S)) :
    Algebra.FormallySmooth R S ↔
      ∃ τ : S ⊗[MvPolynomial ι R] Ω[MvPolynomial ι R⁄R] →ₗ[MvPolynomial ι R]
          (RingHom.ker (algebraMap (MvPolynomial ι R) S)).Cotangent,
        τ ∘ₗ KaehlerDifferential.kerCotangentToTensor R (MvPolynomial ι R) S = LinearMap.id := by
  simpa using
    (Algebra.FormallySmooth.iff_split_injection hSurj)

end
