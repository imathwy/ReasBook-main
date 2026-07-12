import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Lemma_10_30_3
import StacksProject_2024.Chap10.Lemma_10_46_9

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [Algebra R S]

local notation "f" => algebraMap R S

/-
Proof sketch: apply Lemma `10.46.9` to the injective part of the bijectivity hypothesis for
`algebraMap R S` to get a closed embedding of spectra and the corresponding base-change stability
of integrality, injectivity on spectra, and purely inseparable residue-field extensions. Combine
this with Lemma `10.30.3` for surjectivity of `Spec(S) → Spec(R)` and its stability under
arbitrary base change; bijectivity is exactly injectivity together with surjectivity.
-/
/- The closed-embedding and base-change owner theorem is Lemma `10.46.9`. -/
recall integral_isClosedEmbedding_primeSpectrum_comap_and_baseChange

/- The surjectivity and base-change owner theorem is Lemma `10.30.3`. -/
recall specComap_surjective_stable_under_baseChange

/-- Lemma 10.46.10: if `R → S` is integral, induces a bijection `Spec(S) → Spec(R)`, and
induces purely inseparable residue-field extensions, then `Spec(S) → Spec(R)` is a homeomorphism.
Moreover, for every base change `R → R'`, the canonical map `R' → R' ⊗[R] S` is integral,
induces a bijection on spectra, and induces purely inseparable residue-field extensions. -/
@[stacks 0BRD]
theorem isHomeomorph_comap_and_baseChange_of_integral_bijective_and_purelyInseparableResidueFields
    (hInt : (algebraMap R S).IsIntegral)
    (hbij : Function.Bijective (comap f))
    (hres : (algebraMap R S).HasPurelyInseparableResidueFieldExtensions) :
    IsHomeomorph (comap f) ∧
      ∀ {R' : Type w} [CommRing R'] [Algebra R R'],
        let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
        f'.IsIntegral ∧
          Function.Bijective (comap f') ∧
          f'.HasPurelyInseparableResidueFieldExtensions := by
  have hinj : Function.Injective (comap f) := hbij.1
  have hsurj : Function.Surjective (comap f) := hbij.2
  rcases integral_isClosedEmbedding_primeSpectrum_comap_and_baseChange hInt hinj hres with
    ⟨hclosed, hbaseClosed⟩
  refine ⟨?_, ?_⟩
  · exact (isHomeomorph_iff_isEmbedding_surjective).2 ⟨hclosed.isEmbedding, hsurj⟩
  · intro R' _ _
    let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
    have hbaseClosed' : f'.IsIntegral ∧ Function.Injective (comap f') ∧
        f'.HasPurelyInseparableResidueFieldExtensions := by
      simpa [f'] using hbaseClosed
    rcases hbaseClosed' with ⟨hInt', hinj', hres'⟩
    have hsurj' : Function.Surjective (comap f') :=
      specComap_surjective_stable_under_baseChange hsurj
    exact ⟨hInt', ⟨hinj', hsurj'⟩, hres'⟩

end
