import Mathlib
import StacksProject_2024.Chap10.Definition_10_135_1
import StacksProject_2024.Chap10.Lemma_10_137_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

namespace IsRelativeGlobalCompleteIntersection

/-- Over a field, a relative global complete intersection is already a global complete
intersection. -/
theorem isGlobalCompleteIntersection (hS : IsRelativeGlobalCompleteIntersection k S) :
    IsGlobalCompleteIntersection k S := by
  by_cases hsub : Subsingleton S
  · let _ : Subsingleton S := hsub
    infer_instance
  · letI : Nontrivial S := not_subsingleton_iff_nontrivial.mp hsub
    rcases hS.exists_presentation with ⟨n, c, P, hP⟩
    let p : PrimeSpectrum k := ⟨⊥, Ideal.isPrime_bot⟩
    let φ : k →ₐ[k] p.asIdeal.ResidueField := IsScalarTower.toAlgHom k k p.asIdeal.ResidueField
    have hκ : Function.Bijective φ := by
      constructor
      · exact RingHom.injective _
      · simpa [p] using (Ideal.algebraMap_residueField_surjective (⊥ : Ideal k))
    let eκ : p.asIdeal.ResidueField ≃ₐ[k] k :=
      (AlgEquiv.ofBijective φ hκ).symm
    let e : p.asIdeal.Fiber S ≃ₐ[k] S :=
      (Algebra.TensorProduct.congr eκ (AlgEquiv.refl : S ≃ₐ[k] S)).trans
        (Algebra.TensorProduct.lid k S)
    have hp : ringKrullDim (p.asIdeal.Fiber S) = P.dimension := by
      letI : Nontrivial (p.asIdeal.Fiber S) := e.toRingHom.domain_nontrivial
      exact hP p inferInstance
    refine ⟨Or.inr ⟨n, c, P, ?_⟩⟩
    calc
      ringKrullDim S = ringKrullDim (p.asIdeal.Fiber S) := by
        simpa using (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm
      _ = P.dimension := hp

end IsRelativeGlobalCompleteIntersection

-- Proof sketch: use the canonical smooth basic-open cover by standard smooth localizations.
-- Lemma `10.137.6` makes each standard smooth chart a relative global complete intersection, and
-- over a field that owner specializes to a global complete intersection. Packaging the resulting
-- finite cover gives the source-facing local complete intersection owner.
/-- Lemma 10.137.4: every smooth `k`-algebra is a local complete intersection over `k`. -/
instance smooth_isLocalCompleteIntersection [Smooth k S] :
    IsLocalCompleteIntersection k S := by
  obtain ⟨s, hsone, hsstd⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth k S
  obtain ⟨t, hts, htone⟩ := (Ideal.span_eq_top_iff_finite s).mp hsone
  refine ⟨t, htone, ?_⟩
  intro g hg
  let _ : IsStandardSmooth k (Localization.Away g) := hsstd g (hts hg)
  let _ : IsRelativeGlobalCompleteIntersection k (Localization.Away g) :=
    IsStandardSmooth.isRelativeGlobalCompleteIntersection inferInstance
  exact IsRelativeGlobalCompleteIntersection.isGlobalCompleteIntersection inferInstance

end Algebra
